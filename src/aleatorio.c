// RCOM 2026/2027
//
// Link layer protocol implementation

#define _POSIX_SOURCE 1 // POSIX compliant source (must come before the includes)

#include "link_layer.h"
#include "serial_port.h"

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>

/// MISC
#define BUF_SIZE 256

// Supervision frames: FLAG | A | C | BCC1 (= A ^ C) | FLAG
// SET: sent by the Transmitter (A = 0x03, C = 0x03, BCC1 = 0x03 ^ 0x03 = 0x00)
static const unsigned char SET_FRAME[5] = {0x7E, 0x03, 0x03, 0x00, 0x7E};
// UA: sent by the Receiver as the reply (A = 0x03, C = 0x07, BCC1 = 0x03 ^ 0x07 = 0x04)
static const unsigned char UA_FRAME[5] = {0x7E, 0x03, 0x07, 0x04, 0x7E};
// RR0 / RR1: sent by the Receiver to accept an I frame (A = 0x03, C = 0xAA / 0xAB, BCC1 = 0xA9 / 0xA8)
static const unsigned char RR_FRAME[2][5] = {{0x7E, 0x03, 0xAA, 0xA9, 0x7E}, {0x7E, 0x03, 0xAB, 0xA8, 0x7E}};
// REJ0 / REJ1: sent by the Receiver to reject an I frame with errors (A = 0x03, C = 0x54 / 0x55, BCC1 = 0x57 / 0x56)
static const unsigned char REJ_FRAME[2][5] = {{0x7E, 0x03, 0x54, 0x57, 0x7E}, {0x7E, 0x03, 0x55, 0x56, 0x7E}};
// DISC: sent by the Transmitter to end the connection (A = 0x03, C = 0x0B, BCC1 = 0x03 ^ 0x0B = 0x08)
static const unsigned char DISC_TX_FRAME[5] = {0x7E, 0x03, 0x0B, 0x08, 0x7E};
// DISC: sent by the Receiver as the reply (A = 0x01, C = 0x0B, BCC1 = 0x01 ^ 0x0B = 0x0A)
static const unsigned char DISC_RX_FRAME[5] = {0x7E, 0x01, 0x0B, 0x0A, 0x7E};
// UA: sent by the Transmitter as the reply to the Receiver's DISC (A = 0x01, C = 0x07, BCC1 = 0x01 ^ 0x07 = 0x06)
static const unsigned char UA_TX_FRAME[5] = {0x7E, 0x01, 0x07, 0x06, 0x7E};

// Information frames: FLAG | A | C | BCC1 | D1..Dn | BCC2 | FLAG
// (A = 0x03, C = 0x00 / 0x80 for the frame number 0 / 1, BCC2 = D1 ^ D2 ^ ... ^ Dn)
// Byte stuffing of D1..Dn and BCC2: FLAG -> ESC 0x5E, ESC -> ESC 0x5D (the byte ^ 0x20)
#define FLAG 0x7E
#define ESC 0x7D

// States of the supervision frame state machine
typedef enum { START, FLAG_RCV, A_RCV, C_RCV, BCC_OK, STOP } State;

// Set to 1 while waiting for a frame, cleared to 0 by the alarm handler on timeout
static volatile sig_atomic_t alarmEnabled = 0;

// Alarm handler: called when SIGALRM is triggered
static void alarmHandler(int sig) { alarmEnabled = 0; }

// Link layer parameters, saved by llOpen (needed by llSend and llClose)
static LinkLayer parameters;

// Number (0 or 1) of the next I frame to send (Tx) or to receive (Rx)
static int frameNumber = 0;

// Statistics printed by llClose
static int framesCount = 0;    // I frames sent (Tx) or received (Rx), without repetitions
static int timeoutCount = 0;   // timeouts while waiting for RR (Tx)
static int rejCount = 0;       // REJ received (Tx) or sent (Rx)
static int duplicateCount = 0; // repeated I frames received and discarded (Rx)

// Reads bytes from the serial port and, using a state machine, waits for the
// supervision frame `expected` (5 bytes).
// Returns 0 if the frame was received, -1 if the alarm fired first.
static int waitFrame(const unsigned char *expected)
{
    State state = START;
    unsigned char byte;

    while (state != STOP && alarmEnabled)
    {
        // Read one byte (a read interrupted by the alarm returns -1)
        if (readByteSerialPort(&byte) <= 0)
            continue;

        printf("byte = 0x%02X\n", byte); // debug

        switch (state)
        {
        case START:
            // Waiting for the initial FLAG
            if (byte == expected[0]) state = FLAG_RCV;
            break;
        case FLAG_RCV:
            // FLAG received, expecting the A field
            if (byte == expected[1]) state = A_RCV;
            else if (byte != expected[0]) state = START;
            break;
        case A_RCV:
            // A received, expecting the C field
            if (byte == expected[2]) state = C_RCV;
            else if (byte == expected[0]) state = FLAG_RCV;
            else state = START;
            break;
        case C_RCV:
            // C received, expecting BCC1 (A ^ C)
            if (byte == expected[3]) state = BCC_OK;
            else if (byte == expected[0]) state = FLAG_RCV;
            else state = START;
            break;
        case BCC_OK:
            // BCC1 is correct, expecting the final FLAG
            if (byte == expected[4]) state = STOP;
            else state = START;
            break;
        default:
            break;
        }
    }
    return state == STOP ? 0 : -1;
}

// Reads bytes from the serial port and, using a state machine, waits for any
// frame with A = 0x03 and a correct BCC1 (I frame, SET, RR or REJ).
// The bytes between BCC1 and the final FLAG (data and BCC2 of an I frame) are
// saved without byte stuffing in `data` (MAX_PAYLOAD_SIZE + 1 bytes) and their number in `size`.
// Returns the C field of the frame, or -1 if the alarm fired first.
static int readFrame(unsigned char *data, int *size)
{
    State state = START;
    unsigned char byte, c = 0;
    int n = 0, escape = 0;

    while (state != STOP && alarmEnabled)
    {
        // Read one byte (a read interrupted by the alarm returns -1)
        if (readByteSerialPort(&byte) <= 0)
            continue;

        switch (state)
        {
        case START:
            // Waiting for the initial FLAG
            if (byte == FLAG) state = FLAG_RCV;
            break;
        case FLAG_RCV:
            // FLAG received, expecting the A field
            if (byte == 0x03) state = A_RCV;
            else if (byte != FLAG) state = START;
            break;
        case A_RCV:
            // A received, expecting the C field (any value, checked by the caller)
            if (byte == FLAG) state = FLAG_RCV;
            else
            {
                c = byte;
                state = C_RCV;
            }
            break;
        case C_RCV:
            // C received, expecting BCC1 (A ^ C)
            if (byte == (0x03 ^ c))
            {
                state = BCC_OK;
                n = 0;
                escape = 0;
            }
            else if (byte == FLAG) state = FLAG_RCV;
            else state = START;
            break;
        case BCC_OK:
            // BCC1 is correct, reading the data (if any) until the final FLAG
            if (byte == FLAG) state = STOP;
            else if (n > MAX_PAYLOAD_SIZE) state = START; // too long (a FLAG was lost): discard the frame
            else if (byte == ESC) escape = 1;
            else
            {
                data[n++] = escape ? byte ^ 0x20 : byte;
                escape = 0;
            }
            break;
        default:
            break;
        }
    }
    *size = n;
    return state == STOP ? c : -1;
}

////////////////////////////////////////////////
// LLOPEN
////////////////////////////////////////////////
int llOpenTx(LinkLayer llParameters)
{
    // Save the parameters for llSend and llCloseTx
    parameters = llParameters;

    // Install the alarm handler
    struct sigaction sa = {0};
    sa.sa_handler = alarmHandler; // no SA_RESTART: the alarm interrupts a blocked read
    if (sigaction(SIGALRM, &sa, NULL) == -1)
    {
        perror("sigaction");
        exit(1);
    }

    // Open and configure the serial port
    if (openSerialPort(llParameters.serialPort, llParameters.baudRate) < 0)
    {
        perror("openSerialPort");
        return -1;
    }

    printf("Serial port %s opened\n", llParameters.serialPort);

    // Send SET and retransmit it on timeout, up to nRetransmissions attempts
    for (int attempt = 1; attempt <= llParameters.nRetransmissions; attempt++)
    {
        // Send SET
        int bytes = writeBytesSerialPort(SET_FRAME, 5);
        printf("SET sent (%d bytes), attempt #%d\n", bytes, attempt);

        // Wait for UA until the timeout expires
        alarmEnabled = 1;
        alarm(llParameters.timeout);
        int r = waitFrame(UA_FRAME);
        alarm(0); // disable any pending alarm

        if (r == 0)
        {
            printf("UA received. Connection established.\n");
            return 0;
        }
    }

    // All attempts failed
    printf("No UA received. Connection failed.\n");
    closeSerialPort();
    return -1;
}

int llOpenRx(LinkLayer llParameters)
{
    // Save the parameters for llCloseRx
    parameters = llParameters;

    // Install the alarm handler (used by llCloseRx)
    struct sigaction sa = {0};
    sa.sa_handler = alarmHandler; // no SA_RESTART: the alarm interrupts a blocked read
    if (sigaction(SIGALRM, &sa, NULL) == -1)
    {
        perror("sigaction");
        exit(1);
    }

    // Open and configure the serial port
    if (openSerialPort(llParameters.serialPort, llParameters.baudRate) < 0)
    {
        perror("openSerialPort");
        return -1;
    }

    printf("Serial port %s opened\n", llParameters.serialPort);
    printf("Waiting for SET...\n");

    // Wait for SET (no alarm: waits indefinitely)
    alarmEnabled = 1;
    if (waitFrame(SET_FRAME) < 0)
    {
        closeSerialPort();
        return -1;
    }

    // Reply with UA
    int bytes = writeBytesSerialPort(UA_FRAME, 5);
    printf("SET received. UA sent (%d bytes). Connection established.\n", bytes);

    return 0;
}

////////////////////////////////////////////////
// LLSEND
////////////////////////////////////////////////
int llSend(const unsigned char *buf, int bufSize)
{
    if (bufSize < 0 || bufSize > MAX_PAYLOAD_SIZE)
        return -1;

    // Build the I frame (with byte stuffing, the data and BCC2 can take twice their size)
    unsigned char frame[2 * (MAX_PAYLOAD_SIZE + 1) + 5];
    int size = 0;
    frame[size++] = FLAG;
    frame[size++] = 0x03;                             // A: command sent by the Transmitter
    frame[size++] = (frameNumber == 0) ? 0x00 : 0x80; // C: number of the I frame
    frame[size++] = frame[1] ^ frame[2];              // BCC1

    // BCC2 = D1 ^ D2 ^ ... ^ Dn
    unsigned char bcc2 = 0;
    for (int i = 0; i < bufSize; i++)
        bcc2 ^= buf[i];

    // Data and BCC2, with byte stuffing
    for (int i = 0; i <= bufSize; i++)
    {
        unsigned char byte = (i < bufSize) ? buf[i] : bcc2; // the last byte is BCC2
        if (byte == FLAG || byte == ESC)
        {
            frame[size++] = ESC;
            frame[size++] = byte ^ 0x20;
        }
        else
            frame[size++] = byte;
    }
    frame[size++] = FLAG;

    // Send the I frame and retransmit it on REJ or on timeout, up to nRetransmissions attempts
    unsigned char answer[MAX_PAYLOAD_SIZE + 1]; // filled by readFrame (RR and REJ have no data)
    int answerSize;
    for (int attempt = 1; attempt <= parameters.nRetransmissions; attempt++)
    {
        // Send the I frame
        int bytes = writeBytesSerialPort(frame, size);
        printf("I%d sent (%d bytes), attempt #%d\n", frameNumber, bytes, attempt);

        // Wait for RR or REJ until the timeout expires
        alarmEnabled = 1;
        alarm(parameters.timeout);
        int c = readFrame(answer, &answerSize);
        alarm(0); // disable any pending alarm

        if (c == RR_FRAME[1 - frameNumber][2])
        {
            // The Receiver accepted the frame and asks for the next one
            printf("RR%d received.\n", 1 - frameNumber);
            frameNumber = 1 - frameNumber;
            framesCount++;
            return bytes;
        }
        if (c == REJ_FRAME[frameNumber][2])
        {
            // The frame arrived with errors: send it again right away (not a failed attempt)
            printf("REJ%d received.\n", frameNumber);
            rejCount++;
            attempt--;
        }
        if (c < 0)
            timeoutCount++;
        // REJ, timeout or any other frame: send the I frame again
    }

    // All attempts failed
    printf("No RR received. Sending failed.\n");
    return -1;
}

////////////////////////////////////////////////
// LLRECEIVE
////////////////////////////////////////////////
int llReceive(unsigned char *packet)
{
    unsigned char data[MAX_PAYLOAD_SIZE + 1]; // data and BCC2 of the I frame
    int size;

    while (1)
    {
        // Wait for a frame (no alarm: waits indefinitely)
        alarmEnabled = 1;
        int c = readFrame(data, &size);

        if (c == SET_FRAME[2])
        {
            // The Transmitter did not get our UA: reply with UA again
            int bytes = writeBytesSerialPort(UA_FRAME, 5);
            printf("SET received. UA sent (%d bytes).\n", bytes);
            continue;
        }
        if (c != 0x00 && c != 0x80)
            continue; // not an I frame: ignore it

        int number = (c == 0x00) ? 0 : 1;
        if (number != frameNumber)
        {
            // Repeated I frame (our RR was lost): discard it and send the RR again
            writeBytesSerialPort(RR_FRAME[frameNumber], 5);
            printf("Repeated I%d received. RR%d sent.\n", number, frameNumber);
            duplicateCount++;
            continue;
        }

        // BCC2 is the last byte: it must be equal to the XOR of the data bytes
        unsigned char bcc2 = 0;
        for (int i = 0; i < size - 1; i++)
            bcc2 ^= data[i];

        if (size == 0 || bcc2 != data[size - 1])
        {
            // Errors in the data: ask the Transmitter to send the frame again
            writeBytesSerialPort(REJ_FRAME[number], 5);
            printf("I%d received with errors. REJ%d sent.\n", number, number);
            rejCount++;
            continue;
        }

        // New I frame without errors: copy its data to the packet and ask for the next one
        for (int i = 0; i < size - 1; i++)
            packet[i] = data[i];
        frameNumber = 1 - frameNumber;
        writeBytesSerialPort(RR_FRAME[frameNumber], 5);
        printf("I%d received (%d bytes). RR%d sent.\n", number, size - 1, frameNumber);
        framesCount++;
        return size - 1;
    }
}

////////////////////////////////////////////////
// LLCLOSE
////////////////////////////////////////////////
int llCloseTx()
{
    // Send DISC and retransmit it on timeout, up to nRetransmissions attempts
    int r = -1;
    for (int attempt = 1; attempt <= parameters.nRetransmissions && r < 0; attempt++)
    {
        // Send DISC
        int bytes = writeBytesSerialPort(DISC_TX_FRAME, 5);
        printf("DISC sent (%d bytes), attempt #%d\n", bytes, attempt);

        // Wait for the Receiver's DISC until the timeout expires
        alarmEnabled = 1;
        alarm(parameters.timeout);
        r = waitFrame(DISC_RX_FRAME);
        alarm(0); // disable any pending alarm
    }

    if (r == 0)
    {
        // Reply with UA
        int bytes = writeBytesSerialPort(UA_TX_FRAME, 5);
        printf("DISC received. UA sent (%d bytes). Connection closed.\n", bytes);
        sleep(1); // wait until the UA has been written to the serial port
    }
    else
        printf("No DISC received.\n");

    printf("Statistics: %d I frames sent, %d timeouts, %d REJ received\n",
           framesCount, timeoutCount, rejCount);
    closeSerialPort();
    return r;
}

int llCloseRx()
{
    // Wait for DISC (no alarm: waits indefinitely)
    printf("Waiting for DISC...\n");
    alarmEnabled = 1;
    waitFrame(DISC_TX_FRAME);
    printf("DISC received.\n");

    // Reply with DISC and retransmit it on timeout, up to nRetransmissions attempts
    int r = -1;
    for (int attempt = 1; attempt <= parameters.nRetransmissions && r < 0; attempt++)
    {
        // Send DISC
        int bytes = writeBytesSerialPort(DISC_RX_FRAME, 5);
        printf("DISC sent (%d bytes), attempt #%d\n", bytes, attempt);

        // Wait for UA until the timeout expires
        alarmEnabled = 1;
        alarm(parameters.timeout);
        r = waitFrame(UA_TX_FRAME);
        alarm(0); // disable any pending alarm
    }

    if (r == 0)
        printf("UA received. Connection closed.\n");
    else
        printf("No UA received.\n");

    printf("Statistics: %d I frames received, %d repeated, %d REJ sent\n",
           framesCount, duplicateCount, rejCount);
    closeSerialPort();
    return r;
}