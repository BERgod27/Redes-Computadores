// RCOM 2026/2027
//
// Application layer protocol implementation

#include "application_layer.h"
#include "link_layer.h"

#include <stdio.h>
#include <string.h>

// Control field (C) of the packets
#define C_START 1
#define C_DATA 2
#define C_END 3

// Types (T) of the parameters of the control packets: T | L | V
#define T_FILE_SIZE 0
#define T_FILE_NAME 1

// Data packets: C | L2 | L1 | P1..PK (K = 256 * L2 + L1)
#define DATA_HEADER_SIZE 3
#define MAX_DATA_SIZE (MAX_PAYLOAD_SIZE - DATA_HEADER_SIZE)

// Builds a control packet (START or END) with the file size and name.
// Returns the size of the packet.
static int buildControlPacket(unsigned char *packet, unsigned char c, unsigned long fileSize, const char *fileName)
{
    int size = 0;
    packet[size++] = c;

    // File size: V has the minimum number of bytes, most significant byte first
    int length = 1;
    while (length < (int)sizeof(fileSize) && (fileSize >> (8 * length)) != 0)
        length++;
    packet[size++] = T_FILE_SIZE;
    packet[size++] = length;
    for (int i = length - 1; i >= 0; i--)
        packet[size++] = (fileSize >> (8 * i)) & 0xFF;

    // File name: V has the characters of the name, without the final '\0' (L is one byte, so at most 255)
    int nameLength = strlen(fileName);
    if (nameLength > 255)
        nameLength = 255;
    packet[size++] = T_FILE_NAME;
    packet[size++] = nameLength;
    memcpy(packet + size, fileName, nameLength);
    size += nameLength;

    return size;
}

// Reads the parameters of a control packet with `size` bytes.
// `fileName` must have room for 256 characters.
static void parseControlPacket(const unsigned char *packet, int size, unsigned long *fileSize, char *fileName)
{
    int i = 1; // skip C
    while (i + 2 <= size)
    {
        unsigned char type = packet[i];
        int length = packet[i + 1];
        const unsigned char *value = packet + i + 2;
        if (i + 2 + length > size)
            break; // truncated parameter

        if (type == T_FILE_SIZE)
        {
            *fileSize = 0;
            for (int j = 0; j < length; j++)
                *fileSize = (*fileSize << 8) | value[j];
        }
        else if (type == T_FILE_NAME)
        {
            memcpy(fileName, value, length);
            fileName[length] = '\0';
        }
        i += 2 + length;
    }
}

// Transmitter: sends the file `filename` (START packet, data packets, END packet).
static void sendFile(LinkLayer llParameters, const char *filename)
{
    FILE *file = fopen(filename, "rb");
    if (file == NULL)
    {
        perror(filename);
        return;
    }

    // File size
    fseek(file, 0, SEEK_END);
    unsigned long fileSize = ftell(file);
    rewind(file);

    if (llOpenTx(llParameters) < 0)
    {
        // llOpenTx already closed the serial port
        printf("Could not open the connection. Transfer aborted.\n");
        fclose(file);
        return;
    }

    unsigned char packet[MAX_PAYLOAD_SIZE];
    unsigned long bytesSent = 0;

    // START packet
    int size = buildControlPacket(packet, C_START, fileSize, filename);
    int ok = llSend(packet, size) >= 0;
    if (ok)
        printf("START packet sent: %s, %lu bytes\n", filename, fileSize);

    // Data packets, with up to MAX_DATA_SIZE bytes of the file each
    while (ok)
    {
        size_t k = fread(packet + DATA_HEADER_SIZE, 1, MAX_DATA_SIZE, file);
        if (k == 0)
            break; // end of the file (or a read error, checked below)

        packet[0] = C_DATA;
        packet[1] = k / 256; // L2
        packet[2] = k % 256; // L1
        ok = llSend(packet, DATA_HEADER_SIZE + k) >= 0;
        if (ok)
        {
            bytesSent += k;
            printf("Data packet sent: %lu / %lu bytes\n", bytesSent, fileSize);
        }
    }

    if (ok && ferror(file))
    {
        perror(filename);
        ok = 0;
    }

    // END packet (same parameters as the START packet)
    if (ok)
    {
        size = buildControlPacket(packet, C_END, fileSize, filename);
        ok = llSend(packet, size) >= 0;
        if (ok)
            printf("END packet sent.\n");
    }

    fclose(file);

    if (ok)
        printf("File sent: %lu bytes.\n", bytesSent);
    else
        printf("Transfer failed after %lu of %lu bytes.\n", bytesSent, fileSize);

    // Close the connection even after a failure: this closes the serial port, prints the
    // statistics and, if the cable is back, the DISC tells the Receiver to stop too
    llCloseTx();
}

// Receiver: receives the packets and writes the file data to `filename` until the END packet.
static void receiveFile(LinkLayer llParameters, const char *filename)
{
    FILE *file = fopen(filename, "wb");
    if (file == NULL)
    {
        perror(filename);
        return;
    }

    if (llOpenRx(llParameters) < 0)
    {
        printf("Could not open the connection. Transfer aborted.\n");
        fclose(file);
        remove(filename);
        return;
    }

    unsigned char packet[MAX_PAYLOAD_SIZE];
    unsigned long fileSize = 0, bytesReceived = 0;
    char fileName[256] = "";
    int started = 0, ended = 0, failed = 0;

    while (!ended && !failed)
    {
        int n = llReceive(packet);
        if (n < 0)
        {
            printf("Connection ended before the END packet.\n");
            failed = 1;
            break;
        }
        if (n == 0)
            continue;

        switch (packet[0])
        {
        case C_START:
            parseControlPacket(packet, n, &fileSize, fileName);
            started = 1;
            printf("START packet received: %s, %lu bytes\n", fileName, fileSize);
            break;

        case C_DATA:
        {
            if (n < DATA_HEADER_SIZE)
                break;
            int k = 256 * packet[1] + packet[2];
            if (k > n - DATA_HEADER_SIZE)
            {
                printf("Data packet with a wrong size (%d bytes, L2 L1 = %d). Ignored.\n", n, k);
                break;
            }
            if (fwrite(packet + DATA_HEADER_SIZE, 1, k, file) != (size_t)k)
            {
                perror(filename);
                failed = 1;
                break;
            }
            bytesReceived += k;
            printf("Data packet received: %lu / %lu bytes\n", bytesReceived, fileSize);
            break;
        }

        case C_END:
            ended = 1;
            printf("END packet received.\n");
            break;

        default:
            printf("Unknown packet (C = %d). Ignored.\n", packet[0]);
            break;
        }
    }

    if (fclose(file) != 0)
    {
        perror(filename);
        failed = 1;
    }

    llCloseRx();

    if (failed)
        printf("Transfer failed after %lu bytes.\n", bytesReceived);
    else if (started && bytesReceived != fileSize)
        printf("File received with %lu bytes, but START said %lu bytes.\n", bytesReceived, fileSize);
    else
        printf("File received: %lu bytes written to %s.\n", bytesReceived, filename);
}

void applicationLayer(const char *serialPort, const char *role, int baudRate,
                      int nTries, int timeout, const char *filename)
{
    LinkLayer llParameters = {
        .baudRate = baudRate,
        .nRetransmissions = nTries,
        .timeout = timeout,
    };
    strncpy(llParameters.serialPort, serialPort, sizeof(llParameters.serialPort) - 1);

    if (strcmp(role, "tx") == 0)
    {
        sendFile(llParameters, filename);
    }
    else if (strcmp(role, "rx") == 0)
    {
        receiveFile(llParameters, filename);
    }
    else
    {
        printf("Invalid role: %s. Must be 'tx' or 'rx'.\n", role);
        return;
    }
}
