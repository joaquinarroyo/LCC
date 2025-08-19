#include "thread_test_channels.hh"
#include "system.hh"
#include "channel.hh"

#include <stdio.h>
#include <string>
#include <cstring>

#define SENDERS 5
#define RECEIVERS 5
#define MESSAGES_PER_THREAD 10

static Channel *channel;

static void
Sender(void *name)
{
    for (int i = 0; i < MESSAGES_PER_THREAD; i++) {
        channel->Send(i);
        printf("            %s sent message\n", (char*)name);
        currentThread->Yield();
    }
}

static void
Receiver(void *name)
{
    int msg;
    for (int i = 0; i < MESSAGES_PER_THREAD; i++) {
        channel->Receive(&msg);
        printf("            %s received %d\n", (char*)name, msg);
        currentThread->Yield();
    }
}

void
ThreadTestChannels()
{
    channel = new Channel("channel");

    Thread *senders[SENDERS];
    Thread *receivers[RECEIVERS];
    std::string senderNamePrefix = "sender ";
    std::string receiverNamePrefix = "receiver ";
    char *senderNames[SENDERS];
    char *receiverNames[RECEIVERS];

    for (int i = 0; i < SENDERS; i++) {
        senderNames[i] = new char[64];
        strncpy(senderNames[i], (senderNamePrefix + std::to_string(i)).c_str(), 64);
        senders[i] = new Thread(senderNames[i], true);
        senders[i]->Fork(Sender, (void *)senderNames[i]);
    }

    for (int j = 0; j < RECEIVERS; j++) {
        receiverNames[j] = new char[64];
        strncpy(receiverNames[j], (receiverNamePrefix + std::to_string(j)).c_str(), 64);
        receivers[j] = new Thread(receiverNames[j], true);
        receivers[j]->Fork(Receiver, (void *)receiverNames[j]);
    }

    for (int i = 0; i < SENDERS; i++)
        senders[i]->Join();

    for (int i = 0; i < RECEIVERS; i++)
        receivers[i]->Join();
}
