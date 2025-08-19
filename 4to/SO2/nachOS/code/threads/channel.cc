#include "channel.hh"
#include "lock.hh"
#include "system.hh"

Channel::Channel(const char* debugName) {
    name = debugName;

    receiverLock = new Lock("receiver lock");
    senderLock = new Lock("sender lock");

    syncSem1 = new Semaphore("sync sem1", 0); // Notifica que un receptor está listo
    syncSem2 = new Semaphore("sync sem2", 0); // Notifica que un mensaje está listo
}

Channel::~Channel() {
    delete receiverLock;
    delete senderLock;

    delete syncSem1;
    delete syncSem2;
}

void Channel::Send(int msg) {
    senderLock->Acquire();

    // Esperar hasta que un receptor esté listo
    syncSem1->P();

    // Colocar el mensaje en el buffer
    buffer = msg;

    // Notificar al receptor que el mensaje está listo
    syncSem2->V();

    senderLock->Release();
}

void Channel::Receive(int* msg) {
    receiverLock->Acquire();

    // Notificar al emisor que el receptor está listo
    syncSem1->V();

    // Esperar hasta que el mensaje esté disponible
    syncSem2->P();

    // Leer el mensaje del buffer
    *msg = buffer;

    receiverLock->Release();
}