
#include "thread_test_join.hh"
#include "system.hh"
#include <stdio.h>

void SimpleThreadJoin(void *arg) {
    int id = *(int *)arg;
    printf("Thread %d starting\n", id);
    currentThread->Yield();
    printf("Thread %d finishing\n", id);
    currentThread->Finish(0);
}

void ThreadTestJoin() {
    printf("Starting ThreadTestJoin\n");

    int id1 = 1, id2 = 2;

    Thread *t1 = new Thread("Thread 1", true);
    Thread *t2 = new Thread("Thread 2", true);

    t1->Fork(SimpleThreadJoin, &id1);
    t2->Fork(SimpleThreadJoin, &id2);

    t1->Join();
    printf("Joined with Thread 1\n");

    t2->Join();
    printf("Joined with Thread 2\n");

    printf("ThreadTestJoin finished\n");
}