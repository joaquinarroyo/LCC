/// Assembly language assist for user programs running on top of Nachos.
///
/// Since we do not want to pull in the entire C library, we define
/// what we need for a user program here, namely `__start` and the system
/// calls.


#define IN_ASM
#include "syscall.h"


        .text
        .align  2

/// Initialize running a C program, by calling `main`.
///
/// NOTE: this has to be first, so that it gets loaded at location 0.
/// The Nachos kernel always starts a program by jumping to location 0.
        .globl  __start
        .ent    __start
__start:
        jal     main
        // If `main` returns, invoke `Exit` with the return value as
        // argument.
        move    $4, $2
        jal     Exit
        .end    __start

/// System call stubs
///
/// Assembly language assist to make system calls to the Nachos kernel.
/// There is one stub per system call, that places the code for the
/// system call into register r2, and leaves the arguments to the
/// system call alone (in other words, arg1 is in r4, arg2 is
/// in r5, arg3 is in r6, arg4 is in r7).
///
/// The return value is in r2. This follows the standard C calling
/// convention on the MIPS.

        .globl  Halt
        .ent    Halt
Halt:
        addiu   $2, $0, SC_HALT
        syscall
        j       $31
        .end    Halt

        .globl  Exit
        .ent    Exit
Exit:
        addiu   $2, $0, SC_EXIT
        syscall
        j       $31
        .end    Exit

        .globl  Exec
        .ent    Exec
Exec:
        addiu   $2, $0, SC_EXEC
        syscall
        j       $31
        .end    Exec

        .globl  Join
        .ent    Join
Join:
        addiu   $2, $0, SC_JOIN
        syscall
        j       $31
        .end    Join

        .globl  Fork
        .ent    Fork
Fork:
        addiu   $2, $0, SC_FORK
        syscall
        j       $31
        .end    Fork

        .globl  Yield
        .ent    Yield
Yield:
        addiu   $2, $0, SC_YIELD
        syscall
        j       $31
        .end    Yield

        .globl  Create
        .ent    Create
Create:
        addiu   $2, $0, SC_CREATE
        syscall
        j       $31
        .end    Create

        .globl  Remove
        .ent    Remove
Remove:
        addiu   $2, $0, SC_REMOVE
        syscall
        j       $31
        .end    Remove

        .globl  Open
        .ent    Open
Open:
        addiu   $2, $0, SC_OPEN
        syscall
        j       $31
        .end    Open

        .globl  Read
        .ent    Read
Read:
        addiu   $2, $0, SC_READ
        syscall
        j       $31
        .end    Read

        .globl  StatsPrint
        .ent    StatsPrint
StatsPrint:
        addiu   $2, $0, SC_SP
        syscall
        j       $31
        .end    StatsPrint

        .globl  Write
        .ent    Write
Write:
        addiu   $2, $0, SC_WRITE
        syscall
        j       $31
        .end    Write

        .globl  Close
        .ent    Close
Close:
        addiu   $2, $0, SC_CLOSE
        syscall
        j       $31
        .end    Close
Cd:
        addiu   $2, $0, SC_CD
        syscall
        j       $31
        .end    Cd

        .globl  Cd
        .ent    Cd
Ls:
        addiu   $2, $0, SC_LS
        syscall
        j       $31
        .end    Ls

        .globl  Ls
        .ent    Ls
Mkdir:
        addiu   $2, $0, SC_MKDIR
        syscall
        j       $31
        .end    Mkdir

        .globl  Mkdir
        .ent    Mkdir

/// Dummy function to keep gcc happy.
        .globl  __main
        .ent    __main
__main:
        j       $31
        .end    __main
