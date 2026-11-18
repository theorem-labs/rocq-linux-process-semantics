# Name this object in its STT_FILE symbol. Without a .file directive the
# linker names it after the compiler's random temporary object
# (/tmp/ccXXXXXX.o), and in most examples the symbol table sits in loaded
# page slack, so the snapshot would differ on every build (issue #1686).
.file "_start.S"
.section .text
.globl _start
_start:
    .option push
    .option norelax
    lla  gp, __global_pointer$
    .option pop
    ld   a0, 0(sp)
    addi a1, sp, 8
    slli t0, a0, 3
    add  a2, a1, t0
    addi a2, a2, 8
    lla  t1, environ
    sd   a2, 0(t1)
    call main
    # exit(main()) directly. We do NOT call fflush: these source binaries do raw
    # read(2)/write(2) with no stdio buffering, so fflush(NULL) emits no
    # syscalls (trace-neutral) — but its musl machine code (the open-FILE walk
    # + lock stubs) would otherwise sit on the execution path that a target's
    # universal-equivalence proof has to reason through. Dropping it removes
    # that libc distraction from the proof. a0 already holds main()'s return.
    li   a7, 93
    ecall

# long raw_syscall(long nr, long a, long b, long c, long d, long e, long f):
# issue the syscall and return the RAW kernel result — no errno translation.
# musl's wrappers (and musl's syscall()) write errno on error-range returns,
# but errno lives in TLS and this crt never sets up a thread pointer, so an
# -ns binary reaching an errno write faults.  Any syscall whose modeled
# failure path returns an error value (brk's arbitrary query report, mmap's
# and openat's -errno alternatives, ...) must go through this wrapper
# instead of a musl wrapper.  Unused argument slots are simply ignored by
# the kernel; callers pass 0.
.globl raw_syscall
raw_syscall:
    mv   a7, a0
    mv   a0, a1
    mv   a1, a2
    mv   a2, a3
    mv   a3, a4
    mv   a4, a5
    mv   a5, a6
    ecall
    ret
