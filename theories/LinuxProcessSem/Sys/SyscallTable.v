(** * LinuxProcessSem.Sys.SyscallTable — the modeled syscall surface, one line each

    This file answers to Linux [arch/riscv/kernel/syscall_table.c], which
    is where the kernel keeps [sys_call_table] — the array a syscall
    number indexes.  The name follows the rule the rest of [Sys/] does:
    look up where the kernel puts the thing.

    TRUST BOUNDARY: this file is part of the trusted specification.

    This list IS the modeled surface: [Specs.syscall_spec] dispatches over
    it and [Specs.modeled_sysnos] is read off it, so the two cannot
    disagree.

    SORTED BY SYSCALL NUMBER, one arm per line, [nil] on its own.  Two
    changes that model two syscalls insert at different lines and merge
    cleanly; if both appended to the end of the list, they would
    collide.

    An arm reads its own arguments out of the [SyscallInput].  That is the
    same thing [arg 0], [arg 1] and so on do -- those
    readers are deterministic and change neither state nor events -- but
    doing it directly is what lets one lookup serve arms of every arity. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Dispatch
  Syscall Uapi Uaccess
  Fs.DPath Fs.File Fs.ReadWrite Fs.Open Fs.Sync Fs.Stat Fs.Select Fs.Ioctl Fs.Fcntl Fs.Namei
  Fs.Readdir Fs.Locks Fs.Timerfd Fs.Pipe Fs.EventPoll Fs.EventFd
  Mm.Mmap Mm.Mremap Mm.Mprotect Mm.Madvise
  Kernel.Exit Kernel.Fork Kernel.Futex.Syscalls Kernel.Groups Kernel.Sched.Syscalls
  Kernel.Signal Kernel.Sys
  Kernel.Time.Hrtimer Kernel.Time.PosixTimers Kernel.Time.Time
  Net.Socket
  Drivers.Char.Random.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

Definition spec_table : list SpecArm :=
  (* getcwd          *) mkSpecArm  17%Z (fun i => getcwd_spec (in_arg i 1) i) ::
  (* eventfd2        *) mkSpecArm  19%Z (fun i => eventfd2_spec (flag32 (in_arg i 1)) i) ::
  (* epoll_create1   *) mkSpecArm  20%Z (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i) ::
  (* epoll_ctl       *) mkSpecArm  21%Z (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i) ::
  (* epoll_pwait     *) mkSpecArm  22%Z (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i) ::
  (* dup             *) mkSpecArm  23%Z (fun i => dup_spec (fd32 (in_arg i 0)) i) ::
  (* dup3            *) mkSpecArm  24%Z (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i) ::
  (* fcntl           *) mkSpecArm  25%Z (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i) ::
  (* ioctl           *) mkSpecArm  29%Z (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i) ::
  (* flock           *) mkSpecArm  32%Z (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i) ::
  (* unlinkat        *) mkSpecArm  35%Z (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* ftruncate       *) mkSpecArm  46%Z (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i) ::
  (* faccessat       *) mkSpecArm  48%Z (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* openat          *) mkSpecArm  56%Z (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* close           *) mkSpecArm  57%Z (fun i => close_spec (fd32 (in_arg i 0)) i) ::
  (* pipe2           *) mkSpecArm  59%Z (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i) ::
  (* getdents64      *) mkSpecArm  61%Z (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i) ::
  (* lseek           *) mkSpecArm  62%Z (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i) ::
  (* read            *) mkSpecArm  63%Z (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* write           *) mkSpecArm  64%Z (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* readv           *) mkSpecArm  65%Z (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* writev          *) mkSpecArm  66%Z (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* pread64         *) mkSpecArm  67%Z (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* pwrite64        *) mkSpecArm  68%Z (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* pselect6        *) mkSpecArm  72%Z (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) ::
  (* ppoll           *) mkSpecArm  73%Z (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i) ::
  (* readlinkat      *) mkSpecArm  78%Z (fun i => readlinkat_spec (fd32 (in_arg i 0)) i) ::
  (* newfstatat      *) mkSpecArm  79%Z (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i) ::
  (* fstat           *) mkSpecArm  80%Z (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i) ::
  (* fsync           *) mkSpecArm  82%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i) ::
  (* fdatasync       *) mkSpecArm  83%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i) ::
  (* timerfd_create  *) mkSpecArm  85%Z (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i) ::
  (* exit            *) mkSpecArm  93%Z (fun i => exit_spec (in_arg i 0) i) ::
  (* exit_group      *) mkSpecArm  94%Z (fun i => exit_spec (in_arg i 0) i) ::
  (* set_tid_address *) mkSpecArm  96%Z (fun i => set_tid_address_spec i) ::
  (* futex           *) mkSpecArm  98%Z (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* set_robust_list *) mkSpecArm  99%Z (fun i => set_robust_list_spec (in_arg i 1) i) ::
  (* nanosleep       *) mkSpecArm 101%Z (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i) ::
  (* clock_gettime   *) mkSpecArm 113%Z (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i) ::
  (* clock_getres    *) mkSpecArm 114%Z (fun i => clock_getres_spec (clockid32 (in_arg i 0)) (in_arg i 1) i) ::
  (* sched_setscheduler *) mkSpecArm 119%Z (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) ::
  (* sched_getaffinity *) mkSpecArm 123%Z (fun i => sched_getaffinity_spec (in_arg i 1) i) ::
  (* sched_yield     *) mkSpecArm 124%Z (fun i => sched_yield_spec i) ::
  (* tkill           *) mkSpecArm 130%Z (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i) ::
  (* tgkill          *) mkSpecArm 131%Z (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i) ::
  (* sigaltstack     *) mkSpecArm 132%Z (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i) ::
  (* rt_sigaction    *) mkSpecArm 134%Z (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* rt_sigprocmask  *) mkSpecArm 135%Z (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* setgid          *) mkSpecArm 144%Z (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i) ::
  (* setuid          *) mkSpecArm 146%Z (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i) ::
  (* setresuid       *) mkSpecArm 147%Z (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i) ::
  (* setresgid       *) mkSpecArm 149%Z (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i) ::
  (* setsid          *) mkSpecArm 157%Z (fun i => setsid_spec i) ::
  (* getgroups       *) mkSpecArm 158%Z (fun i => getgroups_spec (in_arg i 0) i) ::
  (* setgroups       *) mkSpecArm 159%Z (fun i => setgroups_spec i) ::
  (* uname           *) mkSpecArm 160%Z (fun i => uname_spec (in_arg i 0) i) ::
  (* prctl           *) mkSpecArm 167%Z (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i) ::
  (* gettimeofday    *) mkSpecArm 169%Z (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i) ::
  (* getpid          *) mkSpecArm 172%Z (fun i => getpid_spec i) ::
  (* getuid          *) mkSpecArm 174%Z (fun i => getid_spec cr_uid i) ::
  (* geteuid         *) mkSpecArm 175%Z (fun i => getid_spec cr_euid i) ::
  (* getgid          *) mkSpecArm 176%Z (fun i => getid_spec cr_gid i) ::
  (* getegid         *) mkSpecArm 177%Z (fun i => getid_spec cr_egid i) ::
  (* gettid          *) mkSpecArm 178%Z (fun i => gettid_spec i) ::
  (* socket          *) mkSpecArm 198%Z (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) ::
  (* socketpair      *) mkSpecArm 199%Z (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* bind            *) mkSpecArm 200%Z (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* listen          *) mkSpecArm 201%Z (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i) ::
  (* accept          *) mkSpecArm 202%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i) ::
  (* connect         *) mkSpecArm 203%Z (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* getsockname     *) mkSpecArm 204%Z (fun i => getsockname_spec (fd32 (in_arg i 0)) i) ::
  (* getpeername     *) mkSpecArm 205%Z (fun i => getpeername_spec (fd32 (in_arg i 0)) i) ::
  (* sendto          *) mkSpecArm 206%Z (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) ::
  (* recvfrom        *) mkSpecArm 207%Z (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* setsockopt      *) mkSpecArm 208%Z (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i) ::
  (* getsockopt      *) mkSpecArm 209%Z (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i) ::
  (* shutdown        *) mkSpecArm 210%Z (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i) ::
  (* sendmsg         *) mkSpecArm 211%Z (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) ::
  (* recvmsg         *) mkSpecArm 212%Z (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i) ::
  (* brk             *) mkSpecArm 214%Z (fun i => brk_spec (in_arg i 0) i) ::
  (* munmap          *) mkSpecArm 215%Z (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i) ::
  (* mremap          *) mkSpecArm 216%Z (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* clone           *) mkSpecArm 220%Z (fun i => clone_spec (in_arg i 0) i) ::
  (* mmap            *) mkSpecArm 222%Z (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) ::
  (* mprotect        *) mkSpecArm 226%Z (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) ::
  (* madvise         *) mkSpecArm 233%Z (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i) ::
  (* accept4         *) mkSpecArm 242%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* wait4           *) mkSpecArm 260%Z (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i) ::
  (* prlimit64       *) mkSpecArm 261%Z (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  (* getrandom       *) mkSpecArm 278%Z (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) ::
  (* clone3          *) mkSpecArm 435%Z (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i) ::
  (* faccessat2      *) mkSpecArm 439%Z (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) ::
  nil.
