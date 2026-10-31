(** * LinuxProcessSem.Checks.Sys.DispatchCompute — what the dispatchers compute to

    Split from [Checks.Sys.Dispatch] because these need [check_syscall] and
    [syscall_spec_witness], which dispatch over the table [Arm] builds. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** What the dispatchers compute to, per number.  [reflexivity] here is full
    conversion, which settles the lookup outright -- where [cbn] with a delta
    list cannot, because the arms were built by [refine] and it will not
    unfold them.  A proof that knows its syscall number rewrites with one of
    these and is back to the plain [check_*] it was written against. *)

Lemma check_syscall_dup : forall i eff m,
  bv_unsigned (in_sysno i) = 23%Z ->
  check_syscall i eff m = check_dup (fd32 (in_arg i 0)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_dup : forall i m,
  bv_unsigned (in_sysno i) = 23%Z ->
  syscall_spec_witness i m = dup_witness (fd32 (in_arg i 0)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_dup3 : forall i eff m,
  bv_unsigned (in_sysno i) = 24%Z ->
  check_syscall i eff m = check_dup3 (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_dup3 : forall i m,
  bv_unsigned (in_sysno i) = 24%Z ->
  syscall_spec_witness i m = dup3_witness (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_fcntl : forall i eff m,
  bv_unsigned (in_sysno i) = 25%Z ->
  check_syscall i eff m = check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_fcntl : forall i m,
  bv_unsigned (in_sysno i) = 25%Z ->
  syscall_spec_witness i m = fcntl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_ioctl : forall i eff m,
  bv_unsigned (in_sysno i) = 29%Z ->
  check_syscall i eff m = check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_ioctl : forall i m,
  bv_unsigned (in_sysno i) = 29%Z ->
  syscall_spec_witness i m = ioctl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_flock : forall i eff m,
  bv_unsigned (in_sysno i) = 32%Z ->
  check_syscall i eff m = check_flock (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_flock : forall i m,
  bv_unsigned (in_sysno i) = 32%Z ->
  syscall_spec_witness i m = flock_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_unlinkat : forall i eff m,
  bv_unsigned (in_sysno i) = 35%Z ->
  check_syscall i eff m = check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_unlinkat : forall i m,
  bv_unsigned (in_sysno i) = 35%Z ->
  syscall_spec_witness i m = unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_ftruncate : forall i eff m,
  bv_unsigned (in_sysno i) = 46%Z ->
  check_syscall i eff m = check_ftruncate (fd32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_ftruncate : forall i m,
  bv_unsigned (in_sysno i) = 46%Z ->
  syscall_spec_witness i m = ftruncate_witness (fd32 (in_arg i 0)) (in_arg i 1) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_faccessat : forall i eff m,
  bv_unsigned (in_sysno i) = 48%Z ->
  check_syscall i eff m = check_faccessat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_faccessat : forall i m,
  bv_unsigned (in_sysno i) = 48%Z ->
  syscall_spec_witness i m = faccessat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_openat : forall i eff m,
  bv_unsigned (in_sysno i) = 56%Z ->
  check_syscall i eff m = check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_openat : forall i m,
  bv_unsigned (in_sysno i) = 56%Z ->
  syscall_spec_witness i m = openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_close : forall i eff m,
  bv_unsigned (in_sysno i) = 57%Z ->
  check_syscall i eff m = check_close (fd32 (in_arg i 0)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_close : forall i m,
  bv_unsigned (in_sysno i) = 57%Z ->
  syscall_spec_witness i m = close_witness (fd32 (in_arg i 0)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_pipe2 : forall i eff m,
  bv_unsigned (in_sysno i) = 59%Z ->
  check_syscall i eff m
  = check_pipe2 i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_pipe2 : forall i m,
  bv_unsigned (in_sysno i) = 59%Z ->
  syscall_spec_witness i m
  = pipe2_witness (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_lseek : forall i eff m,
  bv_unsigned (in_sysno i) = 62%Z ->
  check_syscall i eff m = check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_lseek : forall i m,
  bv_unsigned (in_sysno i) = 62%Z ->
  syscall_spec_witness i m = lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_read : forall i eff m,
  bv_unsigned (in_sysno i) = 63%Z ->
  check_syscall i eff m = check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_read : forall i m,
  bv_unsigned (in_sysno i) = 63%Z ->
  syscall_spec_witness i m = read_witness  (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_write : forall i eff m,
  bv_unsigned (in_sysno i) = 64%Z ->
  check_syscall i eff m = check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_write : forall i m,
  bv_unsigned (in_sysno i) = 64%Z ->
  syscall_spec_witness i m = write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_readv : forall i eff m,
  bv_unsigned (in_sysno i) = 65%Z ->
  check_syscall i eff m = check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_readv : forall i m,
  bv_unsigned (in_sysno i) = 65%Z ->
  syscall_spec_witness i m = readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_writev : forall i eff m,
  bv_unsigned (in_sysno i) = 66%Z ->
  check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_writev : forall i m,
  bv_unsigned (in_sysno i) = 66%Z ->
  syscall_spec_witness i m = writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_pselect6 : forall i eff m,
  bv_unsigned (in_sysno i) = 72%Z ->
  check_syscall i eff m = check_pselect6 i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_pselect6 : forall i m,
  bv_unsigned (in_sysno i) = 72%Z ->
  syscall_spec_witness i m = pselect6_witness i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5).
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_ppoll : forall i eff m,
  bv_unsigned (in_sysno i) = 73%Z ->
  check_syscall i eff m = check_ppoll i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_ppoll : forall i m,
  bv_unsigned (in_sysno i) = 73%Z ->
  syscall_spec_witness i m = ppoll_witness i m (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4).
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_readlinkat : forall i eff m,
  bv_unsigned (in_sysno i) = 78%Z ->
  check_syscall i eff m = check_readlinkat (fd32 (in_arg i 0)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_readlinkat : forall i m,
  bv_unsigned (in_sysno i) = 78%Z ->
  syscall_spec_witness i m = readlinkat_witness (fd32 (in_arg i 0)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_newfstatat : forall i eff m,
  bv_unsigned (in_sysno i) = 79%Z ->
  check_syscall i eff m = check_newfstatat i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_newfstatat : forall i m,
  bv_unsigned (in_sysno i) = 79%Z ->
  syscall_spec_witness i m = newfstatat_witness (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_fstat : forall i eff m,
  bv_unsigned (in_sysno i) = 80%Z ->
  check_syscall i eff m = check_fstat i (fd32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_fstat : forall i m,
  bv_unsigned (in_sysno i) = 80%Z ->
  syscall_spec_witness i m = fstat_witness (fd32 (in_arg i 0)) (in_arg i 1) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_fsync : forall i eff m,
  bv_unsigned (in_sysno i) = 82%Z ->
  check_syscall i eff m = check_fsync (fd32 (in_arg i 0)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_fsync : forall i m,
  bv_unsigned (in_sysno i) = 82%Z ->
  syscall_spec_witness i m = fsync_witness (fd32 (in_arg i 0)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_fdatasync : forall i eff m,
  bv_unsigned (in_sysno i) = 83%Z ->
  check_syscall i eff m = check_fsync (fd32 (in_arg i 0)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_fdatasync : forall i m,
  bv_unsigned (in_sysno i) = 83%Z ->
  syscall_spec_witness i m = fsync_witness (fd32 (in_arg i 0)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_exit : forall i eff m,
  bv_unsigned (in_sysno i) = 93%Z ->
  check_syscall i eff m = check_exit (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_exit : forall i m,
  bv_unsigned (in_sysno i) = 93%Z ->
  syscall_spec_witness i m = exit_witness (in_arg i 0) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_exit_group : forall i eff m,
  bv_unsigned (in_sysno i) = 94%Z ->
  check_syscall i eff m = check_exit (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_exit_group : forall i m,
  bv_unsigned (in_sysno i) = 94%Z ->
  syscall_spec_witness i m = exit_witness (in_arg i 0) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_set_tid_address : forall i eff m,
  bv_unsigned (in_sysno i) = 96%Z ->
  check_syscall i eff m = check_set_tid_address eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_set_tid_address : forall i m,
  bv_unsigned (in_sysno i) = 96%Z ->
  syscall_spec_witness i m = set_tid_address_witness m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_nanosleep : forall i eff m,
  bv_unsigned (in_sysno i) = 101%Z ->
  check_syscall i eff m = check_nanosleep i (in_arg i 0) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_nanosleep : forall i m,
  bv_unsigned (in_sysno i) = 101%Z ->
  syscall_spec_witness i m = nanosleep_witness (in_arg i 0) (in_arg i 1) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_clock_gettime : forall i eff m,
  bv_unsigned (in_sysno i) = 113%Z ->
  check_syscall i eff m = check_clock_gettime i (clockid32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_clock_gettime : forall i m,
  bv_unsigned (in_sysno i) = 113%Z ->
  syscall_spec_witness i m = clock_gettime_witness (clockid32 (in_arg i 0)) (in_arg i 1) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_sched_setscheduler : forall i eff m,
  bv_unsigned (in_sysno i) = 119%Z ->
  check_syscall i eff m = check_sched_setscheduler i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_sched_setscheduler : forall i m,
  bv_unsigned (in_sysno i) = 119%Z ->
  syscall_spec_witness i m = sched_setscheduler_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_sched_getaffinity : forall i eff m,
  bv_unsigned (in_sysno i) = 123%Z ->
  check_syscall i eff m = check_sched_getaffinity (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_sched_getaffinity : forall i m,
  bv_unsigned (in_sysno i) = 123%Z ->
  syscall_spec_witness i m = sched_getaffinity_witness (in_arg i 1) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_sched_yield : forall i eff m,
  bv_unsigned (in_sysno i) = 124%Z ->
  check_syscall i eff m = check_sched_yield eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_sched_yield : forall i m,
  bv_unsigned (in_sysno i) = 124%Z ->
  syscall_spec_witness i m = sched_yield_witness m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_rt_sigaction : forall i eff m,
  bv_unsigned (in_sysno i) = 134%Z ->
  check_syscall i eff m = check_rt_sigaction i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_rt_sigaction : forall i m,
  bv_unsigned (in_sysno i) = 134%Z ->
  syscall_spec_witness i m = rt_sigaction_witness (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_rt_sigprocmask : forall i eff m,
  bv_unsigned (in_sysno i) = 135%Z ->
  check_syscall i eff m = check_rt_sigprocmask i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_rt_sigprocmask : forall i m,
  bv_unsigned (in_sysno i) = 135%Z ->
  syscall_spec_witness i m = rt_sigprocmask_witness (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_setgid : forall i eff m,
  bv_unsigned (in_sysno i) = 144%Z ->
  check_syscall i eff m = check_setid cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_setgid : forall i m,
  bv_unsigned (in_sysno i) = 144%Z ->
  syscall_spec_witness i m = setid_witness (uid32 (in_arg i 0)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_setuid : forall i eff m,
  bv_unsigned (in_sysno i) = 146%Z ->
  check_syscall i eff m = check_setid cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_setuid : forall i m,
  bv_unsigned (in_sysno i) = 146%Z ->
  syscall_spec_witness i m = setid_witness (uid32 (in_arg i 0)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_setresuid : forall i eff m,
  bv_unsigned (in_sysno i) = 147%Z ->
  check_syscall i eff m = check_setresid cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_setresuid : forall i m,
  bv_unsigned (in_sysno i) = 147%Z ->
  syscall_spec_witness i m = setresid_witness cred_uids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_setresgid : forall i eff m,
  bv_unsigned (in_sysno i) = 149%Z ->
  check_syscall i eff m = check_setresid cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_setresgid : forall i m,
  bv_unsigned (in_sysno i) = 149%Z ->
  syscall_spec_witness i m = setresid_witness cred_gids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_setsid : forall i eff m,
  bv_unsigned (in_sysno i) = 157%Z ->
  check_syscall i eff m = check_setsid eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_setsid : forall i m,
  bv_unsigned (in_sysno i) = 157%Z ->
  syscall_spec_witness i m = setsid_witness m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_getgroups : forall i eff m,
  bv_unsigned (in_sysno i) = 158%Z ->
  check_syscall i eff m = check_getgroups (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_getgroups : forall i m,
  bv_unsigned (in_sysno i) = 158%Z ->
  syscall_spec_witness i m = getgroups_witness (in_arg i 0) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_setgroups : forall i eff m,
  bv_unsigned (in_sysno i) = 159%Z ->
  check_syscall i eff m = check_setgroups i eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_setgroups : forall i m,
  bv_unsigned (in_sysno i) = 159%Z ->
  syscall_spec_witness i m = setgroups_witness i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_prctl : forall i eff m,
  bv_unsigned (in_sysno i) = 167%Z ->
  check_syscall i eff m = check_prctl i (int32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_prctl : forall i m,
  bv_unsigned (in_sysno i) = 167%Z ->
  syscall_spec_witness i m = prctl_witness (int32 (in_arg i 0)) (in_arg i 1) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_gettimeofday : forall i eff m,
  bv_unsigned (in_sysno i) = 169%Z ->
  check_syscall i eff m = check_gettimeofday i (in_arg i 0) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_gettimeofday : forall i m,
  bv_unsigned (in_sysno i) = 169%Z ->
  syscall_spec_witness i m = gettimeofday_witness (in_arg i 0) (in_arg i 1) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_getpid : forall i eff m,
  bv_unsigned (in_sysno i) = 172%Z ->
  check_syscall i eff m = check_getpid eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_getpid : forall i m,
  bv_unsigned (in_sysno i) = 172%Z ->
  syscall_spec_witness i m = getpid_witness m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_getppid : forall i eff m,
  bv_unsigned (in_sysno i) = 173%Z ->
  check_syscall i eff m = check_getppid eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_getppid : forall i m,
  bv_unsigned (in_sysno i) = 173%Z ->
  syscall_spec_witness i m = getppid_witness m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_getuid : forall i eff m,
  bv_unsigned (in_sysno i) = 174%Z ->
  check_syscall i eff m = check_getid cr_uid eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_getuid : forall i m,
  bv_unsigned (in_sysno i) = 174%Z ->
  syscall_spec_witness i m = getid_witness cr_uid m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_geteuid : forall i eff m,
  bv_unsigned (in_sysno i) = 175%Z ->
  check_syscall i eff m = check_getid cr_euid eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_geteuid : forall i m,
  bv_unsigned (in_sysno i) = 175%Z ->
  syscall_spec_witness i m = getid_witness cr_euid m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_getgid : forall i eff m,
  bv_unsigned (in_sysno i) = 176%Z ->
  check_syscall i eff m = check_getid cr_gid eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_getgid : forall i m,
  bv_unsigned (in_sysno i) = 176%Z ->
  syscall_spec_witness i m = getid_witness cr_gid m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_getegid : forall i eff m,
  bv_unsigned (in_sysno i) = 177%Z ->
  check_syscall i eff m = check_getid cr_egid eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_getegid : forall i m,
  bv_unsigned (in_sysno i) = 177%Z ->
  syscall_spec_witness i m = getid_witness cr_egid m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_gettid : forall i eff m,
  bv_unsigned (in_sysno i) = 178%Z ->
  check_syscall i eff m = check_gettid eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_gettid : forall i m,
  bv_unsigned (in_sysno i) = 178%Z ->
  syscall_spec_witness i m = gettid_witness m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_socket : forall i eff m,
  bv_unsigned (in_sysno i) = 198%Z ->
  check_syscall i eff m = check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_socket : forall i m,
  bv_unsigned (in_sysno i) = 198%Z ->
  syscall_spec_witness i m = socket_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_bind : forall i eff m,
  bv_unsigned (in_sysno i) = 200%Z ->
  check_syscall i eff m = check_bind i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_bind : forall i m,
  bv_unsigned (in_sysno i) = 200%Z ->
  syscall_spec_witness i m = bind_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_listen : forall i eff m,
  bv_unsigned (in_sysno i) = 201%Z ->
  check_syscall i eff m = check_listen (fd32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_listen : forall i m,
  bv_unsigned (in_sysno i) = 201%Z ->
  syscall_spec_witness i m = listen_witness (fd32 (in_arg i 0)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_accept : forall i eff m,
  bv_unsigned (in_sysno i) = 202%Z ->
  check_syscall i eff m = check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_accept : forall i m,
  bv_unsigned (in_sysno i) = 202%Z ->
  syscall_spec_witness i m = accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (Z_to_bv 64 0) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_connect : forall i eff m,
  bv_unsigned (in_sysno i) = 203%Z ->
  check_syscall i eff m = check_connect i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_connect : forall i m,
  bv_unsigned (in_sysno i) = 203%Z ->
  syscall_spec_witness i m = connect_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_brk : forall i eff m,
  bv_unsigned (in_sysno i) = 214%Z ->
  check_syscall i eff m = check_brk (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_brk : forall i m,
  bv_unsigned (in_sysno i) = 214%Z ->
  syscall_spec_witness i m = brk_witness (in_arg i 0) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_munmap : forall i eff m,
  bv_unsigned (in_sysno i) = 215%Z ->
  check_syscall i eff m = check_munmap (in_arg i 0) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_munmap : forall i m,
  bv_unsigned (in_sysno i) = 215%Z ->
  syscall_spec_witness i m = munmap_witness (in_arg i 0) (in_arg i 1) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_mremap : forall i eff m,
  bv_unsigned (in_sysno i) = 216%Z ->
  check_syscall i eff m = check_mremap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_mremap : forall i m,
  bv_unsigned (in_sysno i) = 216%Z ->
  syscall_spec_witness i m = mremap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_clone : forall i eff m,
  bv_unsigned (in_sysno i) = 220%Z ->
  check_syscall i eff m = check_clone (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_clone : forall i m,
  bv_unsigned (in_sysno i) = 220%Z ->
  syscall_spec_witness i m = clone_witness (in_arg i 0) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_mmap : forall i eff m,
  bv_unsigned (in_sysno i) = 222%Z ->
  check_syscall i eff m = check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_mmap : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  syscall_spec_witness i m = mmap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_mprotect : forall i eff m,
  bv_unsigned (in_sysno i) = 226%Z ->
  check_syscall i eff m = check_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_mprotect : forall i m,
  bv_unsigned (in_sysno i) = 226%Z ->
  syscall_spec_witness i m = mprotect_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_madvise : forall i eff m,
  bv_unsigned (in_sysno i) = 233%Z ->
  check_syscall i eff m = check_madvise (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_madvise : forall i m,
  bv_unsigned (in_sysno i) = 233%Z ->
  syscall_spec_witness i m = madvise_witness (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_recvfrom : forall i eff m,
  bv_unsigned (in_sysno i) = 207%Z ->
  check_syscall i eff m = check_recvfrom i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_recvfrom : forall i m,
  bv_unsigned (in_sysno i) = 207%Z ->
  syscall_spec_witness i m = recvfrom_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_recvmsg : forall i eff m,
  bv_unsigned (in_sysno i) = 212%Z ->
  check_syscall i eff m = check_recvmsg (fd32 (in_arg i 0)) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_recvmsg : forall i m,
  bv_unsigned (in_sysno i) = 212%Z ->
  syscall_spec_witness i m = recvmsg_witness (fd32 (in_arg i 0)) (in_arg i 2) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_accept4 : forall i eff m,
  bv_unsigned (in_sysno i) = 242%Z ->
  check_syscall i eff m = check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_accept4 : forall i m,
  bv_unsigned (in_sysno i) = 242%Z ->
  syscall_spec_witness i m = accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 3) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_wait4 : forall i eff m,
  bv_unsigned (in_sysno i) = 260%Z ->
  check_syscall i eff m = check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_wait4 : forall i m,
  bv_unsigned (in_sysno i) = 260%Z ->
  syscall_spec_witness i m = wait4_witness (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_uname : forall i eff m,
  bv_unsigned (in_sysno i) = 160%Z ->
  check_syscall i eff m = check_uname i (in_arg i 0) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_uname : forall i m,
  bv_unsigned (in_sysno i) = 160%Z ->
  syscall_spec_witness i m = uname_witness (in_arg i 0) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_prlimit64 : forall i eff m,
  bv_unsigned (in_sysno i) = 261%Z ->
  check_syscall i eff m = check_prlimit64 i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_prlimit64 : forall i m,
  bv_unsigned (in_sysno i) = 261%Z ->
  syscall_spec_witness i m = prlimit64_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_getrandom : forall i eff m,
  bv_unsigned (in_sysno i) = 278%Z ->
  check_syscall i eff m = check_getrandom i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_getrandom : forall i m,
  bv_unsigned (in_sysno i) = 278%Z ->
  syscall_spec_witness i m = getrandom_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_clone3 : forall i eff m,
  bv_unsigned (in_sysno i) = 435%Z ->
  check_syscall i eff m = check_clone3 i (in_arg i 0) (in_arg i 1) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_clone3 : forall i m,
  bv_unsigned (in_sysno i) = 435%Z ->
  syscall_spec_witness i m = clone3_witness i (in_arg i 0) (in_arg i 1) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_close_range : forall i eff m,
  bv_unsigned (in_sysno i) = 436%Z ->
  check_syscall i eff m
  = check_close_range (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (flag32 (in_arg i 2)) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_close_range : forall i m,
  bv_unsigned (in_sysno i) = 436%Z ->
  syscall_spec_witness i m
  = close_range_witness (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (flag32 (in_arg i 2)) m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

Lemma check_syscall_faccessat2 : forall i eff m,
  bv_unsigned (in_sysno i) = 439%Z ->
  check_syscall i eff m
  = check_faccessat2 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

Lemma syscall_witness_faccessat2 : forall i m,
  bv_unsigned (in_sysno i) = 439%Z ->
  syscall_spec_witness i m
  = faccessat2_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. intros i m H. unfold syscall_spec_witness. rewrite H. reflexivity. Qed.

(** Rewrite whichever one applies, without naming the syscall.  One entry
    per arm, which is the per-syscall cost this whole table exists to make
    small: a line here, a line in [checked_table], a line in
    [Sys.SyscallTable.spec_table]. *)
Ltac arm_dispatch :=
  first [ erewrite check_syscall_dup by eassumption
        | erewrite check_syscall_dup3 by eassumption
        | erewrite check_syscall_fcntl by eassumption
        | erewrite check_syscall_ioctl by eassumption
        | erewrite check_syscall_flock by eassumption
        | erewrite check_syscall_unlinkat by eassumption
        | erewrite check_syscall_ftruncate by eassumption
        | erewrite check_syscall_faccessat by eassumption
        | erewrite check_syscall_openat by eassumption
        | erewrite check_syscall_close by eassumption
        | erewrite check_syscall_pipe2 by eassumption
        | erewrite check_syscall_lseek by eassumption
        | erewrite check_syscall_read by eassumption
        | erewrite check_syscall_write by eassumption
        | erewrite check_syscall_readv by eassumption
        | erewrite check_syscall_writev by eassumption
        | erewrite check_syscall_pselect6 by eassumption
        | erewrite check_syscall_readlinkat by eassumption
        | erewrite check_syscall_newfstatat by eassumption
        | erewrite check_syscall_fstat by eassumption
        | erewrite check_syscall_fsync by eassumption
        | erewrite check_syscall_fdatasync by eassumption
        | erewrite check_syscall_exit by eassumption
        | erewrite check_syscall_exit_group by eassumption
        | erewrite check_syscall_set_tid_address by eassumption
        | erewrite check_syscall_nanosleep by eassumption
        | erewrite check_syscall_clock_gettime by eassumption
        | erewrite check_syscall_rt_sigaction by eassumption
        | erewrite check_syscall_rt_sigprocmask by eassumption
        | erewrite check_syscall_setsid by eassumption
        | erewrite check_syscall_setgid by eassumption
        | erewrite check_syscall_setuid by eassumption
        | erewrite check_syscall_setresuid by eassumption
        | erewrite check_syscall_setresgid by eassumption
        | erewrite check_syscall_setgroups by eassumption
        | erewrite check_syscall_uname by eassumption
        | erewrite check_syscall_prctl by eassumption
        | erewrite check_syscall_gettimeofday by eassumption
        | erewrite check_syscall_getuid by eassumption
        | erewrite check_syscall_geteuid by eassumption
        | erewrite check_syscall_getgid by eassumption
        | erewrite check_syscall_getegid by eassumption
        | erewrite check_syscall_getpid by eassumption
        | erewrite check_syscall_getppid by eassumption
        | erewrite check_syscall_gettid by eassumption
        | erewrite check_syscall_socket by eassumption
        | erewrite check_syscall_bind by eassumption
        | erewrite check_syscall_listen by eassumption
        | erewrite check_syscall_accept by eassumption
        | erewrite check_syscall_connect by eassumption
        | erewrite check_syscall_recvfrom by eassumption
        | erewrite check_syscall_recvmsg by eassumption
        | erewrite check_syscall_accept4 by eassumption
        | erewrite check_syscall_brk by eassumption
        | erewrite check_syscall_munmap by eassumption
        | erewrite check_syscall_mremap by eassumption
        | erewrite check_syscall_clone by eassumption
        | erewrite check_syscall_mmap by eassumption
        | erewrite check_syscall_mprotect by eassumption
        | erewrite check_syscall_madvise by eassumption
        | erewrite check_syscall_wait4 by eassumption
        | erewrite check_syscall_prlimit64 by eassumption
        | erewrite check_syscall_getrandom by eassumption
        | erewrite check_syscall_clone3 by eassumption
        | erewrite check_syscall_close_range by eassumption
        | erewrite check_syscall_faccessat2 by eassumption ].
