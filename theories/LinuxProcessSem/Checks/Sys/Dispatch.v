(** * LinuxProcessSem.Checks.Sys.Dispatch — a checked syscall, and the tables over them

    [Sys.Dispatch] makes a syscall a value on the spec side.  This does the same
    for the two things the Checks layer adds -- the executable checker and
    the progress witness -- and, crucially, carries the PROOFS relating them
    to that syscall's spec as fields.

    TWO RECORDS, not one, and the reason is the trust boundary: the spec
    layer must not depend on [Checks], so a proof about a checker cannot
    live in a [SpecArm].  A [CheckedArm] therefore holds a [SpecArm] and
    everything the Checks layer knows about it, and [checked_table_arms]
    below pins that the two tables describe the same surface.

    What this buys: the four soundness/completeness theorems and
    [receptive] each become one lookup and one field, instead of one block
    per syscall.  They stop growing when a syscall is added, and adding one
    stops touching them. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
(* The per-syscall modules, not ExecutableSpecs.v and Progress.v: those two
   are what will dispatch over the table built here, so depending on them
   would close a cycle.  The lemmas this file needs are the per-syscall
   ones, and they live one level down. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import
  Prelude Uaccess Fs.DPath Fs.File Fs.ReadWrite Fs.Open Fs.Sync Fs.Stat Fs.Select
  Fs.Ioctl Fs.Fcntl Fs.Locks Fs.Namei Fs.Readdir Fs.Timerfd Fs.Pipe
  Fs.EventPoll Fs.EventFd Mm.Mmap Mm.Mremap Mm.Mprotect Mm.Madvise Kernel.Exit
  Kernel.Fork Kernel.Futex.Syscalls Kernel.Groups
  Kernel.Sched.Syscalls
  Kernel.Signal Kernel.Sys Kernel.Time.Hrtimer Kernel.Time.PosixTimers
  Kernel.Time.Time
  Net.Socket
  Drivers.Char.Random.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Import
  Prelude Uaccess Fs.DPath Fs.File Fs.ReadWrite Fs.Open Fs.Sync Fs.Stat Fs.Select
  Fs.Ioctl Fs.Fcntl Fs.Locks Fs.Namei Fs.Readdir Fs.Timerfd Fs.Pipe
  Fs.EventPoll Fs.EventFd Mm.Mmap Mm.Mremap Mm.Mprotect Mm.Madvise Kernel.Exit
  Kernel.Fork Kernel.Futex.Syscalls Kernel.Groups
  Kernel.Sched.Syscalls Kernel.Signal Kernel.Sys
  Kernel.Time.Hrtimer Kernel.Time.PosixTimers Kernel.Time.Time
  Net.Socket
  Drivers.Char.Random.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** One modeled syscall, with its checker, its witness, and the five facts
    that tie them to its spec.  Holding the proofs as FIELDS is what makes
    the dispatcher's theorems constant-size: the theorem does the lookup,
    the field does the work. *)
Record CheckedArm := mkCheckedArm {
  ca_arm     : SpecArm;
  ca_check   : SyscallInput -> SyscallEffect -> Model -> check_result;
  ca_witness : SyscallInput -> Model -> outcome SyscallEffect;

  ca_sound_ok : forall i eff m m' evs,
    ca_check i eff m = CheckOk m' evs -> sa_spec ca_arm i m (Ok eff m' evs);
  ca_sound_unmodeled : forall i eff m,
    ca_check i eff m = CheckUnmodeled -> sa_spec ca_arm i m Unmodeled;
  ca_complete_ok : forall i eff m m' evs,
    sa_spec ca_arm i m (Ok eff m' evs) -> ca_check i eff m = CheckOk m' evs;
  ca_complete_unmodeled : forall i m eff,
    sa_spec ca_arm i m Unmodeled -> ca_check i eff m = CheckUnmodeled;
  ca_receptive : forall i m, sa_spec ca_arm i m (ca_witness i m);
}.

Definition ca_no (c : CheckedArm) : Z := sa_no (ca_arm c).

Fixpoint lookup_ca (t : list CheckedArm) (n : Z) : option CheckedArm :=
  match t with
  | [] => None
  | c :: r => if Z.eqb (ca_no c) n then Some c else lookup_ca r n
  end.

(** The two lookups agree, which is what lets a theorem stated over
    [Specs.syscall_spec] be discharged by a [CheckedArm]'s field.  Proved
    once, by induction on the table; it does not grow with the surface. *)
Lemma lookup_ca_arm : forall t n,
  lookup_arm (map ca_arm t) n = option_map ca_arm (lookup_ca t n).
Proof.
  induction t as [|c r IH]; intros n; [reflexivity|].
  cbn [map lookup_arm lookup_ca option_map]; unfold ca_no.
  (* the two tables' guards must be the SAME term before the destruct
     reaches both of them, which is what unfolding ca_no does *)
  destruct (Z.eqb (sa_no (ca_arm c)) n); [reflexivity|apply IH].
Qed.

(** getcwd (17). *)
Definition arm_getcwd : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 17%Z (fun i => getcwd_spec (in_arg i 1) i))
                       (fun i eff m => check_getcwd (in_arg i 1) eff m)
                       (fun i m => getcwd_witness (in_arg i 1) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getcwd_sound_ok, check_getcwd_sound_unmodeled, check_getcwd_complete_ok, check_getcwd_complete_unmodeled, getcwd_witness_ok.
Defined.

(** eventfd2 (19).  [flag32] is applied HERE, at the ABI boundary,
    exactly as [timerfd_create]'s and [epoll_create1]'s flag words are:
    the kernel's own narrowing happens in the syscall wrapper, so the
    spec, the acceptor and the witness all receive a word already cut to
    32 bits and none of them narrows again.

    THE FLAG WORD IS ARGUMENT 1, NOT ARGUMENT 0.
    [SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)] puts
    the initial counter first, so an arm that read [in_arg i 0] would be
    judging the counter against a flag mask -- which is not a decline
    but a wrong answer, since [eventfd2(1, 0)] would then take the
    -EINVAL Linux gives no [count] at all.  [in_arg i 1] is the flag
    word. *)
Definition arm_eventfd2 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 19%Z (fun i => eventfd2_spec (flag32 (in_arg i 1)) i))
                       (fun i eff m => check_eventfd2 (flag32 (in_arg i 1)) eff m)
                       (fun i m => eventfd2_witness (flag32 (in_arg i 1)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_eventfd2_sound_ok, check_eventfd2_sound_unmodeled, check_eventfd2_complete_ok, check_eventfd2_complete_unmodeled, eventfd2_witness_ok.
Defined.

(** epoll_create1 (20). *)
Definition arm_epoll_create1 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 20%Z (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i))
                       (fun i eff m => check_epoll_create1 (flag32 (in_arg i 0)) eff m)
                       (fun i m => epoll_create1_witness (flag32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_epoll_create1_sound_ok, check_epoll_create1_sound_unmodeled, check_epoll_create1_complete_ok, check_epoll_create1_complete_unmodeled, epoll_create1_witness_ok.
Defined.

(** epoll_ctl (21). *)
Definition arm_epoll_ctl : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 21%Z (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i))
                       (fun i eff m => check_epoll_ctl i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m)
                       (fun i m => epoll_ctl_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_epoll_ctl_sound_ok, check_epoll_ctl_sound_unmodeled, check_epoll_ctl_complete_ok, check_epoll_ctl_complete_unmodeled, epoll_ctl_witness_ok.
Defined.

(** epoll_pwait (22). *)
Definition arm_epoll_pwait : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 22%Z (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i))
                       (fun i eff m => check_epoll_pwait i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m)
                       (fun i m => epoll_pwait_witness (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_epoll_pwait_sound_ok, check_epoll_pwait_sound_unmodeled, check_epoll_pwait_complete_ok, check_epoll_pwait_complete_unmodeled, epoll_pwait_witness_ok.
Defined.

(** dup (23). *)
Definition arm_dup : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 23%Z (fun i => dup_spec (fd32 (in_arg i 0)) i))
                       (fun i eff m => check_dup (fd32 (in_arg i 0)) eff m)
                       (fun i m => dup_witness (fd32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_dup_sound_ok, check_dup_sound_unmodeled, check_dup_complete_ok, check_dup_complete_unmodeled, dup_witness_ok.
Defined.

(** dup3 (24). *)
Definition arm_dup3 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 24%Z (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i))
                       (fun i eff m => check_dup3 (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m)
                       (fun i m => dup3_witness (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_dup3_sound_ok, check_dup3_sound_unmodeled, check_dup3_complete_ok, check_dup3_complete_unmodeled, dup3_witness_ok.
Defined.

(** fcntl (25). *)
Definition arm_fcntl : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 25%Z (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i))
                       (fun i eff m => check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m)
                       (fun i m => fcntl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_fcntl_sound_ok, check_fcntl_sound_unmodeled, check_fcntl_complete_ok, check_fcntl_complete_unmodeled, fcntl_witness_ok.
Defined.

(** ioctl (29). *)
Definition arm_ioctl : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 29%Z (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i))
                       (fun i eff m => check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m)
                       (fun i m => ioctl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_ioctl_sound_ok, check_ioctl_sound_unmodeled, check_ioctl_complete_ok, check_ioctl_complete_unmodeled, ioctl_witness_ok.
Defined.

(** flock (32). *)
Definition arm_flock : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 32%Z (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i))
                       (fun i eff m => check_flock (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m)
                       (fun i m => flock_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_flock_sound_ok, check_flock_sound_unmodeled, check_flock_complete_ok, check_flock_complete_unmodeled, flock_witness_ok.
Defined.

(** unlinkat (35). *)
Definition arm_unlinkat : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 35%Z (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_unlinkat_sound_ok, check_unlinkat_sound_unmodeled, check_unlinkat_complete_ok, check_unlinkat_complete_unmodeled, unlinkat_witness_ok.
Defined.

(** ftruncate (46). *)
Definition arm_ftruncate : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 46%Z (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i))
                       (fun i eff m => check_ftruncate (fd32 (in_arg i 0)) (in_arg i 1) eff m)
                       (fun i m => ftruncate_witness (fd32 (in_arg i 0)) (in_arg i 1) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_ftruncate_sound_ok, check_ftruncate_sound_unmodeled, check_ftruncate_complete_ok, check_ftruncate_complete_unmodeled, ftruncate_witness_ok.
Defined.

(** faccessat (48). *)
Definition arm_faccessat : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 48%Z (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_faccessat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => faccessat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_faccessat_sound_ok, check_faccessat_sound_unmodeled, check_faccessat_complete_ok, check_faccessat_complete_unmodeled, faccessat_witness_ok.
Defined.

(** openat (56). *)
Definition arm_openat : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 56%Z (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_openat_sound_ok, check_openat_sound_unmodeled, check_openat_complete_ok, check_openat_complete_unmodeled, openat_witness_ok.
Defined.

(** close (57). *)
Definition arm_close : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 57%Z (fun i => close_spec (fd32 (in_arg i 0)) i))
                       (fun i eff m => check_close (fd32 (in_arg i 0)) eff m)
                       (fun i m => close_witness (fd32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_close_sound_ok, check_close_sound_unmodeled, check_close_complete_ok, check_close_complete_unmodeled, close_witness_ok.
Defined.

(** pipe2 (59). *)
Definition arm_pipe2 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 59%Z (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i))
                       (fun i eff m => check_pipe2 i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m)
                       (fun i m => pipe2_witness (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_pipe2_sound_ok, check_pipe2_sound_unmodeled, check_pipe2_complete_ok, check_pipe2_complete_unmodeled, pipe2_witness_ok.
Defined.

(** getdents64 (61). *)
Definition arm_getdents64 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 61%Z (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i))
                       (fun i eff m => check_getdents64 (fd32 (in_arg i 0)) (in_arg i 2) eff m)
                       (fun i m => getdents64_witness (fd32 (in_arg i 0)) (in_arg i 2) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getdents64_sound_ok, check_getdents64_sound_unmodeled, check_getdents64_complete_ok, check_getdents64_complete_unmodeled, getdents64_witness_ok.
Defined.

(** lseek (62). *)
Definition arm_lseek : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 62%Z (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i))
                       (fun i eff m => check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m)
                       (fun i m => lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_lseek_sound_ok, check_lseek_sound_unmodeled, check_lseek_complete_ok, check_lseek_complete_unmodeled, lseek_witness_ok.
Defined.

(** read (63). *)
Definition arm_read : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 63%Z (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => read_witness  (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_read_sound_ok, check_read_sound_unmodeled, check_read_complete_ok, check_read_complete_unmodeled, read_witness_ok.
Defined.

(** write (64). *)
Definition arm_write : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 64%Z (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_write_sound_ok, check_write_sound_unmodeled, check_write_complete_ok, check_write_complete_unmodeled, write_witness_ok.
Defined.

(** readv (65). *)
Definition arm_readv : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 65%Z (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_readv_sound_ok, check_readv_sound_unmodeled, check_readv_complete_ok, check_readv_complete_unmodeled, readv_witness_ok.
Defined.

(** writev (66). *)
Definition arm_writev : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 66%Z (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_writev_sound_ok, check_writev_sound_unmodeled, check_writev_complete_ok, check_writev_complete_unmodeled, writev_witness_ok.
Defined.

(** pread64 (67). *)
Definition arm_pread64 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 67%Z (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_pread64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => pread64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_pread64_sound_ok, check_pread64_sound_unmodeled, check_pread64_complete_ok, check_pread64_complete_unmodeled, pread64_witness_ok.
Defined.

(** pwrite64 (68). *)
Definition arm_pwrite64 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 68%Z (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_pwrite64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => pwrite64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_pwrite64_sound_ok, check_pwrite64_sound_unmodeled, check_pwrite64_complete_ok, check_pwrite64_complete_unmodeled, pwrite64_witness_ok.
Defined.

(** pselect6 (72). *)
Definition arm_pselect6 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 72%Z (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i))
                       (fun i eff m => check_pselect6 i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m)
                       (fun i m => pselect6_witness i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_pselect6_sound_ok, check_pselect6_sound_unmodeled, check_pselect6_complete_ok, check_pselect6_complete_unmodeled, pselect6_witness_ok.
Defined.

(** ppoll (73). *)
Definition arm_ppoll : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 73%Z (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i))
                       (fun i eff m => check_ppoll i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m)
                       (fun i m => ppoll_witness i m (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4))
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_ppoll_sound_ok, check_ppoll_sound_unmodeled, check_ppoll_complete_ok, check_ppoll_complete_unmodeled, ppoll_witness_ok.
Defined.

(** readlinkat (78). *)
Definition arm_readlinkat : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 78%Z (fun i => readlinkat_spec (fd32 (in_arg i 0)) i))
                       (fun i eff m => check_readlinkat (fd32 (in_arg i 0)) eff m)
                       (fun i m => readlinkat_witness (fd32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_readlinkat_sound_ok, check_readlinkat_sound_unmodeled, check_readlinkat_complete_ok, check_readlinkat_complete_unmodeled, readlinkat_witness_ok.
Defined.

(** newfstatat (79). *)
Definition arm_newfstatat : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 79%Z (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i))
                       (fun i eff m => check_newfstatat i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m)
                       (fun i m => newfstatat_witness (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_newfstatat_sound_ok, check_newfstatat_sound_unmodeled, check_newfstatat_complete_ok, check_newfstatat_complete_unmodeled, newfstatat_witness_ok.
Defined.

(** fstat (80). *)
Definition arm_fstat : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 80%Z (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i))
                       (fun i eff m => check_fstat i (fd32 (in_arg i 0)) (in_arg i 1) eff m)
                       (fun i m => fstat_witness (fd32 (in_arg i 0)) (in_arg i 1) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_fstat_sound_ok, check_fstat_sound_unmodeled, check_fstat_complete_ok, check_fstat_complete_unmodeled, fstat_witness_ok.
Defined.

(** fsync (82). *)
Definition arm_fsync : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 82%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i))
                       (fun i eff m => check_fsync (fd32 (in_arg i 0)) eff m)
                       (fun i m => fsync_witness (fd32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_fsync_sound_ok, check_fsync_sound_unmodeled, check_fsync_complete_ok, check_fsync_complete_unmodeled, fsync_witness_ok.
Defined.

(** fdatasync (83). *)
Definition arm_fdatasync : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 83%Z (fun i => fsync_spec (fd32 (in_arg i 0)) i))
                       (fun i eff m => check_fsync (fd32 (in_arg i 0)) eff m)
                       (fun i m => fsync_witness (fd32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_fsync_sound_ok, check_fsync_sound_unmodeled, check_fsync_complete_ok, check_fsync_complete_unmodeled, fsync_witness_ok.
Defined.

(** timerfd_create (85).  [clockid32] and [flag32] are applied HERE, at
    the ABI boundary, exactly as [clock_gettime]'s id is: the kernel's
    own narrowing happens in the syscall wrapper, so the spec, the
    acceptor and the witness all receive words already cut to 32 bits
    and none of them narrows again. *)
Definition arm_timerfd_create : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 85%Z (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i))
                       (fun i eff m => check_timerfd_create (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) eff m)
                       (fun i m => timerfd_create_witness (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_timerfd_create_sound_ok, check_timerfd_create_sound_unmodeled, check_timerfd_create_complete_ok, check_timerfd_create_complete_unmodeled, timerfd_create_witness_ok.
Defined.

(** exit (93). *)
Definition arm_exit : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 93%Z (fun i => exit_spec (in_arg i 0) i))
                       (fun i eff m => check_exit (in_arg i 0) eff m)
                       (fun i m => exit_witness (in_arg i 0) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_exit_sound_ok, check_exit_sound_unmodeled, check_exit_complete_ok, check_exit_complete_unmodeled, exit_witness_ok.
Defined.

(** exit_group (94). *)
Definition arm_exit_group : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 94%Z (fun i => exit_spec (in_arg i 0) i))
                       (fun i eff m => check_exit (in_arg i 0) eff m)
                       (fun i m => exit_witness (in_arg i 0) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_exit_sound_ok, check_exit_sound_unmodeled, check_exit_complete_ok, check_exit_complete_unmodeled, exit_witness_ok.
Defined.

(** set_tid_address (96). *)
Definition arm_set_tid_address : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 96%Z (fun i => set_tid_address_spec i))
                       (fun i eff m => check_set_tid_address eff m)
                       (fun i m => set_tid_address_witness m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_set_tid_address_sound_ok, check_set_tid_address_sound_unmodeled, check_set_tid_address_complete_ok, check_set_tid_address_complete_unmodeled, set_tid_address_witness_ok.
Defined.

(** futex (98). *)
Definition arm_futex : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 98%Z (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_futex i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => futex_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_futex_sound_ok, check_futex_sound_unmodeled, check_futex_complete_ok, check_futex_complete_unmodeled, futex_witness_ok.
Defined.

(** set_robust_list (99). *)
Definition arm_set_robust_list : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 99%Z (fun i => set_robust_list_spec (in_arg i 1) i))
                       (fun i eff m => check_set_robust_list (in_arg i 1) eff m)
                       (fun i m => set_robust_list_witness m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_set_robust_list_sound_ok, check_set_robust_list_sound_unmodeled, check_set_robust_list_complete_ok, check_set_robust_list_complete_unmodeled, set_robust_list_witness_ok.
Defined.

(** nanosleep (101). *)
Definition arm_nanosleep : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 101%Z (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i))
                       (fun i eff m => check_nanosleep i (in_arg i 0) (in_arg i 1) eff m)
                       (fun i m => nanosleep_witness (in_arg i 0) (in_arg i 1) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_nanosleep_sound_ok, check_nanosleep_sound_unmodeled, check_nanosleep_complete_ok, check_nanosleep_complete_unmodeled, nanosleep_witness_ok.
Defined.

(** clock_gettime (113). *)
Definition arm_clock_gettime : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 113%Z (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i))
                       (fun i eff m => check_clock_gettime i (clockid32 (in_arg i 0)) (in_arg i 1) eff m)
                       (fun i m => clock_gettime_witness (clockid32 (in_arg i 0)) (in_arg i 1) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_clock_gettime_sound_ok, check_clock_gettime_sound_unmodeled, check_clock_gettime_complete_ok, check_clock_gettime_complete_unmodeled, clock_gettime_witness_ok.
Defined.

(** clock_getres (114). *)
Definition arm_clock_getres : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 114%Z (fun i => clock_getres_spec (clockid32 (in_arg i 0)) (in_arg i 1) i))
                       (fun i eff m => check_clock_getres i (clockid32 (in_arg i 0)) (in_arg i 1) eff m)
                       (fun i m => clock_getres_witness (clockid32 (in_arg i 0)) (in_arg i 1) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_clock_getres_sound_ok, check_clock_getres_sound_unmodeled, check_clock_getres_complete_ok, check_clock_getres_complete_unmodeled, clock_getres_witness_ok.
Defined.

(** sched_setscheduler (119). *)
Definition arm_sched_setscheduler : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 119%Z (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_sched_setscheduler i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => sched_setscheduler_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_sched_setscheduler_sound_ok, check_sched_setscheduler_sound_unmodeled, check_sched_setscheduler_complete_ok, check_sched_setscheduler_complete_unmodeled, sched_setscheduler_witness_ok.
Defined.

(** sched_getaffinity (123). *)
Definition arm_sched_getaffinity : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 123%Z (fun i => sched_getaffinity_spec (in_arg i 1) i))
                       (fun i eff m => check_sched_getaffinity (in_arg i 1) eff m)
                       (fun i m => sched_getaffinity_witness (in_arg i 1) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_sched_getaffinity_sound_ok, check_sched_getaffinity_sound_unmodeled, check_sched_getaffinity_complete_ok, check_sched_getaffinity_complete_unmodeled, sched_getaffinity_witness_ok.
Defined.

(** sched_yield (124).  The only arm here that reads no argument at all:
    riscv's [SYSCALL_DEFINE0] expands without [SC_RISCV_REGS_TO_ARGS], so
    the input is ignored on purpose rather than by omission
    ([Kernel.Sched.Syscalls.sched_yield_spec]). *)
Definition arm_sched_yield : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 124%Z (fun i => sched_yield_spec i))
                       (fun _ eff m => check_sched_yield eff m)
                       (fun _ m => sched_yield_witness m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_sched_yield_sound_ok, check_sched_yield_sound_unmodeled, check_sched_yield_complete_ok, check_sched_yield_complete_unmodeled, sched_yield_witness_ok.
Defined.

(** tkill (130).  The checker's own answer is [CheckUnmodeled] on every
    shape whenever the model's abort declaration is clear, so an arm on a
    number the task did not ask for behaves as a number with no arm. *)
Definition arm_tkill : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 130%Z (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i))
                       (fun i eff m => check_tkill (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m)
                       (fun i m => tkill_witness (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_tkill_sound_ok, check_tkill_sound_unmodeled, check_tkill_complete_ok, check_tkill_complete_unmodeled, tkill_witness_ok.
Defined.

(** tgkill (131). *)
Definition arm_tgkill : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 131%Z (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i))
                       (fun i eff m => check_tgkill (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m)
                       (fun i m => tgkill_witness (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_tgkill_sound_ok, check_tgkill_sound_unmodeled, check_tgkill_complete_ok, check_tgkill_complete_unmodeled, tgkill_witness_ok.
Defined.
(** sigaltstack (132). *)
Definition arm_sigaltstack : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 132%Z (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i))
                       (fun i eff m => check_sigaltstack i (in_arg i 0) (in_arg i 1) eff m)
                       (fun i m => sigaltstack_witness (in_arg i 0) (in_arg i 1) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_sigaltstack_sound_ok, check_sigaltstack_sound_unmodeled, check_sigaltstack_complete_ok, check_sigaltstack_complete_unmodeled, sigaltstack_witness_ok.
Defined.

(** rt_sigaction (134). *)
Definition arm_rt_sigaction : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 134%Z (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_rt_sigaction i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => rt_sigaction_witness (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_rt_sigaction_sound_ok, check_rt_sigaction_sound_unmodeled, check_rt_sigaction_complete_ok, check_rt_sigaction_complete_unmodeled, rt_sigaction_witness_ok.
Defined.

(** rt_sigprocmask (135). *)
Definition arm_rt_sigprocmask : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 135%Z (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_rt_sigprocmask i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => rt_sigprocmask_witness (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_rt_sigprocmask_sound_ok, check_rt_sigprocmask_sound_unmodeled, check_rt_sigprocmask_complete_ok, check_rt_sigprocmask_complete_unmodeled, rt_sigprocmask_witness_ok.
Defined.

(** setgid (144). *)
Definition arm_setgid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 144%Z (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i))
                       (fun i eff m => check_setid cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m)
                       (fun i m => setid_witness (uid32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_setid_sound_ok, check_setid_sound_unmodeled, check_setid_complete_ok, check_setid_complete_unmodeled, setid_witness_ok.
Defined.

(** setuid (146). *)
Definition arm_setuid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 146%Z (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i))
                       (fun i eff m => check_setid cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m)
                       (fun i m => setid_witness (uid32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_setid_sound_ok, check_setid_sound_unmodeled, check_setid_complete_ok, check_setid_complete_unmodeled, setid_witness_ok.
Defined.

(** setresuid (147). *)
Definition arm_setresuid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 147%Z (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i))
                       (fun i eff m => check_setresid cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m)
                       (fun i m => setresid_witness cred_uids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_setresid_sound_ok, check_setresid_sound_unmodeled, check_setresid_complete_ok, check_setresid_complete_unmodeled, setresid_witness_ok.
Defined.

(** setresgid (149). *)
Definition arm_setresgid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 149%Z (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i))
                       (fun i eff m => check_setresid cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m)
                       (fun i m => setresid_witness cred_gids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_setresid_sound_ok, check_setresid_sound_unmodeled, check_setresid_complete_ok, check_setresid_complete_unmodeled, setresid_witness_ok.
Defined.

(** setsid (157). *)
Definition arm_setsid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 157%Z (fun i => setsid_spec i))
                       (fun i eff m => check_setsid eff m)
                       (fun i m => setsid_witness m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_setsid_sound_ok, check_setsid_sound_unmodeled, check_setsid_complete_ok, check_setsid_complete_unmodeled, setsid_witness_ok.
Defined.

(** getgroups (158). *)
Definition arm_getgroups : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 158%Z (fun i => getgroups_spec (in_arg i 0) i))
                       (fun i eff m => check_getgroups (in_arg i 0) eff m)
                       (fun i m => getgroups_witness (in_arg i 0) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getgroups_sound_ok, check_getgroups_sound_unmodeled, check_getgroups_complete_ok, check_getgroups_complete_unmodeled, getgroups_witness_ok.
Defined.

(** setgroups (159). *)
Definition arm_setgroups : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 159%Z (fun i => setgroups_spec i))
                       (fun i eff m => check_setgroups eff m)
                       (fun i m => setgroups_witness m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_setgroups_sound_ok, check_setgroups_sound_unmodeled, check_setgroups_complete_ok, check_setgroups_complete_unmodeled, setgroups_witness_ok.
Defined.

(** prctl (167). *)
Definition arm_prctl : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 167%Z (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i))
                       (fun i eff m => check_prctl (int32 (in_arg i 0)) (in_arg i 1) eff m)
                       (fun i m => prctl_witness (int32 (in_arg i 0)) (in_arg i 1) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_prctl_sound_ok, check_prctl_sound_unmodeled, check_prctl_complete_ok, check_prctl_complete_unmodeled, prctl_witness_ok.
Defined.

(** gettimeofday (169). *)
Definition arm_gettimeofday : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 169%Z (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i))
                       (fun i eff m => check_gettimeofday i (in_arg i 0) (in_arg i 1) eff m)
                       (fun i m => gettimeofday_witness (in_arg i 0) (in_arg i 1) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_gettimeofday_sound_ok, check_gettimeofday_sound_unmodeled, check_gettimeofday_complete_ok, check_gettimeofday_complete_unmodeled, gettimeofday_witness_ok.
Defined.

(** getpid (172). *)
Definition arm_getpid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 172%Z (fun i => getpid_spec i))
                       (fun i eff m => check_getpid eff m)
                       (fun i m => getpid_witness m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getpid_sound_ok, check_getpid_sound_unmodeled, check_getpid_complete_ok, check_getpid_complete_unmodeled, getpid_witness_ok.
Defined.

(** getuid (174). *)
Definition arm_getuid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 174%Z (fun i => getid_spec cr_uid i))
                       (fun i eff m => check_getid cr_uid eff m)
                       (fun i m => getid_witness cr_uid m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getid_sound_ok, check_getid_sound_unmodeled, check_getid_complete_ok, check_getid_complete_unmodeled, getid_witness_ok.
Defined.

(** geteuid (175). *)
Definition arm_geteuid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 175%Z (fun i => getid_spec cr_euid i))
                       (fun i eff m => check_getid cr_euid eff m)
                       (fun i m => getid_witness cr_euid m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getid_sound_ok, check_getid_sound_unmodeled, check_getid_complete_ok, check_getid_complete_unmodeled, getid_witness_ok.
Defined.

(** getgid (176). *)
Definition arm_getgid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 176%Z (fun i => getid_spec cr_gid i))
                       (fun i eff m => check_getid cr_gid eff m)
                       (fun i m => getid_witness cr_gid m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getid_sound_ok, check_getid_sound_unmodeled, check_getid_complete_ok, check_getid_complete_unmodeled, getid_witness_ok.
Defined.

(** getegid (177). *)
Definition arm_getegid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 177%Z (fun i => getid_spec cr_egid i))
                       (fun i eff m => check_getid cr_egid eff m)
                       (fun i m => getid_witness cr_egid m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getid_sound_ok, check_getid_sound_unmodeled, check_getid_complete_ok, check_getid_complete_unmodeled, getid_witness_ok.
Defined.

(** gettid (178). *)
Definition arm_gettid : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 178%Z (fun i => gettid_spec i))
                       (fun i eff m => check_gettid eff m)
                       (fun i m => gettid_witness m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_gettid_sound_ok, check_gettid_sound_unmodeled, check_gettid_complete_ok, check_gettid_complete_unmodeled, gettid_witness_ok.
Defined.

(** socket (198). *)
Definition arm_socket : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 198%Z (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => socket_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_socket_sound_ok, check_socket_sound_unmodeled, check_socket_complete_ok, check_socket_complete_unmodeled, socket_witness_ok.
Defined.

(** socketpair (199). *)
Definition arm_socketpair : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 199%Z (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_socketpair i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => socketpair_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_socketpair_sound_ok, check_socketpair_sound_unmodeled, check_socketpair_complete_ok, check_socketpair_complete_unmodeled, socketpair_witness_ok.
Defined.

(** bind (200). *)
Definition arm_bind : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 200%Z (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_bind i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => bind_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_bind_sound_ok, check_bind_sound_unmodeled, check_bind_complete_ok, check_bind_complete_unmodeled, bind_witness_ok.
Defined.

(** listen (201). *)
Definition arm_listen : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 201%Z (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i))
                       (fun i eff m => check_listen (fd32 (in_arg i 0)) (in_arg i 1) eff m)
                       (fun i m => listen_witness (fd32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_listen_sound_ok, check_listen_sound_unmodeled, check_listen_complete_ok, check_listen_complete_unmodeled, listen_witness_ok.
Defined.

(** accept (202). *)
Definition arm_accept : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 202%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i))
                       (fun i eff m => check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m)
                       (fun i m => accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (Z_to_bv 64 0) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_accept4_sound_ok, check_accept4_sound_unmodeled, check_accept4_complete_ok, check_accept4_complete_unmodeled, accept4_witness_ok.
Defined.

(** connect (203). *)
Definition arm_connect : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 203%Z (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_connect i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => connect_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_connect_sound_ok, check_connect_sound_unmodeled, check_connect_complete_ok, check_connect_complete_unmodeled, connect_witness_ok.
Defined.

(** getsockname (204). *)
Definition arm_getsockname : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 204%Z (fun i => getsockname_spec (fd32 (in_arg i 0)) i))
                       (fun i eff m => check_getsockname (fd32 (in_arg i 0)) eff m)
                       (fun i m => getsockname_witness (fd32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getsockname_sound_ok, check_getsockname_sound_unmodeled, check_getsockname_complete_ok, check_getsockname_complete_unmodeled, getsockname_witness_ok.
Defined.

(** getpeername (205). *)
Definition arm_getpeername : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 205%Z (fun i => getpeername_spec (fd32 (in_arg i 0)) i))
                       (fun i eff m => check_getpeername (fd32 (in_arg i 0)) eff m)
                       (fun i m => getpeername_witness (fd32 (in_arg i 0)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getpeername_sound_ok, check_getpeername_sound_unmodeled, check_getpeername_complete_ok, check_getpeername_complete_unmodeled, getpeername_witness_ok.
Defined.

(** sendto (206). *)
Definition arm_sendto : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 206%Z (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i))
                       (fun i eff m => check_sendto i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m)
                       (fun i m => sendto_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_sendto_sound_ok, check_sendto_sound_unmodeled, check_sendto_complete_ok, check_sendto_complete_unmodeled, sendto_witness_ok.
Defined.

(** recvfrom (207). *)
Definition arm_recvfrom : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 207%Z (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_recvfrom i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => recvfrom_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_recvfrom_sound_ok, check_recvfrom_sound_unmodeled, check_recvfrom_complete_ok, check_recvfrom_complete_unmodeled, recvfrom_witness_ok.
Defined.

(** setsockopt (208). *)
Definition arm_setsockopt : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 208%Z (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i))
                       (fun i eff m => check_setsockopt (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m)
                       (fun i m => setsockopt_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_setsockopt_sound_ok, check_setsockopt_sound_unmodeled, check_setsockopt_complete_ok, check_setsockopt_complete_unmodeled, setsockopt_witness_ok.
Defined.

(** getsockopt (209). *)
Definition arm_getsockopt : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 209%Z (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i))
                       (fun i eff m => check_getsockopt i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m)
                       (fun i m => getsockopt_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getsockopt_sound_ok, check_getsockopt_sound_unmodeled, check_getsockopt_complete_ok, check_getsockopt_complete_unmodeled, getsockopt_witness_ok.
Defined.

(** shutdown (210). *)
Definition arm_shutdown : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 210%Z (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i))
                       (fun i eff m => check_shutdown (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m)
                       (fun i m => shutdown_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_shutdown_sound_ok, check_shutdown_sound_unmodeled, check_shutdown_complete_ok, check_shutdown_complete_unmodeled, shutdown_witness_ok.
Defined.

(** sendmsg (211). *)
Definition arm_sendmsg : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 211%Z (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_sendmsg i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => sendmsg_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_sendmsg_sound_ok, check_sendmsg_sound_unmodeled, check_sendmsg_complete_ok, check_sendmsg_complete_unmodeled, sendmsg_witness_ok.
Defined.

(** brk (214). *)
Definition arm_brk : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 214%Z (fun i => brk_spec (in_arg i 0) i))
                       (fun i eff m => check_brk (in_arg i 0) eff m)
                       (fun i m => brk_witness (in_arg i 0) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_brk_sound_ok, check_brk_sound_unmodeled, check_brk_complete_ok, check_brk_complete_unmodeled, brk_witness_ok.
Defined.

(** munmap (215). *)
Definition arm_munmap : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 215%Z (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i))
                       (fun i eff m => check_munmap (in_arg i 0) (in_arg i 1) eff m)
                       (fun i m => munmap_witness (in_arg i 0) (in_arg i 1) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_munmap_sound_ok, check_munmap_sound_unmodeled, check_munmap_complete_ok, check_munmap_complete_unmodeled, munmap_witness_ok.
Defined.

(** mremap (216). *)
Definition arm_mremap : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 216%Z (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_mremap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => mremap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_mremap_sound_ok, check_mremap_sound_unmodeled, check_mremap_complete_ok, check_mremap_complete_unmodeled, mremap_witness_ok.
Defined.

(** clone (220). *)
Definition arm_clone : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 220%Z (fun i => clone_spec (in_arg i 0) i))
                       (fun i eff m => check_clone (in_arg i 0) eff m)
                       (fun i m => clone_witness (in_arg i 0) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_clone_sound_ok, check_clone_sound_unmodeled, check_clone_complete_ok, check_clone_complete_unmodeled, clone_witness_ok.
Defined.

(** mmap (222). *)
Definition arm_mmap : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 222%Z (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i))
                       (fun i eff m => check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m)
                       (fun i m => mmap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_mmap_sound_ok, check_mmap_sound_unmodeled, check_mmap_complete_ok, check_mmap_complete_unmodeled, mmap_witness_ok.
Defined.

(** mprotect (226). *)
Definition arm_mprotect : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 226%Z (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => mprotect_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_mprotect_sound_ok, check_mprotect_sound_unmodeled, check_mprotect_complete_ok, check_mprotect_complete_unmodeled, mprotect_witness_ok.
Defined.

(** madvise (233). *)
Definition arm_madvise : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 233%Z (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i))
                       (fun i eff m => check_madvise (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m)
                       (fun i m => madvise_witness (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_madvise_sound_ok, check_madvise_sound_unmodeled, check_madvise_complete_ok, check_madvise_complete_unmodeled, madvise_witness_ok.
Defined.

(** recvmsg (212). *)
Definition arm_recvmsg : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 212%Z (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i))
                       (fun i eff m => check_recvmsg (fd32 (in_arg i 0)) (in_arg i 2) eff m)
                       (fun i m => recvmsg_witness (fd32 (in_arg i 0)) (in_arg i 2) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_recvmsg_sound_ok, check_recvmsg_sound_unmodeled, check_recvmsg_complete_ok, check_recvmsg_complete_unmodeled, recvmsg_witness_ok.
Defined.

(** accept4 (242). *)
Definition arm_accept4 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 242%Z (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 3) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_accept4_sound_ok, check_accept4_sound_unmodeled, check_accept4_complete_ok, check_accept4_complete_unmodeled, accept4_witness_ok.
Defined.

(** wait4 (260). *)
Definition arm_wait4 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 260%Z (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i))
                       (fun i eff m => check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m)
                       (fun i m => wait4_witness (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_wait4_sound_ok, check_wait4_sound_unmodeled, check_wait4_complete_ok, check_wait4_complete_unmodeled, wait4_witness_ok.
Defined.

(** uname (160). *)
Definition arm_uname : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 160%Z (fun i => uname_spec (in_arg i 0) i))
                       (fun i eff m => check_uname i (in_arg i 0) eff m)
                       (fun i m => uname_witness (in_arg i 0) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_uname_sound_ok, check_uname_sound_unmodeled, check_uname_complete_ok, check_uname_complete_unmodeled, uname_witness_ok.
Defined.

(** prlimit64 (261). *)
Definition arm_prlimit64 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 261%Z (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_prlimit64 i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => prlimit64_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_prlimit64_sound_ok, check_prlimit64_sound_unmodeled, check_prlimit64_complete_ok, check_prlimit64_complete_unmodeled, prlimit64_witness_ok.
Defined.

(** getrandom (278). *)
Definition arm_getrandom : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 278%Z (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i))
                       (fun i eff m => check_getrandom i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m)
                       (fun i m => getrandom_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_getrandom_sound_ok, check_getrandom_sound_unmodeled, check_getrandom_complete_ok, check_getrandom_complete_unmodeled, getrandom_witness_ok.
Defined.

(** clone3 (435). *)
Definition arm_clone3 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 435%Z (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i))
                       (fun i eff m => check_clone3 i (in_arg i 0) (in_arg i 1) eff m)
                       (fun i m => clone3_witness i (in_arg i 0) (in_arg i 1) m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_clone3_sound_ok, check_clone3_sound_unmodeled, check_clone3_complete_ok, check_clone3_complete_unmodeled, clone3_witness_ok.
Defined.

(** faccessat2 (439). *)
Definition arm_faccessat2 : CheckedArm.
Proof.
  refine (mkCheckedArm (mkSpecArm 439%Z (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i))
                       (fun i eff m => check_faccessat2 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m)
                       (fun i m => faccessat2_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m)
                       _ _ _ _ _);
    cbn [sa_spec sa_no]; intros;
    eauto using check_faccessat2_sound_ok, check_faccessat2_sound_unmodeled, check_faccessat2_complete_ok, check_faccessat2_complete_unmodeled, faccessat2_witness_ok.
Defined.
(** The checked surface, in syscall-number order, one arm per line. *)
Definition checked_table : list CheckedArm :=
  arm_getcwd ::
  arm_eventfd2 ::
  arm_epoll_create1 ::
  arm_epoll_ctl ::
  arm_epoll_pwait ::
  arm_dup ::
  arm_dup3 ::
  arm_fcntl ::
  arm_ioctl ::
  arm_flock ::
  arm_unlinkat ::
  arm_ftruncate ::
  arm_faccessat ::
  arm_openat ::
  arm_close ::
  arm_pipe2 ::
  arm_getdents64 ::
  arm_lseek ::
  arm_read ::
  arm_write ::
  arm_readv ::
  arm_writev ::
  arm_pread64 ::
  arm_pwrite64 ::
  arm_pselect6 ::
  arm_ppoll ::
  arm_readlinkat ::
  arm_newfstatat ::
  arm_fstat ::
  arm_fsync ::
  arm_fdatasync ::
  arm_timerfd_create ::
  arm_exit ::
  arm_exit_group ::
  arm_set_tid_address ::
  arm_futex ::
  arm_set_robust_list ::
  arm_nanosleep ::
  arm_clock_gettime ::
  arm_clock_getres ::
  arm_sched_setscheduler ::
  arm_sched_getaffinity ::
  arm_sched_yield ::
  arm_tkill ::
  arm_tgkill ::
  arm_sigaltstack ::
  arm_rt_sigaction ::
  arm_rt_sigprocmask ::
  arm_setgid ::
  arm_setuid ::
  arm_setresuid ::
  arm_setresgid ::
  arm_setsid ::
  arm_getgroups ::
  arm_setgroups ::
  arm_uname ::
  arm_prctl ::
  arm_gettimeofday ::
  arm_getpid ::
  arm_getuid ::
  arm_geteuid ::
  arm_getgid ::
  arm_getegid ::
  arm_gettid ::
  arm_socket ::
  arm_socketpair ::
  arm_bind ::
  arm_listen ::
  arm_accept ::
  arm_connect ::
  arm_getsockname ::
  arm_getpeername ::
  arm_sendto ::
  arm_recvfrom ::
  arm_setsockopt ::
  arm_getsockopt ::
  arm_shutdown ::
  arm_sendmsg ::
  arm_recvmsg ::
  arm_brk ::
  arm_munmap ::
  arm_mremap ::
  arm_clone ::
  arm_mmap ::
  arm_mprotect ::
  arm_madvise ::
  arm_accept4 ::
  arm_wait4 ::
  arm_prlimit64 ::
  arm_getrandom ::
  arm_clone3 ::
  arm_faccessat2 ::
  nil.
(** The two tables describe the same surface.  [reflexivity] rather than a
    proof: each [CheckedArm] was built around the very [SpecArm] the spec
    table lists, so if this ever fails the two lists have drifted, which is
    exactly the failure the single-table design exists to prevent. *)
Lemma checked_table_arms : map ca_arm checked_table = spec_table.
Proof. reflexivity. Qed.

(** Each arm's three components, pointwise, so a proof that has resolved the
    lookup can get back to the plain [check_*] / [*_witness] / [*_spec] shape
    it was written against.  Every one is [reflexivity]: the arm IS that
    component, and these only give [rewrite] a handle on a constant [cbn]
    will not unfold, because [refine] built it.

    Registered in the [arm_unfold] database, so a caller writes
    [autorewrite with arm_unfold] and does not have to name the syscall. *)

Lemma ca_check_arm_getcwd : forall i eff m,
  ca_check arm_getcwd i eff m = check_getcwd (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getcwd : forall i m,
  ca_witness arm_getcwd i m = getcwd_witness (in_arg i 1) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getcwd : forall i m o,
  sa_spec (ca_arm arm_getcwd) i m o = getcwd_spec (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_eventfd2 : forall i eff m,
  ca_check arm_eventfd2 i eff m = check_eventfd2 (flag32 (in_arg i 1)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_eventfd2 : forall i m,
  ca_witness arm_eventfd2 i m = eventfd2_witness (flag32 (in_arg i 1)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_eventfd2 : forall i m o,
  sa_spec (ca_arm arm_eventfd2) i m o = eventfd2_spec (flag32 (in_arg i 1)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_epoll_create1 : forall i eff m,
  ca_check arm_epoll_create1 i eff m = check_epoll_create1 (flag32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_epoll_create1 : forall i m,
  ca_witness arm_epoll_create1 i m = epoll_create1_witness (flag32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_epoll_create1 : forall i m o,
  sa_spec (ca_arm arm_epoll_create1) i m o = epoll_create1_spec (flag32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_epoll_ctl : forall i eff m,
  ca_check arm_epoll_ctl i eff m = check_epoll_ctl i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_epoll_ctl : forall i m,
  ca_witness arm_epoll_ctl i m = epoll_ctl_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_epoll_ctl : forall i m o,
  sa_spec (ca_arm arm_epoll_ctl) i m o = epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_epoll_pwait : forall i eff m,
  ca_check arm_epoll_pwait i eff m = check_epoll_pwait i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_epoll_pwait : forall i m,
  ca_witness arm_epoll_pwait i m = epoll_pwait_witness (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_epoll_pwait : forall i m o,
  sa_spec (ca_arm arm_epoll_pwait) i m o = epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_dup : forall i eff m,
  ca_check arm_dup i eff m = check_dup (fd32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_dup : forall i m,
  ca_witness arm_dup i m = dup_witness (fd32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_dup : forall i m o,
  sa_spec (ca_arm arm_dup) i m o = dup_spec (fd32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_dup3 : forall i eff m,
  ca_check arm_dup3 i eff m = check_dup3 (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_dup3 : forall i m,
  ca_witness arm_dup3 i m = dup3_witness (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_dup3 : forall i m o,
  sa_spec (ca_arm arm_dup3) i m o = dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_fcntl : forall i eff m,
  ca_check arm_fcntl i eff m = check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_fcntl : forall i m,
  ca_witness arm_fcntl i m = fcntl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_fcntl : forall i m o,
  sa_spec (ca_arm arm_fcntl) i m o = fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_ioctl : forall i eff m,
  ca_check arm_ioctl i eff m = check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_ioctl : forall i m,
  ca_witness arm_ioctl i m = ioctl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_ioctl : forall i m o,
  sa_spec (ca_arm arm_ioctl) i m o = ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_flock : forall i eff m,
  ca_check arm_flock i eff m = check_flock (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_flock : forall i m,
  ca_witness arm_flock i m = flock_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_flock : forall i m o,
  sa_spec (ca_arm arm_flock) i m o = flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_unlinkat : forall i eff m,
  ca_check arm_unlinkat i eff m = check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_unlinkat : forall i m,
  ca_witness arm_unlinkat i m = unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_unlinkat : forall i m o,
  sa_spec (ca_arm arm_unlinkat) i m o = unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_ftruncate : forall i eff m,
  ca_check arm_ftruncate i eff m = check_ftruncate (fd32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_ftruncate : forall i m,
  ca_witness arm_ftruncate i m = ftruncate_witness (fd32 (in_arg i 0)) (in_arg i 1) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_ftruncate : forall i m o,
  sa_spec (ca_arm arm_ftruncate) i m o = ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_faccessat : forall i eff m,
  ca_check arm_faccessat i eff m = check_faccessat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_faccessat : forall i m,
  ca_witness arm_faccessat i m = faccessat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_faccessat : forall i m o,
  sa_spec (ca_arm arm_faccessat) i m o = faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_openat : forall i eff m,
  ca_check arm_openat i eff m = check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_openat : forall i m,
  ca_witness arm_openat i m = openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_openat : forall i m o,
  sa_spec (ca_arm arm_openat) i m o = openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_close : forall i eff m,
  ca_check arm_close i eff m = check_close (fd32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_close : forall i m,
  ca_witness arm_close i m = close_witness (fd32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_close : forall i m o,
  sa_spec (ca_arm arm_close) i m o = close_spec (fd32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_pipe2 : forall i eff m,
  ca_check arm_pipe2 i eff m
  = check_pipe2 i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_pipe2 : forall i m,
  ca_witness arm_pipe2 i m
  = pipe2_witness (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_pipe2 : forall i m o,
  sa_spec (ca_arm arm_pipe2) i m o
  = pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getdents64 : forall i eff m,
  ca_check arm_getdents64 i eff m = check_getdents64 (fd32 (in_arg i 0)) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getdents64 : forall i m,
  ca_witness arm_getdents64 i m = getdents64_witness (fd32 (in_arg i 0)) (in_arg i 2) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getdents64 : forall i m o,
  sa_spec (ca_arm arm_getdents64) i m o = getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_lseek : forall i eff m,
  ca_check arm_lseek i eff m = check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_lseek : forall i m,
  ca_witness arm_lseek i m = lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_lseek : forall i m o,
  sa_spec (ca_arm arm_lseek) i m o = lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_read : forall i eff m,
  ca_check arm_read i eff m = check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_read : forall i m,
  ca_witness arm_read i m = read_witness  (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_read : forall i m o,
  sa_spec (ca_arm arm_read) i m o = read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_write : forall i eff m,
  ca_check arm_write i eff m = check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_write : forall i m,
  ca_witness arm_write i m = write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_write : forall i m o,
  sa_spec (ca_arm arm_write) i m o = write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_readv : forall i eff m,
  ca_check arm_readv i eff m = check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_readv : forall i m,
  ca_witness arm_readv i m = readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_readv : forall i m o,
  sa_spec (ca_arm arm_readv) i m o = readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_writev : forall i eff m,
  ca_check arm_writev i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_writev : forall i m,
  ca_witness arm_writev i m = writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_writev : forall i m o,
  sa_spec (ca_arm arm_writev) i m o = writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_pread64 : forall i eff m,
  ca_check arm_pread64 i eff m = check_pread64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_pread64 : forall i m,
  ca_witness arm_pread64 i m = pread64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_pread64 : forall i m o,
  sa_spec (ca_arm arm_pread64) i m o = pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_pwrite64 : forall i eff m,
  ca_check arm_pwrite64 i eff m = check_pwrite64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_pwrite64 : forall i m,
  ca_witness arm_pwrite64 i m = pwrite64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_pwrite64 : forall i m o,
  sa_spec (ca_arm arm_pwrite64) i m o = pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_pselect6 : forall i eff m,
  ca_check arm_pselect6 i eff m = check_pselect6 i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_pselect6 : forall i m,
  ca_witness arm_pselect6 i m = pselect6_witness i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5).
Proof. reflexivity. Qed.
Lemma sa_spec_arm_pselect6 : forall i m o,
  sa_spec (ca_arm arm_pselect6) i m o = pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_ppoll : forall i eff m,
  ca_check arm_ppoll i eff m = check_ppoll i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_ppoll : forall i m,
  ca_witness arm_ppoll i m = ppoll_witness i m (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4).
Proof. reflexivity. Qed.
Lemma sa_spec_arm_ppoll : forall i m o,
  sa_spec (ca_arm arm_ppoll) i m o = ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_readlinkat : forall i eff m,
  ca_check arm_readlinkat i eff m = check_readlinkat (fd32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_readlinkat : forall i m,
  ca_witness arm_readlinkat i m = readlinkat_witness (fd32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_readlinkat : forall i m o,
  sa_spec (ca_arm arm_readlinkat) i m o = readlinkat_spec (fd32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_newfstatat : forall i eff m,
  ca_check arm_newfstatat i eff m = check_newfstatat i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_newfstatat : forall i m,
  ca_witness arm_newfstatat i m = newfstatat_witness (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_newfstatat : forall i m o,
  sa_spec (ca_arm arm_newfstatat) i m o = newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_fstat : forall i eff m,
  ca_check arm_fstat i eff m = check_fstat i (fd32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_fstat : forall i m,
  ca_witness arm_fstat i m = fstat_witness (fd32 (in_arg i 0)) (in_arg i 1) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_fstat : forall i m o,
  sa_spec (ca_arm arm_fstat) i m o = fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_fsync : forall i eff m,
  ca_check arm_fsync i eff m = check_fsync (fd32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_fsync : forall i m,
  ca_witness arm_fsync i m = fsync_witness (fd32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_fsync : forall i m o,
  sa_spec (ca_arm arm_fsync) i m o = fsync_spec (fd32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_fdatasync : forall i eff m,
  ca_check arm_fdatasync i eff m = check_fsync (fd32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_fdatasync : forall i m,
  ca_witness arm_fdatasync i m = fsync_witness (fd32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_fdatasync : forall i m o,
  sa_spec (ca_arm arm_fdatasync) i m o = fsync_spec (fd32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_timerfd_create : forall i eff m,
  ca_check arm_timerfd_create i eff m
    = check_timerfd_create (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_timerfd_create : forall i m,
  ca_witness arm_timerfd_create i m
    = timerfd_create_witness (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_timerfd_create : forall i m o,
  sa_spec (ca_arm arm_timerfd_create) i m o
    = timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_exit : forall i eff m,
  ca_check arm_exit i eff m = check_exit (in_arg i 0) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_exit : forall i m,
  ca_witness arm_exit i m = exit_witness (in_arg i 0) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_exit : forall i m o,
  sa_spec (ca_arm arm_exit) i m o = exit_spec (in_arg i 0) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_exit_group : forall i eff m,
  ca_check arm_exit_group i eff m = check_exit (in_arg i 0) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_exit_group : forall i m,
  ca_witness arm_exit_group i m = exit_witness (in_arg i 0) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_exit_group : forall i m o,
  sa_spec (ca_arm arm_exit_group) i m o = exit_spec (in_arg i 0) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_set_tid_address : forall i eff m,
  ca_check arm_set_tid_address i eff m = check_set_tid_address eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_set_tid_address : forall i m,
  ca_witness arm_set_tid_address i m = set_tid_address_witness m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_set_tid_address : forall i m o,
  sa_spec (ca_arm arm_set_tid_address) i m o = set_tid_address_spec i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_futex : forall i eff m,
  ca_check arm_futex i eff m = check_futex i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_futex : forall i m,
  ca_witness arm_futex i m = futex_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_futex : forall i m o,
  sa_spec (ca_arm arm_futex) i m o = futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_set_robust_list : forall i eff m,
  ca_check arm_set_robust_list i eff m = check_set_robust_list (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_set_robust_list : forall i m,
  ca_witness arm_set_robust_list i m = set_robust_list_witness m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_set_robust_list : forall i m o,
  sa_spec (ca_arm arm_set_robust_list) i m o = set_robust_list_spec (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_nanosleep : forall i eff m,
  ca_check arm_nanosleep i eff m = check_nanosleep i (in_arg i 0) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_nanosleep : forall i m,
  ca_witness arm_nanosleep i m = nanosleep_witness (in_arg i 0) (in_arg i 1) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_nanosleep : forall i m o,
  sa_spec (ca_arm arm_nanosleep) i m o = nanosleep_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_clock_gettime : forall i eff m,
  ca_check arm_clock_gettime i eff m = check_clock_gettime i (clockid32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_clock_gettime : forall i m,
  ca_witness arm_clock_gettime i m = clock_gettime_witness (clockid32 (in_arg i 0)) (in_arg i 1) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_clock_gettime : forall i m o,
  sa_spec (ca_arm arm_clock_gettime) i m o = clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_clock_getres : forall i eff m,
  ca_check arm_clock_getres i eff m = check_clock_getres i (clockid32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_clock_getres : forall i m,
  ca_witness arm_clock_getres i m = clock_getres_witness (clockid32 (in_arg i 0)) (in_arg i 1) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_clock_getres : forall i m o,
  sa_spec (ca_arm arm_clock_getres) i m o = clock_getres_spec (clockid32 (in_arg i 0)) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_sched_setscheduler : forall i eff m,
  ca_check arm_sched_setscheduler i eff m = check_sched_setscheduler i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_sched_setscheduler : forall i m,
  ca_witness arm_sched_setscheduler i m = sched_setscheduler_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_sched_setscheduler : forall i m o,
  sa_spec (ca_arm arm_sched_setscheduler) i m o = sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_sched_getaffinity : forall i eff m,
  ca_check arm_sched_getaffinity i eff m = check_sched_getaffinity (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_sched_getaffinity : forall i m,
  ca_witness arm_sched_getaffinity i m = sched_getaffinity_witness (in_arg i 1) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_sched_getaffinity : forall i m o,
  sa_spec (ca_arm arm_sched_getaffinity) i m o = sched_getaffinity_spec (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_sched_yield : forall i eff m,
  ca_check arm_sched_yield i eff m = check_sched_yield eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_sched_yield : forall i m,
  ca_witness arm_sched_yield i m = sched_yield_witness m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_sched_yield : forall i m o,
  sa_spec (ca_arm arm_sched_yield) i m o = sched_yield_spec i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_tkill : forall i eff m,
  ca_check arm_tkill i eff m = check_tkill (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_tkill : forall i m,
  ca_witness arm_tkill i m = tkill_witness (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_tkill : forall i m o,
  sa_spec (ca_arm arm_tkill) i m o = tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_tgkill : forall i eff m,
  ca_check arm_tgkill i eff m = check_tgkill (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_tgkill : forall i m,
  ca_witness arm_tgkill i m = tgkill_witness (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_tgkill : forall i m o,
  sa_spec (ca_arm arm_tgkill) i m o = tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i m o.
Proof. reflexivity. Qed.
Lemma ca_check_arm_sigaltstack : forall i eff m,
  ca_check arm_sigaltstack i eff m = check_sigaltstack i (in_arg i 0) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_sigaltstack : forall i m,
  ca_witness arm_sigaltstack i m = sigaltstack_witness (in_arg i 0) (in_arg i 1) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_sigaltstack : forall i m o,
  sa_spec (ca_arm arm_sigaltstack) i m o = sigaltstack_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_rt_sigaction : forall i eff m,
  ca_check arm_rt_sigaction i eff m = check_rt_sigaction i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_rt_sigaction : forall i m,
  ca_witness arm_rt_sigaction i m = rt_sigaction_witness (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_rt_sigaction : forall i m o,
  sa_spec (ca_arm arm_rt_sigaction) i m o = rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_rt_sigprocmask : forall i eff m,
  ca_check arm_rt_sigprocmask i eff m = check_rt_sigprocmask i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_rt_sigprocmask : forall i m,
  ca_witness arm_rt_sigprocmask i m = rt_sigprocmask_witness (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_rt_sigprocmask : forall i m o,
  sa_spec (ca_arm arm_rt_sigprocmask) i m o = rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_setgid : forall i eff m,
  ca_check arm_setgid i eff m = check_setid cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_setgid : forall i m,
  ca_witness arm_setgid i m = setid_witness (uid32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_setgid : forall i m o,
  sa_spec (ca_arm arm_setgid) i m o = setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_setuid : forall i eff m,
  ca_check arm_setuid i eff m = check_setid cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_setuid : forall i m,
  ca_witness arm_setuid i m = setid_witness (uid32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_setuid : forall i m o,
  sa_spec (ca_arm arm_setuid) i m o = setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_setresuid : forall i eff m,
  ca_check arm_setresuid i eff m = check_setresid cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_setresuid : forall i m,
  ca_witness arm_setresuid i m = setresid_witness cred_uids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_setresuid : forall i m o,
  sa_spec (ca_arm arm_setresuid) i m o = setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_setresgid : forall i eff m,
  ca_check arm_setresgid i eff m = check_setresid cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_setresgid : forall i m,
  ca_witness arm_setresgid i m = setresid_witness cred_gids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_setresgid : forall i m o,
  sa_spec (ca_arm arm_setresgid) i m o = setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_setsid : forall i eff m,
  ca_check arm_setsid i eff m = check_setsid eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_setsid : forall i m,
  ca_witness arm_setsid i m = setsid_witness m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_setsid : forall i m o,
  sa_spec (ca_arm arm_setsid) i m o = setsid_spec i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getgroups : forall i eff m,
  ca_check arm_getgroups i eff m = check_getgroups (in_arg i 0) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getgroups : forall i m,
  ca_witness arm_getgroups i m = getgroups_witness (in_arg i 0) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getgroups : forall i m o,
  sa_spec (ca_arm arm_getgroups) i m o = getgroups_spec (in_arg i 0) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_setgroups : forall i eff m,
  ca_check arm_setgroups i eff m = check_setgroups eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_setgroups : forall i m,
  ca_witness arm_setgroups i m = setgroups_witness m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_setgroups : forall i m o,
  sa_spec (ca_arm arm_setgroups) i m o = setgroups_spec i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_uname : forall i eff m,
  ca_check arm_uname i eff m = check_uname i (in_arg i 0) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_uname : forall i m,
  ca_witness arm_uname i m = uname_witness (in_arg i 0) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_uname : forall i m o,
  sa_spec (ca_arm arm_uname) i m o = uname_spec (in_arg i 0) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_prctl : forall i eff m,
  ca_check arm_prctl i eff m = check_prctl (int32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_prctl : forall i m,
  ca_witness arm_prctl i m = prctl_witness (int32 (in_arg i 0)) (in_arg i 1) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_prctl : forall i m o,
  sa_spec (ca_arm arm_prctl) i m o = prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_gettimeofday : forall i eff m,
  ca_check arm_gettimeofday i eff m = check_gettimeofday i (in_arg i 0) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_gettimeofday : forall i m,
  ca_witness arm_gettimeofday i m = gettimeofday_witness (in_arg i 0) (in_arg i 1) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_gettimeofday : forall i m o,
  sa_spec (ca_arm arm_gettimeofday) i m o = gettimeofday_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getpid : forall i eff m,
  ca_check arm_getpid i eff m = check_getpid eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getpid : forall i m,
  ca_witness arm_getpid i m = getpid_witness m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getpid : forall i m o,
  sa_spec (ca_arm arm_getpid) i m o = getpid_spec i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getuid : forall i eff m,
  ca_check arm_getuid i eff m = check_getid cr_uid eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getuid : forall i m,
  ca_witness arm_getuid i m = getid_witness cr_uid m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getuid : forall i m o,
  sa_spec (ca_arm arm_getuid) i m o = getid_spec cr_uid i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_geteuid : forall i eff m,
  ca_check arm_geteuid i eff m = check_getid cr_euid eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_geteuid : forall i m,
  ca_witness arm_geteuid i m = getid_witness cr_euid m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_geteuid : forall i m o,
  sa_spec (ca_arm arm_geteuid) i m o = getid_spec cr_euid i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getgid : forall i eff m,
  ca_check arm_getgid i eff m = check_getid cr_gid eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getgid : forall i m,
  ca_witness arm_getgid i m = getid_witness cr_gid m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getgid : forall i m o,
  sa_spec (ca_arm arm_getgid) i m o = getid_spec cr_gid i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getegid : forall i eff m,
  ca_check arm_getegid i eff m = check_getid cr_egid eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getegid : forall i m,
  ca_witness arm_getegid i m = getid_witness cr_egid m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getegid : forall i m o,
  sa_spec (ca_arm arm_getegid) i m o = getid_spec cr_egid i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_gettid : forall i eff m,
  ca_check arm_gettid i eff m = check_gettid eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_gettid : forall i m,
  ca_witness arm_gettid i m = gettid_witness m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_gettid : forall i m o,
  sa_spec (ca_arm arm_gettid) i m o = gettid_spec i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_socket : forall i eff m,
  ca_check arm_socket i eff m = check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_socket : forall i m,
  ca_witness arm_socket i m = socket_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_socket : forall i m o,
  sa_spec (ca_arm arm_socket) i m o = socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_socketpair : forall i eff m,
  ca_check arm_socketpair i eff m = check_socketpair i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_socketpair : forall i m,
  ca_witness arm_socketpair i m = socketpair_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_socketpair : forall i m o,
  sa_spec (ca_arm arm_socketpair) i m o = socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_bind : forall i eff m,
  ca_check arm_bind i eff m = check_bind i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_bind : forall i m,
  ca_witness arm_bind i m = bind_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_bind : forall i m o,
  sa_spec (ca_arm arm_bind) i m o = bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_listen : forall i eff m,
  ca_check arm_listen i eff m = check_listen (fd32 (in_arg i 0)) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_listen : forall i m,
  ca_witness arm_listen i m = listen_witness (fd32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_listen : forall i m o,
  sa_spec (ca_arm arm_listen) i m o = listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_accept : forall i eff m,
  ca_check arm_accept i eff m = check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_accept : forall i m,
  ca_witness arm_accept i m = accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (Z_to_bv 64 0) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_accept : forall i m o,
  sa_spec (ca_arm arm_accept) i m o = accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_connect : forall i eff m,
  ca_check arm_connect i eff m = check_connect i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_connect : forall i m,
  ca_witness arm_connect i m = connect_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_connect : forall i m o,
  sa_spec (ca_arm arm_connect) i m o = connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getsockname : forall i eff m,
  ca_check arm_getsockname i eff m = check_getsockname (fd32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getsockname : forall i m,
  ca_witness arm_getsockname i m = getsockname_witness (fd32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getsockname : forall i m o,
  sa_spec (ca_arm arm_getsockname) i m o = getsockname_spec (fd32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getpeername : forall i eff m,
  ca_check arm_getpeername i eff m = check_getpeername (fd32 (in_arg i 0)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getpeername : forall i m,
  ca_witness arm_getpeername i m = getpeername_witness (fd32 (in_arg i 0)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getpeername : forall i m o,
  sa_spec (ca_arm arm_getpeername) i m o = getpeername_spec (fd32 (in_arg i 0)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_sendto : forall i eff m,
  ca_check arm_sendto i eff m = check_sendto i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_sendto : forall i m,
  ca_witness arm_sendto i m = sendto_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_sendto : forall i m o,
  sa_spec (ca_arm arm_sendto) i m o = sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_recvfrom : forall i eff m,
  ca_check arm_recvfrom i eff m = check_recvfrom i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_recvfrom : forall i m,
  ca_witness arm_recvfrom i m = recvfrom_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_recvfrom : forall i m o,
  sa_spec (ca_arm arm_recvfrom) i m o = recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_setsockopt : forall i eff m,
  ca_check arm_setsockopt i eff m = check_setsockopt (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_setsockopt : forall i m,
  ca_witness arm_setsockopt i m = setsockopt_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_setsockopt : forall i m o,
  sa_spec (ca_arm arm_setsockopt) i m o = setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getsockopt : forall i eff m,
  ca_check arm_getsockopt i eff m = check_getsockopt i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getsockopt : forall i m,
  ca_witness arm_getsockopt i m = getsockopt_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getsockopt : forall i m o,
  sa_spec (ca_arm arm_getsockopt) i m o = getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_shutdown : forall i eff m,
  ca_check arm_shutdown i eff m = check_shutdown (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_shutdown : forall i m,
  ca_witness arm_shutdown i m = shutdown_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_shutdown : forall i m o,
  sa_spec (ca_arm arm_shutdown) i m o = shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_sendmsg : forall i eff m,
  ca_check arm_sendmsg i eff m = check_sendmsg i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_sendmsg : forall i m,
  ca_witness arm_sendmsg i m = sendmsg_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_sendmsg : forall i m o,
  sa_spec (ca_arm arm_sendmsg) i m o = sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_brk : forall i eff m,
  ca_check arm_brk i eff m = check_brk (in_arg i 0) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_brk : forall i m,
  ca_witness arm_brk i m = brk_witness (in_arg i 0) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_brk : forall i m o,
  sa_spec (ca_arm arm_brk) i m o = brk_spec (in_arg i 0) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_munmap : forall i eff m,
  ca_check arm_munmap i eff m = check_munmap (in_arg i 0) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_munmap : forall i m,
  ca_witness arm_munmap i m = munmap_witness (in_arg i 0) (in_arg i 1) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_munmap : forall i m o,
  sa_spec (ca_arm arm_munmap) i m o = munmap_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_mremap : forall i eff m,
  ca_check arm_mremap i eff m = check_mremap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_mremap : forall i m,
  ca_witness arm_mremap i m = mremap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_mremap : forall i m o,
  sa_spec (ca_arm arm_mremap) i m o = mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_clone : forall i eff m,
  ca_check arm_clone i eff m = check_clone (in_arg i 0) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_clone : forall i m,
  ca_witness arm_clone i m = clone_witness (in_arg i 0) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_clone : forall i m o,
  sa_spec (ca_arm arm_clone) i m o = clone_spec (in_arg i 0) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_mmap : forall i eff m,
  ca_check arm_mmap i eff m = check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_mmap : forall i m,
  ca_witness arm_mmap i m = mmap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_mmap : forall i m o,
  sa_spec (ca_arm arm_mmap) i m o = mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_mprotect : forall i eff m,
  ca_check arm_mprotect i eff m = check_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_mprotect : forall i m,
  ca_witness arm_mprotect i m = mprotect_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_mprotect : forall i m o,
  sa_spec (ca_arm arm_mprotect) i m o = mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_madvise : forall i eff m,
  ca_check arm_madvise i eff m = check_madvise (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_madvise : forall i m,
  ca_witness arm_madvise i m = madvise_witness (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_madvise : forall i m o,
  sa_spec (ca_arm arm_madvise) i m o = madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_recvmsg : forall i eff m,
  ca_check arm_recvmsg i eff m = check_recvmsg (fd32 (in_arg i 0)) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_recvmsg : forall i m,
  ca_witness arm_recvmsg i m = recvmsg_witness (fd32 (in_arg i 0)) (in_arg i 2) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_recvmsg : forall i m o,
  sa_spec (ca_arm arm_recvmsg) i m o = recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_accept4 : forall i eff m,
  ca_check arm_accept4 i eff m = check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_accept4 : forall i m,
  ca_witness arm_accept4 i m = accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 3) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_accept4 : forall i m o,
  sa_spec (ca_arm arm_accept4) i m o = accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_wait4 : forall i eff m,
  ca_check arm_wait4 i eff m = check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_wait4 : forall i m,
  ca_witness arm_wait4 i m = wait4_witness (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_wait4 : forall i m o,
  sa_spec (ca_arm arm_wait4) i m o = wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_prlimit64 : forall i eff m,
  ca_check arm_prlimit64 i eff m = check_prlimit64 i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_prlimit64 : forall i m,
  ca_witness arm_prlimit64 i m = prlimit64_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_prlimit64 : forall i m o,
  sa_spec (ca_arm arm_prlimit64) i m o = prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_getrandom : forall i eff m,
  ca_check arm_getrandom i eff m = check_getrandom i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_getrandom : forall i m,
  ca_witness arm_getrandom i m = getrandom_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_getrandom : forall i m o,
  sa_spec (ca_arm arm_getrandom) i m o = getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_clone3 : forall i eff m,
  ca_check arm_clone3 i eff m = check_clone3 i (in_arg i 0) (in_arg i 1) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_clone3 : forall i m,
  ca_witness arm_clone3 i m = clone3_witness i (in_arg i 0) (in_arg i 1) m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_clone3 : forall i m o,
  sa_spec (ca_arm arm_clone3) i m o = clone3_spec (in_arg i 0) (in_arg i 1) i m o.
Proof. reflexivity. Qed.

Lemma ca_check_arm_faccessat2 : forall i eff m,
  ca_check arm_faccessat2 i eff m = check_faccessat2 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m.
Proof. reflexivity. Qed.
Lemma ca_witness_arm_faccessat2 : forall i m,
  ca_witness arm_faccessat2 i m = faccessat2_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m.
Proof. reflexivity. Qed.
Lemma sa_spec_arm_faccessat2 : forall i m o,
  sa_spec (ca_arm arm_faccessat2) i m o = faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. reflexivity. Qed.

#[export] Hint Rewrite ca_check_arm_getcwd ca_witness_arm_getcwd sa_spec_arm_getcwd : arm_unfold.
#[export] Hint Rewrite ca_check_arm_eventfd2 ca_witness_arm_eventfd2 sa_spec_arm_eventfd2 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_epoll_create1 ca_witness_arm_epoll_create1 sa_spec_arm_epoll_create1 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_epoll_ctl ca_witness_arm_epoll_ctl sa_spec_arm_epoll_ctl : arm_unfold.
#[export] Hint Rewrite ca_check_arm_epoll_pwait ca_witness_arm_epoll_pwait sa_spec_arm_epoll_pwait : arm_unfold.
#[export] Hint Rewrite ca_check_arm_dup ca_witness_arm_dup sa_spec_arm_dup : arm_unfold.
#[export] Hint Rewrite ca_check_arm_dup3 ca_witness_arm_dup3 sa_spec_arm_dup3 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_fcntl ca_witness_arm_fcntl sa_spec_arm_fcntl : arm_unfold.
#[export] Hint Rewrite ca_check_arm_ioctl ca_witness_arm_ioctl sa_spec_arm_ioctl : arm_unfold.
#[export] Hint Rewrite ca_check_arm_flock ca_witness_arm_flock sa_spec_arm_flock : arm_unfold.
#[export] Hint Rewrite ca_check_arm_unlinkat ca_witness_arm_unlinkat sa_spec_arm_unlinkat : arm_unfold.
#[export] Hint Rewrite ca_check_arm_ftruncate ca_witness_arm_ftruncate sa_spec_arm_ftruncate : arm_unfold.
#[export] Hint Rewrite ca_check_arm_faccessat ca_witness_arm_faccessat sa_spec_arm_faccessat : arm_unfold.
#[export] Hint Rewrite ca_check_arm_openat ca_witness_arm_openat sa_spec_arm_openat : arm_unfold.
#[export] Hint Rewrite ca_check_arm_close ca_witness_arm_close sa_spec_arm_close : arm_unfold.
#[export] Hint Rewrite ca_check_arm_pipe2 ca_witness_arm_pipe2 sa_spec_arm_pipe2 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getdents64 ca_witness_arm_getdents64 sa_spec_arm_getdents64 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_lseek ca_witness_arm_lseek sa_spec_arm_lseek : arm_unfold.
#[export] Hint Rewrite ca_check_arm_read ca_witness_arm_read sa_spec_arm_read : arm_unfold.
#[export] Hint Rewrite ca_check_arm_write ca_witness_arm_write sa_spec_arm_write : arm_unfold.
#[export] Hint Rewrite ca_check_arm_readv ca_witness_arm_readv sa_spec_arm_readv : arm_unfold.
#[export] Hint Rewrite ca_check_arm_writev ca_witness_arm_writev sa_spec_arm_writev : arm_unfold.
#[export] Hint Rewrite ca_check_arm_pread64 ca_witness_arm_pread64 sa_spec_arm_pread64 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_pwrite64 ca_witness_arm_pwrite64 sa_spec_arm_pwrite64 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_pselect6 ca_witness_arm_pselect6 sa_spec_arm_pselect6 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_ppoll ca_witness_arm_ppoll sa_spec_arm_ppoll : arm_unfold.
#[export] Hint Rewrite ca_check_arm_readlinkat ca_witness_arm_readlinkat sa_spec_arm_readlinkat : arm_unfold.
#[export] Hint Rewrite ca_check_arm_newfstatat ca_witness_arm_newfstatat sa_spec_arm_newfstatat : arm_unfold.
#[export] Hint Rewrite ca_check_arm_fstat ca_witness_arm_fstat sa_spec_arm_fstat : arm_unfold.
#[export] Hint Rewrite ca_check_arm_fsync ca_witness_arm_fsync sa_spec_arm_fsync : arm_unfold.
#[export] Hint Rewrite ca_check_arm_fdatasync ca_witness_arm_fdatasync sa_spec_arm_fdatasync : arm_unfold.
#[export] Hint Rewrite ca_check_arm_timerfd_create ca_witness_arm_timerfd_create sa_spec_arm_timerfd_create : arm_unfold.
#[export] Hint Rewrite ca_check_arm_exit ca_witness_arm_exit sa_spec_arm_exit : arm_unfold.
#[export] Hint Rewrite ca_check_arm_exit_group ca_witness_arm_exit_group sa_spec_arm_exit_group : arm_unfold.
#[export] Hint Rewrite ca_check_arm_set_tid_address ca_witness_arm_set_tid_address sa_spec_arm_set_tid_address : arm_unfold.
#[export] Hint Rewrite ca_check_arm_futex ca_witness_arm_futex sa_spec_arm_futex : arm_unfold.
#[export] Hint Rewrite ca_check_arm_set_robust_list ca_witness_arm_set_robust_list sa_spec_arm_set_robust_list : arm_unfold.
#[export] Hint Rewrite ca_check_arm_nanosleep ca_witness_arm_nanosleep sa_spec_arm_nanosleep : arm_unfold.
#[export] Hint Rewrite ca_check_arm_clock_gettime ca_witness_arm_clock_gettime sa_spec_arm_clock_gettime : arm_unfold.
#[export] Hint Rewrite ca_check_arm_clock_getres ca_witness_arm_clock_getres sa_spec_arm_clock_getres : arm_unfold.
#[export] Hint Rewrite ca_check_arm_sched_setscheduler ca_witness_arm_sched_setscheduler sa_spec_arm_sched_setscheduler : arm_unfold.
#[export] Hint Rewrite ca_check_arm_sched_getaffinity ca_witness_arm_sched_getaffinity sa_spec_arm_sched_getaffinity : arm_unfold.
#[export] Hint Rewrite ca_check_arm_sched_yield ca_witness_arm_sched_yield sa_spec_arm_sched_yield : arm_unfold.
#[export] Hint Rewrite ca_check_arm_tkill ca_witness_arm_tkill sa_spec_arm_tkill : arm_unfold.
#[export] Hint Rewrite ca_check_arm_tgkill ca_witness_arm_tgkill sa_spec_arm_tgkill : arm_unfold.
#[export] Hint Rewrite ca_check_arm_sigaltstack ca_witness_arm_sigaltstack sa_spec_arm_sigaltstack : arm_unfold.
#[export] Hint Rewrite ca_check_arm_rt_sigaction ca_witness_arm_rt_sigaction sa_spec_arm_rt_sigaction : arm_unfold.
#[export] Hint Rewrite ca_check_arm_rt_sigprocmask ca_witness_arm_rt_sigprocmask sa_spec_arm_rt_sigprocmask : arm_unfold.
#[export] Hint Rewrite ca_check_arm_setsid ca_witness_arm_setsid sa_spec_arm_setsid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_setgid ca_witness_arm_setgid sa_spec_arm_setgid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_setuid ca_witness_arm_setuid sa_spec_arm_setuid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_setresuid ca_witness_arm_setresuid sa_spec_arm_setresuid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_setresgid ca_witness_arm_setresgid sa_spec_arm_setresgid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getgroups ca_witness_arm_getgroups sa_spec_arm_getgroups : arm_unfold.
#[export] Hint Rewrite ca_check_arm_setgroups ca_witness_arm_setgroups sa_spec_arm_setgroups : arm_unfold.
#[export] Hint Rewrite ca_check_arm_uname ca_witness_arm_uname sa_spec_arm_uname : arm_unfold.
#[export] Hint Rewrite ca_check_arm_prctl ca_witness_arm_prctl sa_spec_arm_prctl : arm_unfold.
#[export] Hint Rewrite ca_check_arm_gettimeofday ca_witness_arm_gettimeofday sa_spec_arm_gettimeofday : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getpid ca_witness_arm_getpid sa_spec_arm_getpid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getuid ca_witness_arm_getuid sa_spec_arm_getuid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_geteuid ca_witness_arm_geteuid sa_spec_arm_geteuid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getgid ca_witness_arm_getgid sa_spec_arm_getgid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getegid ca_witness_arm_getegid sa_spec_arm_getegid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_gettid ca_witness_arm_gettid sa_spec_arm_gettid : arm_unfold.
#[export] Hint Rewrite ca_check_arm_socket ca_witness_arm_socket sa_spec_arm_socket : arm_unfold.
#[export] Hint Rewrite ca_check_arm_socketpair ca_witness_arm_socketpair sa_spec_arm_socketpair : arm_unfold.
#[export] Hint Rewrite ca_check_arm_bind ca_witness_arm_bind sa_spec_arm_bind : arm_unfold.
#[export] Hint Rewrite ca_check_arm_listen ca_witness_arm_listen sa_spec_arm_listen : arm_unfold.
#[export] Hint Rewrite ca_check_arm_accept ca_witness_arm_accept sa_spec_arm_accept : arm_unfold.
#[export] Hint Rewrite ca_check_arm_connect ca_witness_arm_connect sa_spec_arm_connect : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getsockname ca_witness_arm_getsockname sa_spec_arm_getsockname : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getpeername ca_witness_arm_getpeername sa_spec_arm_getpeername : arm_unfold.
#[export] Hint Rewrite ca_check_arm_sendto ca_witness_arm_sendto sa_spec_arm_sendto : arm_unfold.
#[export] Hint Rewrite ca_check_arm_recvfrom ca_witness_arm_recvfrom sa_spec_arm_recvfrom : arm_unfold.
#[export] Hint Rewrite ca_check_arm_setsockopt ca_witness_arm_setsockopt sa_spec_arm_setsockopt : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getsockopt ca_witness_arm_getsockopt sa_spec_arm_getsockopt : arm_unfold.
#[export] Hint Rewrite ca_check_arm_shutdown ca_witness_arm_shutdown sa_spec_arm_shutdown : arm_unfold.
#[export] Hint Rewrite ca_check_arm_sendmsg ca_witness_arm_sendmsg sa_spec_arm_sendmsg : arm_unfold.
#[export] Hint Rewrite ca_check_arm_brk ca_witness_arm_brk sa_spec_arm_brk : arm_unfold.
#[export] Hint Rewrite ca_check_arm_munmap ca_witness_arm_munmap sa_spec_arm_munmap : arm_unfold.
#[export] Hint Rewrite ca_check_arm_mremap ca_witness_arm_mremap sa_spec_arm_mremap : arm_unfold.
#[export] Hint Rewrite ca_check_arm_clone ca_witness_arm_clone sa_spec_arm_clone : arm_unfold.
#[export] Hint Rewrite ca_check_arm_mmap ca_witness_arm_mmap sa_spec_arm_mmap : arm_unfold.
#[export] Hint Rewrite ca_check_arm_mprotect ca_witness_arm_mprotect sa_spec_arm_mprotect : arm_unfold.
#[export] Hint Rewrite ca_check_arm_madvise ca_witness_arm_madvise sa_spec_arm_madvise : arm_unfold.
#[export] Hint Rewrite ca_check_arm_recvmsg ca_witness_arm_recvmsg sa_spec_arm_recvmsg : arm_unfold.
#[export] Hint Rewrite ca_check_arm_accept4 ca_witness_arm_accept4 sa_spec_arm_accept4 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_wait4 ca_witness_arm_wait4 sa_spec_arm_wait4 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_prlimit64 ca_witness_arm_prlimit64 sa_spec_arm_prlimit64 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_getrandom ca_witness_arm_getrandom sa_spec_arm_getrandom : arm_unfold.
#[export] Hint Rewrite ca_check_arm_clone3 ca_witness_arm_clone3 sa_spec_arm_clone3 : arm_unfold.
#[export] Hint Rewrite ca_check_arm_faccessat2 ca_witness_arm_faccessat2 sa_spec_arm_faccessat2 : arm_unfold.

(** Each arm's NUMBER, so the lookup can be computed without unfolding the
    arm itself -- [refine] built these, and [cbn] will not unfold a constant
    it built.  Without this the dispatch is stuck at [ca_no arm_ioctl =? 64]
    with neither side able to move. *)

Lemma ca_no_arm_getcwd : ca_no arm_getcwd = 17%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getcwd : arm_unfold.

Lemma ca_no_arm_dup : ca_no arm_dup = 23%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_dup : arm_unfold.

Lemma ca_no_arm_dup3 : ca_no arm_dup3 = 24%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_dup3 : arm_unfold.

Lemma ca_no_arm_fcntl : ca_no arm_fcntl = 25%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_fcntl : arm_unfold.

Lemma ca_no_arm_ioctl : ca_no arm_ioctl = 29%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_ioctl : arm_unfold.

Lemma ca_no_arm_flock : ca_no arm_flock = 32%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_flock : arm_unfold.

Lemma ca_no_arm_unlinkat : ca_no arm_unlinkat = 35%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_unlinkat : arm_unfold.

Lemma ca_no_arm_ftruncate : ca_no arm_ftruncate = 46%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_ftruncate : arm_unfold.

Lemma ca_no_arm_faccessat : ca_no arm_faccessat = 48%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_faccessat : arm_unfold.

Lemma ca_no_arm_openat : ca_no arm_openat = 56%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_openat : arm_unfold.

Lemma ca_no_arm_close : ca_no arm_close = 57%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_close : arm_unfold.

Lemma ca_no_arm_pipe2 : ca_no arm_pipe2 = 59%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_pipe2 : arm_unfold.

Lemma ca_no_arm_lseek : ca_no arm_lseek = 62%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_lseek : arm_unfold.

Lemma ca_no_arm_read : ca_no arm_read = 63%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_read : arm_unfold.

Lemma ca_no_arm_write : ca_no arm_write = 64%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_write : arm_unfold.

Lemma ca_no_arm_readv : ca_no arm_readv = 65%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_readv : arm_unfold.

Lemma ca_no_arm_writev : ca_no arm_writev = 66%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_writev : arm_unfold.

Lemma ca_no_arm_pselect6 : ca_no arm_pselect6 = 72%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_pselect6 : arm_unfold.

Lemma ca_no_arm_ppoll : ca_no arm_ppoll = 73%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_ppoll : arm_unfold.

Lemma ca_no_arm_fstat : ca_no arm_fstat = 80%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_fstat : arm_unfold.

Lemma ca_no_arm_readlinkat : ca_no arm_readlinkat = 78%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_readlinkat : arm_unfold.

Lemma ca_no_arm_newfstatat : ca_no arm_newfstatat = 79%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_newfstatat : arm_unfold.

Lemma ca_no_arm_getdents64 : ca_no arm_getdents64 = 61%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getdents64 : arm_unfold.

Lemma ca_no_arm_fsync : ca_no arm_fsync = 82%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_fsync : arm_unfold.

Lemma ca_no_arm_fdatasync : ca_no arm_fdatasync = 83%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_fdatasync : arm_unfold.

Lemma ca_no_arm_timerfd_create : ca_no arm_timerfd_create = 85%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_timerfd_create : arm_unfold.

Lemma ca_no_arm_exit : ca_no arm_exit = 93%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_exit : arm_unfold.

Lemma ca_no_arm_exit_group : ca_no arm_exit_group = 94%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_exit_group : arm_unfold.

Lemma ca_no_arm_set_tid_address : ca_no arm_set_tid_address = 96%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_set_tid_address : arm_unfold.

Lemma ca_no_arm_futex : ca_no arm_futex = 98%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_futex : arm_unfold.

Lemma ca_no_arm_set_robust_list : ca_no arm_set_robust_list = 99%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_set_robust_list : arm_unfold.

Lemma ca_no_arm_nanosleep : ca_no arm_nanosleep = 101%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_nanosleep : arm_unfold.

Lemma ca_no_arm_clock_gettime : ca_no arm_clock_gettime = 113%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_clock_gettime : arm_unfold.

Lemma ca_no_arm_clock_getres : ca_no arm_clock_getres = 114%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_clock_getres : arm_unfold.

Lemma ca_no_arm_sched_setscheduler : ca_no arm_sched_setscheduler = 119%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_sched_setscheduler : arm_unfold.

Lemma ca_no_arm_sched_getaffinity : ca_no arm_sched_getaffinity = 123%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_sched_getaffinity : arm_unfold.

Lemma ca_no_arm_sched_yield : ca_no arm_sched_yield = 124%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_sched_yield : arm_unfold.

Lemma ca_no_arm_sigaltstack : ca_no arm_sigaltstack = 132%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_sigaltstack : arm_unfold.

Lemma ca_no_arm_rt_sigaction : ca_no arm_rt_sigaction = 134%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_rt_sigaction : arm_unfold.

Lemma ca_no_arm_rt_sigprocmask : ca_no arm_rt_sigprocmask = 135%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_rt_sigprocmask : arm_unfold.

Lemma ca_no_arm_setgid : ca_no arm_setgid = 144%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_setgid : arm_unfold.

Lemma ca_no_arm_setuid : ca_no arm_setuid = 146%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_setuid : arm_unfold.

Lemma ca_no_arm_setresuid : ca_no arm_setresuid = 147%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_setresuid : arm_unfold.

Lemma ca_no_arm_setresgid : ca_no arm_setresgid = 149%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_setresgid : arm_unfold.

Lemma ca_no_arm_setsid : ca_no arm_setsid = 157%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_setsid : arm_unfold.

Lemma ca_no_arm_getgroups : ca_no arm_getgroups = 158%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getgroups : arm_unfold.

Lemma ca_no_arm_setgroups : ca_no arm_setgroups = 159%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_setgroups : arm_unfold.

Lemma ca_no_arm_prctl : ca_no arm_prctl = 167%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_prctl : arm_unfold.

Lemma ca_no_arm_gettimeofday : ca_no arm_gettimeofday = 169%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_gettimeofday : arm_unfold.

Lemma ca_no_arm_getpid : ca_no arm_getpid = 172%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getpid : arm_unfold.

Lemma ca_no_arm_getuid : ca_no arm_getuid = 174%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getuid : arm_unfold.

Lemma ca_no_arm_geteuid : ca_no arm_geteuid = 175%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_geteuid : arm_unfold.

Lemma ca_no_arm_getgid : ca_no arm_getgid = 176%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getgid : arm_unfold.

Lemma ca_no_arm_getegid : ca_no arm_getegid = 177%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getegid : arm_unfold.

Lemma ca_no_arm_gettid : ca_no arm_gettid = 178%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_gettid : arm_unfold.

Lemma ca_no_arm_socket : ca_no arm_socket = 198%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_socket : arm_unfold.

Lemma ca_no_arm_socketpair : ca_no arm_socketpair = 199%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_socketpair : arm_unfold.

Lemma ca_no_arm_bind : ca_no arm_bind = 200%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_bind : arm_unfold.

Lemma ca_no_arm_listen : ca_no arm_listen = 201%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_listen : arm_unfold.

Lemma ca_no_arm_accept : ca_no arm_accept = 202%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_accept : arm_unfold.

Lemma ca_no_arm_connect : ca_no arm_connect = 203%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_connect : arm_unfold.

Lemma ca_no_arm_getsockname : ca_no arm_getsockname = 204%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getsockname : arm_unfold.

Lemma ca_no_arm_getpeername : ca_no arm_getpeername = 205%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getpeername : arm_unfold.

Lemma ca_no_arm_sendto : ca_no arm_sendto = 206%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_sendto : arm_unfold.

Lemma ca_no_arm_recvfrom : ca_no arm_recvfrom = 207%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_recvfrom : arm_unfold.

Lemma ca_no_arm_setsockopt : ca_no arm_setsockopt = 208%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_setsockopt : arm_unfold.

Lemma ca_no_arm_getsockopt : ca_no arm_getsockopt = 209%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getsockopt : arm_unfold.

Lemma ca_no_arm_shutdown : ca_no arm_shutdown = 210%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_shutdown : arm_unfold.

Lemma ca_no_arm_sendmsg : ca_no arm_sendmsg = 211%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_sendmsg : arm_unfold.

Lemma ca_no_arm_brk : ca_no arm_brk = 214%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_brk : arm_unfold.

Lemma ca_no_arm_munmap : ca_no arm_munmap = 215%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_munmap : arm_unfold.

Lemma ca_no_arm_mremap : ca_no arm_mremap = 216%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_mremap : arm_unfold.

Lemma ca_no_arm_clone : ca_no arm_clone = 220%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_clone : arm_unfold.

Lemma ca_no_arm_mmap : ca_no arm_mmap = 222%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_mmap : arm_unfold.

Lemma ca_no_arm_mprotect : ca_no arm_mprotect = 226%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_mprotect : arm_unfold.

Lemma ca_no_arm_madvise : ca_no arm_madvise = 233%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_madvise : arm_unfold.

Lemma ca_no_arm_recvmsg : ca_no arm_recvmsg = 212%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_recvmsg : arm_unfold.

Lemma ca_no_arm_accept4 : ca_no arm_accept4 = 242%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_accept4 : arm_unfold.
Lemma ca_no_arm_wait4 : ca_no arm_wait4 = 260%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_wait4 : arm_unfold.

Lemma ca_no_arm_prlimit64 : ca_no arm_prlimit64 = 261%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_prlimit64 : arm_unfold.

Lemma ca_no_arm_getrandom : ca_no arm_getrandom = 278%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_getrandom : arm_unfold.

Lemma ca_no_arm_clone3 : ca_no arm_clone3 = 435%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_clone3 : arm_unfold.

Lemma ca_no_arm_faccessat2 : ca_no arm_faccessat2 = 439%Z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite ca_no_arm_faccessat2 : arm_unfold.

(** Resolve the dispatch: turn the arms' numbers into literals, compute the
    lookup, then turn the arm that answered back into its plain [check_*] or
    [*_witness].  A caller writes this and never names a syscall. *)
Ltac arm_dispatch :=
  autorewrite with arm_unfold;
  cbn [lookup_ca checked_table Z.eqb Pos.eqb];
  autorewrite with arm_unfold.
