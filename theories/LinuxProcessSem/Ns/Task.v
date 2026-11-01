(** * LinuxProcessSem.Ns.Task — arms on a task's own state

    The calls that read or change only what a task holds: its umask, its
    pid, its capability sets, its no_new_privs bit, its parent-death signal
    and its dumpable mode.  Each header names the Linux 6.18.44 functions it
    follows and its kind. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Arm.
Import ListNotations.

(* =========================================================================
   Arms on the task's own state
   ========================================================================= *)

(** [umask] (166): [SYSCALL_DEFINE1(umask)], kernel/sys.c: the mask's
    permission bits are stored and the old mask returned.  Kind: exact. *)
Definition umask_arm : NsArm := fun i m ctx st o =>
  o = ns_ret (Z_to_bv 64 (cx_umask ctx)) m
             (with_umask ctx (Z.land (bv_unsigned (in_arg i 0)) 511)) st.

(** [getpid] (172) and [gettid] (178): [task_tgid_vnr] and
    [task_pid_vnr] (kernel/sys.c), the pid in the task's active pid
    namespace; one thread per process, so both are the same.  Kind: exact;
    a task with no pid in its own namespace is not one the model holds,
    and declines. *)
Definition getpid_arm : NsArm := fun i m ctx st o =>
  match task_pid ctx with
  | Some p => o = ns_ret (Z_to_bv 64 p) m ctx st
  | None => o = EUnmodeled
  end.

