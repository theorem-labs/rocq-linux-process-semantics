(** * LinuxProcessSem.Ns.Pass — calls a namespace does not change

    For a task in a namespace the tables model, these calls answer as the
    released model answers them ([Ext.released]): nothing they read or
    write depends on a namespace.  Each number was checked against Linux
    6.18.44 and against the released arm:

    - the task's memory: [brk] 214, [munmap] 215, [mremap] 216, [mmap] 222
      (a descriptor of the namespace model is [FdOpaque], which the
      released arm declines), [mprotect] 226, [madvise] 233;
    - signals of the task itself: [sigaltstack] 132, [rt_sigaction] 134,
      [rt_sigprocmask] 135;
    - the task's own futex and robust-list fields: [futex] 98 (private
      futexes only in the released arm), [set_robust_list] 99;
    - time and randomness, with no time namespace modelled: [nanosleep]
      101, [clock_gettime] 113, [clock_getres] 114, [gettimeofday] 169,
      [sched_yield] 124, [getrandom] 278;
    - [uname] 160: a new UTS namespace starts as a copy of its parent's
      ([copy_utsname]) and no modelled call changes it;
    - new descriptors the namespace model does not hold: [eventfd2] 19,
      [pipe2] 59 (the lowest free descriptor: a live descriptor of the
      namespace model is in the table, so it is never reused);
    - [exit] 93 and [exit_group] 94.  LIMIT: when the task is pid 1 of a
      pid namespace the model made, Linux also kills every other task of
      that namespace ([zap_pid_ns_processes], kernel/pid_namespace.c); this
      arm does not, because which tasks are in a namespace is the core's
      table, not the namespace state.  A run in which pid 1 of such a
      namespace exits while another task of it is alive is therefore not
      modelled faithfully; a statement must not depend on one.  When pid 1
      exits with no other task in its namespace (a setup process that
      forks nothing), the answer is exact.

    In the released world the namespace model answers every number with
    the released answer ([Spec.ns_coherent]); these numbers get it in every
    world ([pass_arms_released]).  That coverage is deliberate: each number
    above was checked for a dependence on a namespace.

    Not here, because a namespace changes their answer: the uid and gid
    calls (a user namespace maps them), [set_tid_address] (it returns the
    thread id in the caller's pid namespace, which the released model
    takes from [m_tid]), [getppid], [kill], [tkill], [tgkill],
    [prlimit64] with a pid, [wait4] and [clone] (pid namespaces), the
    socket calls (network namespaces), and every call that walks a path. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Ext Arm.
Import ListNotations.

Definition pass_numbers : list Z :=
  [19; 59; 93; 94; 98; 99; 101; 113; 114; 124; 132; 134; 135; 160; 169; 214; 215; 216; 222;
   226; 233; 278]%Z.

Definition pass_arms : list (Z * NsArm) := map (fun n => (n, released)) pass_numbers.

(** Each listed number has exactly the released answers, for every input,
    in every world. *)
Lemma pass_arms_released : forall n a, In (n, a) pass_arms ->
  forall i m ctx st o, a i m ctx st o <-> released i m ctx st o.
Proof.
  intros n a H i m ctx st o. unfold pass_arms in H. apply in_map_iff in H.
  destruct H as (k & Heq & _). injection Heq as _ <-. reflexivity.
Qed.
