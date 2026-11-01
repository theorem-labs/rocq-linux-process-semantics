(** * Examples.forkwait.Statement — what the pathfinder claims

    ONE STATEMENT ABOUT A PROGRAM THAT STARTS A SECOND PROCESS.  That is the
    whole point of this example: until it exists, the multi-process relation
    of [LinuxProcessSem.Procs] is a definition nobody has used.

    THE PROGRAM, [source/forkwait.S], 26 instructions of static riscv64 with
    no libc: it calls [clone(SIGCHLD, 0, 0, 0, 0)]; the child calls
    [exit_group(7)]; the parent calls [wait4(-1, &status, 0, NULL)] and then
    [exit_group(status >> 8)].  An injected errno from [Fork.clone_errnos]
    sends it to a third [exit_group(7)], so every path exits 7 whether or not
    the environment refuses the clone.

    THE SHAPE IS THE RELEASED ONE, and that is the claim's whole value.
    [Procs.pholts_within_budget] is [HaltsAllowed.halts_allowed_T_scfg_budgets]
    at [Run.forced_only_cfg] with one thing changed: the one-process
    [MustExit.must_exit_in_scfg] becomes the whole-system
    [Procs.must_exit_in_p].  Same quantifier over the [execve] draws and the
    input, same environment, same budget premise.  So this statement is
    comparable with every released halting statement rather than a different
    kind of claim, and the difference between them is exactly the predicate.

    WHAT IT RULES OUT, by [Procs.must_exit_in_p_at]'s own premises: no
    execution reaches the error transition, from any process; no execution
    deadlocks, because the progress premise asks the WHOLE SYSTEM to be able
    to step; no interleaving escapes, because the scheduler is the index of
    [Procs.pstep_at] and the predicate quantifies over every successor; and
    the run ends with the root halted on a code in the allowed set and every
    surviving entry halted too.

    WHAT IT DOES NOT CLAIM.  Nothing about a child that outlives its parent
    (this model has no init to reparent to, so it refuses rather than
    guesses), nothing about a signalled child (the reap arm declines one),
    and nothing about fairness (a program whose child loops forever is
    refuted by this predicate, which is right for a program with no way to
    stop the child). *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType State Run Procs.
(** [pholts_within_budget] lives beside [MustExit], not beside [Procs]:
    see that file's header for why. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExitP.
From LinuxProcessSemantics.Examples.forkwait Require Import ForkwaitMemImage.
Import ListNotations.
Open Scope bv_scope.

Definition forkwait_image : Image :=
  mkImage ForkwaitMemImage_loaded_segments
          ForkwaitMemImage_init_pc
          ForkwaitMemImage_phdrs.

(** The one status the program can exit with.  [Exit.exit_spec] masks its
    argument with 255 before [set_halted], so a set written as a bare byte
    is a set of statuses a waiting parent can really read
    ([MustExit.must_exit_in_at]'s header says why the comparison is plain). *)
Definition forkwait_exits : list word := [Z_to_bv 64 7].

(** THE STATEMENT.  [State.source_alloc_limit] is the shipped budget, 16 GiB,
    the same one the released [halts_allowed_T] fixes. *)
Definition forkwait_halts : Prop :=
  pholts_within_budget source_alloc_limit forkwait_exits forkwait_image.
