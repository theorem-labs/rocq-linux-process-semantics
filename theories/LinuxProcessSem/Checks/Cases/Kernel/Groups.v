(** * LinuxProcessSem.Checks.Cases.Kernel.Groups — worked examples over getgroups (158) and setgroups (159)

    Mirrors [Sys/Kernel/Groups.v], which answers to Linux
    [kernel/groups.c]: this file holds the worked examples for the
    syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
(* [demo_model] and [root_model] are the credential fixtures; they are
   defined beside the id calls that mutate them, and shared rather than
   redefined — [Checks/Examples.v] re-exports every Cases module into one
   namespace, so two definitions of a name would shadow each other. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Kernel.Sys.

(* -------------------------------------------------------------------------
   getgroups (158)

   Every example below is here for the LAST of the four reasons listed
   at the top of [Checks/Examples.v] — the environment cannot be made to
   produce it — and for two separate readings of it.  A user program
   cannot choose how many supplementary groups its own process has:
   [setgroups] needs privilege the run does not have, and the model
   answers it only for the EMPTY list, so the branches that turn on a
   non-zero count are only conditionally reachable from a run and the
   fixtures below choose it instead.  And a [CheckReject] needs a kernel
   answering something no kernel answers.
   ------------------------------------------------------------------------- *)

(** A process with NO supplementary groups.  [Cases.Prelude.demo_groups]
    gives [demo_model] three, so the empty list needs its own fixture —
    and it is the one that reaches the zero-length arm, where a nonzero
    size writes nothing and cannot fault. *)
Definition no_groups_model : Model :=
  with_creds (mkCreds demo_uid demo_uid demo_uid demo_gid demo_gid demo_gid [])
             demo_model.

Definition getgroups_in (gidsetsize grouplist : word) : SyscallInput :=
  mkInput 158 [gidsetsize; grouplist; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** THE COUNT, and it is the LENGTH of the list rather than any id in
    it: [demo_groups] holds 27, 1002 and 4000, and the answer is 3.  The
    [grouplist] pointer is not read at size 0 — the same call with a
    garbage pointer gives the same answer, which is what
    [SYSCALL_DEFINE2(getgroups)]'s [if (gidsetsize)] guard buys. *)
Example getgroups_size_zero_reports_the_count :
  check_syscall (getgroups_in 0 0) (mkEffect 3 [] []) demo_model
    = CheckOk demo_model []
  /\ check_syscall (getgroups_in 0 3735928559) (mkEffect 3 [] []) demo_model
       = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** …and no other count is admissible.  A kernel that reported one more,
    one fewer, or a member of the list instead of its length is
    REJECTED.  This is the negative direction no real run can produce: a
    real kernel always answers truthfully. *)
Example getgroups_wrong_count_rejected :
  check_syscall (getgroups_in 0 0) (mkEffect 4 [] []) demo_model = CheckReject
  /\ check_syscall (getgroups_in 0 0) (mkEffect 2 [] []) demo_model = CheckReject
  /\ check_syscall (getgroups_in 0 0) (mkEffect 1002 [] []) demo_model
       = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** A NEGATIVE SIZE is -EINVAL, decided before the credentials are read,
    so it does not depend on the list at all: the same answer on a model
    with three groups and on one with none.  The size is an [int], so
    the register's high half is discarded first — a0 = 2^32 - 1 is
    [gidsetsize = -1]. *)
Example getgroups_negative_size_is_einval :
  check_syscall (getgroups_in 4294967295 3735928559)
    (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (getgroups_in 4294967295 3735928559)
       (mkEffect (errno_ret EINVAL) [] []) no_groups_model
       = CheckOk no_groups_model []
  /\ check_syscall (getgroups_in 18446744073709551615 0)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE TRUNCATION IS THE BEHAVIOR, in the other direction: a0 = 2^32
    has a zero low half, so it is [gidsetsize = 0] and asks for the
    count.  A model that compared the full 64-bit register would call
    this a huge positive size and answer down the writing path. *)
Example getgroups_size_truncates_to_int :
  check_syscall (getgroups_in 4294967296 0) (mkEffect 3 [] []) demo_model
    = CheckOk demo_model [].
Proof. vm_compute; reflexivity. Qed.

(** A SIZE TOO SMALL is -EINVAL and NOTHING IS WRITTEN, even though the
    call named a size the kernel would otherwise fill: the [i >
    gidsetsize] test fires before [groups_to_user] runs.  So -EFAULT is
    not admissible here however bad the pointer is. *)
Example getgroups_size_too_small_is_einval_not_efault :
  check_syscall (getgroups_in 2 3735928559)
    (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (getgroups_in 2 3735928559)
       (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE ZERO-LENGTH ARM.  With no supplementary groups and a nonzero
    size, [groups_to_user]'s loop runs zero times: the call returns 0,
    touches no memory, and cannot fault — there is no up-front
    [access_ok] over the array, so a garbage pointer is never
    dereferenced.  A model that faulted here would be modeling an
    [access_ok] the kernel does not do. *)
Example getgroups_empty_list_returns_zero_without_touching_the_array :
  check_syscall (getgroups_in 64 3735928559) (mkEffect 0 [] []) no_groups_model
    = CheckOk no_groups_model []
  /\ check_syscall (getgroups_in 64 3735928559)
       (mkEffect (errno_ret EFAULT) [] []) no_groups_model = CheckReject.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE WRITING PATH IS DECLINED.  A size big enough to hold three
    groups reaches [groups_to_user], which stores three 4-byte [gid_t]s
    and can fault part-way through; [Kernel.Groups.getgroups_spec] says
    why that is left [unmodeled] rather than guessed at.  Declining is
    the whole answer, so no observation of it is accepted either. *)
Example getgroups_writing_path_fails_closed :
  check_syscall (getgroups_in 3 4096) (mkEffect 3 [] []) demo_model
    = CheckUnmodeled
  /\ check_syscall (getgroups_in 64 4096) (mkEffect 3 [] []) demo_model
       = CheckUnmodeled
  (* AND THE TWO SIZES ON THE OTHER SIDE OF THE WRITING PATH, at the
     SAME pointer, so the declines above are a boundary rather than a
     description of one.  Both are [CheckUnmodeled] and would survive
     [getgroups] declining MORE -- the counting arm or the -EINVAL arm
     going unmodeled with the writing one -- which is the change this
     lemma exists to notice.  Size 0 asks for the count and never
     reaches [groups_to_user]; size 2 is too small for three groups and
     is refused before it does. *)
  /\ check_syscall (getgroups_in 0 4096) (mkEffect 3 [] []) demo_model
       = CheckOk demo_model []
  /\ check_syscall (getgroups_in 2 4096)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model [].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** THE ID SETTERS DO NOT DROP THE LIST.  [setgid] rebuilds the
    credentials, and the kernel's [prepare_creds] carries the same
    [struct group_info] over; a [State.set_cred_gids] that forgot
    [cr_groups] would make this [getgroups] answer 0.  [ENVIRONMENT]:
    the setter needs a privileged caller to reach an arbitrary gid, so
    this runs on [root_model], whose group list is [demo_groups] too. *)
Example setgid_keeps_the_supplementary_group_list :
  match check_syscall (mkInput 144 [4242; 0; 0; 0; 0; 0] (fun _ => None)
                         (fun _ => None))
          (mkEffect 0 [] []) root_model with
  | CheckOk m' _ => check_syscall (getgroups_in 0 0) (mkEffect 3 [] []) m'
                      = CheckOk m' []
  | _ => False
  end.
Proof. vm_compute; reflexivity. Qed.

(** [setgroups] refuses an unprivileged caller BEFORE it looks at either
    argument, so a size past NGROUPS_MAX, a negative size and an
    unreadable list are all -EPERM. *)
Example setgroups_refuses_before_it_reads_an_argument :
  check_syscall (mkInput 159 [18446744073709551615; 4096; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EPERM) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (mkInput 159 [1; 4096; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject
  /\ check_syscall (mkInput 159 [1; 4096; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) demo_model = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** A PRIVILEGED [setgroups] with a NON-EMPTY list would write a list
    read from user memory, which the model does not import, so it
    declines -- for a size of 1, for a size Linux refuses with -EINVAL
    ([NGROUPS_MAX] + 1), and for a negative size alike.  [ENVIRONMENT]:
    needs uid 0.  The empty list is answered; see
    [root_setgroups_empty_list_clears_the_groups] below. *)
Example privileged_setgroups_fails_closed :
  check_syscall (mkInput 159 [1; 4096; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) root_model = CheckUnmodeled
  /\ check_syscall (mkInput 159 [65537; 4096; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) root_model = CheckUnmodeled
  /\ check_syscall (mkInput 159 [4294967295; 4096; 0; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EINVAL) [] []) root_model = CheckUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition setgroups_in (gidsetsize grouplist : word) : SyscallInput :=
  mkInput 159 [gidsetsize; grouplist; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** THE PRIVILEGED EMPTY LIST, which the model before this arm declined:
    [setgroups(0, NULL)] by root answers 0 and clears the list, or
    answers -ENOMEM ([groups_alloc] or [prepare_creds]) and keeps it.
    The pointer is never read at size 0, so a garbage one is the same
    call, and [gidsetsize] is an [int], so a0 = 2^32 is size 0 too.  No
    other answer is admitted: not -EPERM (the caller is privileged), not
    -EFAULT (nothing is copied).  [ENVIRONMENT]: needs uid 0. *)
Example root_setgroups_empty_list_clears_the_groups :
  check_syscall (setgroups_in 0 0) (mkEffect 0 [] []) root_model
    = CheckOk (with_creds (mkCreds 0 0 0 0 0 0 []) demo_model) []
  /\ check_syscall (setgroups_in 0 3735928559) (mkEffect 0 [] []) root_model
       = CheckOk (with_creds (mkCreds 0 0 0 0 0 0 []) demo_model) []
  /\ check_syscall (setgroups_in 4294967296 0) (mkEffect 0 [] []) root_model
       = CheckOk (with_creds (mkCreds 0 0 0 0 0 0 []) demo_model) []
  /\ check_syscall (setgroups_in 0 0) (mkEffect (errno_ret ENOMEM) [] [])
       root_model = CheckOk root_model []
  /\ check_syscall (setgroups_in 0 0) (mkEffect (errno_ret EPERM) [] [])
       root_model = CheckReject
  /\ check_syscall (setgroups_in 0 0) (mkEffect (errno_ret EFAULT) [] [])
       root_model = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** ...and the list it leaves is the one [getgroups] then reports: the
    count was 3 ([demo_groups]) and is 0 after the call. *)
Example root_setgroups_empty_list_then_getgroups_reports_zero :
  match check_syscall (setgroups_in 0 0) (mkEffect 0 [] []) root_model with
  | CheckOk m' _ => check_syscall (getgroups_in 0 0) (mkEffect 0 [] []) m'
                      = CheckOk m' []
  | _ => False
  end.
Proof. vm_compute; reflexivity. Qed.

(** THE CONTROL, which the model before this arm passed too: the same
    [setgroups(0, NULL)] by an UNPRIVILEGED caller is -EPERM and nothing
    else -- [may_setgroups] is tested before the size. *)
Example setgroups_unprivileged_still_eperm :
  check_syscall (setgroups_in 0 0) (mkEffect (errno_ret EPERM) [] []) demo_model
    = CheckOk demo_model []
  /\ check_syscall (setgroups_in 0 0) (mkEffect 0 [] []) demo_model
       = CheckReject
  /\ check_syscall (setgroups_in 0 0) (mkEffect (errno_ret ENOMEM) [] [])
       demo_model = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.
