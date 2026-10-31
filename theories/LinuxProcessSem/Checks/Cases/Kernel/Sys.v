(** * LinuxProcessSem.Checks.Cases.Kernel.Sys — worked examples over getpid (172), getppid (173), gettid (178), uname (160), prctl (167), prlimit64 (261)

    Mirrors [Sys/Kernel/Sys.v], which answers to Linux [kernel/sys.c]:
    this file holds the worked examples for the syscalls defined there,
    and no others.  [setsid] (157) is defined there too but its worked
    examples are NOT here: they sit in [Checks/ProcessCreation.v], beside
    the process-creation numbers whose refusal they are the counterpart
    of, and they are built on that file's own [pc_model]/[pc_input].

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
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude Fs.ReadWrite Kernel.Fork.

(** The same envelope bound, for [getpid].  Earns its place by reason 1:
    it is a [forall] over admissible outcomes, and a finite set of runs
    can SAMPLE the envelope but cannot quantify over it.

    The proof is [exact] because [Kernel.Sys.getpid_spec] IS
    [Fork.set_tid_address_spec].  That is the point of stating it under
    this name anyway: a reader asking "is every value [getpid] may
    answer inside the envelope?" should find the answer under [getpid],
    not have to already know the two are one relation. *)

Lemma getpid_first_choice_is_within_modeled_envelope :
  forall i m eff m' evs,
  m_tid m = None ->
  getpid_spec i m (Ok eff m' evs) ->
  exists tid,
    (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z /\
    eff = mkEffect tid [] [] /\
    m' = with_tid tid m /\
    evs = [].
Proof. exact set_tid_address_first_choice_is_within_modeled_envelope. Qed.

(** The same envelope bound again, for [gettid], and it earns its place
    the same way: a finite set of runs can sample the envelope but
    cannot quantify over it.

    Stating it under this name is the point, as it is for [getpid]: a
    reader asking "what may [gettid] answer?" should not have to already
    know that three syscall numbers share one relation before the answer
    is reachable. *)

Lemma gettid_first_choice_is_within_modeled_envelope :
  forall i m eff m' evs,
  m_tid m = None ->
  gettid_spec i m (Ok eff m' evs) ->
  exists tid,
    (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z /\
    eff = mkEffect tid [] [] /\
    m' = with_tid tid m /\
    evs = [].
Proof. exact set_tid_address_first_choice_is_within_modeled_envelope. Qed.

(** A write to a FILE emits no events — the file system is observed only
    at exit.  This is the model-level content behind the [equiv] example
    [write_then_diverge_vs_diverge]: no admissible file-write outcome
    carries events. *)

(** ...and so does every other terminal-only request.  This drives the
    checker over the whole set on a CHANNEL. *)

(** Any other request on a LIVE fd is unmodeled (fail closed).  FIONREAD
    and FIONBIO are the two the model most conspicuously declines, and
    they are declined for opposite reasons: FIONREAD SUCCEEDS with an
    answer that depends on the fd's kind — bytes left in a file, bytes
    queued in a pipe — and FIONBIO succeeds and changes the file's
    O_NONBLOCK state, which this model does not carry.  Neither has a
    constant answer, so neither is modeled. *)

(* -------------------------------------------------------------------------
   The fd argument is 32 bits ([Syscall.fd32])

   Every fd-taking syscall declares its fd [int]/[unsigned int], so the
   kernel DISCARDS the high half of the register before touching the fd
   table.  What is here is the cross-run equality, the rejecting halves, the
   boundary sweep that justifies zero-extension, and the constant itself.
   ------------------------------------------------------------------------- *)

(** write(2^32 + 1, "ab", 2) is a write to STDOUT, with exactly the
    verdict and events of write(1, "ab", 2) — a bare 64-bit compare
    against the fd table would answer -EBADF, a behavior no kernel
    produces.  And that -EBADF is NOT admissible. *)

(* -------------------------------------------------------------------------
   uname (160)

   These earn their place by the same reason [prlimit64]'s pinning
   examples do: they are claims about a relation BETWEEN two calls of one
   run, and about the shape of a name no kernel hands out.  A real run
   reaches the first but can never produce the second — no Linux answers
   a uname whose sysname is not "Linux", so the rejecting half exists
   only here.
   ------------------------------------------------------------------------- *)

(** The FIRST uname is where the environment's kernel identity enters the
    model: any name inside [Kernel.Sys.utsname_wf]'s envelope is
    admissible, and it becomes the pin. *)

Example uname_first_copy_pins :
  check_syscall (mkInput 160 [4096; 0; 0; 0; 0; 0] (fun _ => None) uts_out)
    (mkEffect 0 [(4096, uts_demo)] []) uts_model
  = CheckOk (with_utsname uts_demo uts_model) [].
Proof. check_eq. Qed.

(** …but not a name the kernel cannot hold.  [sysname] is written once,
    by [init_uts_ns], and no syscall touches it, so "Linuy" is a
    conformance failure rather than an unusual machine. *)

Example uname_wrong_sysname_rejected :
  check_syscall (mkInput 160 [4096; 0; 0; 0; 0; 0] (fun _ => None) uts_out)
    (mkEffect 0 [(4096, uts_bad_sysname)] []) uts_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** …and not an unterminated member either.  The release's CONTENT is
    free — [uts_demo] and [uts_demo_b] are both admissible — so this
    rejection attributes to the terminator conjunct alone. *)

Example uname_unterminated_release_rejected :
  check_syscall (mkInput 160 [4096; 0; 0; 0; 0; 0] (fun _ => None) uts_out)
    (mkEffect 0 [(4096, uts_unterminated_release)] []) uts_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** Once pinned, a later uname must repeat it exactly.  The defector
    below is itself well-formed — [uts_demo_b] would have been accepted
    as the FIRST answer — so it is refused for disagreeing with the
    record, not for being a bad name.  That is the whole content of "a
    machine has one kernel for the life of a process", and it is the
    conjunct a per-call [choose] would have dropped. *)

Example uname_pinned_copy_repeats :
  check_syscall (mkInput 160 [4096; 0; 0; 0; 0; 0] (fun _ => None) uts_out)
    (mkEffect 0 [(4096, uts_demo)] []) uts_pinned
  = CheckOk uts_pinned [].
Proof. check_eq. Qed.

Example uname_pinned_copy_defector_rejected :
  check_syscall (mkInput 160 [4096; 0; 0; 0; 0; 0] (fun _ => None) uts_out)
    (mkEffect 0 [(4096, uts_demo_b)] []) uts_pinned
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** …and the defector is refused for THAT reason and no other: offered as
    a first answer it is accepted, and pins itself. *)

Example uname_defector_is_itself_admissible_first :
  check_syscall (mkInput 160 [4096; 0; 0; 0; 0; 0] (fun _ => None) uts_out)
    (mkEffect 0 [(4096, uts_demo_b)] []) uts_model
  = CheckOk (with_utsname uts_demo_b uts_model) [].
Proof. check_eq. Qed.

(** A destination past [State.TASK_SIZE] fails [access_ok], which is
    [copy_to_user]'s own gate, so -EFAULT is exact and no byte moves. *)

Example uname_access_ok_fault :
  check_syscall
    (mkInput 160 [9223372036854775808; 0; 0; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) uts_model
  = CheckOk uts_model [].
Proof. check_eq. Qed.

(** A range [access_ok] ADMITS but memory does not wholly back is
    declined, not faulted: [copy_to_user] would commit a prefix and then
    answer -EFAULT, and the model cannot say how long that prefix is.
    One byte short of 390 is the whole difference. *)

Example uname_one_byte_short_is_unmodeled :
  check_syscall (mkInput 160 [4096; 0; 0; 0; 0; 0] (fun _ => None) uts_out_short)
    (mkEffect 0 [(4096, uts_demo)] []) uts_model
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** THE WRAPPING DESTINATION, pinned in both directions.  [uname_spec]
    asks [State.access_okb] BEFORE it walks [State.read_bytes_map], and
    these three say why that order is the arm and not a style choice.
    The group is modelled on [Checks.Cases.Fs.Pipe]'s [pipe2_wrap_]
    examples; the argument for the guard is on [Kernel.Sys.uname_spec]'s
    own arm and is not restated here.

    No real run can reach it: no real process has memory mapped at the
    top of the address space, so the mapping below is one only a
    hand-written model can present. *)

(** What the bare walk says: "wholly writable", because the word
    arithmetic wraps 2^64 - 4 round onto the 386 mapped bytes at 0.
    Pinning it beside the two below is what stops them going vacuous —
    each would also pass if [uts_wrap_name] stopped wrapping or
    [uts_wrap_mem] stopped mapping the range. *)

Example uname_wrap_would_pass_the_bare_walk :
  read_bytes_map uts_wrap_mem uts_wrap_name (Z_to_bv 64 390) <> None.
Proof. vm_compute. discriminate. Qed.

Example uname_wrap_name_is_not_access_ok :
  access_okb uts_wrap_name 390 = false.
Proof. vm_compute. reflexivity. Qed.

(** THE NEGATIVE HALF: the effect offered here is exactly what an
    unguarded arm would have accepted — 0 returned with the 390 bytes
    stored at [2^64 - 4] and, once the word wrapped, at 0.  Linux cannot
    produce it: [copy_to_user]'s [access_ok] refuses the range before a
    byte moves and [SYSCALL_DEFINE1(newuname)] returns -EFAULT. *)

Example uname_wrapping_destination_faults :
  check_syscall (mkInput 160 [uts_wrap_name; 0; 0; 0; 0; 0]
                   (fun _ => None) uts_wrap_mem)
    (mkEffect (errno_ret EFAULT) [] []) uts_model
  = CheckOk uts_model [].
Proof. check_eq. Qed.

Example uname_wrapping_destination_rejects_the_copy :
  check_syscall (mkInput 160 [uts_wrap_name; 0; 0; 0; 0; 0]
                   (fun _ => None) uts_wrap_mem)
    (mkEffect 0 [(uts_wrap_name, uts_demo)] []) uts_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

Example prlimit64_first_read_pins :
  check_syscall (mkInput 261 [0; 4; 0; 4096; 0; 0] (fun _ => None) rlim_out)
    (mkEffect 0 [(4096, rlim_bytes 3 7)] []) rlim_model
  = CheckOk (with_rlimit_core (rlim_bytes 3 7) rlim_model) [].
Proof. check_eq. Qed.

(** …but not an inverted pair.  No Linux reports soft > hard, and this is
    the only place that claim is written down. *)

Example prlimit64_read_soft_over_hard_rejected :
  check_syscall (mkInput 261 [0; 4; 0; 4096; 0; 0] (fun _ => None) rlim_out)
    (mkEffect 0 [(4096, rlim_bytes 1 0)] []) rlim_model
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** Once pinned, a later read must repeat it exactly.  The defector below
    is well-formed — it is refused for disagreeing with the record, not
    for being a bad pair. *)

Example prlimit64_pinned_read_repeats :
  check_syscall (mkInput 261 [0; 4; 0; 4096; 0; 0] (fun _ => None) rlim_out)
    (mkEffect 0 [(4096, rlim_bytes 3 7)] []) rlim_pinned
  = CheckOk rlim_pinned [].
Proof. check_eq. Qed.

Example prlimit64_pinned_read_defector_rejected :
  check_syscall (mkInput 261 [0; 4; 0; 4096; 0; 0] (fun _ => None) rlim_out)
    (mkEffect 0 [(4096, rlim_bytes 2 7)] []) rlim_pinned
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(** dropbear's own call, and the reason the syscall is modeled at all:
    zero the soft limit, write the hard limit back unchanged.  The
    recorded pair MOVES to what was set — 3 becomes 0. *)

Example prlimit64_set_new_soft_replaces_the_record :
  check_syscall (mkInput 261 [0; 4; 8192; 0; 0; 0] (rlim_src_at 0 7) (fun _ => None))
    (with_copyins [(8192, 16%nat)] (mkEffect 0 [] [])) rlim_pinned
  = CheckOk (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) [].
Proof. check_eq. Qed.

(** A pointer past [TASK_SIZE] fails [access_ok] before
    [copy_from_user] issues a load.  The EFAULT therefore carries no copy-in
    provenance, and claiming the unreachable struct as read is rejected. *)

Example prlimit64_set_access_ok_fault_has_no_copyins :
  check_syscall
    (mkInput 261 [0; 4; 9223372036854775808; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) rlim_pinned
  = CheckOk rlim_pinned [].
Proof. check_eq. Qed.

Example prlimit64_set_access_ok_fault_rejects_copyins :
  check_syscall
    (mkInput 261 [0; 4; 9223372036854775808; 0; 0; 0]
      (fun _ => None) (fun _ => None))
    (with_copyins [(9223372036854775808, 16%nat)]
      (mkEffect (errno_ret EFAULT) [] [])) rlim_pinned
  = CheckReject.
Proof. check_eq. Qed.

(** …so a read AFTER that set reports the pair the set installed, and the
    pair that was there before it is now refused.  Together with the
    example above this is the whole content of "a set replaces the
    record"; nothing observable from a single run distinguishes it. *)

Example prlimit64_read_after_set_reports_the_set_pair :
  check_syscall (mkInput 261 [0; 4; 0; 4096; 0; 0] (fun _ => None) rlim_out)
    (mkEffect 0 [(4096, rlim_bytes 0 7)] [])
    (with_rlimit_core (rlim_bytes 0 7) rlim_pinned)
  = CheckOk (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) [].
Proof. check_eq. Qed.

Example prlimit64_read_after_set_rejects_the_old_pair :
  check_syscall (mkInput 261 [0; 4; 0; 4096; 0; 0] (fun _ => None) rlim_out)
    (mkEffect 0 [(4096, rlim_bytes 3 7)] [])
    (with_rlimit_core (rlim_bytes 0 7) rlim_pinned)
  = CheckReject.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------
   prlimit64 (261): THE TWO STRUCT COPIES THAT WALKED OFF THE TOP

   Both arms read their 16-byte [struct rlimit64] through
   [State.copy_bytes_map], which asks [State.access_okb] before the
   walk; [Kernel.Sys.prlimit64_spec]'s note says why, and
   [State.copy_bytes_map]'s note carries the wrap argument.  Each group
   has the shape of [Checks.Cases.Net.Socket]'s wrapping-read groups:
   the wrapping call refused, a NEIGHBOURING ordinary call at the top of
   what [State.access_okb] accepts still answered — so the guard is not
   a blanket refusal of high addresses — and the control that the bare
   walk really would have passed, without which the refusal would also
   hold if the memory quietly stopped short.

   THE MEMORIES MAP EXACTLY THEIR OWN RANGE: [wmem_open] answers [Some]
   everywhere and could not tell a wrapping pointer from any other.
   ------------------------------------------------------------------------- *)

(* ---- the read's [old_rlim] --------------------------------------------- *)

(** Eight writable bytes below the top and eight from 0: the 16-byte
    copy-out covers both halves, so the bare walk answered [Some] and
    the first read was answered 0, with the pair stored across the wrap
    and pinned as the record. *)
Definition prlimit64_wrap_old_rlim : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition prlimit64_wrap_old_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example prlimit64_wrap_old_would_pass_the_bare_walk :
  read_bytes_map prlimit64_wrap_old_mem prlimit64_wrap_old_rlim (Z_to_bv 64 16)
    <> None.
Proof. vm_compute. discriminate. Qed.

Example prlimit64_wrap_old_is_not_copyable :
  copy_bytes_map prlimit64_wrap_old_mem prlimit64_wrap_old_rlim 16 = None.
Proof. vm_compute. reflexivity. Qed.

(** -EFAULT, nothing stored and nothing pinned: the model it answers in
    is the one the call started in.  The [copy_to_user] of [old_rlim] in
    [SYSCALL_DEFINE4(prlimit64)] (kernel/sys.c) refuses this range in
    [access_ok] before it stores a byte.  The first read the bare walk
    admitted is refused, and so is an -EFAULT claiming a copy-in. *)
Example prlimit64_wrapping_old_rlim_is_efault :
  check_syscall (mkInput 261 [0; 4; 0; prlimit64_wrap_old_rlim; 0; 0]
                   (fun _ => None) prlimit64_wrap_old_mem)
    (mkEffect (errno_ret EFAULT) [] []) rlim_model
  = CheckOk rlim_model []
  /\ check_syscall (mkInput 261 [0; 4; 0; prlimit64_wrap_old_rlim; 0; 0]
                     (fun _ => None) prlimit64_wrap_old_mem)
       (mkEffect 0 [(prlimit64_wrap_old_rlim, rlim_bytes 3 7)] []) rlim_model
     = CheckReject
  /\ check_syscall (mkInput 261 [0; 4; 0; prlimit64_wrap_old_rlim; 0; 0]
                     (fun _ => None) prlimit64_wrap_old_mem)
       (with_copyins [(prlimit64_wrap_old_rlim, 16%nat)]
          (mkEffect (errno_ret EFAULT) [] [])) rlim_model
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** THE NEIGHBOUR: the last sixteen bytes [State.access_okb] accepts,
    writable end to end.  The same first read is still answered there —
    0, the pair stored at the top, the record pinned — and -EFAULT is
    refused. *)
Definition prlimit64_top_old_rlim : word := Z_to_bv 64 (TASK_SIZE - 16).

Definition prlimit64_top_old_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 16 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example prlimit64_old_rlim_at_the_top_still_answers :
  check_syscall (mkInput 261 [0; 4; 0; prlimit64_top_old_rlim; 0; 0]
                   (fun _ => None) prlimit64_top_old_mem)
    (mkEffect 0 [(prlimit64_top_old_rlim, rlim_bytes 3 7)] []) rlim_model
  = CheckOk (with_rlimit_core (rlim_bytes 3 7) rlim_model) []
  /\ check_syscall (mkInput 261 [0; 4; 0; prlimit64_top_old_rlim; 0; 0]
                     (fun _ => None) prlimit64_top_old_mem)
       (mkEffect (errno_ret EFAULT) [] []) rlim_model
     = CheckReject.
Proof. split; check_eq. Qed.

(* ---- the set's [new_rlim] ---------------------------------------------- *)

(** Eight readable bytes below the top and eight from 0, holding
    dropbear's own set: soft 0 in the eight bytes below the top, hard 7
    in the byte at 0.  The bare walk reads exactly that pair across the
    wrap, and against [rlim_pinned]'s hard limit of 7 it is the set
    [Kernel.Sys.prlimit64_spec] answers 0 to and records. *)
Definition prlimit64_wrap_new_rlim : word := Z_to_bv 64 (2 ^ 64 - 8).

Definition prlimit64_wrap_new_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (if (bv_unsigned a =? 0)%Z then Z_to_bv 8 7 else Z_to_bv 8 0)
           else None.

Example prlimit64_wrap_new_would_pass_the_bare_walk :
  read_bytes_map prlimit64_wrap_new_mem prlimit64_wrap_new_rlim (Z_to_bv 64 16)
    <> None.
Proof. vm_compute. discriminate. Qed.

(** ...and what it reads is the pair the set arm would have installed. *)
Example prlimit64_wrap_new_bare_walk_reads_a_settable_pair :
  read_bytes_map prlimit64_wrap_new_mem prlimit64_wrap_new_rlim (Z_to_bv 64 16)
    = Some (rlim_bytes 0 7).
Proof. check_eq. Qed.

Example prlimit64_wrap_new_is_not_copyable :
  copy_bytes_map prlimit64_wrap_new_mem prlimit64_wrap_new_rlim 16 = None.
Proof. vm_compute. reflexivity. Qed.

(** -EFAULT with an empty copy-in ledger and the record unchanged.  The
    [copy_from_user] of [new_rlim] in [SYSCALL_DEFINE4(prlimit64)]
    (kernel/sys.c) refuses this range in [access_ok] before it loads a
    byte, and before the pid lookup.  The set the bare walk admitted —
    0, the 16 bytes in the ledger, the record moved to [(0, 7)] — is
    refused, and so is an -EFAULT claiming the copy-in. *)
Example prlimit64_wrapping_new_rlim_is_efault :
  check_syscall (mkInput 261 [0; 4; prlimit64_wrap_new_rlim; 0; 0; 0]
                   prlimit64_wrap_new_mem (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) rlim_pinned
  = CheckOk rlim_pinned []
  /\ check_syscall (mkInput 261 [0; 4; prlimit64_wrap_new_rlim; 0; 0; 0]
                     prlimit64_wrap_new_mem (fun _ => None))
       (with_copyins [(prlimit64_wrap_new_rlim, 16%nat)] (mkEffect 0 [] []))
       rlim_pinned
     = CheckReject
  /\ check_syscall (mkInput 261 [0; 4; prlimit64_wrap_new_rlim; 0; 0; 0]
                     prlimit64_wrap_new_mem (fun _ => None))
       (with_copyins [(prlimit64_wrap_new_rlim, 16%nat)]
          (mkEffect (errno_ret EFAULT) [] [])) rlim_pinned
     = CheckReject.
Proof. split; [|split]; check_eq. Qed.

(** THE NEIGHBOUR: the same pair in the last sixteen bytes
    [State.access_okb] accepts, readable end to end.  The set is still
    answered — 0, the copy-in recorded, the record moved — and -EFAULT
    is refused. *)
Definition prlimit64_top_new_rlim : word := Z_to_bv 64 (TASK_SIZE - 16).

Definition prlimit64_top_new_mem : word -> option byte :=
  fun a => if ((TASK_SIZE - 16 <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some (if (bv_unsigned a =? TASK_SIZE - 8)%Z
                      then Z_to_bv 8 7 else Z_to_bv 8 0)
           else None.

Example prlimit64_new_rlim_at_the_top_still_sets :
  check_syscall (mkInput 261 [0; 4; prlimit64_top_new_rlim; 0; 0; 0]
                   prlimit64_top_new_mem (fun _ => None))
    (with_copyins [(prlimit64_top_new_rlim, 16%nat)] (mkEffect 0 [] []))
    rlim_pinned
  = CheckOk (with_rlimit_core (rlim_bytes 0 7) rlim_pinned) []
  /\ check_syscall (mkInput 261 [0; 4; prlimit64_top_new_rlim; 0; 0; 0]
                     prlimit64_top_new_mem (fun _ => None))
       (mkEffect (errno_ret EFAULT) [] []) rlim_pinned
     = CheckReject.
Proof. split; check_eq. Qed.

(* =========================================================================
   PART 5 — process inputs (argv and the auxv)

   Properties of the initial stack image, which no syscall observes:
   [Run.run] quantifies over these, so they are inputs to the theorem
   rather than anything a trace records.
   ========================================================================= *)

(** [valid_argv] requires at least one argument (kernel commit
    dcd46d897adb rewrites an empty [execve] argv to a single empty
    string), so a reference binary may rely on argv[0] existing.  The
    rewritten form — a single empty string — stays valid: argv[0] need
    not be nonempty. *)

(* =========================================================================
   Credentials — worked examples over the eight id calls
   ========================================================================= *)

(** The model a demo run starts in: an ordinary unprivileged launch, its
    six ids derived from [Cases.Prelude.demo_uid] / [demo_gid] by
    [State.init_model]. *)
Definition demo_model : Model := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** A ROOT process: all six ids 0, which is what [State.init_model]
    builds for a launch by root and what makes
    [State.creds_privileged] true. *)
Definition root_model : Model :=
  with_creds (mkCreds 0 0 0 0 0 0 demo_groups) demo_model.

(** A process whose six ids are SIX DIFFERENT NUMBERS.  Nothing at launch
    looks like this — [State.init_model] collapses each triple to one
    value — so only a privilege change produces it and no run
    starts here.  Six distinct values are what make the checks below
    discriminate: on a state where the uid triple and the gid triple
    coincide, a dispatcher that wired [getegid] to [cr_euid] would pass. *)
Definition split_ids_model : Model :=
  with_creds (mkCreds 1000 1001 1002 2000 2001 2002 demo_groups) demo_model.

(** Each reader reads ITS OWN field.  [ENVIRONMENT] twice over: the four
    answers are distinguishable only on a state with six different ids,
    and a run whose uid and gid are equal cannot even distinguish
    [getuid] from [getgid]. *)
Example each_reader_reads_its_own_field :
  check_syscall (mkInput 174 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1000 [] []) split_ids_model = CheckOk split_ids_model []
  /\ check_syscall (mkInput 175 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1001 [] []) split_ids_model = CheckOk split_ids_model []
  /\ check_syscall (mkInput 176 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2000 [] []) split_ids_model = CheckOk split_ids_model []
  /\ check_syscall (mkInput 177 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 2001 [] []) split_ids_model = CheckOk split_ids_model []
  (* and no reader will answer any of the other five ids *)
  /\ check_syscall (mkInput 176 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1000 [] []) split_ids_model = CheckReject
  /\ check_syscall (mkInput 177 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1001 [] []) split_ids_model = CheckReject
  /\ check_syscall (mkInput 175 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 1002 [] []) split_ids_model = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** PRIVILEGED [setuid]: real, effective and saved all become the
    argument — the transition that gives root away for good, and the
    reason a privilege drop must set the group ids FIRST.
    [ENVIRONMENT]: needs uid 0. *)
Example privileged_setuid_moves_all_three_ids :
  check_syscall (mkInput 146 [1000; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) root_model
  = CheckOk (with_creds (mkCreds 1000 1000 1000 0 0 0 demo_groups) demo_model) [].
Proof. solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** -EAGAIN, in the one place it is admissible, and nowhere else.
    [set_user] and [set_cred_ucounts] allocate only when the REAL uid
    moves, and neither has a group-side counterpart, so the errno set is
    [ENOMEM; EAGAIN] for exactly one shape: a USER-id setter, privileged,
    naming an id other than the current real one.  Move any one of those
    three and -EAGAIN must be refused.  This is the only place the
    [user] parameter of [Kernel.Sys.setid_spec] and the [true] arm of
    [Kernel.Sys.setid_errnos] are exercised in the ACCEPTING direction:
    an unprivileged run cannot reach a privileged setter at all.
    [ENVIRONMENT]: needs uid 0. *)
Example eagain_only_when_a_privileged_setuid_moves_the_real_uid :
  (* user setter, privileged, real uid moves 0 -> 1000: admissible *)
  check_syscall (mkInput 146 [1000; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EAGAIN) [] []) root_model = CheckOk root_model []
  (* the GROUP setter on the same shape: no set_user, so refused *)
  /\ check_syscall (mkInput 144 [1000; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) root_model = CheckReject
  (* privileged, but the real uid does not move: refused *)
  /\ check_syscall (mkInput 146 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) root_model = CheckReject
  (* the same call by an unprivileged caller: refused *)
  /\ check_syscall (mkInput 146 [1000; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) split_ids_model = CheckReject
  (* -ENOMEM, by contrast, is admissible on every one of those *)
  /\ check_syscall (mkInput 144 [1000; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) root_model = CheckOk root_model [].
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** UNPRIVILEGED [setuid] moves the EFFECTIVE id and nothing else, and
    reaches the saved id as well as the real one — a disjunct that is
    dead in every state an unprivileged run can reach, since [State.init_model]
    makes the two agree at launch.  [ENVIRONMENT]: needs split ids. *)
Example unprivileged_setuid_moves_only_the_effective_id :
  check_syscall (mkInput 146 [1000; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) split_ids_model
  = CheckOk (with_creds (mkCreds 1000 1000 1002 2000 2001 2002 demo_groups) demo_model) []
  /\ check_syscall (mkInput 146 [1002; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) split_ids_model
     = CheckOk (with_creds (mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) demo_model) []
  /\ check_syscall (mkInput 146 [1003; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) split_ids_model = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** [setresgid(-1, -1, g)] parks a group in the SAVED gid and touches
    nothing else — dropbear's way of keeping the utmp group in reach.
    Unlike [setuid], these calls never move an id the caller did not
    name.  [ENVIRONMENT]: needs the privilege to name a group the process
    does not hold. *)
Example setresgid_parks_a_group_in_the_saved_id :
  check_syscall (mkInput 149 [4294967295; 4294967295; 22; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) root_model
  = CheckOk (with_creds (mkCreds 0 0 0 0 0 22 demo_groups) demo_model) [].
Proof. solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** [setresuid] (147) past its no-op and -EPERM paths, which nothing
    else here reaches.  From a launch state all three ids agree,
    so every unprivileged call either asks for nothing or names an id the
    process does not hold — meaning no unprivileged run touches the allocating arm,
    and with it the [user] parameter that is the ONLY difference between
    [Kernel.Sys.setresid_spec]'s two instantiations.  [ENVIRONMENT]:
    uid 0. *)
Example setresuid_reaches_its_allocating_branch :
  check_syscall (mkInput 147 [1000; 1000; 1000; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) root_model
  = CheckOk (with_creds (mkCreds 1000 1000 1000 0 0 0 demo_groups) demo_model) []
  (* -EAGAIN is admissible: the REAL uid moves, and this is the user
     setter *)
  /\ check_syscall (mkInput 147 [1000; 1000; 1000; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) root_model = CheckOk root_model []
  (* the group twin on the identical shape: no set_user, so refused *)
  /\ check_syscall (mkInput 149 [1000; 1000; 1000; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) root_model = CheckReject
  (* -ENOMEM is admissible on both: this arm is past [prepare_creds] *)
  /\ check_syscall (mkInput 149 [1000; 1000; 1000; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) root_model = CheckOk root_model [].
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** UNPRIVILEGED [setresuid] REARRANGING ids the process already holds:
    permitted, and it moves them.  This is the arm between the no-op fast
    path and -EPERM, dead in every state an unprivileged run can reach because a
    launch gives all three ids one value and leaves nothing to
    rearrange.  [ENVIRONMENT]: split ids. *)
Example unprivileged_setresuid_may_rearrange_held_ids :
  check_syscall (mkInput 147 [4294967295; 1002; 4294967295; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect 0 [] []) split_ids_model
  = CheckOk (with_creds (mkCreds 1000 1002 1002 2000 2001 2002 demo_groups) demo_model) []
  (* the real uid does not move here, so -ENOMEM is admissible and
     -EAGAIN is not *)
  /\ check_syscall (mkInput 147 [4294967295; 1002; 4294967295; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret ENOMEM) [] []) split_ids_model
     = CheckOk split_ids_model []
  /\ check_syscall (mkInput 147 [4294967295; 1002; 4294967295; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect (errno_ret EAGAIN) [] []) split_ids_model = CheckReject
  (* one id the process does not hold, and the whole call is refused *)
  /\ check_syscall (mkInput 147 [4294967295; 1003; 4294967295; 0; 0; 0]
                     (fun _ => None) (fun _ => None))
       (mkEffect 0 [] []) split_ids_model = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(* =========================================================================
   prctl (167): the three options kernel/sys.c answers

   Each extension is pinned in pairs: the call the model used to DECLINE
   (every option but [PR_CAPBSET_READ] was [unmodeled]) now answered, its
   refusal answered too, and beside them a control the old model already
   passed -- an option that still declines, and [PR_CAPBSET_READ]
   unchanged -- so a [prctl] that answered everything would fail here as
   surely as one that answered nothing.  The model is [demo_model]
   throughout and comes back unchanged: none of the three is stored.
   ========================================================================= *)

Definition prctl_in (opt a2 a3 a4 a5 : word) : SyscallInput :=
  mkInput 167 [opt; a2; a3; a4; a5; 0] (fun _ => None) (fun _ => None).

(** [prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)] is 0, the call bwrap makes
    in [main]; any other [arg2], or any nonzero [arg3]..[arg5] -- a2..a4,
    read as whole registers -- is -EINVAL.  The option is an [int], so a
    high half on a0 is discarded and 2^32 + 38 is the same call. *)
Example prctl_no_new_privs_answered :
  check_syscall (prctl_in 38 1 0 0 0) (mkEffect 0 [] []) demo_model
    = CheckOk demo_model []
  /\ check_syscall (prctl_in 38 2 0 0 0)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (prctl_in 38 1 0 0 1)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (prctl_in 38 1 4294967296 0 0)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (prctl_in 4294967334 1 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckOk demo_model []
  (* and each answer is the only one: no 0 for a refused shape, no
     -EINVAL for the accepted one *)
  /\ check_syscall (prctl_in 38 2 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckReject
  /\ check_syscall (prctl_in 38 1 0 0 0)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** [prctl(PR_SET_PDEATHSIG, sig)] is 0 for [sig] in 0..64 -- the full
    register, [valid_signal] on an [unsigned long] -- and -EINVAL above,
    65 and 2^32 + 9 included.  bwrap's call is [SIGKILL] (9). *)
Example prctl_pdeathsig_answered :
  check_syscall (prctl_in 1 9 0 0 0) (mkEffect 0 [] []) demo_model
    = CheckOk demo_model []
  /\ check_syscall (prctl_in 1 0 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckOk demo_model []
  /\ check_syscall (prctl_in 1 64 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckOk demo_model []
  /\ check_syscall (prctl_in 1 65 0 0 0)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (prctl_in 1 4294967305 0 0 0)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (prctl_in 1 65 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckReject
  (* arg3..arg5 are not read on this option *)
  /\ check_syscall (prctl_in 1 9 7 7 7) (mkEffect 0 [] []) demo_model
       = CheckOk demo_model [].
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** [prctl(PR_SET_DUMPABLE, v)] is 0 for [SUID_DUMP_DISABLE] (0) and
    [SUID_DUMP_USER] (1), the call bwrap makes after it drops privilege,
    and -EINVAL for anything else, [SUID_DUMP_ROOT] (2) included. *)
Example prctl_dumpable_answered :
  check_syscall (prctl_in 4 1 0 0 0) (mkEffect 0 [] []) demo_model
    = CheckOk demo_model []
  /\ check_syscall (prctl_in 4 0 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckOk demo_model []
  /\ check_syscall (prctl_in 4 2 0 0 0)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = CheckOk demo_model []
  /\ check_syscall (prctl_in 4 2 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** THE CONTROL, which the model before these three options passed too.
    The readers of what they set -- [PR_GET_NO_NEW_PRIVS] (39),
    [PR_GET_PDEATHSIG] (2), [PR_GET_DUMPABLE] (3) -- still decline, as
    does the tagging option 55 the [State.access_okb] argument rests on,
    and [PR_CAPBSET_READ] still answers 1. *)
Example prctl_options_still_declined :
  check_syscall (prctl_in 39 0 0 0 0) (mkEffect 0 [] []) demo_model
    = CheckUnmodeled
  /\ check_syscall (prctl_in 2 0 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckUnmodeled
  /\ check_syscall (prctl_in 3 0 0 0 0) (mkEffect 1 [] []) demo_model
       = CheckUnmodeled
  /\ check_syscall (prctl_in 55 0 0 0 0) (mkEffect 0 [] []) demo_model
       = CheckUnmodeled
  /\ check_syscall (prctl_in 23 0 0 0 0) (mkEffect 1 [] []) demo_model
       = CheckOk demo_model [].
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(* =========================================================================
   getppid (173): a fresh choice on every call
   ========================================================================= *)

Definition getppid_in : SyscallInput :=
  mkInput 173 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None).

(** Any pid below [Fork.PID_MAX_ENVELOPE] is admitted, 0 (a parent in
    an ancestor pid namespace) included, and the model comes back
    UNCHANGED: two different answers are both admissible on the same
    model, which is the "no pin" half of the spec.  The envelope bound
    and an errno are refused.  The model before this arm declined every
    [getppid]. *)
Example getppid_answers_any_pid_in_the_envelope :
  check_syscall getppid_in (mkEffect 4242 [] []) demo_model
    = CheckOk demo_model []
  /\ check_syscall getppid_in (mkEffect 1 [] []) demo_model
       = CheckOk demo_model []
  /\ check_syscall getppid_in (mkEffect 0 [] []) demo_model
       = CheckOk demo_model []
  /\ check_syscall getppid_in (mkEffect (Z_to_bv 64 PID_MAX_ENVELOPE) [] [])
       demo_model = CheckReject
  /\ check_syscall getppid_in (mkEffect (errno_ret EPERM) [] []) demo_model
       = CheckReject.
Proof. repeat split; solve [ check_eq | vm_compute; reflexivity ]. Qed.

(** THE CONTROL, which the model before this arm passed too: [getpid]
    on the same model is untouched by the new number -- it still pins
    the tid at its first answer, where [getppid] pins nothing. *)
Example getppid_leaves_getpid_alone :
  check_syscall (mkInput 172 [0; 0; 0; 0; 0; 0] (fun _ => None) (fun _ => None))
    (mkEffect 4242 [] []) demo_model
  = CheckOk (with_tid 4242 demo_model) [].
Proof. check_eq. Qed.
