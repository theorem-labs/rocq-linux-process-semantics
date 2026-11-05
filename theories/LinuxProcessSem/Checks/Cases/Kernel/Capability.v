(** * LinuxProcessSem.Checks.Cases.Kernel.Capability — worked examples over capget (90) and capset (91)

    Mirrors [Sys/Kernel/Capability.v], which answers to Linux
    [kernel/capability.c]: this file holds the worked examples for the
    syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    THE PAIRED TESTS.  Before [Kernel.Capability], 90 and 91 had no entry
    in [Sys.SyscallTable.spec_table], so [check_syscall] answered
    [CheckUnmodeled] for EVERY input of either number.  Each pair below
    is the case that model declined and the new one answers, and a
    control that is [CheckUnmodeled] under both: a shape the new arms
    still decline.

    THE INHERITABLE PAIRS.  Before the arms read [State.m_cap_inheritable],
    [capget] let the environment choose both inheritable words within the
    valid bits, and [capset] declined every non-zero data word.  Each pair
    marked INHERITABLE below is a case where that text and this one differ,
    and a control both answer alike. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** The header at 4096 and the data image at 8192. *)
Definition cap_header : word := Z_to_bv 64 4096.
Definition cap_dataptr : word := Z_to_bv 64 8192.

(** Readable memory: a header at 4096 holding version [ver] and pid 0,
    and the 24 data bytes [db] at 8192.  Nothing else is readable. *)
Definition cap_mem (ver : Z) (db : list byte) : word -> option byte :=
  fun a =>
    let z := bv_unsigned a in
    if ((4096 <=? z)%Z && (z <? 4100)%Z)%bool
    then Some (Z_to_bv 8 ((ver / 2 ^ (8 * (z - 4096))) mod 256))
    else if ((4100 <=? z)%Z && (z <? 4104)%Z)%bool then Some (Z_to_bv 8 0)
    else if ((8192 <=? z)%Z && (z <? 8216)%Z)%bool
    then Some (nth (Z.to_nat (z - 8192)) db (Z_to_bv 8 0))
    else None.

(** Writable memory: the 24 data bytes at 8192, and nothing else. *)
Definition cap_wmem : word -> option byte :=
  fun a =>
    let z := bv_unsigned a in
    if ((8192 <=? z)%Z && (z <? 8216)%Z)%bool then Some (Z_to_bv 8 0) else None.

Definition capget_input (ver : Z) (dataptr : word) : SyscallInput :=
  mkInput 90 [cap_header; dataptr; 0; 0; 0; 0] (cap_mem ver []) cap_wmem.

Definition capset_input (db : list byte) : SyscallInput :=
  mkInput 91 [cap_header; cap_dataptr; 0; 0; 0; 0]
    (cap_mem LINUX_CAPABILITY_VERSION_3 db) cap_wmem.

Definition cap_base : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 demo_limit) IEof [] None None None.

(** An ordinary user: uid, euid and suid 1000. *)
Definition cap_user_model : Model :=
  with_creds (mkCreds 1000 1000 1000 1002 1002 1002 []) cap_base.

(** Root: all three uids 0. *)
Definition cap_root_model : Model :=
  with_creds (mkCreds 0 0 0 0 0 0 []) cap_base.

(** A process that dropped only its effective uid ([setresuid(-1, 1000,
    -1)] from root): the permitted set stays non-empty, the effective set
    is empty. *)
Definition cap_dropped_model : Model :=
  with_creds (mkCreds 0 1000 0 0 0 0 []) cap_base.

(** A non-empty inheritable set: CAP_NET_BIND_SERVICE (10) in the low
    half and CAP_SYSLOG (34) in the high half, so [kdata[0].inheritable]
    is 0x400 and [kdata[1].inheritable] is 4. *)
Definition cap_inh : Z := 0x400000400.

(** The ordinary user holding [cap_inh]; the same user holding
    CAP_NET_BIND_SERVICE alone; and the same user holding a launch word
    with every bit set, bits 41 to 63 included, which name no
    capability. *)
Definition cap_inh_model : Model :=
  with_cap_inheritable (Z_to_bv 64 cap_inh) cap_user_model.
Definition cap_inh_low_model : Model :=
  with_cap_inheritable (Z_to_bv 64 0x400) cap_user_model.
Definition cap_allbits_model : Model :=
  with_cap_inheritable (Z_to_bv 64 (2 ^ 64 - 1)) cap_user_model.

Definition cap_ledger2 : list (word * nat) :=
  [(cap_header, 4%nat); (Z_to_bv 64 4100, 4%nat)].

Definition cap_ledger3 : list (word * nat) :=
  [(cap_header, 4%nat); (Z_to_bv 64 4100, 4%nat); (cap_dataptr, 24%nat)].

(** A data image from its six [__u32]s, in kernel order. *)
Definition cap_image (elo plo ilo ehi phi ihi : Z) : list byte :=
  Z_to_le_bytes 4 elo ++ Z_to_le_bytes 4 plo ++ Z_to_le_bytes 4 ilo
  ++ Z_to_le_bytes 4 ehi ++ Z_to_le_bytes 4 phi ++ Z_to_le_bytes 4 ihi.

Definition cap_get (m : Model) (bs : list byte) : check_result :=
  check_syscall (capget_input LINUX_CAPABILITY_VERSION_3 cap_dataptr)
    (mkEffectU 0 [(cap_dataptr, bs)] [] [] [] cap_ledger2) m.

(** PAIRED TEST, capget, the case.  Version 3 and pid 0 as uid 1000: the
    call writes 24 bytes whose effective and permitted words are all 0
    and whose inheritable words are the held set, here 0, and the model
    is unchanged.  The old model had no arm for 90 and answered
    [CheckUnmodeled].  A claim of any effective capability for this
    caller is a kernel the model refuses. *)
Example capget_v3_pid0_as_uid_1000_reports_no_capability :
  cap_get cap_user_model (cap_image 0 0 0 0 0 0) = CheckOk cap_user_model []
  /\ cap_get cap_user_model (cap_image 1 0 0 0 0 0) = CheckReject
  /\ cap_get cap_user_model (cap_image 0 0 0 0 1 0) = CheckReject.
Proof. split; [check_eq|split; vm_compute; reflexivity]. Qed.

(** PAIRED TEST, capget, the control.  Version 1 ([0x19980330]) is
    declined by the new arm, as it was by the old model. *)
Example capget_v1_declined :
  check_syscall (capget_input 0x19980330 cap_dataptr)
    (mkEffectU 0 [(cap_dataptr, Z_to_le_bytes 12 0)] [] [] []
       [(cap_header, 4%nat); (Z_to_bv 64 4100, 4%nat)])
    cap_user_model = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** PAIRED TEST, capget from a caller with a uid 0, the case.  Root,
    and a caller that dropped only its effective uid, are DECLINED at
    the copy-out: their permitted set is [cap_bset | cap_inheritable],
    and the model assumes of the bounding set only that it holds
    CAP_SETUID and CAP_SETGID ([State.creds_privileged]).  The arm before
    that narrowing accepted the first and third images below (every
    capability 0..40 in the derived sets), which a container's bounding
    set makes false; no image is accepted now. *)
Example capget_with_a_uid_0_declined :
  cap_get cap_root_model (cap_image 0xffffffff 0xffffffff 0 0x1ff 0x1ff 0)
    = CheckUnmodeled
  /\ cap_get cap_root_model (cap_image 0 0 0 0 0 0) = CheckUnmodeled
  /\ cap_get cap_dropped_model (cap_image 0 0xffffffff 0 0 0x1ff 0)
       = CheckUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ...and its CONTROLS, which the arm before the narrowing passed too.
    The gates before the copy-out do not read the sets, so root still
    gets the NULL-[dataptr] 0 and the -EFAULT of a [dataptr] that
    [access_ok] refuses; and a caller with no uid 0 still gets its empty
    sets ([capget_v3_pid0_as_uid_1000_reports_no_capability]). *)
Example capget_with_a_uid_0_gates_still_answered :
  check_syscall (capget_input LINUX_CAPABILITY_VERSION_3 0)
    (mkEffectU 0 [] [] [] [] [(cap_header, 4%nat)]) cap_root_model
    = CheckOk cap_root_model []
  /\ check_syscall (capget_input LINUX_CAPABILITY_VERSION_3 (Z_to_bv 64 (2 ^ 64 - 8)))
       (mkEffectU (errno_ret EFAULT) [] [] [] [] cap_ledger2) cap_root_model
       = CheckOk cap_root_model [].
Proof. split; check_eq. Qed.

(** PAIRED TEST, INHERITABLE, capget, the case.  A caller holding
    [cap_inh] gets that set back, 0x400 then 4.  The text that let the
    environment choose the inheritable words accepted all three images
    below; the held set accepts the first alone. *)
Example capget_reports_the_held_inheritable_set :
  cap_get cap_inh_model (cap_image 0 0 0x400 0 0 4) = CheckOk cap_inh_model []
  /\ cap_get cap_inh_model (cap_image 0 0 0 0 0 0) = CheckReject
  /\ cap_get cap_user_model (cap_image 0 0 0x400 0 0 4) = CheckReject.
Proof. split; [check_eq|split; vm_compute; reflexivity]. Qed.

(** ...and its CONTROL, answered alike by both texts: the effective and
    permitted words of this caller are still 0, so an image that claims
    an effective or a permitted capability is refused, and a caller with
    a uid 0 is still declined at the copy-out whatever set it holds. *)
Example capget_effective_and_permitted_words_unchanged :
  cap_get cap_inh_model (cap_image 1 0 0x400 0 0 4) = CheckReject
  /\ cap_get cap_inh_model (cap_image 0 0x400 0x400 0 0 4) = CheckReject
  /\ cap_get cap_inh_model (cap_image 0 0 0x400 0 4 4) = CheckReject
  /\ cap_get (with_cap_inheritable (Z_to_bv 64 cap_inh) cap_root_model)
       (cap_image 0 0 0x400 0 0 4) = CheckUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** A held word with bits above [CAP_LAST_CAP] is read through
    [CAP_VALID_MASK]: any low word, a high word of caps 32 to 40, and
    nothing above.  A control: the text that chose the words bounded the
    high word the same way. *)
Example capget_reads_the_held_set_within_the_valid_bits :
  cap_get cap_allbits_model (cap_image 0 0 0xffffffff 0 0 0x1ff)
    = CheckOk cap_allbits_model []
  /\ cap_get cap_allbits_model (cap_image 0 0 0xffffffff 0 0 0xffffffff)
    = CheckReject.
Proof. split; [check_eq|vm_compute; reflexivity]. Qed.

(** [setresuid] leaves the inheritable set: root holding [cap_inh]
    moves all three uids to 1000, and capget then reports [cap_inh]
    ([cap_emulate_setxuid] clears the permitted and effective sets, not
    the inheritable one).  The text that chose the words also accepted
    the second, empty image. *)
Example setresuid_keeps_the_inheritable_set :
  match check_syscall (mkInput 147 [1000; 1000; 1000; 0; 0; 0]
                         (fun _ => None) (fun _ => None))
          (mkEffect 0 [] []) (with_cap_inheritable (Z_to_bv 64 cap_inh) cap_root_model) with
  | CheckOk m' _ =>
      cap_get m' (cap_image 0 0 0x400 0 0 4) = CheckOk m' []
      /\ cap_get m' (cap_image 0 0 0 0 0 0) = CheckReject
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** A NULL [dataptr] with version 3 answers 0 after reading the version
    alone; the pid is never read, so the ledger holds one range. *)
Example capget_null_dataptr_reads_the_version_only :
  check_syscall (capget_input LINUX_CAPABILITY_VERSION_3 0)
    (mkEffectU 0 [] [] [] [] [(cap_header, 4%nat)]) cap_user_model
    = CheckOk cap_user_model []
  /\ check_syscall (capget_input LINUX_CAPABILITY_VERSION_3 0)
       (mkEffectU 0 [] [] [] [] cap_ledger2) cap_user_model = CheckReject.
Proof. split; [check_eq|vm_compute; reflexivity]. Qed.

(** An unwritable [dataptr] that [access_ok] admits is the partial copy
    the arm declines; one [access_ok] refuses is -EFAULT after both
    header reads. *)
Example capget_destination_faults :
  check_syscall (capget_input LINUX_CAPABILITY_VERSION_3 (Z_to_bv 64 0x10000))
    (mkEffectU (errno_ret EFAULT) [] [] [] [] cap_ledger2) cap_user_model
    = CheckUnmodeled
  /\ check_syscall (capget_input LINUX_CAPABILITY_VERSION_3 (Z_to_bv 64 (2 ^ 64 - 8)))
       (mkEffectU (errno_ret EFAULT) [] [] [] [] cap_ledger2) cap_user_model
       = CheckOk cap_user_model [].
Proof. split; [vm_compute; reflexivity|check_eq]. Qed.

(** PAIRED TEST, capset, the case.  All six words 0, version 3, pid 0,
    from uid 1000: 0, or -ENOMEM from [prepare_creds], with the three
    reads on the ledger.  The new inheritable set is 0, the set this
    caller already holds, so the model is unchanged.  The old model had
    no arm for 91 and answered [CheckUnmodeled]. *)
Example capset_all_zero_as_uid_1000 :
  check_syscall (capset_input (Z_to_le_bytes 24 0))
    (mkEffectU 0 [] [] [] [] cap_ledger3) cap_user_model
    = CheckOk cap_user_model []
  /\ check_syscall (capset_input (Z_to_le_bytes 24 0))
       (mkEffectU (errno_ret ENOMEM) [] [] [] [] cap_ledger3) cap_user_model
       = CheckOk cap_user_model []
  /\ check_syscall (capset_input (Z_to_le_bytes 24 0))
       (mkEffectU (errno_ret EPERM) [] [] [] [] cap_ledger3) cap_user_model
       = CheckReject.
Proof. split; [check_eq|split; [check_eq|vm_compute; reflexivity]]. Qed.

(** PAIRED TEST, capset, the control.  The same call from root would
    DROP its non-empty permitted set, which the model's euid-based
    privilege cannot follow: declined, as the old model declined every
    91.  So is the same call from a caller that keeps uid 0 as its real
    and saved ids, a non-zero effective or permitted word from anyone,
    and an inheritable set from root.  The text that declined every
    non-zero data word declines these too. *)
Example capset_from_root_declined :
  check_syscall (capset_input (Z_to_le_bytes 24 0))
    (mkEffectU 0 [] [] [] [] cap_ledger3) cap_root_model = CheckUnmodeled
  /\ check_syscall (capset_input (Z_to_le_bytes 24 0))
       (mkEffectU 0 [] [] [] [] cap_ledger3) cap_dropped_model = CheckUnmodeled
  /\ check_syscall (capset_input (cap_image 0 1 0 0 0 0))
       (mkEffectU 0 [] [] [] [] cap_ledger3) cap_user_model = CheckUnmodeled
  /\ check_syscall (capset_input (cap_image 1 0 0 0 0 0))
       (mkEffectU (errno_ret EPERM) [] [] [] [] cap_ledger3) cap_user_model
       = CheckUnmodeled
  /\ check_syscall (capset_input (cap_image 0 0 0x400 0 0 0))
       (mkEffectU 0 [] [] [] [] cap_ledger3)
       (with_cap_inheritable (Z_to_bv 64 cap_inh) cap_root_model) = CheckUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** PAIRED TEST, INHERITABLE, capset, the case.  From [cap_inh], a new
    inheritable set of CAP_NET_BIND_SERVICE alone is inside the held
    set, so [cap_capset] allows it: 0 with the new set held, or -ENOMEM
    with the model unchanged; -EPERM is refused.  A high word of 0x200
    names bit 41, which [mk_kernel_cap] masks away: from uid 1000 with an
    empty set that is the empty set, allowed.  The text that declined
    every non-zero data word declined all of these. *)
Example capset_installs_an_allowed_inheritable_set :
  check_syscall (capset_input (cap_image 0 0 0x400 0 0 0))
    (mkEffectU 0 [] [] [] [] cap_ledger3) cap_inh_model
    = CheckOk cap_inh_low_model []
  /\ check_syscall (capset_input (cap_image 0 0 0x400 0 0 0))
       (mkEffectU (errno_ret ENOMEM) [] [] [] [] cap_ledger3) cap_inh_model
       = CheckOk cap_inh_model []
  /\ check_syscall (capset_input (cap_image 0 0 0x400 0 0 0))
       (mkEffectU (errno_ret EPERM) [] [] [] [] cap_ledger3) cap_inh_model
       = CheckReject
  /\ check_syscall (capset_input (cap_image 0 0 0 0 0 0x200))
       (mkEffectU 0 [] [] [] [] cap_ledger3) cap_user_model
       = CheckOk cap_user_model [].
Proof.
  split; [check_eq|split; [check_eq|split; [vm_compute; reflexivity|check_eq]]].
Qed.

(** ...and a later capget reads the installed set back: CAP_NET_BIND_SERVICE
    in the low word, nothing in the high word. *)
Example capget_after_capset_reads_the_installed_set :
  match check_syscall (capset_input (cap_image 0 0 0x400 0 0 0))
          (mkEffectU 0 [] [] [] [] cap_ledger3) cap_inh_model with
  | CheckOk m' _ =>
      cap_get m' (cap_image 0 0 0x400 0 0 0) = CheckOk m' []
      /\ cap_get m' (cap_image 0 0 0x400 0 0 4) = CheckReject
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** PAIRED TEST, INHERITABLE, capset, the case.  A new inheritable set
    with a bit outside the held one fails [cap_capset]'s first test, for
    this caller has no CAP_SETPCAP: -EPERM or -ENOMEM, the model
    unchanged, and 0 refused.  From uid 1000 with an empty set, CAP_CHOWN
    (0); from [cap_inh], CAP_CHOWN beside the held capabilities.  The text
    that declined every non-zero data word declined both.  The controls,
    answered alike by both texts, are [capset_all_zero_as_uid_1000] and
    [capset_from_root_declined]. *)
Example capset_outside_the_held_set_is_eperm :
  check_syscall (capset_input (cap_image 0 0 1 0 0 0))
    (mkEffectU (errno_ret EPERM) [] [] [] [] cap_ledger3) cap_user_model
    = CheckOk cap_user_model []
  /\ check_syscall (capset_input (cap_image 0 0 1 0 0 0))
       (mkEffectU 0 [] [] [] [] cap_ledger3) cap_user_model = CheckReject
  /\ check_syscall (capset_input (cap_image 0 0 0x401 0 0 4))
       (mkEffectU (errno_ret EPERM) [] [] [] [] cap_ledger3) cap_inh_model
       = CheckOk cap_inh_model []
  /\ check_syscall (capset_input (cap_image 0 0 0x401 0 0 4))
       (mkEffectU (errno_ret ENOMEM) [] [] [] [] cap_ledger3) cap_inh_model
       = CheckOk cap_inh_model []
  /\ check_syscall (capset_input (cap_image 0 0 0x401 0 0 4))
       (mkEffectU 0 [] [] [] [] cap_ledger3) cap_inh_model = CheckReject.
Proof.
  split; [check_eq|split; [vm_compute; reflexivity|
    split; [check_eq|split; [check_eq|vm_compute; reflexivity]]]].
Qed.
