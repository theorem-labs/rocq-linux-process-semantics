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
    still decline. *)

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
    -1)] from root): the permitted set stays full, the effective set is
    empty. *)
Definition cap_dropped_model : Model :=
  with_creds (mkCreds 0 1000 0 0 0 0 []) cap_base.

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
    call writes 24 bytes whose effective and permitted words are all 0,
    and the model is unchanged.  The old model had no arm for 90 and
    answered [CheckUnmodeled].  A claim of any effective capability for
    this caller is a kernel the model refuses. *)
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

(** The derivation, for root and for a caller that dropped only its
    effective uid: every capability 0..40 is 0xffffffff in the low word
    and 0x1ff in the high word. *)
Example capget_sets_follow_the_uids :
  cap_get cap_root_model (cap_image 0xffffffff 0xffffffff 0 0x1ff 0x1ff 0)
    = CheckOk cap_root_model []
  /\ cap_get cap_root_model (cap_image 0 0 0 0 0 0) = CheckReject
  /\ cap_get cap_dropped_model (cap_image 0 0xffffffff 0 0 0x1ff 0)
       = CheckOk cap_dropped_model []
  /\ cap_get cap_dropped_model (cap_image 0xffffffff 0xffffffff 0 0x1ff 0x1ff 0)
       = CheckReject.
Proof.
  split; [check_eq|]. split; [vm_compute; reflexivity|].
  split; [check_eq|vm_compute; reflexivity].
Qed.

(** The inheritable set is the environment's, within the valid bits:
    any low word, a high word up to 0x1ff, and nothing above. *)
Example capget_inheritable_is_chosen_within_the_valid_bits :
  cap_get cap_user_model (cap_image 0 0 0xdeadbeef 0 0 0x1ff)
    = CheckOk cap_user_model []
  /\ cap_get cap_user_model (cap_image 0 0 0 0 0 0x200) = CheckReject.
Proof. split; [check_eq|vm_compute; reflexivity]. Qed.

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
    reads on the ledger and the model unchanged.  The old model had no
    arm for 91 and answered [CheckUnmodeled]. *)
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
    DROP the full permitted set, which the model's euid-based privilege
    cannot follow: declined, as the old model declined every 91.  So is
    the same call from a caller that keeps uid 0 as its real and saved
    ids, and any non-zero data word from anyone. *)
Example capset_from_root_declined :
  check_syscall (capset_input (Z_to_le_bytes 24 0))
    (mkEffectU 0 [] [] [] [] cap_ledger3) cap_root_model = CheckUnmodeled
  /\ check_syscall (capset_input (Z_to_le_bytes 24 0))
       (mkEffectU 0 [] [] [] [] cap_ledger3) cap_dropped_model = CheckUnmodeled
  /\ check_syscall (capset_input (cap_image 0 0 1 0 0 0))
       (mkEffectU 0 [] [] [] [] cap_ledger3) cap_user_model = CheckUnmodeled.
Proof. repeat split; vm_compute; reflexivity. Qed.
