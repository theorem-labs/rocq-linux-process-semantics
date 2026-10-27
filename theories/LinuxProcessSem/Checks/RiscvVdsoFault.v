(** * LinuxProcessSem.Checks.RiscvVdsoFault — faults on the vDSO pair

    A fetch or a load that faults on the vDSO pair is [MachineUnmodeled]:
    Linux maps both ranges readable and reads on, with bytes the kernel
    holds and the model does not.  A store there, and an access outside the
    pair, stays [MachineFault] ([Run.mi_fault_reads_vdso]).

    The model is the one a run starts from ([State.init_model]), so the
    pair is where [State.vdso_at] places it: right below the mmap base.
    The base here is the lowest one a run admits, [State.mmap_base_min] =
    0x154555557000, and the geometry is the default one (four vvar pages,
    two text pages), so the pair is

      vvar  [0x154555551000, 0x154555555000)
      text  [0x154555555000, 0x154555557000)

    The image is two instructions at 0x100, both addressing through x11:

      0x100  ld  x10, 0(x11)   03b50500
      0x104  sd  x12, 0(x11)   23b0c500 *)

From Stdlib Require Import ZArith NArith List String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Import Prelude.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope string_scope.

Definition vdso_code_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 8;
  seg_perms := "r-x";
  seg_bytes := ["03b5050023b0c500"%pstring]
|}.

Definition vdso_segments : list Segment := [vdso_code_segment].

Definition vdso_model : Model :=
  init_model [] 0 (Z_to_bv 64 mmap_base_min) demo_sp demo_limit
    (demo_input [] IEof).

Definition vvar_lo : Z := 0x154555551000.
Definition text_lo : Z := 0x154555555000.
Definition pair_hi : Z := 0x154555557000.

(** The pair is where the header says, both ranges mapped. *)
Example vdso_model_pair :
  m_vdso vdso_model = mkVdsoState vvar_lo 0x4000 0x2000 true true.
Proof. vm_compute. reflexivity. Qed.

(** A state at [pc] with x11 = [addr]; no memory but the image. *)
Definition vdso_state (pc addr : Z) : machine_state := {|
  ms_regs :=
    bvmap_set (Z_to_bv 5 11) (Z_to_bv 64 addr)
      (bvmap_set (Z_to_bv 5 12) (Z_to_bv 64 0x1122334455667788)
        bvmap_empty);
  ms_fregs := bvmap_empty;
  ms_pc_val := Z_to_bv 64 pc;
  ms_svc_pending := None;
  ms_resv := None;
  ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None;
  ms_rom := fun _ => None
|}.

Definition account (st : machine_state)
    : machine_result (machine_state * Model) :=
  mi_account_step vdso_segments st vdso_model.

(** The interpreter faults on the load, and [step_fault_access] names it:
    eight bytes at the address x11 holds. *)
Example vdso_load_step_faults :
  step vdso_segments (vdso_state 0x100 vvar_lo) = MachineFault /\
  step_fault_access vdso_segments (vdso_state 0x100 vvar_lo)
    = Some (AccLoad, (Z_to_bv 64 vvar_lo, 8%nat)).
Proof. split; check_eq. Qed.

(** A load from either range of the pair: unmodeled. *)
Example vdso_load_unmodeled :
  account (vdso_state 0x100 vvar_lo) = MachineUnmodeled /\
  account (vdso_state 0x100 text_lo) = MachineUnmodeled /\
  account (vdso_state 0x100 (pair_hi - 8)) = MachineUnmodeled.
Proof. vm_compute. repeat split. Qed.

(** The same load one page below the pair, and right above it: a fault. *)
Example load_off_pair_faults :
  account (vdso_state 0x100 (vvar_lo - 0x1000)) = MachineFault /\
  account (vdso_state 0x100 pair_hi) = MachineFault.
Proof. vm_compute. repeat split. Qed.

(** A load that meets the pair in part is unmodeled too.  Linux faults on
    this one (its first four bytes are unmapped); the model fails closed
    on the range it cannot read. *)
Example load_into_pair_unmodeled :
  account (vdso_state 0x100 (vvar_lo - 4)) = MachineUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** A store to either range of the pair: a fault, as on Linux, where
    neither range is writable.  [step_fault_access] names the store. *)
Example vdso_store_faults :
  step_fault_access vdso_segments (vdso_state 0x104 vvar_lo)
    = Some (AccStore, (Z_to_bv 64 vvar_lo, 8%nat)) /\
  account (vdso_state 0x104 vvar_lo) = MachineFault /\
  account (vdso_state 0x104 text_lo) = MachineFault.
Proof. split; [check_eq|]. vm_compute. repeat split. Qed.

(** A fetch at a pc in the pair: unmodeled.  [step_fault_access] names
    the first parcel, the only bytes the fetch inspected.  (A fetch from
    the vvar range, which lacks VM_EXEC, faults on Linux; the model fails
    closed there too.) *)
Example vdso_fetch_unmodeled :
  step_fault_access vdso_segments (vdso_state text_lo 0)
    = Some (AccFetch, (Z_to_bv 64 text_lo, 2%nat)) /\
  account (vdso_state text_lo 0) = MachineUnmodeled /\
  account (vdso_state vvar_lo 0) = MachineUnmodeled.
Proof. split; [check_eq|]. vm_compute. repeat split. Qed.

(** The same fetch one page below the pair: a fault. *)
Example fetch_below_pair_faults :
  account (vdso_state (vvar_lo - 0x1000) 0) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** What it buys: a run that loads from the pair reaches a configuration
    the model does not cover, so [Equivalence.modeled] fails for it and
    its error cannot carry [Equivalence.equiv]'s all-errors escape.  The
    load below the pair is a genuine fault, and covered. *)
Example vdso_load_reaches_unmodeled :
  reaches_unmodeled vdso_segments (mkCfg (vdso_state 0x100 vvar_lo) vdso_model).
Proof.
  apply reaches_unmodeled_intro; [reflexivity | reflexivity |].
  vm_compute. reflexivity.
Qed.

Example load_below_pair_covered :
  ~ unmodeled_at vdso_segments
      (mkCfg (vdso_state 0x100 (vvar_lo - 0x1000)) vdso_model).
Proof.
  intros (_ & [(_ & H) | (x8 & Hsvc & _)]).
  - vm_compute in H. discriminate H.
  - cbn in Hsvc. discriminate Hsvc.
Qed.
