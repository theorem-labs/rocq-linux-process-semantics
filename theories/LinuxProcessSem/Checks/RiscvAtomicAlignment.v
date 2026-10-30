(** * LinuxProcessSem.Checks.RiscvAtomicAlignment — misaligned atomics fault

    Regression checks for the A-extension alignment gate in [Sem.exec]:
    lr/sc/amo at an address that is not naturally aligned to the operand
    width (4 for .w, 8 for .d) is [Sem.EFault], which [interp_eff] turns
    into [MachineFault] — the SIGBUS the real process takes.  Plain
    loads and stores are deliberately NOT gated (the model permits
    misaligned ones, as the emulated hart and Linux on real hardware
    do), so these checks pin the split.

    Anti-vacuity: every misaligned case below differs from a green
    aligned twin ONLY in the low bits of the address register, and the
    data window is readable and writable at both addresses — so only
    the alignment gate can make the misaligned one fault. *)

From Stdlib Require Import ZArith NArith List String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope string_scope.

(** Six atomics, one per instruction word, all using x11 as the address
    and x12 as the source, rd = x10:

      0x100  lr.w     x10, (x11)        2fa50510
      0x104  lr.d     x10, (x11)        2fb50510
      0x108  sc.w     x10, x12, (x11)   2fa5c518
      0x10c  sc.d     x10, x12, (x11)   2fb5c518
      0x110  amoadd.w x10, x12, (x11)   2fa5c500
      0x114  amoadd.d x10, x12, (x11)   2fb5c500 *)
Definition atomic_code_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 24;
  seg_perms := "r-x";
  seg_bytes := ["2fa505102fb505102fa5c5182fb5c5182fa5c5002fb5c500"%pstring]
|}.

Definition atomic_segments : list Segment := [atomic_code_segment].

(** A 32-byte writable data window at [0x200], present in the overlay:
    [ov_read_bytes] answers loads from it and [store_ok] accepts stores
    into it, so an atomic aimed anywhere inside is otherwise fully
    executable. *)
Definition atomic_data (a : word) : option byte :=
  if andb (Z.leb 0x200 (bv_unsigned a)) (Z.ltb (bv_unsigned a) 0x220)
  then Some (Z_to_bv 8 0x5a) else None.

Definition atomic_state (pc : word) (addr : Z) (resv : option word)
    : machine_state := {|
  ms_regs := bvmap_set (Z_to_bv 5 11) (Z_to_bv 64 addr)
               (bvmap_set (Z_to_bv 5 12) (Z_to_bv 64 0x1122334455667788)
                  bvmap_empty);
  ms_fregs := bvmap_empty;
  ms_pc_val := pc;
  ms_svc_pending := None;
  ms_resv := resv; ms_fcsr := Z_to_bv 32 0;
  ms_mem := atomic_data;
  ms_rom := fun _ => None
|}.

Definition pc_lr_w : word := Z_to_bv 64 0x100.
Definition pc_lr_d : word := Z_to_bv 64 0x104.
Definition pc_sc_w : word := Z_to_bv 64 0x108.
Definition pc_sc_d : word := Z_to_bv 64 0x10c.
Definition pc_amo_w : word := Z_to_bv 64 0x110.
Definition pc_amo_d : word := Z_to_bv 64 0x114.

Definition steps_ok (st : machine_state) : Prop :=
  match step atomic_segments st with MachineOk _ => True | _ => False end.

(** *** lr: the aligned twin retires, every misaligned residue faults. *)

Example lr_w_aligned : steps_ok (atomic_state pc_lr_w 0x204 None).
Proof. vm_compute. exact I. Qed.

Example lr_w_mod_2 :
  step atomic_segments (atomic_state pc_lr_w 0x206 None) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Example lr_w_mod_1 :
  step atomic_segments (atomic_state pc_lr_w 0x205 None) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Example lr_d_aligned : steps_ok (atomic_state pc_lr_d 0x200 None).
Proof. vm_compute. exact I. Qed.

(** 4 mod 8: aligned for lr.w (green above), misaligned for lr.d. *)
Example lr_d_mod_4 :
  step atomic_segments (atomic_state pc_lr_d 0x204 None) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** *** amo: same split, and the aligned twin's store retires. *)

Example amo_w_aligned : steps_ok (atomic_state pc_amo_w 0x204 None).
Proof. vm_compute. exact I. Qed.

Example amo_w_mod_2 :
  step atomic_segments (atomic_state pc_amo_w 0x206 None) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Example amo_d_aligned : steps_ok (atomic_state pc_amo_d 0x200 None).
Proof. vm_compute. exact I. Qed.

Example amo_d_mod_4 :
  step atomic_segments (atomic_state pc_amo_d 0x204 None) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** *** sc: the alignment check runs BEFORE the reservation check.

    A misaligned sc faults even with NO live reservation — without the
    gate (or with it placed after the reservation test) this case would
    retire cleanly with rd = 1, since the failing arm's permission check
    is an ordinary load and store and those may be misaligned.  With a
    live matching reservation the aligned twin stores and retires. *)

Example sc_w_aligned_success :
  steps_ok (atomic_state pc_sc_w 0x204 (Some (Z_to_bv 64 0x204))).
Proof. vm_compute. exact I. Qed.

Example sc_w_aligned_fail_retires :
  steps_ok (atomic_state pc_sc_w 0x204 None).
Proof. vm_compute. exact I. Qed.

Example sc_w_mod_2_no_resv :
  step atomic_segments (atomic_state pc_sc_w 0x206 None) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Example sc_w_mod_2_live_resv :
  step atomic_segments
    (atomic_state pc_sc_w 0x206 (Some (Z_to_bv 64 0x206))) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Example sc_d_aligned_success :
  steps_ok (atomic_state pc_sc_d 0x200 (Some (Z_to_bv 64 0x200))).
Proof. vm_compute. exact I. Qed.

(** 4 mod 8 with a matching reservation: only the width's own alignment
    can be what faults here. *)
Example sc_d_mod_4_live_resv :
  step atomic_segments
    (atomic_state pc_sc_d 0x204 (Some (Z_to_bv 64 0x204))) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** *** sc: a FAILING sc still passes the store permission check
    ([Sem.exec]'s [Sc] arm).  On memory the process may write it retires
    with rd = 1 and every byte reads as before.  On the read-only code
    segment at [0x100], which is readable and naturally aligned for
    both widths, it faults on the store check; on an unmapped address it
    faults too. *)
Example sc_fail_retires_and_keeps_memory :
  match step atomic_segments (atomic_state pc_sc_w 0x204 None) with
  | MachineOk ms' =>
      bv_unsigned (ms_gpr ms' 0) = 1%Z
      /\ option_map bv_unsigned (ms_mem ms' (Z_to_bv 64 0x204)) = Some 0x5a%Z
      /\ option_map bv_unsigned (ms_mem ms' (Z_to_bv 64 0x207)) = Some 0x5a%Z
  | _ => False
  end.
Proof. vm_compute. repeat split. Qed.

Example sc_fail_on_read_only_memory_faults :
  step atomic_segments (atomic_state pc_sc_w 0x100 None) = MachineFault
  /\ step atomic_segments (atomic_state pc_sc_d 0x100 None) = MachineFault
  /\ step atomic_segments
       (atomic_state pc_sc_w 0x100 (Some (Z_to_bv 64 0x104))) = MachineFault.
Proof. vm_compute. repeat split. Qed.

Example sc_fail_on_unmapped_memory_faults :
  step atomic_segments (atomic_state pc_sc_w 0x300 None) = MachineFault
  /\ step atomic_segments (atomic_state pc_sc_d 0x300 None) = MachineFault.
Proof. vm_compute. repeat split. Qed.
