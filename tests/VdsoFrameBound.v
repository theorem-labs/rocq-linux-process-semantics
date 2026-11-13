(** * VdsoFrameBound — a vDSO call writes at most its frame of F bytes,
      all of them below the caller's sp.

    [Run.vdso_post] answers a call to an exported vDSO entry with the
    launch's draw ([StackLayout.ed_vdso]): the draw's [vl_frame] bytes go
    into [[sp - F, sp)], where F is the chosen image's measured frame
    ([Vdso.vi_frame], 240 bytes for the image in the list).  A draw is any
    function, so nothing bounds the length of the list it gives back.
    The measured image's functions write no memory but their own frame
    below sp and the buffers their arguments point at
    (measure/MEASUREMENT.md, "The callee-saved registers and the memory
    writes"; SCOPE.md, "A vDSO function keeps the callee-saved registers
    and [sp]").  So the model may write at most F bytes, from [sp - F] up to
    [sp - 1], and, for an sp of at least F such as this file's, never a
    byte at or above sp, where the caller keeps its own saved registers
    and return address.

    This file applies [vdso_post] once, with a draw whose frame is F + 64
    bytes long, to a state whose memory is writable zeros on
    [[sp - 512, sp + 512)], and reads the memory after it:

    - [vdso_post_leaves_sp_and_above]: no byte of [[sp, sp + 512)]
      changed.  Before the bound, the 64 bytes past F landed on
      [[sp, sp + 64)], so this Example was false.
    - [vdso_post_leaves_below_the_frame]: no byte of
      [[sp - 512, sp - F)] changed.
    - [vdso_post_writes_the_whole_frame]: every byte of [[sp - F, sp)] is
      the draw's, so the bound is F and not less.

    [vf_mapped_around_sp] shows the first two are not vacuous: every byte
    they read was mapped and writable before the call, so a write there
    would have landed. *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel Require Vdso.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(** The model of [Checks.Cases.Kernel.Vdso]'s fixture launch.  [vdso_post]
    reads only its [m_vdso], which [vf_model] below replaces. *)
Module KV := LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Vdso.

(* =========================================================================
   The call
   ========================================================================= *)

(** F: the measured image's frame, the one the step relation uses for a
    run of that image ([RiscvSemantics.vdso_frame]). *)
Definition vf_F : N := vi_frame vdso_image_default.

Example vf_F_is_the_measured_frame : vf_F = 240%N.
Proof. vm_compute. reflexivity. Qed.

Definition vf_sp_z : Z := 0x7ffffffffdf0.
Definition vf_sp : word := Z_to_bv 64 vf_sp_z.

(** How far on each side of sp the fixture's memory is mapped. *)
Definition vf_span : Z := 512.

(** The draw: a frame of F + 64 bytes, each 0xaa, and the registers as
    they were. *)
Definition vf_draw : VdsoDraw :=
  fun _ regs _ _ =>
    mkVdsoLeftovers regs (repeat (Z_to_bv 8 0xaa) (N.to_nat vf_F + 64)%nat).

Example vf_draw_is_longer_than_F :
  length (vl_frame (vf_draw 0%N [] [] (Z_to_bv 64 0)))
  = (N.to_nat vf_F + 64)%nat.
Proof. vm_compute. reflexivity. Qed.

(** Writable zeros on [[sp - 512, sp + 512)], nothing else. *)
Definition vf_ms : machine_state :=
  {| ms_regs := bvmap_set 2 vf_sp bvmap_empty;
     ms_fregs := bvmap_empty;
     ms_pc_val := Z_to_bv 64 0;
     ms_svc_pending := None;
     ms_resv := None;
     ms_fcsr := Z_to_bv 32 0;
     ms_mem := fun a =>
       if ((vf_sp_z - vf_span <=? bv_unsigned a)
           && (bv_unsigned a <? vf_sp_z + vf_span))%Z
       then Some (Z_to_bv 8 0) else None;
     ms_rom := fun _ => None |}.

Definition vf_model : Model :=
  with_vdso (mkVdsoRun vf_draw 0%N) KV.fx_model0.

(** The system call's own effect: a0 = 0, no bytes written. *)
Definition vf_eff : SyscallEffect := mkEffect (Z_to_bv 64 0) [] [].

Definition vf_after : machine_state :=
  vdso_post [] vf_ms vf_model vf_F vf_eff.

(* =========================================================================
   Reading the memory
   ========================================================================= *)

(** The byte at [a], as a number; -1 where nothing is mapped. *)
Definition byte_z (ms : machine_state) (a : Z) : Z :=
  match ms_mem ms (Z_to_bv 64 a) with
  | Some b => bv_unsigned b
  | None => -1
  end.

(** [p] holds at each of the [n] addresses from [lo] up. *)
Definition all_from (lo n : Z) (p : Z -> bool) : bool :=
  forallb (fun i => p (lo + Z.of_nat i)) (seq 0 (Z.to_nat n)).

(** Each of the [n] bytes from [lo] up is the same in [after] as in
    [before].  The two states are arguments, so each is computed once. *)
Definition unchanged (before after : machine_state) (lo n : Z) : bool :=
  all_from lo n (fun a => Z.eqb (byte_z after a) (byte_z before a)).

(** Each of the [n] bytes from [lo] up is [v] in [ms]. *)
Definition all_are (ms : machine_state) (lo n v : Z) : bool :=
  all_from lo n (fun a => Z.eqb (byte_z ms a) v).

(* =========================================================================
   The bound
   ========================================================================= *)

(** Before the call every byte the Examples below read is a mapped,
    writable zero, so a write to any of them would have landed. *)
Example vf_mapped_around_sp :
  all_are vf_ms (vf_sp_z - vf_span) (2 * vf_span) 0 = true.
Proof. vm_compute. reflexivity. Qed.

(** THE BOUND.  Nothing at or above sp changed. *)
Example vdso_post_leaves_sp_and_above :
  unchanged vf_ms vf_after vf_sp_z vf_span = true.
Proof. vm_compute. reflexivity. Qed.

(** Nothing below the frame changed either. *)
Example vdso_post_leaves_below_the_frame :
  unchanged vf_ms vf_after (vf_sp_z - vf_span) (vf_span - Z.of_N vf_F)
  = true.
Proof. vm_compute. reflexivity. Qed.

(** And the whole frame is the draw's: the bound is F, not less. *)
Example vdso_post_writes_the_whole_frame :
  all_are vf_after (vf_sp_z - Z.of_N vf_F) (Z.of_N vf_F) 0xaa = true.
Proof. vm_compute. reflexivity. Qed.
