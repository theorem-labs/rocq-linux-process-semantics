(** * Examples.forkwait.Measure — the measure that closes the pathfinder

    [MustExitP.must_exit_in_p_at_by_measure] takes the measure as a
    parameter: every step, whichever entry takes it, must make it go down.
    This file supplies the one for [forkwait], and it is the whole reason the
    schedule never has to be enumerated.

    THE COUNT IS PER ENTRY AND THE SYSTEM'S MEASURE IS THE SUM, through
    [MustExitP.pmeasure].  Since every step belongs to exactly one entry, the
    sum falls by that entry's own decrease and nothing else moves.

    IT IS AN OVER-ESTIMATE, DELIBERATELY.  The measure has to DECREASE, not
    to be exact, and that is what makes a table on the program counter
    possible at all: at [0x1101c] and [0x11020] the parent and the child
    share a program counter but have very different amounts left to do (15
    against 6), so an exact count would need to look at a0.  Taking the
    larger at each shared address is sound and needs nothing but the pc.

    IT DEPENDS ON [ms_svc_pending] AS WELL AS THE PC, and that is not an
    optimisation either.  [RiscvSemantics.step] executes the [ecall] WORD
    ITSELF as an ordinary instruction: it leaves the pc alone and sets
    [ms_svc_pending].  So the state before the fetch and the state after it
    share a program counter and must not share a count, or the fetch would
    not decrease the measure.  [fw_at] is the count with no call pending and
    [fw_pending] is the count with one pending; the second is always the
    first less one.

    THE TWO INTERESTING ENTRIES IN THE TABLE:

    [0x11018], the [clone].  Its resolution does not replace one entry, it
    ADDS one, so the sum jumps to two copies of [fw_at 0x1101c] = 15 + 15 =
    30.  For that to be a decrease the pending count there must exceed 30,
    which is why it is 31 and why everything before it is thirty-something
    rather than single digits.  A measure that forgot the child would be off
    by the whole of the child's run and would fail exactly at the step the
    pathfinder exists to take.

    [0x1103c], the blocking [wait4].  Its step reaps: the parent moves to
    [0x11040] (5) and the zombie LEAVES the table (0).  Pending count 6 falls
    to 5.  The blocked parent itself needs no entry of its own kind, because
    a blocked entry simply has no arm and so contributes no successor. *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics State Run Procs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExitP.
Import ListNotations.
Open Scope bv_scope.

(** Steps remaining with NO system call pending, by program counter.
    Addresses are the ones in the committed snapshot; the disassembly is in
    [source/forkwait.S] and every one of these is an instruction boundary. *)
Definition fw_at (pc : Z) : nat :=
  match pc with
  (* the straight run into the clone: thirty-something because the count
     has to cover the child's run as well, see the header *)
  | 0x11000%Z => 38  (* li a0, 17   -- SIGCHLD *)
  | 0x11004%Z => 37  (* li a1, 0    -- newsp *)
  | 0x11008%Z => 36  (* li a2, 0    -- parent_tidptr *)
  | 0x1100c%Z => 35  (* li a3, 0    -- tls *)
  | 0x11010%Z => 34  (* li a4, 0    -- child_tidptr *)
  | 0x11014%Z => 33  (* li a7, 220 *)
  | 0x11018%Z => 32  (* ecall       -- clone *)
  (* shared by parent and child: the larger of the two, see the header *)
  | 0x1101c%Z => 15  (* bltz a0, fail *)
  | 0x11020%Z => 14  (* beqz a0, child *)
  (* the parent *)
  | 0x11024%Z => 13  (* addi sp, sp, -16 *)
  | 0x11028%Z => 12  (* li a0, -1 *)
  | 0x1102c%Z => 11  (* mv a1, sp *)
  | 0x11030%Z => 10  (* li a2, 0    -- options = 0, blocking *)
  | 0x11034%Z => 9   (* li a3, 0    -- rusage = NULL *)
  | 0x11038%Z => 8   (* li a7, 260 *)
  | 0x1103c%Z => 7   (* ecall       -- wait4; the reap is the extra step *)
  | 0x11040%Z => 5   (* lw a0, 0(sp) *)
  | 0x11044%Z => 4   (* srli a0, a0, 8 *)
  | 0x11048%Z => 3   (* li a7, 94 *)
  | 0x1104c%Z => 2   (* ecall       -- exit_group *)
  (* the child *)
  | 0x11050%Z => 4   (* li a0, 7 *)
  | 0x11054%Z => 3   (* li a7, 94 *)
  | 0x11058%Z => 2   (* ecall       -- exit_group *)
  (* the clone-failed arm, unreachable at forced_only_cfg *)
  | 0x1105c%Z => 4   (* li a0, 7 *)
  | 0x11060%Z => 3   (* li a7, 94 *)
  | 0x11064%Z => 2   (* ecall       -- exit_group *)
  | _ => 0%nat
  end.

(** And with one pending: the fetch has happened, so one step fewer. *)
Definition fw_pending (pc : Z) : nat :=
  match fw_at pc with
  | O => 0%nat
  | S k => k
  end.

Lemma fw_pending_lt : forall pc,
  (0 < fw_at pc)%nat -> (fw_pending pc < fw_at pc)%nat.
Proof.
  intros pc H. unfold fw_pending. destruct (fw_at pc); [inversion H | auto].
Qed.

(** The per-entry count.  A zombie is worth nothing: it cannot step, and a
    reap drops it, so charging it would make the reap fail to decrease. *)
Definition fw_entry (e : ProcessEntry) : nat :=
  match pe_zombie e with
  | Some _ => 0%nat
  | None =>
      match ms_svc_pending (pe_ms e) with
      | None => fw_at (bv_unsigned (ms_pc_val (pe_ms e)))
      | Some _ => fw_pending (bv_unsigned (ms_pc_val (pe_ms e)))
      end
  end.

(** The system's measure. *)
Definition fw_measure (P : pconfig) : nat := pmeasure fw_entry P.

(** The clone is the step the table is shaped around: it ADDS an entry, so
    the pending count at the [ecall] has to exceed what BOTH entries are
    worth afterwards.  31 against 15 + 15. *)
Lemma fw_clone_decreases :
  (fw_at 0x1101c%Z + fw_at 0x1101c%Z < fw_pending 0x11018%Z)%nat.
Proof. cbn. lia. Qed.

(** And the reap: the parent falls from 6 to 5 and the zombie, worth 0,
    leaves the table. *)
Lemma fw_reap_decreases :
  (fw_at 0x11040%Z + 0 < fw_pending 0x1103c%Z)%nat.
Proof. cbn. lia. Qed.
