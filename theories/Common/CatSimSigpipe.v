(** * The SIGPIPE death of a write-then-exit program, at the program level

    The four syscall-level Example pairs in [Checks.Cases.Fs.ReadWrite]
    and [Checks.Cases.Net.Socket] pin what ONE write answers when the far
    end has no reader.  This file pins what that does to a WHOLE RUN: a
    concrete program that writes one byte to stdout and then exits 0 is
    killed by signal 13 when its launch has no reader on stdout, and on
    the same launch with a reader it writes its byte and exits 0, as it
    always did.

    Both halves go through [CatSim]'s run-level lemmas -- the kill path
    [cat_kill_omni_run_te] / [cat_kill_obs_iff_te] and the exit path
    [cat_must_exit_with_te] / [cat_obs_iff_te] -- on one [to_wexit]
    derivation of the program, so a change that made the kill
    unreachable, or that let the reader-gone write deliver, breaks
    [w1x_sigpipe_pair] here instead of passing quietly. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.Common Require Import CatSim.
Import ListNotations.
Open Scope bv_scope.

(* ========================================================================= *)
(* The program: [write(1, 0x100, 1)], then [exit(0)].                         *)
(* ========================================================================= *)

(** [addi a7, x0, 64; addi a0, x0, 1; addi a1, x0, 0x100; addi a2, x0, 1;
    ecall] -- [Checks.Omni.wloop_segment]'s write -- then [addi a7, x0, 93;
    addi a0, x0, 0; ecall] -- [Checks.Examples.exit0_segment]'s exit.  The
    byte written is the first byte of the program's own code. *)
Definition w1x_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 32;
  seg_perms := "r-x"%string;
  seg_bytes := ["93080004130510009305001013061000730000009308d0051305000073000000"%pstring]
|}.
Definition w1x_segments : list Segment := [w1x_segment].
Definition w1x_image : Image := mkImage w1x_segments 0x100 demo_phdrs.

(** The byte the write sends: the low byte of [addi a7, x0, 64]. *)
Definition w1x_byte : byte := Z_to_bv 8 0x93.

(** The two launches: [Checks.Examples.demo_input_valid]'s input, with the
    far end of stdout read ([reader = true], which is that input exactly)
    or not ([reader = false]).  Every other field is the same, and in
    particular SIGPIPE's disposition is the default, the last field. *)
Definition w1x_input (reader : bool) : ProcInput :=
  mkProcInput_full [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48 default_urandom []
    default_kernel default_execfn reader true.

(* ========================================================================= *)
(* The derivation: five silent steps, the write, three silent steps, exit.   *)
(* ========================================================================= *)

Definition w1x_ms0 : machine_state :=
  init_machine_state w1x_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_mbase demo_draw (w1x_input true).

(** [n] instruction steps, refusing at a pending syscall: a [Some] answer
    is a run of [CatSim.msteps]. *)
Fixpoint w1x_srun (n : nat) (ms : machine_state) : option machine_state :=
  match n with
  | O => Some ms
  | S n' =>
      match ms_svc_pending ms with
      | Some _ => None
      | None =>
          match RiscvSemantics.step w1x_segments ms with
          | MachineOk ms' => w1x_srun n' ms'
          | MachineFault | MachineUnmodeled => None
          end
      end
  end.

Lemma w1x_srun_msteps : forall n ms ms',
  w1x_srun n ms = Some ms' -> msteps w1x_segments ms ms'.
Proof.
  induction n as [| n IH]; intros ms ms' H; cbn [w1x_srun] in H.
  - injection H as <-. apply mst_refl.
  - destruct (ms_svc_pending ms) eqn:Hs; [discriminate |].
    destruct (RiscvSemantics.step w1x_segments ms) eqn:Hst; try discriminate.
    eapply mst_step; [exact Hs | exact Hst | apply IH; exact H].
Qed.

Definition w1x_at (o : option machine_state) : machine_state :=
  match o with Some ms => ms | None => w1x_ms0 end.

(** On the write's [ecall]. *)
Definition w1x_s5 : machine_state := w1x_at (w1x_srun 5 w1x_ms0).
(** Past it, with the one delivered byte reported in [a0]. *)
Definition w1x_s5' : machine_state :=
  advance_past_svc (set_gpr0 w1x_s5 (len_word (firstn 1 [w1x_byte]))).
(** On the exit's [ecall]. *)
Definition w1x_s8 : machine_state := w1x_at (w1x_srun 3 w1x_s5').

(** These two say the runs succeed WITHOUT reading the resulting state
    back: [vm_compute] of the state itself reads back the initial memory
    under binders, which does not finish.  Only a boolean is computed. *)
Lemma w1x_srun5 : w1x_srun 5 w1x_ms0 = Some w1x_s5.
Proof.
  unfold w1x_s5, w1x_at.
  destruct (w1x_srun 5 w1x_ms0) eqn:E; [reflexivity | exfalso].
  assert (Hb : match w1x_srun 5 w1x_ms0 with Some _ => true | None => false end = true)
    by (vm_compute; reflexivity).
  rewrite E in Hb. discriminate Hb.
Qed.

Lemma w1x_srun8 : w1x_srun 3 w1x_s5' = Some w1x_s8.
Proof.
  unfold w1x_s8, w1x_at.
  destruct (w1x_srun 3 w1x_s5') eqn:E; [reflexivity | exfalso].
  assert (Hb : match w1x_srun 3 w1x_s5' with Some _ => true | None => false end = true)
    by (vm_compute; reflexivity).
  rewrite E in Hb. discriminate Hb.
Qed.

Lemma w1x_svc5 : ms_svc_pending w1x_s5 = Some (Z_to_bv 64 64).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

Lemma w1x_a0 : ms_gpr w1x_s5 0 = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma w1x_read : ms_read_bytes w1x_s5 (ms_gpr w1x_s5 1) (ms_gpr w1x_s5 2) = Some [w1x_byte].
Proof. vm_compute. first [reflexivity | f_equal; f_equal; apply bv_eq; reflexivity]. Qed.

Lemma w1x_access : access_okb (ms_gpr w1x_s5 1) (bv_unsigned (ms_gpr w1x_s5 2)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma w1x_svc8 : ms_svc_pending w1x_s8 = Some (Z_to_bv 64 93).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

Lemma w1x_code : bv_and (ms_gpr w1x_s8 0) (Z_to_bv 64 255) = Z_to_bv 64 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma w1x_te0 : to_wexit w1x_segments w1x_ms0 [[w1x_byte]] (Z_to_bv 64 0).
Proof.
  apply (msteps_to_wexit w1x_segments _ w1x_s5);
    [apply (w1x_srun_msteps 5); exact w1x_srun5 |].
  apply (tw_write w1x_segments w1x_s5 (Z_to_bv 64 64) [w1x_byte] [] (Z_to_bv 64 0));
    [exact w1x_svc5 | vm_compute; reflexivity | exact w1x_a0 | exact w1x_read
    | cbn [length]; lia |].
  intros n Hn1 Hn2. cbn [length] in Hn2.
  assert (n = 1%nat) by lia. subst n.
  change (to_wexit w1x_segments w1x_s5' [] (Z_to_bv 64 0)).
  apply (msteps_to_wexit w1x_segments _ w1x_s8);
    [apply (w1x_srun_msteps 3); exact w1x_srun8 |].
  rewrite <- w1x_code.
  apply (tw_exit w1x_segments w1x_s8 (Z_to_bv 64 93));
    [exact w1x_svc8 | left; vm_compute; reflexivity].
Qed.

(** The same derivation from either launch's initial state.  The machine
    state is built from the whole input, but it reads only the fields the
    two launches share -- the arguments, the environment, the launching
    user, AT_HWCAP, the kernel build and the exec file name -- and
    [w1x_input] is a constructor application, so both spellings reduce to
    the same term whatever [r] is. *)
Lemma w1x_te : forall r,
  to_wexit w1x_segments
    (init_machine_state w1x_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
       demo_mbase demo_draw (w1x_input r))
    [[w1x_byte]] (Z_to_bv 64 0).
Proof. intros r. exact w1x_te0. Qed.

(** The write is the first syscall, and its range passes [access_ok]. *)
Lemma w1x_wfirst : forall r,
  wfirst_ok w1x_segments
    (init_machine_state w1x_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
       demo_mbase demo_draw (w1x_input r)).
Proof.
  intros r. change (wfirst_ok w1x_segments w1x_ms0).
  apply (msteps_wfirst_ok w1x_segments _ w1x_s5);
    [apply (w1x_srun_msteps 5); exact w1x_srun5 |].
  exact (wfo_write w1x_segments w1x_s5 (Z_to_bv 64 64) w1x_svc5 w1x_access).
Qed.

Lemma w1x_modeled : bufs_modeled [[w1x_byte]].
Proof. apply bufs_modeled_single. unfold buf_modeled. vm_compute. discriminate. Qed.

(** SIGPIPE is fatal at the reader-gone launch: the disposition is the
    default and the empty mask leaves signal 13 open. *)
Lemma w1x_fatal : sigpipe_fatal (w1x_input false).
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.

Lemma is_prefix_In : forall {A} (l1 l2 : list A) x,
  is_prefix l1 l2 -> In x l1 -> In x l2.
Proof.
  intros A l1. induction l1 as [| a l1 IH]; intros l2 x Hp Hin; [destruct Hin |].
  destruct l2 as [| b l2]; [destruct Hp |]. destruct Hp as [-> Hp].
  destruct Hin as [-> | Hin]; [left; reflexivity | right; exact (IH _ _ Hp Hin)].
Qed.

(** Every event a [CatSim.wpick] delivery emits is a write. *)
Lemma wpick_writes : forall ch bufs full,
  wpick ch bufs full -> forall e, In e full -> exists b, e = WriteEv ch b.
Proof.
  intros ch bufs full H.
  induction H as [| buf bufs n tr Hn1 Hn2 H IH]; intros e Hin; [destruct Hin |].
  apply in_app_iff in Hin as [Hin | Hin]; [| exact (IH e Hin)].
  apply in_map_iff in Hin as (b & <- & _). exists b. reflexivity.
Qed.

(* ========================================================================= *)
(* The pair.                                                                  *)
(* ========================================================================= *)

(** THE SAME PROGRAM ON THE SAME INPUT, WITH AND WITHOUT A READER ON STDOUT.

    No reader: every run of the program halts KILLED by signal 13 at its
    first write ([CatSim.wkill_post]); its one maximal trace is that
    [KillEv], so it dies by a signal ([Equivalence.dies_by_signal]), and
    no trace carries anything else -- the byte never reaches stdout and
    the run never exits.  This is Linux's [anon_pipe_write] (fs/pipe.c)
    for a pipe and [sk_stream_error] (net/core/stream.c) for a socket,
    v6.18.46, commit 1f99e9ab748f: both send SIGPIPE when the far end has
    no reader, and at the default disposition it terminates the process.

    A reader: the same program must exit 0 ([MustExit.must_exit_with]),
    the trace [write 0x93; exit 0] is one of its observations, and it
    never dies by a signal.

    Both launches are VALID inputs, which is what makes the first half
    bite under the ordinary quantifier: [Run.valid_input] says nothing
    of the reader, and it PINS [in_sigpipe_default] to [true]
    ([Run.valid_input_sigpipe_default]), so the SIG_DFL half of the
    [sigpipe_fatal] premise the kill path needs costs a caller nothing;
    the other half is the launch mask, empty here.  Under
    [Run.valid_input_sigpipe_ignored] the disposition is SIG_IGN instead,
    and the reader-gone write would return -EPIPE and the program run on,
    which this pair does not cover. *)
Example w1x_sigpipe_pair : forall lim,
  valid_input (w1x_input false) /\ valid_input (w1x_input true)
  (* no reader: killed by signal 13 *)
  /\ omni_run w1x_image lim demo_entry (w1x_input false)
       (wkill_post (in_fs (w1x_input false)))
  /\ dies_by_signal (run w1x_image lim demo_entry (w1x_input false))
  /\ (forall tr e, bh_traces (run w1x_image lim demo_entry (w1x_input false)) tr ->
        In e tr -> e = KillEv (Z_to_bv 64 SIGPIPE) (in_fs (w1x_input false)))
  (* a reader: the byte, then exit 0 *)
  /\ must_exit_with (Z_to_bv 64 0) w1x_image lim demo_entry (w1x_input true)
  /\ bh_traces (run w1x_image lim demo_entry (w1x_input true))
       [WriteEv (Z_to_bv 64 1) w1x_byte; ExitEv (Z_to_bv 64 0) (in_fs (w1x_input true))]
  /\ ~ dies_by_signal (run w1x_image lim demo_entry (w1x_input true)).
Proof.
  intros lim.
  pose proof (fun tr => cat_kill_obs_iff_te w1x_segments 0x100 demo_phdrs
                (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max)
                demo_draw lim (w1x_input false) [[w1x_byte]] (Z_to_bv 64 0)
                (w1x_te false) ltac:(discriminate) (w1x_wfirst false) eq_refl w1x_fatal tr)
    as Hdead.
  pose proof (fun tr => cat_obs_iff_te w1x_segments 0x100 demo_phdrs
                (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max)
                demo_draw lim (w1x_input true) [[w1x_byte]] (Z_to_bv 64 0)
                (w1x_te true) w1x_modeled (or_intror eq_refl) tr)
    as Hlive.
  cbn [run bh_traces w1x_image demo_entry].
  split; [exact demo_input_valid |].
  split; [exact demo_input_valid |].
  split.
  { exact (cat_kill_omni_run_te w1x_segments 0x100 demo_phdrs
             (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max)
             demo_draw lim (w1x_input false) [[w1x_byte]] (Z_to_bv 64 0)
             (w1x_te false) ltac:(discriminate) (w1x_wfirst false) eq_refl w1x_fatal). }
  split.
  { unfold dies_by_signal. cbn [run bh_traces w1x_image demo_entry].
    exists [KillEv (Z_to_bv 64 SIGPIPE) (in_fs (w1x_input false))],
      (Z_to_bv 64 SIGPIPE), (in_fs (w1x_input false)).
    split; [apply Hdead; apply is_prefix_refl | left; reflexivity]. }
  split.
  { intros tr e Htr Hin.
    destruct (is_prefix_In _ _ _ (proj1 (Hdead tr) Htr) Hin) as [<- | []].
    reflexivity. }
  split.
  { exact (cat_must_exit_with_te w1x_segments 0x100 demo_phdrs
             (Z_to_bv 64 0x7fff80000000) (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max)
             demo_draw lim (w1x_input true) [[w1x_byte]] (Z_to_bv 64 0)
             (w1x_te true) w1x_modeled (or_intror eq_refl)). }
  split.
  { apply Hlive. exists [WriteEv (Z_to_bv 64 1) w1x_byte].
    split; [| apply is_prefix_refl].
    exact (wp_cons (Z_to_bv 64 1) [w1x_byte] [] 1 [] (le_n 1) (le_n 1) (wp_nil _)). }
  unfold dies_by_signal. cbn [run bh_traces w1x_image demo_entry].
  intros (tr & sig & fs & Htr & Hin).
  destruct (proj1 (Hlive tr) Htr) as (full & Hpick & Hp).
  pose proof (is_prefix_In _ _ _ Hp Hin) as Hin'.
  apply in_app_iff in Hin' as [Hin' | [Hk | []]];
    [destruct (wpick_writes _ _ _ Hpick _ Hin') as (b & Hk) |];
    discriminate Hk.
Qed.
