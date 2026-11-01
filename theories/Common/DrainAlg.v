(** * Common.DrainAlg — the [read(0, …)] node and the BOUNDED drain loop,
      in the shape algebra of [Common.ShapeAlg].

    TRUST BOUNDARY: image-INDEPENDENT proof library, written against the
    star-based [LinuxProcessSem.Run] trace semantics.  Additive: nothing
    in [ShapeAlg], [StreamSim] or [DrainSim] is changed or shadowed.

    Two things live here.

    ** 1. The [read(0, buf, cnt)] node ([node_read0] / [rz_read0]).

    [ShapeAlg]'s table of nodes lists "read(0, …) — chunkings of the
    stream" but the file itself stops at [mmap]; this supplies the
    missing entry.  The ingredients are exactly the [*_ok] +
    [sstep_*_inv] pair [Common/StreamSim.v] already proves ([read0_ok_eof],
    [read0_ok_bytes], [sstep_read_inv]), repackaged as the single
    [node_ok] interface, so the index type is the set of ADMISSIBLE READ
    RESOLUTIONS at the current stream:

      [rd_adm s cnt bs]  =  "bs = [] and the stream is at EOF"
                         or "bs is a nonempty <= cnt byte prefix of s".

    Both resolutions are packaged as one sigma type ([RdIdx]) rather than
    a sum, which is what makes the successor a plain function of [bs]
    ([rd_next] matches on [bs]: the empty list is EOF and every block is
    nonempty, so the match is exhaustive and non-overlapping).

    ** 2. The BOUNDED drain loop ([t_drain] / [rz_drain]).

    [Common/DrainSim.v] covers "read stdin to EOF in fixed-size chunks,
    folding each byte through [f]".  That loop has NO bound: on an
    infinite [InputStream] it never terminates, so — as
    [Common/SHAPE_ALGEBRA.md] records under "What this does not cover
    yet" — it cannot be given an INDUCTIVE [realizes] derivation, and
    [DrainSim] has to keep its own bespoke [drain_obs_iff]/[drain_no_error]
    pair.  ([DrainSim.drain_from] itself is fine on an infinite stream:
    the [out_tail s'] of a chunking that leaves [s' = ICons _ _] is [],
    so the trace set is a perfectly ordinary prefix-closed set with no
    maximal element.  It is the DERIVATION, not the denotation, that the
    inductive [realizes] cannot supply.)

    The loop shape here is different and strictly easier: the common
    "slurp stdin into a fixed-size arena" prologue

      len = 0;
      for (;;) {
        if (len >= CAP) break;
        r = read(0, buf + len, CAP - len);
        if (r < 0) die(...);        (* not reachable in the model *)
        if (r == 0) break;
        len += r;
      }

    is bounded by CAP: every admissible read delivers at least one byte,
    so the loop runs at most CAP times WHATEVER the stream is, including
    an infinite one.  That makes it an ordinary structural recursion on a
    [nat] fuel, and hence an ordinary inductive [realizes] derivation —
    no coinduction and no step indexing.  [rz_drain] below is that
    derivation, proved once, with the continuation [Tfin] (the shape of
    everything after the loop) as a parameter, and with the per-binary
    obligation stated as a single "every loop head runs to a read whose
    EOF successor is the tail and whose block successors are loop heads"
    hypothesis.

    The pay-off is that the arena's contents at loop exit are
    [firstn CAP stdin] — a FUNCTION of the stream, not a nondeterministic
    fold — which is what lets an otherwise wildly nondeterministic
    chunking collapse to a deterministic tail.  [t_drain_ch_collapse] proves
    that: every [acc] the loop can exit with is [firstn CAP] of the
    original stream (as a list).

    Conventions follow [StreamSim]/[DrainSim]: bytes are [byte = bv 8],
    counts are [word = bv 64], the read fd/count checks are
    Z-characterized ([bv_unsigned x8 = 63%Z]). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamExec WallSim StreamSim MmapSim ShapeAlg.

Import ListNotations.
Open Scope bv_scope.

(* ========================================================================= *)
(* Admissible read resolutions                                               *)
(* ========================================================================= *)

(** The resolutions of a [read(0, buf, cnt)] against remaining input [s].
    [StreamSim.read0_ok_inv] says these are exactly the outcomes the
    model admits. *)
Definition rd_adm (s : InputStream) (cnt : word) (bs : list byte) : Prop :=
  (bs = [] /\ s = IEof)
  \/ ((1 <= Z.of_nat (length bs))%Z
      /\ (Z.of_nat (length bs) <= bv_unsigned cnt)%Z
      /\ fst (stream_take s (length bs)) = bs).

Definition RdIdx (s : InputStream) (cnt : word) : Type :=
  { bs : list byte | rd_adm s cnt bs }.

(** Every read has at least one resolution: EOF, or the one-byte block. *)
Lemma rd_adm_inhab : forall s cnt, (0 < bv_unsigned cnt)%Z ->
  exists bs, rd_adm s cnt bs.
Proof.
  intros [|b s'] cnt Hcnt.
  - exists []. left. split; reflexivity.
  - exists [b]. right. cbn [length].
    split; [lia | split; [lia | reflexivity]].
Qed.

Lemma rd_adm_eof_nil : forall s cnt bs, rd_adm s cnt bs -> bs = [] -> s = IEof.
Proof.
  intros s cnt bs [(_ & Hs) | (Hlo & _ & _)] ->; [exact Hs | cbn in Hlo; lia].
Qed.

(** A block resolution is nonempty. *)
Lemma rd_adm_block_nonnil : forall bs : list byte,
  (1 <= Z.of_nat (length bs))%Z -> bs <> [].
Proof. intros [|b bs] H; [cbn in H; lia | discriminate]. Qed.

(** The successor configuration of a read resolution.  The match on [bs]
    is exhaustive and non-overlapping: EOF returns 0 bytes, every block
    is nonempty. *)
Definition rd_next (ms : machine_state) (model : Model) (buf : word)
    (bs : list byte) : config :=
  match bs with
  | [] => mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
  | _ :: _ =>
      mkCfg (advance_past_svc (apply_effect ms (mkEffect (len_word bs) [(buf, bs)] [])))
            (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
  end.

Lemma rd_next_stdin_block : forall ms model buf bs, bs <> [] ->
  m_stdin (cfg_model (rd_next ms model buf bs))
  = snd (stream_take (m_stdin model) (length bs)).
Proof. intros ms model buf [|b bs] H; [congruence | reflexivity]. Qed.

(* ========================================================================= *)
(* The arena contents are a FUNCTION of the stream                           *)
(* ========================================================================= *)

(** The list of bytes an [InputStream] delivers in its first [k]. *)
Definition stream_firstn (s : InputStream) (k : nat) : list byte :=
  fst (stream_take s k).

Lemma stream_take_split : forall k1 k2 s,
  fst (stream_take s (k1 + k2))
  = fst (stream_take s k1)
    ++ fst (stream_take (snd (stream_take s k1)) k2).
Proof.
  induction k1 as [|k1 IH]; intros k2 s; [reflexivity|].
  destruct s as [|b s']; cbn [stream_take fst snd Nat.add].
  - rewrite (stream_take_nil_of_eof k2). reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma stream_take_cons_pos : forall b s k, (1 <= k)%nat ->
  fst (stream_take (ICons b s) k) = b :: fst (stream_take s (k - 1)).
Proof.
  intros b s [|k] H; [lia|].
  cbn [stream_take fst]. replace (S k - 1)%nat with k by lia. reflexivity.
Qed.

Lemma stream_take_ge : forall k1 k2 s,
  (k1 <= k2)%nat ->
  (length (fst (stream_take s k1)) < k1)%nat ->
  fst (stream_take s k2) = fst (stream_take s k1).
Proof.
  induction k1 as [|k1 IH]; intros k2 s Hle Hlen; [cbn in Hlen; lia|].
  destruct k2 as [|k2]; [lia|].
  destruct s as [|b s']; cbn [stream_take fst snd] in *; [reflexivity|].
  cbn [length] in Hlen. rewrite (IH k2 s'); [reflexivity | lia | lia].
Qed.

(** Whatever chunking the loop takes, it exits with exactly the first
    [cap] bytes of the stream (or all of them, if there are fewer).  This
    is why the tail is a function of the input even though the read loop
    is nondeterministic. *)
Lemma stream_take_app_take : forall s bs k,
  fst (stream_take s (length bs)) = bs ->
  bs ++ fst (stream_take (snd (stream_take s (length bs))) k)
  = fst (stream_take s (length bs + k)).
Proof.
  intros s bs k Hpre. rewrite stream_take_split, Hpre. reflexivity.
Qed.

(* ========================================================================= *)
(* The node                                                                  *)
(* ========================================================================= *)

Section WithSegs.
Variable segs : list Segment.

(** The [read(0, buf, cnt)] node: the admissible transitions out of a
    read-pending configuration are EXACTLY the [RdIdx]-indexed family.
    Clause 1 is [StreamSim.read0_ok_eof]/[read0_ok_bytes], clause 2 is
    [StreamSim.sstep_read_inv]. *)
Lemma node_read0 : forall ms model buf cnt x8 w,
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  ms_gpr ms 1 = buf ->
  ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* the range passes [access_ok]: [vfs_read] tests it before the fd's
     content is consulted *)
  access_okb buf (bv_unsigned cnt) = true ->
  node_ok segs (mkCfg ms model) (RdIdx (m_stdin model) cnt)
          (fun i => map (ReadEv (Z_to_bv 64 0)) (proj1_sig i))
          (fun i => rd_next ms model buf (proj1_sig i)).
Proof.
  intros ms model buf cnt x8 w Hcnt Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok. split.
  - (* completeness *)
    intros [bs Hadm]; cbn [proj1_sig].
    destruct Hadm as [(-> & Heof) | (Hlo & Hhi & Hpre)].
    + (* EOF: return 0, no events, model unchanged *)
      cbn [map rd_next].
      rewrite <- (apply_effect_no_write ms (Z_to_bv 64 0)).
      apply (sstep_syscall segs ms model x8 (mkEffect (Z_to_bv 64 0) [] []) model model []);
        [exact Hh | exact Hsvc
         | eapply (read0_ok_eof cnt Hcnt segs ms x8 model w); try eassumption;
           rewrite Hg1; assumption
         | exact Hh |].
      rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + (* a block off the head of the stream *)
      assert (Hne : bs <> []) by (destruct bs; [cbn in Hlo; lia | discriminate]).
      destruct bs as [|b0 bs0]; [congruence|].
      cbn [rd_next].
      apply (sstep_syscall segs ms model x8
               (mkEffect (len_word (b0 :: bs0)) [(buf, b0 :: bs0)] [])
               (with_stdin (snd (stream_take (m_stdin model) (length (b0 :: bs0)))) model)
               (with_stdin (snd (stream_take (m_stdin model) (length (b0 :: bs0)))) model)
               (map (ReadEv (Z_to_bv 64 0)) (b0 :: bs0)));
        [exact Hh | exact Hsvc | | rewrite m_halted_with_stdin; exact Hh |].
      * rewrite <- Hg1.
        eapply (read0_ok_bytes cnt Hcnt segs ms x8 model w); try eassumption;
          rewrite Hg1; assumption.
      * rewrite (materialize_model_accesses_no_lazy _ _).
        -- reflexivity.
        -- rewrite m_vm_lazy_with_stdin. exact Hlazy.
  - (* soundness *)
    intros e st Hss.
    destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w e st
                Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
      as [(Heof & -> & ->) | (bs & Hlo & Hhi & Hpre & -> & ->)].
    + exists (exist _ [] (or_introl (conj eq_refl Heof))). split; reflexivity.
    + assert (Hadm : rd_adm (m_stdin model) cnt bs)
        by (right; split; [exact Hlo | split; [exact Hhi | exact Hpre]]).
      exists (exist _ bs Hadm). cbn [proj1_sig].
      destruct bs as [|b0 bs0]; [cbn in Hlo; lia|].
      split; reflexivity.
Qed.

(** The trace set of a read node on channel [rch]: choose a resolution,
    emit its [ReadEv]s, continue as [K bs].  The write-side twin is
    [ShapeAlg.t_write_ch]. *)
Definition t_read_ch (rch : word) (s : InputStream) (cnt : word)
    (K : list byte -> TSet) : TSet :=
  t_alt (fun i : RdIdx s cnt =>
           t_emit (map (ReadEv rch) (proj1_sig i)) (K (proj1_sig i))).

(** The same node on channel 0, the only channel a read can name:
    [ReadWrite.read_spec] answers -EBADF on the rest directly, and
    [ReadWrite.readv_spec] does so through [ReadWrite.readable_fd].  This is the
    form [rz_read0] realizes. *)
Definition t_read0 (s : InputStream) (cnt : word) (K : list byte -> TSet) : TSet :=
  t_read_ch (Z_to_bv 64 0) s cnt K.

(** The introduction rule.  Continuation-polymorphic, like every other
    combinator in [ShapeAlg]. *)
Lemma rz_read0 : forall ms model buf cnt x8 w K,
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  ms_gpr ms 1 = buf ->
  ms_gpr ms 2 = cnt ->
  read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
  (* the range passes [access_ok]: [vfs_read] tests it before the fd's
     content is consulted *)
  access_okb buf (bv_unsigned cnt) = true ->
  (forall bs, rd_adm (m_stdin model) cnt bs ->
     realizes segs (rd_next ms model buf bs) (K bs)) ->
  realizes segs (mkCfg ms model) (t_read0 (m_stdin model) cnt K).
Proof.
  intros ms model buf cnt x8 w K Hcnt Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok HK.
  destruct (rd_adm_inhab (m_stdin model) cnt (proj1 Hcnt)) as [bs0 Hbs0].
  unfold t_read0, t_read_ch.
  apply (rz_node segs (mkCfg ms model) (RdIdx (m_stdin model) cnt)
           (fun i => map (ReadEv (Z_to_bv 64 0)) (proj1_sig i))
           (fun i => rd_next ms model buf (proj1_sig i))
           (fun i => K (proj1_sig i))
           (exist _ bs0 Hbs0)).
  - eapply node_read0; eassumption.
  - intros [bs Hbs]; cbn [proj1_sig]. apply HK; exact Hbs.
Qed.

(** Emitting [a] then [b] is emitting [a ++ b].  (Purely about [t_emit];
    it belongs next to [ShapeAlg.t_emit_nil_eq], but [ShapeAlg] is not
    edited here.) *)
Lemma t_emit_app : forall a b T, t_eq (t_emit a (t_emit b T)) (t_emit (a ++ b) T).
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. split; [reflexivity | exact HT].
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr'. split; [reflexivity | left; exact Hp].
    + right. exists (b ++ tr').
      split; [symmetry; apply app_assoc
             | right; exists tr'; split; [reflexivity | exact HT]].
Qed.

(** [t_emit] respects [t_eq] in its continuation.  ([t_eq] is not a
    registered setoid relation, so this replaces a [rewrite].) *)
Lemma t_emit_cong : forall e T T', t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit. split;
    intros [Hp | (tr' & -> & HT)];
    solve [ left; exact Hp
          | right; exists tr'; split; [reflexivity | apply H; exact HT] ].
Qed.

(* ========================================================================= *)
(* The bounded drain loop                                                    *)
(* ========================================================================= *)

Section Drain.

(** The arena capacity.  Every read is [read(0, buf + |acc|, cap - |acc|)]
    and the loop stops at [|acc| = cap] or at EOF, whichever comes first. *)
Variable cap : nat.
Hypothesis Hcap : (Z.of_nat cap < 2 ^ 64)%Z.
(** The loop never asks for more than the model judges
    ([Uaccess.rw_bytes_max]): each read is capped by what is left of
    [cap]. *)
Hypothesis Hcap_modeled : (Z.of_nat cap <= rw_bytes_max)%Z.

(** The per-binary loop-head predicate, indexed by the bytes read so far. *)
Variable LH : list byte -> config -> Prop.

(** The shape of everything after the loop, as a function of the bytes the
    loop ended up with. *)
Variable Tfin : list byte -> TSet.

(** The count word of the next read at loop head [acc]. *)
Definition dcnt (acc : list byte) : word := Z_to_bv 64 (Z.of_nat (cap - length acc)).

Lemma dcnt_pos : forall acc, (length acc < cap)%nat -> (0 < bv_unsigned (dcnt acc))%Z.
Proof.
  intros acc H. unfold dcnt. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small; lia.
Qed.

Lemma dcnt_max : forall acc, (length acc <= cap)%nat ->
  (bv_unsigned (dcnt acc) <= rw_bytes_max)%Z.
Proof.
  intros acc H. unfold dcnt. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Z.mod_small; lia.
Qed.

Lemma dcnt_val : forall acc, (length acc <= cap)%nat ->
  bv_unsigned (dcnt acc) = Z.of_nat (cap - length acc).
Proof.
  intros acc H. unfold dcnt. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small; lia.
Qed.

(** The loop's trace set.  [n] is a FUEL: structural recursion needs one,
    because a resolution consumes [length bs] units of capacity rather
    than exactly one.  It is instantiated at [cap] by [rz_drain_top]; the
    invariant [cap - length acc <= n] (which every iteration preserves,
    since blocks are nonempty) is what makes the fuel never bite. *)
Fixpoint t_drain_ch (rch : word) (n : nat) (s : InputStream) (acc : list byte)
    : TSet :=
  match n with
  | O => Tfin acc
  | S n' =>
      if (cap <=? length acc)%nat then Tfin acc
      else t_read_ch rch s (dcnt acc)
             (fun bs =>
                match bs with
                | [] => Tfin acc
                | _ :: _ =>
                    t_drain_ch rch n' (snd (stream_take s (length bs))) (acc ++ bs)
                end)
  end.

(** The loop at channel 0, which is what a binary realizes.  NOTE that
    this is a [Definition] wrapping the [Fixpoint] above, so it does not
    reduce on its own: unfolding one iteration takes
    [cbn [t_drain t_drain_ch]], not [cbn [t_drain]], which is silently
    inert. *)
Definition t_drain (n : nat) (s : InputStream) (acc : list byte) : TSet :=
  t_drain_ch (Z_to_bv 64 0) n s acc.

(* ------------------------------------------------------------------------- *)
(* The chunking is INVISIBLE: the drain shape collapses to one deterministic  *)
(* block of read events followed by the tail at [firstn cap stdin].           *)
(* ------------------------------------------------------------------------- *)

(** The tail shape is nonempty — automatic for anything a binary can
    realize ([ShapeAlg.realizes_nonempty]), stated as a hypothesis so
    that the collapse below is a fact about [TSet]s alone. *)
Hypothesis Htfin_ne : forall acc, Tfin acc [].

(** A [read] emits one [ReadEv] PER BYTE, so a chunking contributes
    [map (ReadEv rch) (concat blocks)] to the trace no matter how the
    bytes were split across syscalls.  Therefore the whole nondeterministic
    loop denotes a SINGLE deterministic shape: emit the first
    [cap - |acc|] bytes of the remaining stream, then run the tail on
    what the arena ended up holding.

    This is the lemma that makes the pattern usable.  Two binaries may
    chunk stdin completely differently — different buffer sizes,
    different short-read behavior — and still realize the same [TSet],
    because the [TSet] does not mention the chunking at all.  It is also
    what turns "the arena holds SOME interleaving of the input" into
    "the arena holds [firstn cap stdin]", i.e. what makes the tail a
    function of the input. *)
Lemma t_drain_ch_collapse : forall rch n s acc,
  (cap - length acc <= n)%nat ->
  (length acc <= cap)%nat ->
  t_eq (t_drain_ch rch n s acc)
       (t_emit (map (ReadEv rch) (fst (stream_take s (cap - length acc))))
               (Tfin (acc ++ fst (stream_take s (cap - length acc))))).
Proof.
  intro rch. induction n as [|n IH]; intros s acc Hn Hle.
  - (* fuel out: the invariant forces the capacity to be out too *)
    replace (cap - length acc)%nat with O by lia.
    cbn [stream_take fst map]. rewrite app_nil_r.
    apply t_eq_sym, t_emit_nil_eq, Htfin_ne.
  - cbn [t_drain_ch].
    destruct (Nat.leb_spec cap (length acc)) as [Hfullc | Hlt].
    + replace (cap - length acc)%nat with O by lia.
      cbn [stream_take fst map]. rewrite app_nil_r.
      apply t_eq_sym, t_emit_nil_eq, Htfin_ne.
    + (* one read, then the rest of the loop *)
      set (m := (cap - length acc)%nat).
      assert (Hm : (1 <= m)%nat) by (unfold m; lia).
      assert (Hdc : bv_unsigned (dcnt acc) = Z.of_nat m)
        by (apply dcnt_val; lia).
      intro tr. unfold t_read_ch, t_alt. split.
      * (* every resolution's traces are in the collapsed shape *)
        intros [[bs Hadm] Hi]; cbn [proj1_sig] in Hi.
        destruct bs as [|b0 bs0].
        { (* EOF: the stream is empty, so [firstn m] of it is [] *)
          destruct Hadm as [(_ & ->) | (Hlo & _ & _)]; [|cbn in Hlo; lia].
          rewrite stream_take_nil_of_eof, app_nil_r. exact Hi. }
        { (* a block: peel it off and use the induction hypothesis *)
          set (bs := b0 :: bs0) in *.
          destruct Hadm as [(Hbad & _) | (Hlo & Hhi & Hpre)]; [discriminate|].
          assert (Hblen : (length bs <= m)%nat) by (rewrite Hdc in Hhi; lia).
          assert (Hlen' : length (acc ++ bs) = (length acc + length bs)%nat)
            by (rewrite length_app; reflexivity).
          assert (Hsplit :
            fst (stream_take s m)
            = bs ++ fst (stream_take (snd (stream_take s (length bs)))
                                     (m - length bs)))
            by (replace m with (length bs + (m - length bs))%nat at 1 by lia;
                rewrite stream_take_split, Hpre; reflexivity).
          pose proof (IH (snd (stream_take s (length bs))) (acc ++ bs)
                       ltac:(lia) ltac:(lia)) as IHb.
          replace (cap - length (acc ++ bs))%nat with (m - length bs)%nat
            in IHb by lia.
          rewrite <- app_assoc in IHb.
          rewrite Hsplit, map_app.
          apply (proj1 (t_emit_app (map (ReadEv rch) bs) _ _ tr)).
          exact (proj1 (t_emit_cong _ _ _ IHb tr) Hi). }
      * (* conversely, the byte-at-a-time chunking realizes everything *)
        intro Hrhs.
        destruct s as [|b s'].
        { (* nothing left to read: the EOF resolution *)
          unshelve eexists (exist _ [] _); [left; split; reflexivity|].
          cbn [proj1_sig]. rewrite stream_take_nil_of_eof, app_nil_r in Hrhs.
          exact Hrhs. }
        { (* deliver exactly one byte: the finest chunking realizes
             every trace the collapsed shape contains *)
          unshelve eexists (exist _ [b] _).
          { right. cbn [length]. split; [lia | split; [lia | reflexivity]]. }
          cbn [proj1_sig length stream_take fst snd map].
          assert (Hlen' : length (acc ++ [b]) = S (length acc))
            by (rewrite length_app; cbn [length]; lia).
          pose proof (IH s' (acc ++ [b]) ltac:(lia) ltac:(lia)) as IHb.
          replace (cap - length (acc ++ [b]))%nat with (m - 1)%nat in IHb by lia.
          rewrite <- app_assoc in IHb. cbn [app] in IHb.
          apply (proj2 (t_emit_cong [ReadEv rch b] _ _ IHb tr)).
          apply (proj2 (t_emit_app [ReadEv rch b]
                          (map (ReadEv rch)
                             (fst (stream_take s' (m - 1)))) _ tr)).
          rewrite (stream_take_cons_pos b s' m Hm) in Hrhs.
          cbn [map app] in Hrhs |- *. exact Hrhs. }
Qed.

(** The collapse at channel 0, which is the form a binary uses. *)
Lemma t_drain_collapse : forall n s acc,
  (cap - length acc <= n)%nat ->
  (length acc <= cap)%nat ->
  t_eq (t_drain n s acc)
       (t_emit (map (ReadEv (Z_to_bv 64 0)) (fst (stream_take s (cap - length acc))))
               (Tfin (acc ++ fst (stream_take s (cap - length acc))))).
Proof. exact (t_drain_ch_collapse (Z_to_bv 64 0)). Qed.

(** The same collapse at the loop's entry, with an empty accumulator. *)
Corollary t_drain_ch_top_collapse : forall rch s,
  t_eq (t_drain_ch rch cap s [])
       (t_emit (map (ReadEv rch) (stream_firstn s cap))
               (Tfin (stream_firstn s cap))).
Proof.
  intros rch s. unfold stream_firstn.
  pose proof (t_drain_ch_collapse rch cap s [] ltac:(cbn [length]; lia)
                ltac:(cbn [length]; lia)) as H.
  replace (cap - length (@nil byte))%nat with cap in H
    by (cbn [length]; lia).
  cbn [app] in H. exact H.
Qed.

(** The collapse at the loop's entry on channel 0, which is how a binary
    uses it ([Examples.arena_tee_ns] is the one in the tree). *)
Corollary t_drain_top_collapse : forall s,
  t_eq (t_drain cap s [])
       (t_emit (map (ReadEv (Z_to_bv 64 0)) (stream_firstn s cap))
               (Tfin (stream_firstn s cap))).
Proof. exact (t_drain_ch_top_collapse (Z_to_bv 64 0)). Qed.

(** The loop exits (breaks out of the [read] loop) at [|acc| = cap]. *)
Hypothesis Hfull : forall acc c,
  LH acc c -> (cap <= length acc)%nat -> realizes segs c (Tfin acc).

(** The single per-binary obligation: a loop head with capacity left runs
    (silently, straight-line) to a [read(0, buf, cap - |acc|)] whose EOF
    resolution enters the tail and whose block resolutions land on the
    next loop head.  The buffer address [buf] is existential — the
    combinator does not care WHERE the arena is, only that the whole
    remaining count is writable there. *)
Hypothesis Hread : forall acc c,
  LH acc c -> (length acc < cap)%nat ->
  exists ms1 buf x8 w,
    m_halted (cfg_model c) = None /\
    m_vm_lazy (cfg_model c) = [] /\
    fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
    msteps segs (cfg_ms c) ms1 /\
    ms_svc_pending ms1 = Some x8 /\
    bv_unsigned x8 = 63%Z /\
    ms_gpr ms1 0 = Z_to_bv 64 0 /\
    ms_gpr ms1 1 = buf /\
    ms_gpr ms1 2 = dcnt acc /\
    read_bytes_map (ms_writable_byte segs ms1) buf (dcnt acc) = Some w /\
    (** the range passes [access_ok], which [vfs_read] tests before the
        input is consulted.  [read_bytes_map] walks the range in word
        arithmetic, which wraps at 2^64, so being mapped is not it; an
        arena address is far under [State.TASK_SIZE], so this is one
        inequality per binary. *)
    access_okb buf (bv_unsigned (dcnt acc)) = true /\
    (** EOF: the loop breaks and the tail runs *)
    realizes segs (rd_next ms1 (cfg_model c) buf []) (Tfin acc) /\
    (** a block: back to the loop head with the block appended *)
    (forall bs, rd_adm (m_stdin (cfg_model c)) (dcnt acc) bs -> bs <> [] ->
       LH (acc ++ bs) (rd_next ms1 (cfg_model c) buf bs)).

(** The loop rule.  Ordinary induction on the fuel — no coinduction, no
    step indexing, because the loop is bounded by [cap] on EVERY stream. *)
Lemma rz_drain : forall n acc c,
  (cap - length acc <= n)%nat ->
  LH acc c ->
  realizes segs c (t_drain n (m_stdin (cfg_model c)) acc).
Proof.
  induction n as [|n IH]; intros acc c Hn HLH.
  - cbn [t_drain t_drain_ch]. apply Hfull; [exact HLH | lia].
  - cbn [t_drain t_drain_ch].
    destruct (Nat.leb_spec cap (length acc)) as [Hle | Hlt].
    + apply Hfull; [exact HLH | exact Hle].
    + destruct (Hread acc c HLH Hlt)
        as (ms1 & buf & x8 & w & Hh & Hlazy & Hfd & Hms & Hsvc & Hno & Hg0 & Hg1 & Hg2 & Hw
            & Haok & Heof & Hblk).
      destruct c as [ms0 model]; cbn [cfg_ms cfg_model] in *.
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
      apply (rz_read0 ms1 model buf (dcnt acc) x8 w);
        try assumption;
        [split; [apply dcnt_pos; exact Hlt | apply dcnt_max; lia] |].
      intros bs Hadm. destruct bs as [|b0 bs0].
      * exact Heof.
      * specialize (Hblk (b0 :: bs0) Hadm ltac:(discriminate)).
        specialize (IH (acc ++ b0 :: bs0) _ ltac:(
          rewrite length_app; cbn [length]; lia) Hblk).
        rewrite (rd_next_stdin_block ms1 model buf (b0 :: bs0) ltac:(discriminate))
          in IH.
        exact IH.
Qed.

(** The loop rule as a binary would use it: from the initial loop head
    with an empty accumulator. *)
Corollary rz_drain_top : forall c,
  LH [] c -> realizes segs c (t_drain cap (m_stdin (cfg_model c)) []).
Proof. intros c H. apply rz_drain; [cbn [length]; lia | exact H]. Qed.

(* ========================================================================= *)
(* A COMMON COMPOSITION: mmap arena, then drain, then the tail              *)
(* ========================================================================= *)

(** "Single anonymous [mmap] prologue, then slurp stdin into the arena,
    then a deterministic tail."  This is a common composition.  Without
    the shape algebra it would need a bespoke [Common/] file per
    (allocator, loop, tail) triple: [MmapSim] owns the two-resolution mmap node and
    [DrainSim] owns the read loop, and neither can appear under the
    other's relation.

    Here it is [rz_mmap] with [rz_drain_top] plugged into its success
    continuation and [ShapeAlg.cat_realizes] into its failure
    continuation.  The two facts that make it go through are that
    [MmapSim.mmap_model] touches only [vm_maps] — so the post-mmap
    model has the SAME [m_stdin] as the pre-mmap one, which is what
    makes the drain shape independent of WHICH address the kernel
    granted — and that [t_drain]'s continuation [Tfin] is a parameter,
    so the tail may be any [realizes] derivation at all (a write list
    and an exit, as here; or a nested loop).

    Note the shape of the conclusion: a two-element [t_alt2], exactly
    the two-element outcome set a single-mmap example is
    specified against. *)
Corollary rz_mmap_drain : forall ms0 ms model x8 bf cf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  msteps segs ms0 ms ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (** the mmap failed: the binary's failure tail, a (retry-loop) write
      list and an exit *)
  (forall e, In e mmap_errnos ->
     to_wallexit segs (Z_to_bv 64 1) bf cf
       (advance_past_svc (set_gpr0 ms (errno_ret e)))) ->
  (** the mmap succeeded at [a]: the binary reaches its drain loop head *)
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     LH [] (mkCfg (advance_past_svc
                     (apply_effect ms
                        (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                  (mmap_model a (page_round_up (ms_gpr ms 1)) model))) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  bufs_modeled bf ->
  realizes segs (mkCfg ms0 model)
    (t_alt2 (t_writes bf (t_exit cf (m_fs model)))
            (t_drain cap (m_stdin model) [])).
Proof.
  intros ms0 ms model x8 bf cf Hh Hlazy Hfd Hms Hsvc Hno Hargs Hfail Hsucc Hex Hbf.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  eapply rz_mmap; try eassumption.
  - intros e He. apply wall_realizes;
      [exact Hh | exact Hlazy | exact Hfd | apply Hfail; exact He | exact Hbf].
  - intros a Ha.
    (* [mmap_model] rewrites only [vm_maps], so the remaining stdin — and
       hence the whole drain shape — is untouched by the grant. *)
    exact (rz_drain_top _ (Hsucc a Ha)).
Qed.

Lemma t_alt2_cong : forall A A' B B',
  t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof.
  intros A A' B B' HA HB tr. unfold t_alt2.
  split; (intros [H | H]; [left; apply HA; exact H | right; apply HB; exact H]).
Qed.

(** The same composition with the drain's chunking nondeterminism
    ELIMINATED ([t_drain_top_collapse]).  This is the shape a
    single-mmap-then-slurp binary is actually specified against: a
    two-element outcome set, one branch per [mmap] resolution, the
    success branch a deterministic function of the input stream.  Note
    that [cap] and [Tfin] are the only things the source and the target
    have to agree on — NOT how either of them chunks its reads. *)
Corollary rz_mmap_drain_det : forall ms0 ms model x8 bf cf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  msteps segs ms0 ms ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall e, In e mmap_errnos ->
     to_wallexit segs (Z_to_bv 64 1) bf cf
       (advance_past_svc (set_gpr0 ms (errno_ret e)))) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     LH [] (mkCfg (advance_past_svc
                     (apply_effect ms
                        (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                  (mmap_model a (page_round_up (ms_gpr ms 1)) model))) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  bufs_modeled bf ->
  realizes segs (mkCfg ms0 model)
    (t_alt2 (t_writes bf (t_exit cf (m_fs model)))
            (t_emit (map (ReadEv (Z_to_bv 64 0))
                         (stream_firstn (m_stdin model) cap))
                    (Tfin (stream_firstn (m_stdin model) cap)))).
Proof.
  intros ms0 ms model x8 bf cf Hh Hlazy Hfd Hms Hsvc Hno Hargs Hfail Hsucc Hex Hbf.
  eapply rz_conseq;
    [ eapply rz_mmap_drain; eassumption
    | apply t_alt2_cong; [apply t_eq_refl | apply t_drain_top_collapse] ].
Qed.

End Drain.

End WithSegs.
