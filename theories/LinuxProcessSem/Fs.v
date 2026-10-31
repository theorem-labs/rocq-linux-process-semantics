(** * LinuxProcessSem.Fs — the interpreted file-system model

    TRUST BOUNDARY: this file is part of the trusted specification.

    Paths and file contents are [byte = bv 8] lists; offsets and counts
    arrive from registers as [word = bv 64] and are bridged to [nat]
    for the list operations.  Well-formedness clauses bounding bytes
    are unnecessary — [bv 8] enforces them by type.

    The file system has an INTERNAL, INTERPRETED model (unlike channels,
    whose contents are supplied non-deterministically by the environment):
    it is a finite map from paths to byte contents, threaded through the
    syscall model.  The initial file-system image is an input to the
    program (quantified in [Equivalence.strong_universal_T], like argv/envp),
    and the file system is OBSERVED ONLY AT EXIT: [ExitEv] carries the
    final map, and no file operation emits a trace event.

    CANONICAL FORM: because the final map appears inside a trace event
    (compared with [=]), the representation must not depend on the order
    in which files were written.  We keep the association list strictly
    sorted by path ([fs_sorted]); [fs_set] preserves sortedness, so two
    runs that create the same files with the same contents produce equal
    [Fs] values.  [valid_fs] requires the initial image to be sorted as
    well. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope bv_scope.

(** A path is the raw byte string the program passed to the kernel (no
    NUL terminator).  Paths are uninterpreted: there is no directory
    structure, no normalization ("./x" and "x" are different files), and
    no symlinks.

    That is a statement about this MAP, and it is NOT the same as a
    statement about what the model admits.  A spec that would have to
    walk a path in order to answer correctly is expected to decline
    rather than read the map as if it had walked one; which specs
    currently do is not written here, because a list of them is a claim
    nothing checks and it goes stale silently.  Grep for
    [Sys.Fs.Namei.path_has_slash] to see the current set.

    What is worth writing down is the consequence: the only spec that
    CREATES a key is [Open.create_wronly], and it is behind that guard,
    so no program can make "./x" and "x" two keys.  Where a spec answers
    off the map instead of declining, it can diverge from Linux: [newfstatat]
    on the flat namespace can reject a path Linux accepts. *)
Definition path : Type := list byte.

Fixpoint path_eqb (p q : path) : bool :=
  match p, q with
  | [], [] => true
  | a :: p', b :: q' => bv_eqb a b && path_eqb p' q'
  | _, _ => false
  end.

Lemma bv_eqb_eq {n} (a b : bv n) : bv_eqb a b = true <-> a = b.
Proof.
  unfold bv_eqb. rewrite Z.eqb_eq.
  split; [apply bv_eq | intros ->; reflexivity].
Qed.

Lemma path_eqb_eq : forall p q, path_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, bv_eqb_eq, IH.
  split; [intros [-> ->] | intros H; inversion H]; auto.
Qed.

Lemma path_eqb_refl : forall p, path_eqb p p = true.
Proof. intros p. apply path_eqb_eq. reflexivity. Qed.

(** Strict lexicographic order on paths (shorter prefixes first);
    bytes compare unsigned. *)
Fixpoint path_ltb (p q : path) : bool :=
  match p, q with
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: p', b :: q' => bv_ltu a b || (bv_eqb a b && path_ltb p' q')
  end.

(** The file system: a path-to-contents association list, kept strictly
    sorted by [path_ltb] (see the canonical-form note above). *)
Definition Fs : Type := list (path * list byte).

Fixpoint fs_lookup (fs : Fs) (p : path) : option (list byte) :=
  match fs with
  | [] => None
  | (q, data) :: r => if path_eqb p q then Some data else fs_lookup r p
  end.

(** Insert-or-replace, preserving strict sortedness of the keys. *)
Fixpoint fs_set (fs : Fs) (p : path) (data : list byte) : Fs :=
  match fs with
  | [] => [(p, data)]
  | (q, d) :: r =>
      if path_ltb p q then (p, data) :: (q, d) :: r
      else if path_eqb p q then (p, data) :: r
      else (q, d) :: fs_set r p data
  end.

(** [path_ltb] is transitive.  This is what makes "drop one entry"
    preserve the canonical form: the neighbours either side of a removed
    key were separated only through it. *)
Lemma path_ltb_trans : forall a b c,
  path_ltb a b = true -> path_ltb b c = true -> path_ltb a c = true.
Proof.
  induction a as [|x a IH]; intros b c H1 H2;
    destruct b as [|y b]; destruct c as [|z c];
    cbn in *; try discriminate; try reflexivity.
  unfold bv_ltu, bv_eqb in *.
  apply Bool.orb_true_iff in H1 as [H1|H1];
    apply Bool.orb_true_iff in H2 as [H2|H2];
    apply Bool.orb_true_iff.
  - left. rewrite Z.ltb_lt in H1, H2 |- *. lia.
  - apply Bool.andb_true_iff in H2 as [H2 _]. rewrite Z.eqb_eq in H2.
    left. rewrite Z.ltb_lt in H1 |- *. lia.
  - apply Bool.andb_true_iff in H1 as [H1 _]. rewrite Z.eqb_eq in H1.
    left. rewrite Z.ltb_lt in H2 |- *. lia.
  - apply Bool.andb_true_iff in H1 as [Hx1 Hp1].
    apply Bool.andb_true_iff in H2 as [Hx2 Hp2].
    right. apply Bool.andb_true_iff.
    rewrite Z.eqb_eq in Hx1, Hx2 |- *.
    split; [lia | exact (IH b c Hp1 Hp2)].
Qed.

(** Remove a path.  A path absent from the map leaves it unchanged, so a
    caller that has already decided the path is present (unlink) and one
    that has not both get the same function. *)
Fixpoint fs_remove (fs : Fs) (p : path) : Fs :=
  match fs with
  | [] => []
  | (q, d) :: r => if path_eqb p q then r else (q, d) :: fs_remove r p
  end.

(** Keys strictly increasing — the canonical form. *)
Fixpoint fs_sorted (fs : Fs) : bool :=
  match fs with
  | [] => true
  | (p, _) :: r =>
      match r with
      | [] => true
      | (q, _) :: _ => path_ltb p q && fs_sorted r
      end
  end.

(** The head-key clause of [fs_sorted], named so the two lemmas below
    can talk about it. *)
Definition fs_lt_head (a : path) (fs : Fs) : bool :=
  match fs with
  | [] => true
  | (q, _) :: _ => path_ltb a q
  end.

Lemma fs_sorted_cons : forall p d r,
  fs_sorted ((p, d) :: r) = fs_lt_head p r && fs_sorted r.
Proof. intros p d r. destruct r as [|[q e] r']; reflexivity. Qed.

Lemma fs_remove_lt_head : forall fs a p,
  fs_sorted fs = true -> fs_lt_head a fs = true ->
  fs_lt_head a (fs_remove fs p) = true.
Proof.
  induction fs as [|[q d] r IH]; intros a p Hs Hh; [exact Hh|].
  cbn [fs_remove]. destruct (path_eqb p q) eqn:Hpq; [|exact Hh].
  rewrite fs_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hq Hr].
  destruct r as [|[q' d'] r']; [reflexivity|].
  cbn in Hh, Hq |- *. exact (path_ltb_trans _ _ _ Hh Hq).
Qed.

(** Dropping an entry preserves the canonical form, so a modeled unlink
    keeps the final [Fs] comparable with [=] (see the CANONICAL FORM note
    above). *)
Lemma fs_remove_sorted : forall fs p,
  fs_sorted fs = true -> fs_sorted (fs_remove fs p) = true.
Proof.
  induction fs as [|[q d] r IH]; intros p Hs; [reflexivity|].
  rewrite fs_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hq Hr].
  cbn [fs_remove]. destruct (path_eqb p q) eqn:Hpq; [exact Hr|].
  rewrite fs_sorted_cons, Bool.andb_true_iff. split.
  - now apply fs_remove_lt_head.
  - now apply IH.
Qed.

(** [path_ltb] is TOTAL against [path_eqb]: two paths that are neither
    equal nor in that order are in the opposite one.  This is what lets
    an insertion that has ruled out both of [fs_set]'s first two
    branches conclude that the key it is walking PAST is strictly below
    the key it is carrying. *)
Lemma path_ltb_total : forall p q,
  path_ltb p q = false -> path_eqb p q = false -> path_ltb q p = true.
Proof.
  induction p as [|a p IH]; destruct q as [|b q];
    cbn [path_ltb path_eqb]; try discriminate; try reflexivity.
  intros Hlt Heq.
  apply Bool.orb_false_iff in Hlt. destruct Hlt as [Hab Hrest].
  destruct (bv_eqb a b) eqn:He.
  - assert (Hba : bv_eqb b a = true)
      by (apply bv_eqb_eq in He; subst b; apply bv_eqb_eq; reflexivity).
    cbn [andb] in Hrest, Heq.
    rewrite Hba, (IH q Hrest Heq). now rewrite Bool.orb_true_r.
  - apply Bool.orb_true_iff. left.
    unfold bv_ltu, bv_eqb in *.
    rewrite Z.ltb_ge in Hab. rewrite Z.eqb_neq in He.
    rewrite Z.ltb_lt. lia.
Qed.

(** Inserting a key strictly above [a] cannot put anything at or below
    [a] at the head: the insertion either lands at the head (and the key
    is above [a] by hypothesis) or leaves the old head in place. *)
Lemma fs_set_lt_head : forall fs a p d,
  path_ltb a p = true -> fs_lt_head a fs = true ->
  fs_lt_head a (fs_set fs p d) = true.
Proof.
  induction fs as [|[q e] r IH]; intros a p d Hap Hh; [exact Hap|].
  cbn [fs_set].
  destruct (path_ltb p q) eqn:Hpq; [exact Hap|].
  destruct (path_eqb p q) eqn:Hpe; [exact Hap|exact Hh].
Qed.

(** Insert-or-replace preserves the canonical form.  This is the fact
    the header's "[fs_set] preserves sortedness" claims and the one
    [State.fs_seed_tmp] rests on: an initial image assembled by
    repeated insertion is canonical WHATEVER list it was assembled
    from, which is why the run's declared private /tmp needs no validity
    clause of its own. *)
Lemma fs_set_sorted : forall fs p d,
  fs_sorted fs = true -> fs_sorted (fs_set fs p d) = true.
Proof.
  induction fs as [|[q e] r IH]; intros p d Hs; [reflexivity|].
  cbn [fs_set].
  destruct (path_ltb p q) eqn:Hpq.
  { rewrite fs_sorted_cons, Bool.andb_true_iff. split; [exact Hpq|exact Hs]. }
  destruct (path_eqb p q) eqn:Hpe.
  { apply path_eqb_eq in Hpe; subst q.
    rewrite fs_sorted_cons. rewrite fs_sorted_cons in Hs. exact Hs. }
  rewrite fs_sorted_cons, Bool.andb_true_iff.
  rewrite fs_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hh Hr].
  split.
  - apply fs_set_lt_head; [now apply path_ltb_total | exact Hh].
  - now apply IH.
Qed.

(** Insertion keeps any property that holds of every key and of the key
    being inserted.  [valid_fs]'s NUL-free clause is the instance this
    file is written for. *)
Lemma fs_set_keys : forall (P : path -> Prop) fs p d,
  Forall (fun pf => P (fst pf)) fs -> P p ->
  Forall (fun pf => P (fst pf)) (fs_set fs p d).
Proof.
  intros P fs p d Hfs Hp. induction fs as [|[q e] r IH]; cbn [fs_set].
  - now constructor.
  - inversion Hfs as [|? ? Hq Hr]; subst.
    destruct (path_ltb p q).
    + now repeat constructor.
    + destruct (path_eqb p q).
      * now constructor.
      * constructor; [exact Hq | exact (IH Hr)].
Qed.

(** A lookup misses when no key IS the path.  The counterpart of
    [fs_set_keys] for the read side: a caller holding a fact about every
    key of an image gets the [None] from it without unfolding the
    fixpoint.  [Run.absolute_divergent_not_seeded] is the caller this is
    written for. *)
Lemma fs_lookup_none_of_keys : forall fs p,
  Forall (fun qd => fst qd <> p) fs -> fs_lookup fs p = None.
Proof.
  induction fs as [|[q d] fs IH]; intros p H; [reflexivity|].
  inversion H as [|? ? Hq Hr]; subst. cbn [fs_lookup].
  cbn [fst] in Hq.
  destruct (path_eqb p q) eqn:Hpq; [|now apply IH].
  apply path_eqb_eq in Hpq. subst q. now destruct (Hq eq_refl).
Qed.

(** Validity predicate for an initial file-system image: it must be in
    the CANONICAL sorted form (trace events compare final file systems
    with [=], so the representation must be unique — see the header
    note), and paths must be NUL-free byte strings so a program can
    actually name them.  (Bounding clauses on bytes are enforced by the
    [byte] type.) *)
Definition valid_fs (fs0 : Fs) : Prop :=
  fs_sorted fs0 = true /\
  Forall (fun pf => ~ In (Z_to_bv 8 0) (fst pf)) fs0.

(** The byte '/', the one byte this file has to interpret.

    Paths are uninterpreted here (see the header), and the separator's
    MEANING lives in [Sys.Fs.Namei] — [path_has_slash], [dir_prefixb]
    and the trailing-separator tests are all there.  What is needed at
    this rung is only the byte itself, for [key_is_relative] below, and
    that file sits above this one, so the constant is spelled here too.
    The two are pinned equal where the second is defined
    ([Sys.Fs.Namei.slash_byte_is_path_slash_byte]), so moving either is a
    compile error rather than a silent divergence. *)
Definition path_slash_byte : byte := Z_to_bv 8 47.

(** A key is CWD-RELATIVE when it does not begin with the separator.

    THE EMPTY KEY COUNTS AS RELATIVE.  It begins with nothing, so it
    begins with no '/'; and it is a key no program can name anyway
    ([Uaccess.read_cstr] of an empty pathname is the -ENOENT every path
    spec answers before it looks anything up), so admitting it costs no
    reachable behaviour and excluding it would be a clause about a key
    nothing reads.

    This is a statement about the FIRST byte and about nothing else: a
    key may still carry separators inside it ("a/b"), and that key is
    relative.  What "relative" buys is exactly the one thing the device
    arms need — such a key is not, and does not live under, an absolute
    path like "/dev/null". *)
Definition key_is_relative (p : path) : Prop :=
  match p with
  | [] => True
  | b :: _ => b <> path_slash_byte
  end.

(** Every key of an image is cwd-relative.

    THIS IS NOT A CLAUSE OF [valid_fs], and the reason is the seeding.
    [Run.valid_input] reads [valid_fs] on [State.in_fs], the image AFTER
    [State.fs_seed_tmp] has inserted each declared /tmp entry under the
    absolute key "/tmp/<name>"; a clause here would therefore make every
    input with a non-empty declaration invalid and silently remove those
    inputs from every theorem.  So this predicate is carried by
    [Run.valid_input] over [State.in_image_fs], the PRE-SEED image, as a
    conjunct of its own — see the note on that definition.

    No boolean twin, because [valid_fs] beside it has none: the image
    predicates in this file are read by proofs, not computed by the
    checker. *)
Definition fs_keys_relative (fs : Fs) : Prop :=
  Forall (fun pf => key_is_relative (fst pf)) fs.

(* =========================================================================
   File contents: byte-list read/write at an offset
   ========================================================================= *)

(** [firstn] is unchanged when its index is capped at the input list's
    length. *)
Lemma firstn_min_length : forall {A} (n : nat) (l : list A),
  firstn (Nat.min n (length l)) l = firstn n l.
Proof.
  intros A n l. destruct (Nat.le_ge_cases n (length l)) as [H|H].
  - now rewrite Nat.min_l.
  - rewrite Nat.min_r by exact H. rewrite firstn_all.
    symmetry. now apply firstn_all2.
Qed.

(** The file's bytes from [off] onward, counted down IN [Z] against the
    list rather than through a [nat] index.

    This exists so that no read builds [word_to_nat off], and that is
    load-bearing rather than an optimization.  [word_to_nat] is
    [Z.to_nat] (BvBase), and the extracted checker keeps [nat] as unary
    Peano — Checks/Extraction.v imports ExtrOcamlZBigInt, which realizes
    [Z] with zarith and leaves [nat] alone — so [word_to_nat off] costs
    one OCaml stack frame per unit of [off], and an lseek can put [off]
    anywhere below 2^63.  [skipn] would stop at the end of the list, but
    only after that numeral had been built.

    Recursing on the LIST instead bounds the work by the file rather
    than by the offset, and the recursive call is in tail position, so
    the extracted form runs in constant stack.  [file_from_skipn] proves
    it equal to the [skipn] it replaces, so nothing downstream has to
    know it is here. *)
Fixpoint file_from (data : list byte) (off : Z) : list byte :=
  match data with
  | [] => []
  | _ :: tl => if (off <=? 0)%Z then data else file_from tl (off - 1)
  end.

Lemma file_from_skipn : forall data off,
  (0 <= off)%Z ->
  file_from data off = skipn (Z.to_nat off) data.
Proof.
  induction data as [|b tl IH]; intros off Hoff.
  - now destruct (Z.to_nat off).
  - cbn [file_from]. destruct (off <=? 0)%Z eqn:Hle.
    + rewrite Z.leb_le in Hle.
      replace off with 0%Z by lia. reflexivity.
    + rewrite Z.leb_gt in Hle.
      rewrite IH by lia.
      replace (Z.to_nat off) with (S (Z.to_nat (off - 1))) by lia.
      reflexivity.
Qed.

(** Read up to [count] bytes starting at [off]; truncated at end-of-file
    (this is where a file read returns fewer bytes than asked, and 0
    bytes at or past the end).

    NEITHER argument reaches [nat] unbounded.  [off] does not cross at
    all: [file_from] walks the file in [Z], so a read is not charged for
    how far out it seeks.  [count] crosses only after being capped at
    what is left of the file, so a vectored read may name the whole
    [State.MAX_RW_COUNT] aggregate without building that numeral — a
    caller-side bound such as [Uaccess.rw_bytes_max] is then a statement
    about the transfer, not the only thing standing between the checker
    and its stack.  [file_read_unguarded] proves the pair is
    extensionally the ordinary [firstn]/[skipn] definition. *)
Definition file_read (data : list byte) (off count : word) : list byte :=
  let rest := file_from data (bv_unsigned off) in
  firstn (word_to_nat_bounded count (length rest)) rest.

Lemma file_read_unguarded : forall data off count,
  file_read data off count
  = firstn (word_to_nat count) (skipn (word_to_nat off) data).
Proof.
  intros data off count. unfold file_read. cbv zeta.
  rewrite word_to_nat_bounded_eq_min, firstn_min_length.
  rewrite file_from_skipn by (pose proof (bv_unsigned_in_range 64 off); lia).
  reflexivity.
Qed.

(** The file grown to [off] with zeros, and left alone at or below its
    current end: the content [i_size_write(inode, pos)] leaves behind
    when the page-cache write moved NO bytes.

    Two call sites, and they are the same kernel statement seen twice.
    [file_write] below pads with this before it overwrites; and a write
    whose source buffer faults reaches
    [a_ops->write_end(iocb, mapping, pos, bytes, copied = 0, ...)]
    (mm/filemap.c, [generic_perform_write]), whose
    [if (pos + copied > inode->i_size) i_size_write(inode, pos + copied)]
    (mm/shmem.c, [shmem_write_end]) extends the file to the write's own
    offset and no further.  The region it opens is a hole, which reads
    back as zeros, so a byte list of zeros is the right content — the
    same argument [file_truncate] below makes for a grow.  Linux v6.18.46.

    [word_to_nat off] is built in full here, exactly as [file_write]
    does; what bounds it is each caller's [ReadWrite.modeled_zero_fill]
    guard. *)
Definition file_extend (data : list byte) (off : word) : list byte :=
  data ++ repeat (Z_to_bv 8 0) (word_to_nat off - length data)%nat.

(** Overwrite [bs] at offset [off], extending the file if needed.  A write
    of a NONEMPTY [bs] past the current end zero-fills the gap
    (sparse-file semantics).

    A zero-length write leaves the file untouched, as on Linux: [write(fd,
    buf, 0)] on a regular file transfers nothing and never extends the
    file, even when the fd's offset sits past end-of-file (an lseek can
    put it there).  Without the [[]] arm the padding below would zero-
    extend the file out to [off] on a write that Linux makes no change
    for.  For [off <= length data] the two arms agree, so this is exactly
    the past-EOF corner.  A write whose source FAULTS is neither of
    these two: it moves no byte and still extends the file, and
    [file_extend] above is that post-state. *)
Definition file_write (data : list byte) (off : word) (bs : list byte)
    : list byte :=
  match bs with
  | [] => data                                (* zero-length write: no effect *)
  | _ :: _ =>
      let padded := file_extend data off in
      firstn (word_to_nat off) padded
        ++ bs ++ skipn (word_to_nat off + length bs)%nat padded
  end.

(** A delivering write's padding IS the faulting write's post-state, so
    the two arms of the same kernel statement cannot drift apart. *)
Lemma file_write_padding : forall data off b bs,
  file_write data off (b :: bs)
  = firstn (word_to_nat off) (file_extend data off)
    ++ (b :: bs) ++ skipn (word_to_nat off + length (b :: bs))%nat
                        (file_extend data off).
Proof. reflexivity. Qed.

(** At or below end-of-file nothing is added, which is what makes the
    guard on this padding a PAST-EOF question. *)
Lemma file_extend_within : forall data off,
  (word_to_nat off <= length data)%nat -> file_extend data off = data.
Proof.
  intros data off H. unfold file_extend.
  replace (word_to_nat off - length data)%nat with 0%nat by lia.
  cbn [repeat]. apply app_nil_r.
Qed.

(** Set the file's length to exactly [len]: a SHRINK drops the tail, a
    GROW zero-fills out to the new length ([ftruncate]; see
    [Open.ftruncate_spec]).  Both directions are one expression — for
    [len <= length data] the [repeat] is empty (its count is a [nat]
    subtraction), and for [len >= length data] the [firstn] is the whole
    file.

    Linux makes the grown region a HOLE rather than allocating it, but a
    hole reads back as zero bytes ([truncate_setsize] in mm/truncate.c
    zeroes the partial tail folio through [folio_zero_range], and the
    read path materializes an unmapped block as zeros; Linux v6.1
    through v6.12), so a byte list of zeros is the right content — it is
    the representation that differs, not the observation.

    [word_to_nat len] is built in full here, exactly as [file_write]
    builds [word_to_nat off], and NOTHING IN THIS DEFINITION BOUNDS IT.
    What bounds it is the guard that all three of its call sites apply
    first — [Open.ftruncate_spec], [Checks.Sys.Fs.Open.check_ftruncate] and
    [Checks.Witness.Fs.Open.ftruncate_witness], which agree arm for arm:
    [Open.modeled_truncate_gap] admits a grow only while
    [len <= length data + rw_bytes_max], and a shrink has
    [len <= length data] outright, so on both sides the numeral is
    bounded by the file itself plus a constant.  The
    [word_to_nat_bounded] trick [file_read] uses does not apply — capping
    the [firstn] by [length data] would be invisible, but the [repeat]
    count is exactly what a grow must add and capping THAT would drop
    the zeros — so there is no version of this that is safe without the
    call-site guard, and pretending otherwise with a half-cap would only
    hide where the bound really lives. *)
Definition file_truncate (data : list byte) (len : word) : list byte :=
  firstn (word_to_nat len) data
    ++ repeat (Z_to_bv 8 0) (word_to_nat len - length data)%nat.
