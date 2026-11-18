(** * LinuxProcessSem.Fs — the interpreted file-system model

    TRUST BOUNDARY: this file is part of the trusted specification.

    Paths and file contents are [byte = bv 8] lists; offsets and counts
    arrive from registers as [word = bv 64] and are bridged to [nat]
    for the list operations.  Well-formedness clauses bounding bytes
    are unnecessary — [bv 8] enforces them by type.

    The file system has an INTERNAL, INTERPRETED model (unlike channels,
    whose contents are supplied non-deterministically by the environment):
    a NAME TREE from ABSOLUTE CANONICAL PATHS to ENTRIES — a regular
    file's inode number, a directory, one of the two character devices,
    or a symbolic link with its body — beside an INODE TABLE that holds
    each regular file's bytes, and a table of folder link counts.  It is
    threaded through the syscall model.  The initial file-system image is
    an input to the program (quantified in
    [Equivalence.strong_universal_T], like argv/envp), and the file system
    is OBSERVED ONLY AT EXIT: [ExitEv] carries the final image, and no
    file operation emits a trace event.

    NO CONCURRENT WRITER.  The image is the WHOLE TRUTH about the run's
    file system for the run's whole life: what it holds is this
    declaration, plus what the modeled creating specs created, minus what
    the modeled removing specs removed, and nothing else can put a file
    there or take one away.  Nothing outside the run writes any part of
    it — not /tmp, not the working directory, not the devices.  That is
    a premise about the environment the model cannot check, and it is the
    premise the whole interpreted image carries; it is stated once here
    rather than per directory (it retired
    bugs/tmp-assumed-private-directory.md, which said it of /tmp alone).

    CANONICAL FORM: because the final image appears inside a trace event
    (compared with [=]), the representation must not depend on the order
    in which names were made.  We keep the name tree strictly sorted by
    path ([tree_sorted]); [tree_set] preserves sortedness, so two runs
    that make the same names with the same entries produce equal trees.
    Inode numbers are handed out deterministically ([fs_fresh_ino]), so
    two runs that create the same files in the same order produce equal
    images.  [wf_fs] requires the initial tree to be sorted as well, and
    three things besides: every key is an absolute canonical path, the
    root is a directory, and every key's parent is one.  It asks nothing
    of the two tables: an inode number with no row reads as an empty file
    named nowhere else, and a folder with no row has the counts
    [fs_dir_links] gives it, so no image can be written whose tables
    disagree with its tree.

    THE PATH NAMESPACE lives in the last section of this file: the key
    discipline ([canonical_key]), one resolution function ([resolve]) in
    [link_path_walk]'s own left-to-right order, the well-formedness
    predicate and its executable twin ([wf_fs], [wf_fsb]), the default
    image ([standard_root]) and the migration of a pre-namespace image
    ([migrate_image]).  Design note: issue #1011.

    Ported from theorem-labs/linux-process-semantics
    r22/namespace-core at 6ff3d045 (issue #1011). *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope bv_scope.

(** A path is the raw byte string the program passed to the kernel (no
    NUL terminator).  A path the program names is ARBITRARY BYTES: it
    may be relative or absolute, may hold "." and ".." components,
    repeated and trailing separators, and components of any length.  It
    is [resolve] that interprets one, against the image and the working
    directory, in the kernel's own order.

    A KEY of the name tree is narrower: an ABSOLUTE CANONICAL path, the
    normal form [canonical_key] decides.  Nothing but a canonical key is
    ever stored, so "./x", "x" and "/work/x" are one name and not three,
    and the tree still compares with [=]. *)


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

Lemma bv_eqb_refl {n} (a : bv n) : bv_eqb a a = true.
Proof. apply bv_eqb_eq. reflexivity. Qed.

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

(** THE TWO CHARACTER DEVICES the model answers for.  They are ENTRIES
    rather than magic pathnames: an image says where they are, and
    [Sys.Fs.Open] mints [State.FdDevNull] / [State.FdUrandom] from the
    entry it resolved, not from a name it recognised.  The pair is the
    pair the targets need — Linux's 1:3 and 1:9 — and adding a third is
    adding a constructor here and an answer table beside the other two,
    not a new pathname arm. *)
Inductive DevKind := DevNull | DevUrandom.

(** INODE NUMBERS, the model's own: the IDENTITY of a regular file.
    Two names of one file carry one number, and that is the whole of what
    a hard link is here.  The number is not [st_ino] -- that member is the
    environment's, pinned per identity by [State.procst_statpins] -- it
    is the key of the inode table. *)
Definition ino : Type := Z.
(** An inode number written as a numeral reads as a [Z] wherever an [ino]
    is expected, whatever scope the text around it has open. *)
Bind Scope Z_scope with ino.

(** WHAT A KEY HOLDS.  A regular file's inode, a directory, a character
    device, or a SYMBOLIC LINK.

    A directory is a KEY of its own, so an EMPTY directory exists in the
    model, and a directory's identity IS its key: a folder has exactly
    one name, because [vfs_link] refuses to link one
    ([if (S_ISDIR(inode->i_mode)) return -EPERM;], fs/namei.c:4929-4930,
    Linux v6.18.46).  A regular file is an inode number, looked up in
    [fs_inodes] for its bytes and its link count.

    A LINK carries its BODY, the bytes [->get_link] hands back, read up
    to the first NUL as Linux reads a C string ([vfs_readlink]'s
    [strlen(link)], fs/namei.c:5469), so no image clause limits what a
    body may hold.  A link carries no inode number of its own: its
    identity is its key (see [State.StatId]). *)
Inductive Entry :=
  | EFile (i : ino)
  | EDir
  | EDev (k : DevKind)
  | ELink (body : path).

(** ONE REGULAR FILE'S INODE.  [ino_data] is its bytes, its page cache up
    to [i_size].  [ino_outside] is the number of its names the image does
    NOT show: a name on another mount of the same file system, or under a
    bind mount, counts in Linux's [i_nlink] and is not a key of the tree.
    The LINK COUNT is derived ([fs_ino_nlink]): the names the tree shows
    plus [ino_outside].  So a file with a name has a count of at least
    one, and no image can give a file fewer links than the names it
    shows. *)
Record Inode := mkInode { ino_data : list byte ; ino_outside : nat }.

(** ONE FOLDER'S LINK COUNT, under each of the two rules the model
    admits.  [dl_counting] is the count when the folder counts its
    subfolders, the rule of tmpfs and ramfs, the file systems of the
    configuration of record (SCOPE.md): a new folder starts at 2 and its
    parent's count goes up by one (tmpfs: [shmem_get_inode]'s
    [inc_nlink] at mm/shmem.c:3133-3134 over the 1 [inode_init_always]
    sets at fs/inode.c:242, and the parent's is raised by [shmem_mkdir]
    at mm/shmem.c:3952; ramfs: the same in [ramfs_get_inode]
    (fs/ramfs/inode.c:82) and [ramfs_mkdir] (:127)).  [dl_fixed] is the
    count when it does not,
    btrfs's rule ([btrfs_mkdir] makes the folder with [new_inode] and
    never raises the parent's count, fs/btrfs/inode.c:7020-7031, so
    every folder stays at 1).  No supported kernel follows that rule,
    since the configuration of record builds no btrfs, so the counts it
    admits are a priority-2 gap, and sound: SCOPE.md, "Known gaps in
    precision".  Which rule a folder follows is not image data: it is
    chosen at the first [stat] that tells them apart and then kept
    ([State.StatPin]). *)
Record DirLinks := mkDirLinks { dl_counting : nat ; dl_fixed : nat }.

(** Entries are compared for equality wherever an image is
    ([EquivalenceDefinition.MeasureLib]'s [FinCore] instance, and the
    [=] on the final map inside a trace event). *)
#[global] Instance DevKind_eq_dec : EqDecision DevKind.
Proof. solve_decision. Defined.

#[global] Instance Entry_eq_dec : EqDecision Entry.
Proof. solve_decision. Defined.

#[global] Instance Inode_eq_dec : EqDecision Inode.
Proof. solve_decision. Defined.

#[global] Instance DirLinks_eq_dec : EqDecision DirLinks.
Proof. solve_decision. Defined.

(** Is this entry a symbolic link? *)
Definition entry_is_link (e : Entry) : bool :=
  match e with ELink _ => true | EFile _ | EDir | EDev _ => false end.

(** The NAME TREE: a key-to-entry association list, kept strictly
    sorted by [path_ltb] (see the canonical-form note above). *)
Definition Tree : Type := list (path * Entry).

Fixpoint tree_lookup (t : Tree) (p : path) : option Entry :=
  match t with
  | [] => None
  | (q, e) :: r => if path_eqb p q then Some e else tree_lookup r p
  end.

(** Insert-or-replace, preserving strict sortedness of the keys. *)
Fixpoint tree_set (t : Tree) (p : path) (e : Entry) : Tree :=
  match t with
  | [] => [(p, e)]
  | (q, d) :: r =>
      if path_ltb p q then (p, e) :: (q, d) :: r
      else if path_eqb p q then (p, e) :: r
      else (q, d) :: tree_set r p e
  end.

(** The two laws every caller of [tree_set] reads it through. *)
Lemma tree_lookup_set_eq : forall t p e,
  tree_lookup (tree_set t p e) p = Some e.
Proof.
  induction t as [|[q d] r IH]; intros p e; cbn [tree_set tree_lookup].
  - now rewrite path_eqb_refl.
  - destruct (path_ltb p q) eqn:Hlt; cbn [tree_lookup].
    + now rewrite path_eqb_refl.
    + destruct (path_eqb p q) eqn:Heq; cbn [tree_lookup].
      * now rewrite path_eqb_refl.
      * rewrite Heq. apply IH.
Qed.

Lemma tree_lookup_set_neq : forall t p q e,
  path_eqb q p = false -> tree_lookup (tree_set t p e) q = tree_lookup t q.
Proof.
  induction t as [|[k d] r IH]; intros p q e Hne; cbn [tree_set tree_lookup].
  - now rewrite Hne.
  - destruct (path_ltb p k) eqn:Hlt; cbn [tree_lookup].
    + now rewrite Hne.
    + destruct (path_eqb p k) eqn:Heq; cbn [tree_lookup].
      * apply path_eqb_eq in Heq; subst k. now rewrite Hne.
      * destruct (path_eqb q k) eqn:Hqk; [reflexivity|]. now apply IH.
Qed.

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

(** Remove a path.  A path absent from the tree leaves it unchanged, so
    a caller that has already decided the path is present (unlink) and
    one that has not both get the same function. *)
Fixpoint tree_remove (t : Tree) (p : path) : Tree :=
  match t with
  | [] => []
  | (q, d) :: r => if path_eqb p q then r else (q, d) :: tree_remove r p
  end.

(** Keys strictly increasing — the canonical form. *)
Fixpoint tree_sorted (t : Tree) : bool :=
  match t with
  | [] => true
  | (p, _) :: r =>
      match r with
      | [] => true
      | (q, _) :: _ => path_ltb p q && tree_sorted r
      end
  end.

(** The head-key clause of [tree_sorted], named so the two lemmas below
    can talk about it. *)
Definition tree_lt_head (a : path) (t : Tree) : bool :=
  match t with
  | [] => true
  | (q, _) :: _ => path_ltb a q
  end.

Lemma tree_sorted_cons : forall p d r,
  tree_sorted ((p, d) :: r) = tree_lt_head p r && tree_sorted r.
Proof. intros p d r. destruct r as [|[q e] r']; reflexivity. Qed.

Lemma tree_remove_lt_head : forall t a p,
  tree_sorted t = true -> tree_lt_head a t = true ->
  tree_lt_head a (tree_remove t p) = true.
Proof.
  induction t as [|[q d] r IH]; intros a p Hs Hh; [exact Hh|].
  cbn [tree_remove]. destruct (path_eqb p q) eqn:Hpq; [|exact Hh].
  rewrite tree_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hq Hr].
  destruct r as [|[q' d'] r']; [reflexivity|].
  cbn in Hh, Hq |- *. exact (path_ltb_trans _ _ _ Hh Hq).
Qed.

(** Dropping an entry preserves the canonical form, so a modeled unlink
    keeps the final image comparable with [=] (see the CANONICAL FORM
    note above). *)
Lemma tree_remove_sorted : forall t p,
  tree_sorted t = true -> tree_sorted (tree_remove t p) = true.
Proof.
  induction t as [|[q d] r IH]; intros p Hs; [reflexivity|].
  rewrite tree_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hq Hr].
  cbn [tree_remove]. destruct (path_eqb p q) eqn:Hpq; [exact Hr|].
  rewrite tree_sorted_cons, Bool.andb_true_iff. split.
  - now apply tree_remove_lt_head.
  - now apply IH.
Qed.

(** [path_ltb] is TOTAL against [path_eqb]: two paths that are neither
    equal nor in that order are in the opposite one.  This is what lets
    an insertion that has ruled out both of [tree_set]'s first two
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
Lemma tree_set_lt_head : forall t a p (d : Entry),
  path_ltb a p = true -> tree_lt_head a t = true ->
  tree_lt_head a (tree_set t p d) = true.
Proof.
  induction t as [|[q e] r IH]; intros a p d Hap Hh; [exact Hap|].
  cbn [tree_set].
  destruct (path_ltb p q) eqn:Hpq; [exact Hap|].
  destruct (path_eqb p q) eqn:Hpe; [exact Hap|exact Hh].
Qed.

(** Insert-or-replace preserves the canonical form.  This is the fact
    the header's "[tree_set] preserves sortedness" claims and the one
    [standard_root] and [migrate_image] rest on: a tree assembled by
    repeated insertion is canonical WHATEVER list it was assembled
    from. *)
Lemma tree_set_sorted : forall t p (d : Entry),
  tree_sorted t = true -> tree_sorted (tree_set t p d) = true.
Proof.
  induction t as [|[q e] r IH]; intros p d Hs; [reflexivity|].
  cbn [tree_set].
  destruct (path_ltb p q) eqn:Hpq.
  { rewrite tree_sorted_cons, Bool.andb_true_iff. split; [exact Hpq|exact Hs]. }
  destruct (path_eqb p q) eqn:Hpe.
  { apply path_eqb_eq in Hpe; subst q.
    rewrite tree_sorted_cons. rewrite tree_sorted_cons in Hs. exact Hs. }
  rewrite tree_sorted_cons, Bool.andb_true_iff.
  rewrite tree_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hh Hr].
  split.
  - apply tree_set_lt_head; [now apply path_ltb_total | exact Hh].
  - now apply IH.
Qed.

(** Insertion keeps any property that holds of every key and of the key
    being inserted.  [wf_fs]'s canonical-key clause is the instance this
    file is written for. *)
Lemma tree_set_keys : forall (P : path -> Prop) t p (d : Entry),
  Forall (fun pf => P (fst pf)) t -> P p ->
  Forall (fun pf => P (fst pf)) (tree_set t p d).
Proof.
  intros P t p d Ht Hp. induction t as [|[q e] r IH]; cbn [tree_set].
  - now constructor.
  - inversion Ht as [|? ? Hq Hr]; subst.
    destruct (path_ltb p q).
    + now repeat constructor.
    + destruct (path_eqb p q).
      * now constructor.
      * constructor; [exact Hq | exact (IH Hr)].
Qed.

(* -------------------------------------------------------------------------
   The image: the name tree, the inode table, the folder link counts
   ------------------------------------------------------------------------- *)

(** THE FILE SYSTEM.  Three tables, and only the first is a namespace:

    - [fs_tree], the names, sorted ([wf_fs]);
    - [fs_inodes], one row per regular file the run can still reach,
      keyed by inode number.  A number the tree names and the table has
      no row for reads as an EMPTY file with no name outside the image
      ([fs_inode]), which is why no image clause ties the two together;
    - [fs_dirs], one row per folder whose link counts the image states;
      a folder with no row has the counts [fs_dir_links] derives.

    A ROW MAY OUTLIVE EVERY NAME.  A file whose last name [unlinkat]
    removes while a descriptor holds it keeps its row, and the
    descriptor keeps reading and writing it ([State.FdFile] carries the
    inode number): that is Linux's open unlinked file, alive until the
    last [fput] ([iput_final], fs/inode.c:1874-1915; [inode_generic_drop]
    keeps an inode that has a link, include/linux/fs.h:3345-3348).
    [Open.close_spec] removes the descriptor and nothing else, so the
    row of such a file stays in the table after its last descriptor
    goes; nothing names it then and no arm can reach it.  A file with no
    name and no holder at the moment its last name goes has its row
    dropped there ([fs_unlink_file]). *)
Record Fs := mkFs {
  fs_tree : Tree;
  fs_inodes : list (ino * Inode);
  fs_dirs : list (path * DirLinks)
}.

#[global] Instance Fs_eq_dec : EqDecision Fs.
Proof. solve_decision. Defined.

(** An image with only names: no inode row and no folder row. *)
Definition fs_of_tree (t : Tree) : Fs := mkFs t [] [].

Definition fs_with_tree (fs : Fs) (t : Tree) : Fs :=
  mkFs t (fs_inodes fs) (fs_dirs fs).
Definition fs_with_inodes (fs : Fs) (t : list (ino * Inode)) : Fs :=
  mkFs (fs_tree fs) t (fs_dirs fs).
Definition fs_with_dirs (fs : Fs) (t : list (path * DirLinks)) : Fs :=
  mkFs (fs_tree fs) (fs_inodes fs) t.

Definition fs_lookup (fs : Fs) (p : path) : option Entry :=
  tree_lookup (fs_tree fs) p.

Definition fs_set (fs : Fs) (p : path) (e : Entry) : Fs :=
  fs_with_tree fs (tree_set (fs_tree fs) p e).

Definition fs_remove (fs : Fs) (p : path) : Fs :=
  fs_with_tree fs (tree_remove (fs_tree fs) p).

Definition fs_sorted (fs : Fs) : bool := tree_sorted (fs_tree fs).

Lemma fs_lookup_set_eq : forall fs p e,
  fs_lookup (fs_set fs p e) p = Some e.
Proof. intros fs p e. apply tree_lookup_set_eq. Qed.

Lemma fs_lookup_set_neq : forall fs p q e,
  path_eqb q p = false -> fs_lookup (fs_set fs p e) q = fs_lookup fs q.
Proof. intros fs p q e H. now apply tree_lookup_set_neq. Qed.

Lemma fs_set_sorted : forall fs p (d : Entry),
  fs_sorted fs = true -> fs_sorted (fs_set fs p d) = true.
Proof. intros fs p d H. now apply tree_set_sorted. Qed.

Lemma fs_remove_sorted : forall fs p,
  fs_sorted fs = true -> fs_sorted (fs_remove fs p) = true.
Proof. intros fs p H. now apply tree_remove_sorted. Qed.

(** Writing the inode table or the folder table leaves the names. *)
Lemma fs_lookup_with_inodes : forall fs t p,
  fs_lookup (fs_with_inodes fs t) p = fs_lookup fs p.
Proof. reflexivity. Qed.

Lemma fs_lookup_with_dirs : forall fs t p,
  fs_lookup (fs_with_dirs fs t) p = fs_lookup fs p.
Proof. reflexivity. Qed.

(* --- the inode table --- *)

Fixpoint itab_find (t : list (ino * Inode)) (i : ino) : option Inode :=
  match t with
  | [] => None
  | (j, n) :: r => if Z.eqb i j then Some n else itab_find r i
  end.

(** Insert-or-replace, in increasing inode order. *)
Fixpoint itab_put (t : list (ino * Inode)) (i : ino) (n : Inode)
    : list (ino * Inode) :=
  match t with
  | [] => [(i, n)]
  | (j, m) :: r =>
      if Z.ltb i j then (i, n) :: (j, m) :: r
      else if Z.eqb i j then (i, n) :: r
      else (j, m) :: itab_put r i n
  end.

Definition itab_drop (t : list (ino * Inode)) (i : ino) : list (ino * Inode) :=
  List.filter (fun jn => negb (Z.eqb (fst jn) i)) t.

Lemma itab_find_put_eq : forall t i n, itab_find (itab_put t i n) i = Some n.
Proof.
  induction t as [|[j m] r IH]; intros i n; cbn [itab_put itab_find].
  - now rewrite Z.eqb_refl.
  - destruct (Z.ltb i j); cbn [itab_find]; [now rewrite Z.eqb_refl|].
    destruct (Z.eqb i j) eqn:E; cbn [itab_find]; [now rewrite Z.eqb_refl|].
    rewrite E. apply IH.
Qed.

Lemma itab_find_put_neq : forall t i j n,
  Z.eqb j i = false -> itab_find (itab_put t i n) j = itab_find t j.
Proof.
  induction t as [|[k m] r IH]; intros i j n Hne; cbn [itab_put itab_find].
  - now rewrite Hne.
  - destruct (Z.ltb i k); cbn [itab_find]; [now rewrite Hne|].
    destruct (Z.eqb i k) eqn:E; cbn [itab_find].
    + apply Z.eqb_eq in E; subst k. now rewrite Hne.
    + destruct (Z.eqb j k); [reflexivity|]. now apply IH.
Qed.

Lemma itab_find_drop_eq : forall t i, itab_find (itab_drop t i) i = None.
Proof.
  induction t as [|[j m] r IH]; intros i; [reflexivity|].
  unfold itab_drop in *. cbn [List.filter fst].
  destruct (Z.eqb j i) eqn:E; cbn [negb].
  - apply IH.
  - cbn [itab_find]. rewrite Z.eqb_sym, E. apply IH.
Qed.

Lemma itab_find_drop_neq : forall t i j,
  Z.eqb j i = false -> itab_find (itab_drop t i) j = itab_find t j.
Proof.
  induction t as [|[k m] r IH]; intros i j Hne; [reflexivity|].
  unfold itab_drop in *. cbn [List.filter fst itab_find].
  destruct (Z.eqb k i) eqn:E; cbn [negb].
  - apply Z.eqb_eq in E; subst k. rewrite Hne. now apply IH.
  - cbn [itab_find]. destruct (Z.eqb j k); [reflexivity|]. now apply IH.
Qed.

(** The inode an inode number names: its row, or an EMPTY file with no
    name outside the image when the table has none.  This is what lets
    an image name an inode number the table leaves out, with no clause
    against it. *)
Definition empty_inode : Inode := mkInode [] 0.

Definition fs_inode (fs : Fs) (i : ino) : Inode :=
  match itab_find (fs_inodes fs) i with
  | Some n => n
  | None => empty_inode
  end.

(** A regular file's bytes. *)
Definition fs_ino_data (fs : Fs) (i : ino) : list byte := ino_data (fs_inode fs i).

Definition fs_put_inode (fs : Fs) (i : ino) (n : Inode) : Fs :=
  fs_with_inodes fs (itab_put (fs_inodes fs) i n).

(** Replace a regular file's bytes, keeping what its inode says of its
    other names.  Every write, truncate and truncating open goes through
    this, so a write through one name is seen through every other name
    and through every descriptor of the file. *)
Definition fs_set_ino_data (fs : Fs) (i : ino) (d : list byte) : Fs :=
  fs_put_inode fs i (mkInode d (ino_outside (fs_inode fs i))).

Definition fs_drop_inode (fs : Fs) (i : ino) : Fs :=
  fs_with_inodes fs (itab_drop (fs_inodes fs) i).

Lemma fs_ino_data_set_eq : forall fs i d,
  fs_ino_data (fs_set_ino_data fs i d) i = d.
Proof.
  intros fs i d. unfold fs_ino_data, fs_set_ino_data, fs_put_inode, fs_inode.
  cbn [fs_inodes fs_with_inodes]. now rewrite itab_find_put_eq.
Qed.

Lemma fs_ino_data_set_neq : forall fs i j d,
  Z.eqb j i = false -> fs_ino_data (fs_set_ino_data fs i d) j = fs_ino_data fs j.
Proof.
  intros fs i j d H. unfold fs_ino_data, fs_set_ino_data, fs_put_inode, fs_inode.
  cbn [fs_inodes fs_with_inodes]. now rewrite itab_find_put_neq.
Qed.

Lemma fs_lookup_set_ino_data : forall fs i d p,
  fs_lookup (fs_set_ino_data fs i d) p = fs_lookup fs p.
Proof. reflexivity. Qed.

Lemma fs_lookup_put_inode : forall fs i n p,
  fs_lookup (fs_put_inode fs i n) p = fs_lookup fs p.
Proof. reflexivity. Qed.

Lemma fs_lookup_drop_inode : forall fs i p,
  fs_lookup (fs_drop_inode fs i) p = fs_lookup fs p.
Proof. reflexivity. Qed.

Lemma fs_ino_data_set_name : forall fs p e i,
  fs_ino_data (fs_set fs p e) i = fs_ino_data fs i.
Proof. reflexivity. Qed.

Lemma fs_ino_data_remove_name : forall fs p i,
  fs_ino_data (fs_remove fs p) i = fs_ino_data fs i.
Proof. reflexivity. Qed.

(** Does entry [e] name inode [i]? *)
Definition entry_names_ino (i : ino) (e : Entry) : bool :=
  match e with
  | EFile j => Z.eqb i j
  | EDir | EDev _ | ELink _ => false
  end.

(** How many keys of the tree name inode [i]. *)
Definition fs_ino_names (fs : Fs) (i : ino) : nat :=
  length (List.filter (fun ke => entry_names_ino i (snd ke)) (fs_tree fs)).

(** A REGULAR FILE'S LINK COUNT, [i_nlink] as [generic_fillattr]
    reports it ([stat->nlink = inode->i_nlink], fs/stat.c:88): the names
    the image shows, plus the names it does not.  Each [unlinkat] of a
    name is one [drop_nlink] ([shmem_unlink], mm/shmem.c; ramfs's
    [simple_unlink], fs/libfs.c), and it is the removal of the key that
    lowers this by one; a file [openat] creates has one name and nothing
    outside, so one link. *)
Definition fs_ino_nlink (fs : Fs) (i : ino) : nat :=
  (fs_ino_names fs i + ino_outside (fs_inode fs i))%nat.

(** THE NEXT INODE NUMBER: one above every number the tree names and
    every row the table holds.  Deterministic, so two runs that create
    the same files in the same order produce equal images; and never a
    number a descriptor holds, because a held file keeps a name or a row
    ([fs_unlink_file]). *)
Fixpoint tree_max_ino (t : Tree) : Z :=
  match t with
  | [] => 0
  | (_, EFile j) :: r => Z.max j (tree_max_ino r)
  | _ :: r => tree_max_ino r
  end.

Fixpoint itab_max (t : list (ino * Inode)) : Z :=
  match t with
  | [] => 0
  | (j, _) :: r => Z.max j (itab_max r)
  end.

Definition fs_fresh_ino (fs : Fs) : ino :=
  (1 + Z.max (tree_max_ino (fs_tree fs)) (itab_max (fs_inodes fs)))%Z.

(** CREATE A REGULAR FILE at [k] holding [d]: a fresh inode, with no
    name outside the image, named by [k].  The entry at [k] is replaced
    if there is one; every caller has decided there is none. *)
Definition fs_create_file (fs : Fs) (k : path) (d : list byte) : Fs :=
  let i := fs_fresh_ino fs in
  fs_set (fs_put_inode fs i (mkInode d 0)) k (EFile i).

(** REMOVE THE NAME [k] of inode [i], [held] saying whether a descriptor
    still holds the file.  The name goes.  If it was the file's last
    name in the image, the row stays when a descriptor holds the file
    (and is written if the file had none, so the next [fs_fresh_ino]
    cannot hand the number out again) and goes when none does: nothing
    the run does can reach that file afterwards. *)
Definition fs_unlink_file (fs : Fs) (k : path) (i : ino) (held : bool) : Fs :=
  let fs1 := fs_remove fs k in
  if Nat.eqb (fs_ino_names fs1 i) 0 then
    (if held then fs_put_inode fs1 i (fs_inode fs1 i)
     else fs_drop_inode fs1 i)
  else fs1.

Lemma fs_lookup_unlink_file : forall fs k i held p,
  fs_lookup (fs_unlink_file fs k i held) p = fs_lookup (fs_remove fs k) p.
Proof.
  intros fs k i held p. unfold fs_unlink_file. cbv zeta.
  destruct (Nat.eqb (fs_ino_names (fs_remove fs k) i) 0); [destruct held|]; reflexivity.
Qed.

Lemma fs_ino_data_unlink_file_held : forall fs k i j,
  fs_ino_data (fs_unlink_file fs k i true) j = fs_ino_data fs j.
Proof.
  intros fs k i j. unfold fs_unlink_file. cbv zeta.
  destruct (Nat.eqb (fs_ino_names (fs_remove fs k) i) 0); [|reflexivity].
  unfold fs_ino_data, fs_put_inode, fs_inode.
  cbn [fs_inodes fs_with_inodes fs_remove fs_with_tree].
  destruct (Z.eqb j i) eqn:E.
  - apply Z.eqb_eq in E; subst j. rewrite itab_find_put_eq.
    destruct (itab_find (fs_inodes fs) i); reflexivity.
  - rewrite itab_find_put_neq by exact E. reflexivity.
Qed.

(* -------------------------------------------------------------------------
   What a run is observed to leave
   ------------------------------------------------------------------------- *)

(** The inode numbers the tree names, each once, in KEY ORDER of its
    first name.  The tree is sorted ([wf_fs]), so this order is a
    function of the names alone. *)
Fixpoint tree_inos_acc (t : Tree) (acc : list ino) : list ino :=
  match t with
  | [] => rev acc
  | (_, EFile i) :: r =>
      if existsb (Z.eqb i) acc then tree_inos_acc r acc else tree_inos_acc r (i :: acc)
  | (_, EDir) :: r | (_, EDev _) :: r | (_, ELink _) :: r => tree_inos_acc r acc
  end.

Definition tree_inos (t : Tree) : list ino := tree_inos_acc t [].

(** [i]'s position in [order], counted from [n]. *)
Fixpoint ino_index (order : list ino) (i : ino) (n : Z) : Z :=
  match order with
  | [] => 0
  | j :: r => if Z.eqb i j then n else ino_index r i (n + 1)%Z
  end.

Definition entry_renum (order : list ino) (e : Entry) : Entry :=
  match e with
  | EFile i => EFile (ino_index order i 1)
  | EDir | EDev _ | ELink _ => e
  end.

(** THE FILE SYSTEM A RUN IS OBSERVED TO LEAVE: what [Run.sstep_exit]
    and [Run.sstep_killed] put in [ExitEv] and [KillEv], where the
    equivalence compares it with [=].  So it must be CANONICAL: two runs
    that Linux leaves in the same state must be observed equal, and
    [fs_observe] makes them so in two ways.

    - IT OBSERVES ONLY WHAT A NAME REACHES.  An inode row no name of the
      tree reaches is not observed.  At the end of a run the process's
      descriptors are gone ([do_exit] -> [exit_files], kernel/exit.c), so
      a file whose last name was removed while it was open is freed then
      ([iput_final], fs/inode.c:1874-1915), whether the run closed its
      descriptor first or not; the image keeps such a row after the last
      [close] ([Fs]'s note: [Open.close_spec] moves no inode), and this
      is where it stops counting.  A folder row of a key that is no
      longer a folder is dropped for the same reason.
    - IT OBSERVES NO INODE NUMBER THE RUN HAPPENED TO ALLOCATE.  Inode
      numbers are the model's ([ino]): [fs_fresh_ino] hands them out in
      the order files are created, so two runs that create the same files
      in different orders hold different numbers for them.  The
      observation renumbers every named inode by the key order of its
      first name ([tree_inos]), so what is compared is the names, the
      bytes and outside-name count each file holds, and which names share
      one file -- not which number it got.  ([st_ino] is the
      environment's and is not in the image at all.)

    The renumbered table is in increasing order and has one row per
    named inode; a named inode the table has no row for is observed as
    [empty_inode], what it reads as. *)
Definition fs_observe (fs : Fs) : Fs :=
  let order := tree_inos (fs_tree fs) in
  mkFs (map (fun ke => (fst ke, entry_renum order (snd ke))) (fs_tree fs))
       (map (fun i => (ino_index order i 1, fs_inode fs i)) order)
       (List.filter (fun kd => match tree_lookup (fs_tree fs) (fst kd) with
                               | Some EDir => true
                               | _ => false
                               end) (fs_dirs fs)).

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

(* =========================================================================
   THE PATH NAMESPACE

   Keys, one resolution function, well-formedness, the default image and
   the migration of a pre-namespace image.  Design note: issue #1011.

   Kernel citations in this section are to Linux v6.18.46 (commit
   1f99e9ab748fc5c32120de9c4eca31abfe54a4d5), by file, function and
   line: fs/namei.c's [link_path_walk] (:2441-2537), [walk_component]
   (:2134-2158), [handle_dots] (:2096-2132), [step_into] (:1984-2022),
   [follow_dotdot] (:2064-2094), [lookup_last] (:2647-2653),
   [may_open] (:3527-3584), [do_rmdir] (:4570-4622), [do_mkdirat]
   (:4474-4503), and fs/namei.c's [getname_flags] (:136-216) for the
   empty pathname (its -ENOENT at :168-170 and :202-205).
   ========================================================================= *)

(** The NUL byte.  A key holding one could not be named by a program:
    every pathname the specs see comes out of [State.read_cstr],
    which stops at the first NUL. *)
Definition path_nul_byte : byte := Z_to_bv 8 0.

(** The one byte this file interprets.  [Sys.Fs.Namei.slash_byte] is
    pinned equal to it, so moving either is a compile error. *)
Definition path_slash_byte : byte := Z_to_bv 8 47.

(** "." and ".." as COMPONENTS.  [Sys.Uapi.dot_path] and
    [Sys.Fs.Namei.dotdot_path] are pinned equal to these. *)
Definition dot_comp : path := [Z_to_bv 8 46].
Definition dotdot_comp : path := [Z_to_bv 8 46; Z_to_bv 8 46].

(** "proc" and "sys": the two first components under the root that put a
    pathname OUTSIDE the model.  See [ROutside]. *)
Definition proc_comp : path :=
  [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 99].
Definition sys_comp : path :=
  [Z_to_bv 8 115; Z_to_bv 8 121; Z_to_bv 8 115].

(** The root directory's key: the one-byte path "/". *)
Definition root : path := [path_slash_byte].

(** "/dev", the folder the two device entries live in.  It is a key
    like any other: [standard_root] holds it as an [EDir], [wf_fs]
    treats it as an ordinary directory, and [walk_comps] answers a
    name it does not find under it exactly as it answers one in any
    other folder.  What names it here is the validity clause
    [Run.devices_in_dev_subtree], which keeps every [EDev] entry in its
    subtree ([in_dev_subtree]).

    THE IMAGE DESCRIBES /dev COMPLETELY AT LAUNCH, AND THE KERNEL MAKES
    NO DEVICE NODE DURING THE RUN.  In Linux v6.18.46 a node appears in
    devtmpfs through [devtmpfs_create_node]
    (drivers/base/devtmpfs.c:129-154; the file's own summary at
    drivers/base/devtmpfs.c:7-10 reads "Every driver-core device which
    requests a device node, will add a node in this filesystem"), which
    [device_add] (drivers/base/core.c:3638) calls at
    drivers/base/core.c:3730 when a driver-core device with a device
    number is registered.  That is a kernel event, not an effect of any
    syscall this model answers, so a name the run finds absent under
    /dev stays absent unless the run itself creates it.  That the
    launch /dev holds no name the image does not declare is a premise
    about the launch environment, of the same kind as the header's NO
    CONCURRENT WRITER paragraph, and the model does not check it. *)
Definition dev_dir : path :=
  [Z_to_bv 8 47; Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 118].          (* /dev *)

(** The longest single component a directory entry may have.
    [Sys.Uapi.NAME_MAX] is pinned equal to it. *)
Definition name_max : nat := 255.

Lemma path_eq_dec : forall p q : path, {p = q} + {p <> q}.
Proof.
  intros p q. destruct (path_eqb p q) eqn:H.
  - left. now apply path_eqb_eq.
  - right. intros ->. rewrite path_eqb_refl in H. discriminate.
Qed.

(* -------------------------------------------------------------------------
   Splitting and joining
   ------------------------------------------------------------------------- *)

(** Split a path at every "/", keeping the EMPTY pieces: "/a//b" splits
    as ["", "a", "", "b"] and "a/" as ["a", ""].  Nothing is dropped and
    nothing is normalised — the walk skips the empty pieces as
    [link_path_walk] skips repeated separators, and the trailing empty
    piece is what [path_ends_slash] sees. *)
Fixpoint path_split_aux (acc : path) (p : path) : list path :=
  match p with
  | [] => [rev acc]
  | b :: r =>
      if bv_eqb b path_slash_byte
      then rev acc :: path_split_aux [] r
      else path_split_aux (b :: acc) r
  end.

Definition path_split (p : path) : list path := path_split_aux [] p.

(** Build an ABSOLUTE path out of components: each one preceded by "/".
    The empty list gives the empty path, which is why [key_of_comps]
    sends it to the root instead. *)
Fixpoint path_join (cs : list path) : path :=
  match cs with
  | [] => []
  | c :: r => path_slash_byte :: c ++ path_join r
  end.

(** The two steps of [path_split_aux], as rewrites: nothing below reduces
    the [if] by hand, because [cbn] would have to unfold [bv_eqb] and the
    byte constants to do it. *)
Lemma path_split_aux_slash : forall acc r,
  path_split_aux acc (path_slash_byte :: r) = rev acc :: path_split_aux [] r.
Proof. intros acc r. cbn [path_split_aux]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma path_split_aux_other : forall acc b r,
  bv_eqb b path_slash_byte = false ->
  path_split_aux acc (b :: r) = path_split_aux (b :: acc) r.
Proof. intros acc b r H. cbn [path_split_aux]. now rewrite H. Qed.

(** Joining is a left inverse of splitting, up to the leading "/" that
    splitting consumed.  Everything the key discipline below needs about
    the two rests on this one equation. *)
Lemma path_join_split_aux : forall p acc,
  path_join (path_split_aux acc p) = path_slash_byte :: rev acc ++ p.
Proof.
  induction p as [|b r IH]; intros acc.
  - cbn [path_split_aux path_join]. now rewrite app_nil_r.
  - destruct (bv_eqb b path_slash_byte) eqn:Hb.
    + apply bv_eqb_eq in Hb; subst b.
      rewrite path_split_aux_slash. cbn [path_join].
      rewrite IH. cbn [rev app]. reflexivity.
    + rewrite (path_split_aux_other acc b r Hb), IH. cbn [rev].
      rewrite <- app_assoc. reflexivity.
Qed.

Lemma path_join_split : forall p, path_join (path_split p) = path_slash_byte :: p.
Proof. intros p. unfold path_split. now rewrite path_join_split_aux. Qed.

(* -------------------------------------------------------------------------
   Components and the key discipline
   ------------------------------------------------------------------------- *)

(** A NAMEABLE COMPONENT: non-empty, not "." and not "..", and free of
    the two bytes no component may hold — "/" (it would be a second
    component) and NUL (no program could name it).  Length is NOT part
    of this: an over-long component is something the walk records
    ([wr_long]), not a malformed key. *)
(** A piece of a split that is a real component rather than the artefact
    of a leading, repeated or trailing separator. *)
Definition comp_nonempty (c : path) : bool := negb (Nat.eqb (length c) 0).

Definition comp_ok (c : path) : bool :=
  comp_nonempty c
  && negb (path_eqb c dot_comp)
  && negb (path_eqb c dotdot_comp)
  && negb (existsb (fun b => bv_eqb b path_slash_byte) c)
  && negb (existsb (fun b => bv_eqb b path_nul_byte) c).

(** A KEY of the map: an absolute canonical path.  It begins with "/",
    its components are separated by single "/", none is empty, "." or
    "..", none holds a NUL, and it does not end in "/".  The root is the
    one-byte key "/".

    This is the ONLY shape ever stored, which is what keeps [=] on the
    final map meaningful: "./x", "x" and "/work/x" name one key and not
    three. *)
Definition canonical_key (p : path) : bool :=
  match p with
  | [] => false
  | b :: rest =>
      bv_eqb b path_slash_byte
      && match rest with
         | [] => true
         | _ :: _ => forallb comp_ok (path_split rest)
         end
  end.

(** The components of a key, in order; [] for the root. *)
Definition key_comps (k : path) : list path :=
  List.filter comp_nonempty (path_split k).

(** The key a component list names. *)
Definition key_of_comps (cs : list path) : path :=
  match cs with
  | [] => root
  | _ :: _ => path_join cs
  end.

Lemma comp_ok_nonempty : forall c, comp_ok c = true -> comp_nonempty c = true.
Proof.
  intros c H. unfold comp_ok in H.
  repeat (apply Bool.andb_true_iff in H as [H ?]).
  exact H.
Qed.

Lemma comp_ok_no_slash : forall c b,
  comp_ok c = true -> In b c -> bv_eqb b path_slash_byte = false.
Proof.
  intros c b H Hin. unfold comp_ok in H.
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [_ H].
  apply Bool.negb_true_iff in H.
  destruct (bv_eqb b path_slash_byte) eqn:Hb; [|reflexivity].
  exfalso. apply Bool.not_true_iff_false in H. apply H.
  apply existsb_exists. now exists b.
Qed.

Lemma comp_ok_not_dot : forall c, comp_ok c = true -> path_eqb c dot_comp = false.
Proof.
  intros c H. unfold comp_ok in H.
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [_ H].
  now apply Bool.negb_true_iff in H.
Qed.

Lemma comp_ok_not_dotdot : forall c,
  comp_ok c = true -> path_eqb c dotdot_comp = false.
Proof.
  intros c H. unfold comp_ok in H.
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [_ H].
  now apply Bool.negb_true_iff in H.
Qed.

(** Splitting steps over a slash-free block without emitting anything. *)
Lemma path_split_aux_app_noslash : forall c acc rest,
  (forall b, In b c -> bv_eqb b path_slash_byte = false) ->
  path_split_aux acc (c ++ rest) = path_split_aux (rev c ++ acc) rest.
Proof.
  induction c as [|b c IH]; intros acc rest Hns; cbn [app path_split_aux rev].
  - reflexivity.
  - rewrite (Hns b (or_introl eq_refl)).
    rewrite IH by (intros x Hx; apply Hns; now right).
    now rewrite <- app_assoc.
Qed.

(** Splitting a JOIN gives the components back, behind the leading empty
    piece the absolute path's first "/" produces. *)
Lemma path_split_join : forall cs,
  Forall (fun c => comp_ok c = true) cs ->
  path_split (path_join cs) = [] :: cs.
Proof.
  induction cs as [|c cs IH]; intros Hall.
  - reflexivity.
  - inversion Hall as [|? ? Hc Hcs]; subst.
    cbn [path_join]. unfold path_split.
    rewrite path_split_aux_slash. cbn [rev]. f_equal.
    rewrite path_split_aux_app_noslash
      by (intros b Hb; exact (comp_ok_no_slash c b Hc Hb)).
    rewrite app_nil_r.
    destruct cs as [|c' cs'].
    + cbn [path_join path_split_aux]. now rewrite rev_involutive.
    + cbn [path_join]. rewrite path_split_aux_slash, rev_involutive. f_equal.
      specialize (IH Hcs). unfold path_split in IH.
      cbn [path_join] in IH. rewrite path_split_aux_slash in IH.
      cbn [rev] in IH. now inversion IH.
Qed.

(** List helpers this section needs and the standard library does not
    name in this shape. *)
Lemma in_removelast : forall {A} (l : list A) (x : A),
  In x (removelast l) -> In x l.
Proof.
  induction l as [|y l IH]; intros x H; [contradiction|].
  destruct l as [|z l]; cbn [removelast] in H; [contradiction|].
  destruct H as [->|H]; [now left|].
  right. now apply IH.
Qed.

Lemma filter_all_true : forall {A} (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros A f l. induction l as [|x l IH]; intros H; [reflexivity|].
  assert (Hx : f x = true) by (apply H; now left).
  change (List.filter f (x :: l))
    with (if f x then x :: List.filter f l else List.filter f l).
  rewrite Hx. f_equal. apply IH. intros y Hy. apply H. now right.
Qed.

Lemma Forall_filter_of_forallb : forall {A} (P f : A -> bool) (l : list A),
  forallb P l = true -> Forall (fun c => P c = true) (List.filter f l).
Proof.
  intros A P f l H. apply Forall_forall. intros x Hx.
  apply filter_In in Hx as [Hx _].
  rewrite forallb_forall in H. now apply H.
Qed.


(** Splitting an absolute path and dropping the empty pieces is
    splitting what follows the leading "/" and dropping them. *)
Lemma key_comps_split : forall p,
  key_comps (path_slash_byte :: p) = List.filter comp_nonempty (path_split p).
Proof.
  intros p. unfold key_comps, path_split.
  rewrite path_split_aux_slash. reflexivity.
Qed.

Lemma key_comps_ok : forall k,
  canonical_key k = true -> Forall (fun c => comp_ok c = true) (key_comps k).
Proof.
  intros [|b rest] H; [discriminate|].
  cbn [canonical_key] in H. apply Bool.andb_true_iff in H as [Hb H].
  apply bv_eqb_eq in Hb; subst b.
  rewrite key_comps_split.
  destruct rest as [|x r].
  - cbn. constructor.
  - apply Forall_forall. intros c Hc.
    apply filter_In in Hc as [Hin _].
    rewrite forallb_forall in H. now apply H.
Qed.

Lemma key_comps_of_comps : forall cs,
  Forall (fun c => comp_ok c = true) cs -> key_comps (key_of_comps cs) = cs.
Proof.
  intros [|c cs] Hall.
  - reflexivity.
  - unfold key_of_comps, key_comps.
    rewrite path_split_join by exact Hall.
    change (List.filter comp_nonempty (([] : path) :: c :: cs))
      with (List.filter comp_nonempty (c :: cs)).
    apply filter_all_true. intros x Hx.
    apply comp_ok_nonempty. rewrite Forall_forall in Hall. now apply Hall.
Qed.

Lemma canonical_key_of_comps : forall cs,
  Forall (fun c => comp_ok c = true) cs -> canonical_key (key_of_comps cs) = true.
Proof.
  intros [|c cs] Hall.
  - reflexivity.
  - inversion Hall as [|? ? Hc Hcs]; subst.
    assert (Hsp : path_split (path_join (c :: cs)) = [] :: c :: cs)
      by (now apply path_split_join).
    assert (HX : path_split (c ++ path_join cs) = c :: cs).
    { cbn [path_join] in Hsp. unfold path_split in Hsp.
      rewrite path_split_aux_slash in Hsp. cbn [rev] in Hsp.
      now inversion Hsp. }
    assert (Hne : c ++ path_join cs <> []).
    { intros Hnil. apply app_eq_nil in Hnil as [Hc0 _].
      rewrite Hc0 in Hc. discriminate. }
    unfold key_of_comps. cbn [path_join canonical_key].
    destruct (c ++ path_join cs) as [|y ys] eqn:Hy; [exfalso; now apply Hne|].
    rewrite bv_eqb_refl. cbn [andb].
    rewrite HX. cbn [forallb]. rewrite Hc. cbn [andb].
    apply forallb_forall. intros x Hx.
    rewrite Forall_forall in Hcs. now apply Hcs.
Qed.

Lemma key_of_comps_comps : forall k,
  canonical_key k = true -> key_of_comps (key_comps k) = k.
Proof.
  intros [|b rest] H; [discriminate|].
  cbn [canonical_key] in H. apply Bool.andb_true_iff in H as [Hb H].
  apply bv_eqb_eq in Hb; subst b.
  rewrite key_comps_split.
  destruct rest as [|x r]; [reflexivity|].
  assert (Hid : List.filter comp_nonempty (path_split (x :: r)) = path_split (x :: r)).
  { apply filter_all_true. intros z Hz.
    apply comp_ok_nonempty. rewrite forallb_forall in H. now apply H. }
  rewrite Hid.
  assert (Hne : path_split (x :: r) <> []).
  { unfold path_split. destruct (bv_eqb x path_slash_byte) eqn:Hx.
    - apply bv_eqb_eq in Hx; subst x. rewrite path_split_aux_slash. discriminate.
    - rewrite (path_split_aux_other [] x r Hx).
      generalize ([x] : path). clear.
      induction r as [|z zs IH]; intros acc; [discriminate|].
      destruct (bv_eqb z path_slash_byte) eqn:Hz.
      + apply bv_eqb_eq in Hz; subst z. rewrite path_split_aux_slash. discriminate.
      + rewrite (path_split_aux_other acc z zs Hz). apply IH. }
  destruct (path_split (x :: r)) as [|c cs] eqn:Hsp; [exfalso; now apply Hne|].
  unfold key_of_comps.
  pose proof (path_join_split (x :: r)) as Hj. rewrite Hsp in Hj. exact Hj.
Qed.

(* -------------------------------------------------------------------------
   Parents and children
   ------------------------------------------------------------------------- *)

(** The key of [k]'s parent directory.  The root's parent is the root,
    which is what [follow_dotdot] does when it is already there. *)
Definition path_parent (k : path) : path :=
  key_of_comps (removelast (key_comps k)).

(** The key of [k]'s child named [c]. *)
Definition child_key (k : path) (c : path) : path :=
  key_of_comps (key_comps k ++ [c]).

Lemma path_parent_root : path_parent root = root.
Proof. reflexivity. Qed.

Lemma canonical_key_root : canonical_key root = true.
Proof. reflexivity. Qed.

Lemma removelast_forall : forall {A} (P : A -> Prop) (l : list A),
  Forall P l -> Forall P (removelast l).
Proof.
  intros A P l H. apply Forall_forall. intros x Hx.
  rewrite Forall_forall in H. apply H.
  apply (in_removelast _ _ Hx).
Qed.

Lemma canonical_key_parent : forall k,
  canonical_key k = true -> canonical_key (path_parent k) = true.
Proof.
  intros k H. unfold path_parent. apply canonical_key_of_comps.
  apply removelast_forall. now apply key_comps_ok.
Qed.

Lemma canonical_key_child : forall k c,
  canonical_key k = true -> comp_ok c = true ->
  canonical_key (child_key k c) = true.
Proof.
  intros k c Hk Hc. unfold child_key. apply canonical_key_of_comps.
  apply Forall_app. split; [now apply key_comps_ok | now constructor].
Qed.

Lemma path_parent_child : forall k c,
  canonical_key k = true -> comp_ok c = true ->
  path_parent (child_key k c) = k.
Proof.
  intros k c Hk Hc. unfold path_parent, child_key.
  rewrite key_comps_of_comps
    by (apply Forall_app; split; [now apply key_comps_ok | now constructor]).
  rewrite removelast_last. now apply key_of_comps_comps.
Qed.

(* -------------------------------------------------------------------------
   The ancestor chain
   ------------------------------------------------------------------------- *)

Fixpoint inits {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: r => [] :: map (cons x) (inits r)
  end.

(** Every ancestor of [k], the root first, [k] itself last. *)
Definition key_chain (k : path) : list path :=
  map key_of_comps (inits (key_comps k)).

Lemma inits_self : forall {A} (l : list A), In l (inits l).
Proof.
  induction l as [|x r IH]; cbn [inits]; [now left|].
  right. apply in_map. exact IH.
Qed.

Lemma inits_prefix : forall {A} (l cs : list A),
  In cs (inits l) -> exists r, l = cs ++ r.
Proof.
  induction l as [|x l IH]; intros cs H; cbn [inits] in H.
  - destruct H as [<-|[]]. now exists [].
  - destruct H as [<-|H]; [now exists (x :: l)|].
    apply in_map_iff in H as [cs' [<- Hcs']].
    destruct (IH cs' Hcs') as [r ->]. now exists r.
Qed.

Lemma inits_removelast : forall {A} (l cs : list A),
  In cs (inits l) -> cs = [] \/ In (removelast cs) (inits l).
Proof.
  induction l as [|x l IH]; intros cs H; cbn [inits] in H.
  - destruct H as [<-|[]]. now left.
  - destruct H as [<-|H]; [now left|].
    apply in_map_iff in H as [cs' [<- Hcs']].
    right. destruct cs' as [|y cs''].
    + cbn [removelast]. now left.
    + cbn [removelast]. cbn [inits]. right. apply in_map.
      destruct (IH (y :: cs'') Hcs') as [Hnil|Hin]; [discriminate|exact Hin].
Qed.

Lemma key_chain_self : forall k,
  canonical_key k = true -> In k (key_chain k).
Proof.
  intros k Hk. unfold key_chain.
  rewrite <- (key_of_comps_comps k Hk) at 1.
  apply in_map. apply inits_self.
Qed.

Lemma key_chain_root : forall k, In root (key_chain k).
Proof.
  intros k. unfold key_chain.
  change root with (key_of_comps ([] : list path)).
  apply in_map. destruct (key_comps k) as [|x r]; cbn [inits]; now left.
Qed.

Lemma key_chain_canonical : forall k q,
  canonical_key k = true -> In q (key_chain k) -> canonical_key q = true.
Proof.
  intros k q Hk Hq. unfold key_chain in Hq.
  apply in_map_iff in Hq as [cs [<- Hcs]].
  apply canonical_key_of_comps.
  destruct (inits_prefix _ _ Hcs) as [r Hr].
  pose proof (key_comps_ok k Hk) as Hall. rewrite Hr in Hall.
  now apply Forall_app in Hall as [Hall _].
Qed.

(** The chain is PREFIX CLOSED: the parent of every key in it is in it. *)
Lemma key_chain_parent : forall k q,
  canonical_key k = true -> In q (key_chain k) ->
  In (path_parent q) (key_chain k).
Proof.
  intros k q Hk Hq. unfold key_chain in Hq |- *.
  apply in_map_iff in Hq as [cs [<- Hcs]].
  assert (Hall : Forall (fun c => comp_ok c = true) cs).
  { destruct (inits_prefix _ _ Hcs) as [r Hr].
    pose proof (key_comps_ok k Hk) as H. rewrite Hr in H.
    now apply Forall_app in H as [H _]. }
  unfold path_parent. rewrite key_comps_of_comps by exact Hall.
  destruct (inits_removelast _ _ Hcs) as [->|Hin].
  - cbn [removelast]. apply key_chain_root.
  - now apply in_map.
Qed.

(* -------------------------------------------------------------------------
   Well-formedness
   ------------------------------------------------------------------------- *)

(** Is [k]'s parent a directory in [fs]?  The root's parent is the root,
    and the root's own clause is [fs_root_is_dir], so the root is
    exempted here rather than made to be its own parent's directory. *)
Definition parent_is_dir (fs : Fs) (k : path) : bool :=
  path_eqb k root
  || match fs_lookup fs (path_parent k) with
     | Some EDir => true
     | _ => false
     end.

Definition fs_root_is_dir (fs : Fs) : bool :=
  match fs_lookup fs root with
  | Some EDir => true
  | _ => false
  end.

(** THE IMAGE PREDICATE, executable.  This is the first image predicate
    with a boolean twin: a fixture's validity is decided by computation
    ([wf_fsb _ = true] by [vm_compute]) rather than argued, which is what
    the satisfiability pins in
    theories/LinuxProcessSem/Checks/Cases/Fs/Resolve.v rest on. *)
Definition wf_fsb (fs : Fs) : bool :=
  fs_sorted fs
  && forallb (fun ke => canonical_key (fst ke)) (fs_tree fs)
  && fs_root_is_dir fs
  && forallb (fun ke => parent_is_dir fs (fst ke)) (fs_tree fs).

(** THE IMAGE PREDICATE.  Four clauses, all on the NAME TREE, and each
    one is load-bearing:

    - SORTED, so the final image compares with [=] inside a trace event
      (the canonical-form note at the head of this file);
    - every key CANONICAL, so one name is one key;
    - the ROOT is a directory, so every absolute walk has somewhere to
      start;
    - every key's PARENT is a directory, so a walk that reaches a key
      reaches it through directories, and [RNotDir] is the only way a
      non-directory can stop one.

    NOTHING IS ASKED OF THE INODE TABLE OR THE FOLDER TABLE: every row
    and every missing row means something ([fs_inode], [fs_dir_links]),
    so there is no image the two tables could make inconsistent.  A
    link's body is any bytes ([ELink]).

    It replaced the old validity predicate and the name ladder around
    it, both of which are deleted: the NUL-free
    clause is inside [canonical_key], and the "keys are relative"
    conjunct that made the device arms' guards unreachable is gone with
    the arms it protected. *)
Definition wf_fs (fs : Fs) : Prop :=
  fs_sorted fs = true
  /\ Forall (fun ke => canonical_key (fst ke) = true) (fs_tree fs)
  /\ fs_lookup fs root = Some EDir
  /\ Forall (fun ke => parent_is_dir fs (fst ke) = true) (fs_tree fs).

Lemma fs_root_is_dir_iff : forall fs,
  fs_root_is_dir fs = true <-> fs_lookup fs root = Some EDir.
Proof.
  intros fs. unfold fs_root_is_dir.
  destruct (fs_lookup fs root) as [[d| |k|b]|]; split; intros H;
    try discriminate; try reflexivity; try congruence.
Qed.

(** THE BRIDGE.  Everything that decides an image by computation goes
    through this; everything that reasons about one uses [wf_fs]. *)
Lemma wf_fsb_iff : forall fs, wf_fsb fs = true <-> wf_fs fs.
Proof.
  intros fs. unfold wf_fsb, wf_fs.
  rewrite !Bool.andb_true_iff.
  rewrite fs_root_is_dir_iff.
  rewrite !(forallb_forall).
  split.
  - intros [[[H1 H2] H3] H4]. repeat split; try assumption;
      apply Forall_forall; assumption.
  - intros [H1 [H2 [H3 H4]]]. rewrite Forall_forall in H2, H4.
    repeat split; assumption.
Qed.

(** An image with the same NAMES is well formed when this one is: the
    predicate reads the tree alone. *)
Lemma wf_fs_same_tree : forall fs fs',
  fs_tree fs' = fs_tree fs -> wf_fs fs -> wf_fs fs'.
Proof.
  intros fs fs' H Hwf. unfold wf_fs, fs_sorted, parent_is_dir, fs_lookup in *.
  rewrite H. exact Hwf.
Qed.

(* -------------------------------------------------------------------------
   Folder link counts
   ------------------------------------------------------------------------- *)

Fixpoint dtab_find (t : list (path * DirLinks)) (k : path) : option DirLinks :=
  match t with
  | [] => None
  | (q, d) :: r => if path_eqb k q then Some d else dtab_find r k
  end.

Fixpoint dtab_put (t : list (path * DirLinks)) (k : path) (d : DirLinks)
    : list (path * DirLinks) :=
  match t with
  | [] => [(k, d)]
  | (q, e) :: r =>
      if path_ltb k q then (k, d) :: (q, e) :: r
      else if path_eqb k q then (k, d) :: r
      else (q, e) :: dtab_put r k d
  end.

Definition dtab_drop (t : list (path * DirLinks)) (k : path)
    : list (path * DirLinks) :=
  List.filter (fun qd => negb (path_eqb (fst qd) k)) t.

(** How many folders the tree shows DIRECTLY under [k].  The root is its
    own parent ([path_parent_root]) and is not its own subfolder. *)
Definition fs_nsubdirs (fs : Fs) (k : path) : nat :=
  length (List.filter
            (fun ke => match snd ke with
                       | EDir => path_eqb (path_parent (fst ke)) k
                                 && negb (path_eqb (fst ke) root)
                       | EFile _ | EDev _ | ELink _ => false
                       end)
            (fs_tree fs)).

(** A FOLDER'S COUNT UNDER EACH RULE.  A folder the image gives a row
    has the counts the row holds; a folder with none has the count a
    counting file system gives a folder whose subfolders are all in the
    image (two, plus one per subfolder: the [inc_nlink]s cited at
    [DirLinks]), and 1 under the fixed rule.  So an image says nothing
    of a folder whose counts are the ones its own tree implies, and a
    folder whose count also reflects names the image leaves out -- the
    root, whose [/proc] and [/sys] mountpoints are folders of the root
    file system -- takes a row. *)
Definition fs_dir_links (fs : Fs) (k : path) : DirLinks :=
  match dtab_find (fs_dirs fs) k with
  | Some d => d
  | None => mkDirLinks (2 + fs_nsubdirs fs k)%nat 1
  end.

(** The count past which the model declines the [mkdirat] that would take
    a folder's counting count further ([Sys.Fs.Namei.mkdirat_body_spec]).
    The number is ext4's [EXT4_LINK_MAX] (fs/ext4/ext4.h:328, Linux
    v6.18.46), past which an indexed ext4 folder's count switches to 1
    (fs/ext4/namei.c:2754-2760).  tmpfs and ramfs, the file systems of
    the configuration of record (SCOPE.md), have no such switch and no
    [s_max_links], so [vfs_mkdir] (fs/namei.c) sets them no limit and
    every supported kernel goes on counting: the decline is a
    fail-closed gap, priority 3 only. *)
Definition dir_count_max : nat := 65000.

(** A subfolder is made under [k]: the counting count of a folder with
    a row goes up by one, and the fixed count stays.  A folder with no
    row derives both from the tree, which the new key moves. *)
Definition fs_dir_add_sub (fs : Fs) (k : path) : Fs :=
  match dtab_find (fs_dirs fs) k with
  | Some d => fs_with_dirs fs (dtab_put (fs_dirs fs) k
                                (mkDirLinks (S (dl_counting d)) (dl_fixed d)))
  | None => fs
  end.

(** A subfolder of [k] is removed: the counting count goes down by one
    ([drop_nlink(dir)] in [shmem_rmdir] at mm/shmem.c:4037-4038, and in
    ramfs's [simple_rmdir] at fs/libfs.c:806). *)
Definition fs_dir_drop_sub (fs : Fs) (k : path) : Fs :=
  match dtab_find (fs_dirs fs) k with
  | Some d => fs_with_dirs fs (dtab_put (fs_dirs fs) k
                                (mkDirLinks (pred (dl_counting d)) (dl_fixed d)))
  | None => fs
  end.

(** MAKE THE FOLDER [k]: the name, its parent's count, and no row of its
    own, so it starts at 2 under the counting rule and 1 under the fixed
    one ([fs_dir_links]).  A row a removed name left at [k] goes. *)
Definition fs_mkdir (fs : Fs) (k : path) : Fs :=
  let fs1 := fs_dir_add_sub fs (path_parent k) in
  fs_set (fs_with_dirs fs1 (dtab_drop (fs_dirs fs1) k)) k EDir.

(** REMOVE THE FOLDER [k]: the name, its row, and its parent's count. *)
Definition fs_rmdir (fs : Fs) (k : path) : Fs :=
  let fs1 := fs_dir_drop_sub fs (path_parent k) in
  fs_remove (fs_with_dirs fs1 (dtab_drop (fs_dirs fs1) k)) k.

Lemma fs_tree_dir_add_sub : forall fs k, fs_tree (fs_dir_add_sub fs k) = fs_tree fs.
Proof. intros fs k. unfold fs_dir_add_sub. now destruct (dtab_find (fs_dirs fs) k). Qed.

Lemma fs_tree_dir_drop_sub : forall fs k, fs_tree (fs_dir_drop_sub fs k) = fs_tree fs.
Proof. intros fs k. unfold fs_dir_drop_sub. now destruct (dtab_find (fs_dirs fs) k). Qed.

Lemma fs_inodes_dir_add_sub : forall fs k,
  fs_inodes (fs_dir_add_sub fs k) = fs_inodes fs.
Proof. intros fs k. unfold fs_dir_add_sub. now destruct (dtab_find (fs_dirs fs) k). Qed.

Lemma fs_inodes_dir_drop_sub : forall fs k,
  fs_inodes (fs_dir_drop_sub fs k) = fs_inodes fs.
Proof. intros fs k. unfold fs_dir_drop_sub. now destruct (dtab_find (fs_dirs fs) k). Qed.

Lemma fs_tree_mkdir : forall fs k,
  fs_tree (fs_mkdir fs k) = fs_tree (fs_set fs k EDir).
Proof.
  intros fs k. unfold fs_mkdir, fs_set, fs_with_tree, fs_with_dirs. cbn [fs_tree].
  now rewrite fs_tree_dir_add_sub.
Qed.

Lemma fs_tree_rmdir : forall fs k,
  fs_tree (fs_rmdir fs k) = fs_tree (fs_remove fs k).
Proof.
  intros fs k. unfold fs_rmdir, fs_remove, fs_with_tree, fs_with_dirs. cbn [fs_tree].
  now rewrite fs_tree_dir_drop_sub.
Qed.

Lemma fs_lookup_mkdir : forall fs k p,
  fs_lookup (fs_mkdir fs k) p = fs_lookup (fs_set fs k EDir) p.
Proof. intros fs k p. unfold fs_lookup. now rewrite fs_tree_mkdir. Qed.

Lemma fs_lookup_rmdir : forall fs k p,
  fs_lookup (fs_rmdir fs k) p = fs_lookup (fs_remove fs k) p.
Proof. intros fs k p. unfold fs_lookup. now rewrite fs_tree_rmdir. Qed.

Lemma fs_inodes_mkdir : forall fs k, fs_inodes (fs_mkdir fs k) = fs_inodes fs.
Proof.
  intros fs k. unfold fs_mkdir, fs_set, fs_with_tree, fs_with_dirs. cbn [fs_inodes].
  now rewrite fs_inodes_dir_add_sub.
Qed.

Lemma fs_inodes_rmdir : forall fs k, fs_inodes (fs_rmdir fs k) = fs_inodes fs.
Proof.
  intros fs k. unfold fs_rmdir, fs_remove, fs_with_tree, fs_with_dirs. cbn [fs_inodes].
  now rewrite fs_inodes_dir_drop_sub.
Qed.

(* -------------------------------------------------------------------------
   One resolution function
   ------------------------------------------------------------------------- *)

(** The LAST COMPONENT'S TYPE, which [link_path_walk] computes textually
    ([last_type], fs/namei.c:2475-2486) and [do_rmdir] switches on BEFORE
    it looks anything up.  Trailing separators do not change which
    component is the last one, so they do not change this; a path with no
    component at all (the root, "//", and the empty pathname every arm
    answers ahead of resolution) is [LastRoot] (fs/namei.c:2446,
    :2455-2458). *)
Inductive LastKind := LastNorm | LastDot | LastDotDot | LastRoot.

(** WHAT A PATHNAME RESOLVES TO.  Linux v6.18.46, fs/namei.c throughout.

    - [RFound k e]: the walk ended standing on the key [k], which holds
      [e] ([path_lookupat] :2664-2695).  [e] is an [ELink] only when the
      caller asked not to follow the last component.
    - [RMissing par nm]: the LAST name [nm] is absent from the folder
      [par] (a negative dentry, [step_into] -> [handle_mounts]
      :1989-1992 -> [traverse_mounts] :1537-1538).  The name may be a
      followed link body's last name, which is where [O_CREAT] creates
      ([lookup_open] :3788-3800).
    - [RNotDir k]: a component (or a trailing separator, or the caller's
      folder demand) met the non-folder at [k] (:2529-2535, :2685-2687).
    - [RAbsent k]: a name that is NOT the last one is absent; [k] is its
      key.
    - [RLoop]: the 41st link to follow ([reserve_stack]'s
      [total_link_count++ >= MAXSYMLINKS], :1878-1879, with
      [MAXSYMLINKS] 40 at include/linux/namei.h:13).
    - [ROutside]: "proc" or "sys" looked up while the walk stands on the
      root, whatever spelling or link led there.  Every arm declines it:
      procfs and sysfs are not in the image.
    - [RParent dir nm]: the walk stopped IN FRONT of its last name [nm],
      standing on the folder [dir], without looking [nm] up.  The parent
      end of [path_parentat] (:2719-2733), which [unlinkat], [rmdir] and
      [mkdirat] walk; and, for [open] with [O_CREAT], a last normal name
      followed by a separator, which [lookup_fast_for_open] refuses with
      -EISDIR before any lookup (:3821-3823).  [nm] is empty when the
      path has no component at all.

    An over-long component is not an outcome: the length limit belongs
    to the file system's [->lookup], not to fs/namei.c, so the walk goes
    on as a file system with a larger limit would, and records that the
    limit was crossed ([wr_long]); the arms admit -ENAMETOOLONG beside
    that answer (see [WalkRes]).  No supported kernel gives the other
    answer: tmpfs and ramfs both refuse at [simple_lookup] (see
    [comp_too_long]). *)
Inductive Resolved :=
  | RFound   (key : path) (e : Entry)
  | RMissing (parent : path) (name : path)
  | RNotDir  (key : path)
  | RAbsent  (prefix : path)
  | RLoop
  | ROutside
  | RParent  (dir : path) (name : path).

(** Are all the remaining pieces empty?  Trailing separators leave empty
    pieces behind them, and they do not make a component the
    second-to-last one. *)
Definition comps_done (cs : list path) : bool := forallb (fun c => negb (comp_nonempty c)) cs.

(** IS THIS KEY IN THE /dev SUBTREE?  [dev_dir] itself, or anything
    beneath it, and nothing else.  The walk does not read it; the
    validity clause [Run.devices_in_dev_subtree] does, to keep every
    device entry under /dev.

    It is decided through [key_chain], so the comparison is COMPONENT BY
    COMPONENT and not byte by byte: "/devices" and "/devil" are ordinary
    keys, and "/dev/pts/0" is in the subtree however deep it sits.  A
    byte-prefix test would report the first two, which is the shape a
    reader will assume this has. *)
Definition in_dev_subtree (k : path) : bool :=
  existsb (path_eqb dev_dir) (key_chain k).

(** The two directions worth stating, both by computation: the
    directory itself is in its own subtree, and the root is not. *)
Lemma in_dev_subtree_dev : in_dev_subtree dev_dir = true.
Proof. reflexivity. Qed.

Lemma in_dev_subtree_root : in_dev_subtree root = false.
Proof. reflexivity. Qed.

(** A component's type, as [link_path_walk] classifies it
    (fs/namei.c:2475-2486). *)
Definition comp_kind (c : path) : LastKind :=
  if path_eqb c dot_comp then LastDot
  else if path_eqb c dotdot_comp then LastDotDot
  else LastNorm.

(** Is a separator left after the last component?  [last.name[last.len]]
    in the kernel: a remaining piece exists only when a "/" followed. *)
Definition comps_trailing (r : list path) : bool :=
  match r with [] => false | _ :: _ => true end.

(** The component in front of [r] is the LAST one and a separator follows
    it: what [lookup_last] tests to force the follow and demand a folder
    (fs/namei.c:2649-2650) and what [lookup_fast_for_open] tests under
    [O_CREAT] (:3821-3823). *)
Definition last_slash (r : list path) : bool := comps_done r && comps_trailing r.

(** "proc" or "sys" looked up at the root: outside the model. *)
Definition at_outside (k c : path) : bool :=
  path_eqb k root && (path_eqb c proc_comp || path_eqb c sys_comp).

(** Over [NAME_MAX] (include/uapi/linux/limits.h:12): the file system's
    [->lookup] refuses it with -ENAMETOOLONG ([simple_lookup] at
    fs/libfs.c:71-72, the lookup of tmpfs (mm/shmem.c:5285) and of ramfs
    (fs/ramfs/inode.c:193), the file systems of the configuration of
    record: SCOPE.md).  The walk admits the answer of a file system with
    a larger limit beside it ([wr_long]), which no supported kernel
    gives: a priority-2 gap, and sound (SCOPE.md, "Known gaps in
    precision"). *)
Definition comp_too_long (c : path) : bool := Nat.ltb name_max (length c).

(** The same, for a last name the parent end hands to its arm: "." and
    ".." are never looked up, so never refused for length. *)
Definition norm_too_long (c : path) : bool :=
  match comp_kind c with LastNorm => comp_too_long c | _ => false end.

(** A LINK BODY AS THE WALK READS IT: the bytes up to the first NUL, as
    [vfs_readlink] measures it ([strlen(link)], fs/namei.c:5469). *)
Fixpoint link_text (b : path) : path :=
  match b with
  | [] => []
  | x :: r => if bv_eqb x path_nul_byte then [] else x :: link_text r
  end.

(** Does a pathname start at the root? *)
Definition path_absolute (p : path) : bool :=
  match p with b :: _ => bv_eqb b path_slash_byte | [] => false end.

(** Where a followed body is walked from: the root for an absolute body
    (fs/namei.c:1962-1967, in [pick_link], which calls [nd_jump_root]),
    else the folder that holds the link, because [step_into] hands
    [pick_link] the body without moving the walk (:2013-2021).  An empty
    body is walked from that folder too and leaves the walk there
    (:1957-1958, :1969-1973). *)
Definition link_start (k : path) (b : path) : path :=
  if path_absolute (link_text b) then root else k.

(** [MAXSYMLINKS], include/linux/namei.h:13. *)
Definition link_max : nat := 40.

(** WHAT THE CALLER ASKS OF THE END OF THE WALK.

    - [WalkFull follow dir]: [path_lookupat] (fs/namei.c:2664-2695) and
      [open] without [O_CREAT]: the last link is followed iff [follow]
      ([LOOKUP_FOLLOW]), and [dir] ([LOOKUP_DIRECTORY]) demands a folder
      at the end.
    - [WalkCreate follow]: [open] with [O_CREAT]: as above, except that a
      last normal name followed by a separator stops the walk in front of
      it (-EISDIR before any lookup, :3821-3823).
    - [WalkParent]: [path_parentat] (:2719-2733): the last name is never
      looked up or followed. *)
Inductive WalkMode :=
  | WalkFull (follow dir : bool)
  | WalkCreate (follow : bool)
  | WalkParent.

Definition mode_parent (md : WalkMode) : bool :=
  match md with WalkParent => true | _ => false end.
Definition mode_create (md : WalkMode) : bool :=
  match md with WalkCreate _ => true | _ => false end.
Definition mode_follow (md : WalkMode) : bool :=
  match md with WalkFull f _ | WalkCreate f => f | WalkParent => false end.
Definition mode_dir (md : WalkMode) : bool :=
  match md with WalkFull _ d => d | _ => false end.

(** WHAT A WALK ANSWERS: the outcome, the type and trailing separator of
    the last component it walked (a followed body's last name included),
    and two facts the arms turn into ADMITTED errnos beside the outcome:

    - [wr_followed]: a link was followed.  Every follow also admits
      -ELOOP: a [nosymfollow] mount refuses it ([pick_link],
      fs/namei.c:1927-1929), and the link count is not reset when the
      kernel repeats a walk after an RCU -ECHILD ([filename_lookup]
      :2705-2709, [__filename_parentat] :2747-2751; [path_init] does not
      reset [total_link_count], which only :671 sets), so a chain of 40
      or fewer may still meet the limit.
    - [wr_long]: a component over [name_max] was handed to a file
      system's [->lookup] (see [comp_too_long]): -ENAMETOOLONG is
      admitted beside the answer a larger limit would give, which no
      supported kernel gives. *)
Record WalkRes := mkWalkRes {
  wr_res : Resolved;
  wr_kind : LastKind;
  wr_slash : bool;
  wr_followed : bool;
  wr_long : bool
}.

Definition upd_kind (r : list path) (c : path) (lk : LastKind) : LastKind :=
  if comps_done r then comp_kind c else lk.
Definition upd_slash (r : list path) (ts : bool) : bool :=
  if comps_done r then last_slash r else ts.

(** Must the entry just found be followed?  A link that is not the last
    component always is ([WALK_MORE] or flags 0, fs/namei.c:2516,
    :2519); the last one is followed iff [LOOKUP_FOLLOW] is set
    (:1994-1996). *)
Definition link_needed (e : Entry) (r : list path) (f : bool) : bool :=
  match e with ELink _ => negb (comps_done r) || f | _ => false end.

(** What the walk does with a link it must follow: [None] once the
    budget is spent. *)
Definition FollowK : Type :=
  bool -> bool -> path -> Entry -> list path -> LastKind -> bool -> bool -> WalkRes.

(** THE WALK OVER ONE STRING OF COMPONENTS, exactly in [link_path_walk]'s
    order (fs/namei.c:2441-2537) and with no textual pre-normalisation.
    [k] is the key the walk stands on and [e] its entry; [cs] the pieces
    still to walk, a followed body's spliced in front ([nd->stack],
    :2515, :2525-2526); [f] and [d] are [LOOKUP_FOLLOW] and
    [LOOKUP_DIRECTORY], which stay set once set (:2650, :3831); [lk] and
    [ts] the last component's type and separator so far; [fd] and [lg]
    the two admitted facts of [WalkRes].

    The rules, each in the order the kernel applies them, are stated
    once more as the relations [walk_step] and [walk_end] below, and
    [walk_from_spec] proves the two agree. *)
Fixpoint walk_comps (fs : Fs) (md : WalkMode) (fd : bool) (next : option FollowK)
    (f d : bool) (k : path) (e : Entry) (cs : list path)
    (lk : LastKind) (ts lg : bool) : WalkRes :=
  match cs with
  | [] =>
      if mode_parent md then
        match e with
        | EDir => mkWalkRes (RParent k []) LastRoot false fd lg
        | _ => mkWalkRes (RNotDir k) lk ts fd lg
        end
      else
        mkWalkRes
          (match e with
           | EDir => RFound k EDir
           | _ => if d then RNotDir k else RFound k e
           end) lk ts fd lg
  | c :: r =>
      if negb (comp_nonempty c) then walk_comps fs md fd next f d k e r lk ts lg
      else
        match e with
        | EDir =>
            if mode_parent md && comps_done r then
              mkWalkRes (RParent k c) (comp_kind c) (last_slash r) fd
                (lg || norm_too_long c)
            else
              match comp_kind c with
              | LastDot =>
                  walk_comps fs md fd next f d k EDir r
                    (upd_kind r c lk) (upd_slash r ts) lg
              | LastDotDot =>
                  match fs_lookup fs (path_parent k) with
                  | Some e' =>
                      walk_comps fs md fd next f d (path_parent k) e' r
                        (upd_kind r c lk) (upd_slash r ts) lg
                  | None =>
                      mkWalkRes (RAbsent (path_parent k)) (upd_kind r c lk)
                        (upd_slash r ts) fd lg
                  end
              | _ =>
                  if at_outside k c then
                    mkWalkRes ROutside (upd_kind r c lk) (upd_slash r ts) fd lg
                  else if mode_create md && last_slash r then
                    mkWalkRes (RParent k c) LastNorm true fd lg
                  else
                    match fs_lookup fs (child_key k c) with
                    | None =>
                        mkWalkRes
                          (if comps_done r then RMissing k c else RAbsent (child_key k c))
                          (upd_kind r c lk) (upd_slash r ts) fd (lg || comp_too_long c)
                    | Some (ELink b) =>
                        if negb (comps_done r) || (f || last_slash r) then
                          match next with
                          | None =>
                              mkWalkRes RLoop (upd_kind r c lk) (upd_slash r ts) true
                                (lg || comp_too_long c)
                          | Some go =>
                              match fs_lookup fs (link_start k b) with
                              | Some e0 =>
                                  go (f || last_slash r) (d || last_slash r) (link_start k b) e0
                                    (path_split (link_text b) ++ r)
                                    (upd_kind r c lk) (upd_slash r ts) (lg || comp_too_long c)
                              | None =>
                                  mkWalkRes (RAbsent (link_start k b)) (upd_kind r c lk)
                                    (upd_slash r ts) true (lg || comp_too_long c)
                              end
                          end
                        else
                          walk_comps fs md fd next (f || last_slash r) (d || last_slash r)
                            (child_key k c) (ELink b) r (upd_kind r c lk) (upd_slash r ts)
                            (lg || comp_too_long c)
                    | Some e' =>
                        walk_comps fs md fd next (f || last_slash r) (d || last_slash r)
                          (child_key k c) e' r (upd_kind r c lk) (upd_slash r ts)
                          (lg || comp_too_long c)
                    end
              end
        | _ => mkWalkRes (RNotDir k) lk ts fd lg
        end
  end.

(** THE ONE WALK.  Structural on the follow budget [n]; between two
    follows, structural on the pieces ([walk_comps]).  A followed link
    spends one unit of [n] and continues with [fd] set; with [n] spent,
    the next link to follow is [RLoop].  [vm_compute] evaluates it on a
    concrete image. *)
Fixpoint walk (fs : Fs) (md : WalkMode) (n : nat) (f d : bool)
    (k : path) (e : Entry) (cs : list path) (lk : LastKind)
    (ts fd lg : bool) {struct n} : WalkRes :=
  walk_comps fs md fd
    (match n with
     | O => None
     | S n' => Some (fun f d k e cs lk ts lg => walk fs md n' f d k e cs lk ts true lg)
     end)
    f d k e cs lk ts lg.

(** THE ENTRY POINT any path-taking call walks through: the pathname [p]
    from the start key [s], with the follow budget [n] and the end the
    caller asks for.  The start is looked up first; every caller hands a
    key it already holds (the root, or a working folder). *)
Definition walk_from (fs : Fs) (md : WalkMode) (n : nat) (s p : path) : WalkRes :=
  match fs_lookup fs s with
  | Some e =>
      walk fs md n (mode_follow md) (mode_dir md) s e (path_split p)
        LastRoot false false false
  | None => mkWalkRes (RAbsent s) LastRoot false false false
  end.

(** Where a pathname starts: the root if it is absolute ([path_init]
    :2582-2587), else the working directory (:2590-2604).
    [valid_input] guarantees the declared working directory resolves to
    a directory. *)
Definition resolve_start (cwd : path) (p : path) : path :=
  if path_absolute p then root else cwd.

(** Does the pathname end in a separator? *)
Definition path_ends_slash (p : path) : bool :=
  match rev p with
  | [] => false
  | b :: _ => bv_eqb b path_slash_byte
  end.

Fixpoint last_comp (cs : list path) (acc : option path) : option path :=
  match cs with
  | [] => acc
  | c :: r => last_comp r (if comp_nonempty c then Some c else acc)
  end.

(** The type of a pathname's own last component, read off its text: what
    tells a pathname with a component (which the walk's search
    permission check can refuse) from one with none. *)
Definition path_last_kind (p : path) : LastKind :=
  match last_comp (path_split p) None with
  | None => LastRoot
  | Some c => comp_kind c
  end.

(** A pathname from the working directory [cwd], with the full budget. *)
Definition resolve_res (md : WalkMode) (fs : Fs) (cwd p : path) : WalkRes :=
  walk_from fs md link_max (resolve_start cwd p) p.

(** THE RESOLUTION every path-taking arm matches on: the outcome with
    the last component's type and separator.  The empty pathname never
    reaches here with any meaning: every arm answers [-ENOENT] for it
    ahead of resolution, as [getname_flags] does before any walk. *)
Definition resolve (md : WalkMode) (fs : Fs) (cwd p : path)
    : Resolved * LastKind * bool :=
  let w := resolve_res md fs cwd p in (wr_res w, wr_kind w, wr_slash w).

(** THE PARENT END'S LAST NAME, looked up the way each parent-end call
    looks it up next ([lookup_one_qstr_excl], fs/namei.c:1685-1722, from
    [do_unlinkat] :4729, [do_rmdir] :4600 and [filename_create]
    :4231-4232): the entry at the child key, NOT followed, or nothing.
    "." and ".." and a path with no component are never looked up --
    the three calls switch on the kind first (:4720-4722, :4583-4593,
    :4219-4220) -- so the folder itself stands for them.  "proc" and
    "sys" at the root stay outside. *)
Definition parent_last (fs : Fs) (r : Resolved) (lk : LastKind) : Resolved :=
  match r with
  | RParent dir nm =>
      match lk with
      | LastNorm =>
          if at_outside dir nm then ROutside
          else match fs_lookup fs (child_key dir nm) with
               | Some e => RFound (child_key dir nm) e
               | None => RMissing dir nm
               end
      | _ => RFound dir EDir
      end
  | _ => r
  end.

(** The resolution [unlinkat], [rmdir] and [mkdirat] match on: the
    parent walk, then its last name looked up unfollowed. *)
Definition resolve_parent (fs : Fs) (cwd p : path) : Resolved * LastKind * bool :=
  let '(r, lk, ts) := resolve WalkParent fs cwd p in (parent_last fs r lk, lk, ts).

(** No component a split produces holds a separator, and every byte of
    one is a byte of the path. *)
Lemma path_split_aux_comp : forall p acc c b,
  (forall x, In x acc -> bv_eqb x path_slash_byte = false) ->
  In c (path_split_aux acc p) -> In b c ->
  In b (rev acc ++ p) /\ bv_eqb b path_slash_byte = false.
Proof.
  induction p as [|x r IH]; intros acc c b Hacc Hc Hb.
  - cbn [path_split_aux] in Hc. destruct Hc as [<-|[]].
    rewrite app_nil_r. split; [exact Hb|].
    apply Hacc. apply in_rev in Hb. exact Hb.
  - destruct (bv_eqb x path_slash_byte) eqn:Hx.
    + apply bv_eqb_eq in Hx; subst x.
      rewrite path_split_aux_slash in Hc.
      destruct Hc as [<-|Hc].
      * split; [apply in_or_app; now left|].
        apply Hacc. apply in_rev in Hb. exact Hb.
      * destruct (IH [] c b ltac:(intros ? []) Hc Hb) as [Hin Hns].
        cbn [rev app] in Hin. split; [|exact Hns].
        apply in_or_app. right. now right.
    + rewrite (path_split_aux_other acc x r Hx) in Hc.
      assert (Hacc' : forall y, In y (x :: acc) -> bv_eqb y path_slash_byte = false).
      { intros y [<-|Hy]; [exact Hx | now apply Hacc]. }
      destruct (IH (x :: acc) c b Hacc' Hc Hb) as [Hin Hns].
      cbn [rev] in Hin. rewrite <- app_assoc in Hin. cbn [app] in Hin.
      split; [exact Hin | exact Hns].
Qed.

Lemma path_split_comp : forall p c b,
  In c (path_split p) -> In b c ->
  In b p /\ bv_eqb b path_slash_byte = false.
Proof.
  intros p c b Hc Hb.
  destruct (path_split_aux_comp p [] c b ltac:(intros ? []) Hc Hb) as [Hin Hns].
  cbn [rev app] in Hin. split; [exact Hin | exact Hns].
Qed.

(** A pathname with no NUL in it.  Every pathname a spec sees satisfies
    this: it came out of [State.read_cstr], which stops at the
    first NUL.  It is what makes the components of a path that resolves
    NAMEABLE, and so the resolved key canonical. *)
Definition path_nul_free (p : path) : bool :=
  negb (existsb (fun b => bv_eqb b path_nul_byte) p).

Lemma path_nul_free_in : forall p b,
  path_nul_free p = true -> In b p -> bv_eqb b path_nul_byte = false.
Proof.
  intros p b H Hb. unfold path_nul_free in H.
  apply Bool.negb_true_iff in H.
  destruct (bv_eqb b path_nul_byte) eqn:Hn; [|reflexivity].
  exfalso. apply Bool.not_true_iff_false in H. apply H.
  apply existsb_exists. now exists b.
Qed.

(** A component the walk actually steps through is NAMEABLE. *)
Lemma comp_ok_of_step : forall p c,
  path_nul_free p = true ->
  In c (path_split p) ->
  comp_nonempty c = true ->
  path_eqb c dot_comp = false ->
  path_eqb c dotdot_comp = false ->
  comp_ok c = true.
Proof.
  intros p c Hnul Hin Hne Hd Hdd. unfold comp_ok.
  rewrite Hne, Hd, Hdd. cbn [negb andb].
  rewrite !Bool.andb_true_iff. repeat split.
  - apply Bool.negb_true_iff. apply Bool.not_true_is_false. intros Hex.
    apply existsb_exists in Hex as [b [Hb Hs]].
    destruct (path_split_comp p c b Hin Hb) as [_ Hns]. congruence.
  - apply Bool.negb_true_iff. apply Bool.not_true_is_false. intros Hex.
    apply existsb_exists in Hex as [b [Hb Hs]].
    destruct (path_split_comp p c b Hin Hb) as [Hp _].
    rewrite (path_nul_free_in p b Hnul Hp) in Hs. discriminate.
Qed.

(* -------------------------------------------------------------------------
   What resolution guarantees
   ------------------------------------------------------------------------- *)

(** THE WALK AS RULES.  [WSt] is the walk's state: the key it stands on
    ([nd->path]), the pieces still to walk ([nd->last] and the bodies
    open on [nd->stack], fs/namei.c:2515, :2525-2526), the follows left
    ([MAXSYMLINKS] minus [nd->total_link_count], :1878), the
    [LOOKUP_FOLLOW] and [LOOKUP_DIRECTORY] bits (set at :2650 and :3831
    and never cleared during a walk), the type and separator of the last
    component walked, and the two admitted facts of [WalkRes]. *)
Record WSt := mkWSt {
  st_cur : path;
  st_rest : list path;
  st_budget : nat;
  st_follow : bool;
  st_dir : bool;
  st_kind : LastKind;
  st_slash : bool;
  st_followed : bool;
  st_long : bool
}.

(** The walk of [p] from [s] before its first step. *)
Definition walk_init (md : WalkMode) (n : nat) (s p : path) : WSt :=
  mkWSt s (path_split p) n (mode_follow md) (mode_dir md) LastRoot false false false.

(** ONE STEP of [link_path_walk] or [lookup_last] that leaves the walk
    going.  Linux v6.18.46, fs/namei.c. *)
Inductive walk_step (fs : Fs) (md : WalkMode) : WSt -> WSt -> Prop :=
  (* An empty piece: leading, repeated and trailing separators are
     skipped (:2450-2454, :2502-2504). *)
  | ws_skip : forall k c r n f d lk ts fd lg e,
      comp_nonempty c = false ->
      fs_lookup fs k = Some e ->
      walk_step fs md (mkWSt k (c :: r) n f d lk ts fd lg)
                      (mkWSt k r n f d lk ts fd lg)
  (* "." from a folder: [walk_component] hands it to [handle_dots]
     (:2142-2145), which does nothing for [LAST_DOT] (:2096-2098, :2131);
     it never sets the trailing flags, which :2649 sets for [LAST_NORM]
     only. *)
  | ws_dot : forall k c r n f d lk ts fd lg,
      comp_nonempty c = true -> comp_kind c = LastDot ->
      fs_lookup fs k = Some EDir ->
      (mode_parent md && comps_done r) = false ->
      walk_step fs md (mkWSt k (c :: r) n f d lk ts fd lg)
        (mkWSt k r n f d (upd_kind r c lk) (upd_slash r ts) fd lg)
  (* ".." from a folder: [follow_dotdot] (:2064-2094) stays at the root
     (:2068-2069, :2090-2093; [path_parent root] is the root) and
     otherwise moves to the parent dentry ([dget_parent] :2083), which
     in one tree is the parent of the key the walk stands on -- after a
     link, the TARGET's parent; [step_into] is then called with
     [WALK_NOFOLLOW] (:2113). *)
  | ws_dotdot : forall k c r n f d lk ts fd lg,
      comp_nonempty c = true -> comp_kind c = LastDotDot ->
      fs_lookup fs k = Some EDir ->
      (mode_parent md && comps_done r) = false ->
      walk_step fs md (mkWSt k (c :: r) n f d lk ts fd lg)
        (mkWSt (path_parent k) r n f d (upd_kind r c lk) (upd_slash r ts) fd lg)
  (* A normal name from a folder, found, and not to be followed:
     [walk_component] (:2147-2157), [step_into]'s no-follow branch
     (:1994-2011).  A last name with a separator after it sets
     [LOOKUP_FOLLOW] and [LOOKUP_DIRECTORY] ([lookup_last] :2649-2650). *)
  | ws_child : forall k c r n f d lk ts fd lg e',
      comp_nonempty c = true -> comp_kind c = LastNorm ->
      fs_lookup fs k = Some EDir ->
      (mode_parent md && comps_done r) = false ->
      at_outside k c = false ->
      (mode_create md && last_slash r) = false ->
      fs_lookup fs (child_key k c) = Some e' ->
      link_needed e' r (f || last_slash r) = false ->
      walk_step fs md (mkWSt k (c :: r) n f d lk ts fd lg)
        (mkWSt (child_key k c) r n (f || last_slash r) (d || last_slash r)
           (upd_kind r c lk) (upd_slash r ts) fd (lg || comp_too_long c))
  (* A link to follow with follows left: [step_into] hands it to
     [pick_link] without moving the walk (:2013-2021); [pick_link]
     counts it ([reserve_stack] :1878-1879) and returns the body, read
     to its first NUL (:1945-1961), which is walked from the root if it
     is absolute ([nd_jump_root] :1962-1967) and from the folder holding
     the link otherwise; an empty body leaves the walk on that folder
     (:1957-1958, :1969-1973).  The body's pieces go in front of what is
     left. *)
  | ws_link : forall k c r n f d lk ts fd lg b,
      comp_nonempty c = true -> comp_kind c = LastNorm ->
      fs_lookup fs k = Some EDir ->
      (mode_parent md && comps_done r) = false ->
      at_outside k c = false ->
      (mode_create md && last_slash r) = false ->
      fs_lookup fs (child_key k c) = Some (ELink b) ->
      (negb (comps_done r) || (f || last_slash r)) = true ->
      walk_step fs md (mkWSt k (c :: r) (S n) f d lk ts fd lg)
        (mkWSt (link_start k b) (path_split (link_text b) ++ r) n
           (f || last_slash r) (d || last_slash r)
           (upd_kind r c lk) (upd_slash r ts) true (lg || comp_too_long c)).

(** HOW A WALK ENDS.  Linux v6.18.46, fs/namei.c. *)
Inductive walk_end (fs : Fs) (md : WalkMode) : WSt -> WalkRes -> Prop :=
  (* The walk stands on a key the image does not hold.  It gets there
     only through ".." or a link restart on an image that is not well
     formed; [wf_fs] keeps every folder's parent and the root. *)
  | we_absent : forall k rest n f d lk ts fd lg,
      fs_lookup fs k = None ->
      walk_end fs md (mkWSt k rest n f d lk ts fd lg)
        (mkWalkRes (RAbsent k) lk ts fd lg)
  (* Nothing left: the walk's answer ([path_lookupat] :2675-2683),
     unless [LOOKUP_DIRECTORY] asks for a folder (next rule). *)
  | we_found : forall k n f d lk ts fd lg e,
      fs_lookup fs k = Some e -> mode_parent md = false ->
      (d = false \/ e = EDir) ->
      walk_end fs md (mkWSt k [] n f d lk ts fd lg)
        (mkWalkRes (RFound k e) lk ts fd lg)
  (* [LOOKUP_DIRECTORY] and no folder at the end: -ENOTDIR (:2685-2687;
     [do_open] :3958-3959). *)
  | we_notdir_end : forall k n f d lk ts fd lg e,
      fs_lookup fs k = Some e -> e <> EDir -> (mode_parent md || d) = true ->
      walk_end fs md (mkWSt k [] n f d lk ts fd lg)
        (mkWalkRes (RNotDir k) lk ts fd lg)
  (* The parent end of a path with no component, such as "/":
     [link_path_walk] returns at once with [LAST_ROOT] (:2446,
     :2455-2458). *)
  | we_parent_root : forall k n f d lk ts fd lg,
      fs_lookup fs k = Some EDir -> mode_parent md = true ->
      walk_end fs md (mkWSt k [] n f d lk ts fd lg)
        (mkWalkRes (RParent k []) LastRoot false fd lg)
  (* A component left and a non-folder under the walk: -ENOTDIR, tested
     right after the component that landed there (:2529-2535). *)
  | we_notdir : forall k c r n f d lk ts fd lg e,
      comp_nonempty c = true -> fs_lookup fs k = Some e -> e <> EDir ->
      walk_end fs md (mkWSt k (c :: r) n f d lk ts fd lg)
        (mkWalkRes (RNotDir k) lk ts fd lg)
  (* The parent end: [path_parentat] (:2719-2733) stops in front of the
     last name, which it neither looks up nor follows ([link_path_walk]
     returns at :2496-2513; [__filename_parentat] :2752-2755).  A last
     normal name over [name_max] admits -ENAMETOOLONG, because each
     parent-end arm looks it up next ([lookup_one_qstr_excl]'s
     [->lookup], :1705). *)
  | we_parent : forall k c r n f d lk ts fd lg,
      comp_nonempty c = true -> fs_lookup fs k = Some EDir ->
      mode_parent md = true -> comps_done r = true ->
      walk_end fs md (mkWSt k (c :: r) n f d lk ts fd lg)
        (mkWalkRes (RParent k c) (comp_kind c) (last_slash r) fd (lg || norm_too_long c))
  (* "proc" or "sys" looked up at the root: procfs and sysfs are not in
     the image, so every arm declines. *)
  | we_outside : forall k c r n f d lk ts fd lg,
      comp_nonempty c = true -> comp_kind c = LastNorm ->
      fs_lookup fs k = Some EDir ->
      (mode_parent md && comps_done r) = false ->
      at_outside k c = true ->
      walk_end fs md (mkWSt k (c :: r) n f d lk ts fd lg)
        (mkWalkRes ROutside (upd_kind r c lk) (upd_slash r ts) fd lg)
  (* [open] with [O_CREAT], a last normal name with a separator after
     it: -EISDIR before any lookup ([lookup_fast_for_open] :3821-3823). *)
  | we_create_slash : forall k c r n f d lk ts fd lg,
      comp_nonempty c = true -> comp_kind c = LastNorm ->
      fs_lookup fs k = Some EDir ->
      at_outside k c = false ->
      mode_create md = true -> last_slash r = true ->
      walk_end fs md (mkWSt k (c :: r) n f d lk ts fd lg)
        (mkWalkRes (RParent k c) LastNorm true fd lg)
  (* A normal name the folder does not hold: a negative dentry
     ([step_into] -> [handle_mounts] :1989-1992 -> [traverse_mounts]
     :1537-1538).  The last name is [RMissing], where [O_CREAT] creates
     ([lookup_open] :3788-3800); any other is [RAbsent]. *)
  | we_miss : forall k c r n f d lk ts fd lg,
      comp_nonempty c = true -> comp_kind c = LastNorm ->
      fs_lookup fs k = Some EDir ->
      (mode_parent md && comps_done r) = false ->
      at_outside k c = false ->
      (mode_create md && last_slash r) = false ->
      fs_lookup fs (child_key k c) = None ->
      walk_end fs md (mkWSt k (c :: r) n f d lk ts fd lg)
        (mkWalkRes (if comps_done r then RMissing k c else RAbsent (child_key k c))
           (upd_kind r c lk) (upd_slash r ts) fd (lg || comp_too_long c))
  (* A link to follow with no follow left: the 41st, refused by
     [reserve_stack]'s [nd->total_link_count++ >= MAXSYMLINKS]
     (:1878-1879; include/linux/namei.h:13). *)
  | we_loop : forall k c r f d lk ts fd lg b,
      comp_nonempty c = true -> comp_kind c = LastNorm ->
      fs_lookup fs k = Some EDir ->
      (mode_parent md && comps_done r) = false ->
      at_outside k c = false ->
      (mode_create md && last_slash r) = false ->
      fs_lookup fs (child_key k c) = Some (ELink b) ->
      (negb (comps_done r) || (f || last_slash r)) = true ->
      walk_end fs md (mkWSt k (c :: r) 0 f d lk ts fd lg)
        (mkWalkRes RLoop (upd_kind r c lk) (upd_slash r ts) true (lg || comp_too_long c)).

(** A WALK FROM A STATE TO ITS ANSWER: steps, then an end. *)
Inductive walk_runs (fs : Fs) (md : WalkMode) : WSt -> WalkRes -> Prop :=
  | runs_end : forall s w, walk_end fs md s w -> walk_runs fs md s w
  | runs_step : forall s s' w,
      walk_step fs md s s' -> walk_runs fs md s' w -> walk_runs fs md s w.

(** [comp_kind] never answers [LastRoot]: every component has a type. *)
Lemma comp_kind_not_root : forall c, comp_kind c <> LastRoot.
Proof.
  intros c. unfold comp_kind.
  destruct (path_eqb c dot_comp); [discriminate|].
  destruct (path_eqb c dotdot_comp); discriminate.
Qed.

(** The follow continuation of budget [n], named so a proof can carry
    it. *)
Definition walk_next (fs : Fs) (md : WalkMode) (n : nat) : option FollowK :=
  match n with
  | O => None
  | S n' => Some (fun f d k e cs lk ts lg => walk fs md n' f d k e cs lk ts true lg)
  end.

Lemma walk_unfold : forall fs md n f d k e cs lk ts fd lg,
  walk fs md n f d k e cs lk ts fd lg
  = walk_comps fs md fd (walk_next fs md n) f d k e cs lk ts lg.
Proof. intros. destruct n; reflexivity. Qed.

(** What the function answers from a state, given the entry under it. *)
Definition run_fn (fs : Fs) (md : WalkMode) (s : WSt) (e : Entry) : WalkRes :=
  walk_comps fs md (st_followed s) (walk_next fs md (st_budget s)) (st_follow s)
    (st_dir s) (st_cur s) e (st_rest s) (st_kind s) (st_slash s) (st_long s).

(** The continuation's contract, as the soundness induction carries it. *)
Definition next_runs (fs : Fs) (md : WalkMode) (n : nat) (next : option FollowK) : Prop :=
  match n with
  | O => next = None
  | S n' => exists go, next = Some go /\
      forall f d k e cs lk ts lg, fs_lookup fs k = Some e ->
        walk_runs fs md (mkWSt k cs n' f d lk ts true lg) (go f d k e cs lk ts lg)
  end.

(** SOUNDNESS, one string of pieces: every answer of [walk_comps] is
    derived by the rules. *)
Lemma walk_comps_runs : forall fs md fd n next, next_runs fs md n next ->
  forall cs f d k e lk ts lg, fs_lookup fs k = Some e ->
  walk_runs fs md (mkWSt k cs n f d lk ts fd lg)
    (walk_comps fs md fd next f d k e cs lk ts lg).
Proof.
  intros fs md fd n next Hnext cs.
  induction cs as [|c r IH]; intros f d k e lk ts lg Hk; cbn [walk_comps].
  - apply runs_end. destruct (mode_parent md) eqn:Hp.
    + destruct e as [i| |dk|b];
        [ eapply we_notdir_end; [exact Hk | discriminate | now rewrite Hp]
        | now apply we_parent_root
        | eapply we_notdir_end; [exact Hk | discriminate | now rewrite Hp]
        | eapply we_notdir_end; [exact Hk | discriminate | now rewrite Hp] ].
    + destruct e as [i| |dk|b].
      2: apply we_found; [exact Hk | exact Hp | now right].
      all: destruct d;
        [ eapply we_notdir_end; [exact Hk | discriminate | now rewrite Hp]
        | apply we_found; [exact Hk | exact Hp | now left] ].
  - destruct (comp_nonempty c) eqn:Hne; cbn [negb].
    2: { eapply runs_step; [eapply ws_skip; [exact Hne | exact Hk] |].
         apply IH. exact Hk. }
    destruct e as [i| |dk|b].
    1, 3, 4: apply runs_end; eapply we_notdir; [exact Hne | exact Hk | discriminate].
    destruct (mode_parent md && comps_done r) eqn:Hpl.
    { apply runs_end. apply Bool.andb_true_iff in Hpl as [Hp Hd].
      apply we_parent; assumption. }
    destruct (comp_kind c) eqn:Hkind.
    + destruct (at_outside k c) eqn:Hout.
      { apply runs_end. apply we_outside; assumption. }
      destruct (mode_create md && last_slash r) eqn:Hcs.
      { apply runs_end. apply Bool.andb_true_iff in Hcs as [Hc Hs].
        apply we_create_slash; assumption. }
      destruct (fs_lookup fs (child_key k c)) as [e'|] eqn:Hch.
      2: { apply runs_end. apply we_miss; assumption. }
      destruct e' as [i| |dk|b].
      1, 2, 3: eapply runs_step;
        [ eapply ws_child; first [eassumption | reflexivity]
        | apply IH; exact Hch ].
      destruct (negb (comps_done r) || (f || last_slash r)) eqn:Hneed.
      2: { eapply runs_step;
             [ eapply ws_child; first [eassumption | exact Hneed]
             | apply IH; exact Hch ]. }
      destruct n as [|n'].
      * cbn [next_runs] in Hnext. subst next.
        apply runs_end. eapply we_loop; eassumption.
      * destruct Hnext as [go [-> Hgo]].
        destruct (fs_lookup fs (link_start k b)) as [e0|] eqn:H0.
        -- eapply runs_step; [eapply ws_link; eassumption |].
           apply Hgo. exact H0.
        -- eapply runs_step; [eapply ws_link; eassumption |].
           apply runs_end. apply we_absent. exact H0.
    + eapply runs_step; [eapply ws_dot; eassumption |].
      apply IH. exact Hk.
    + destruct (fs_lookup fs (path_parent k)) as [e'|] eqn:Hp.
      * eapply runs_step; [eapply ws_dotdot; eassumption |].
        apply IH. exact Hp.
      * eapply runs_step; [eapply ws_dotdot; eassumption |].
        apply runs_end. apply we_absent. exact Hp.
    + exfalso. exact (comp_kind_not_root c Hkind).
Qed.

(** SOUNDNESS: every answer of [walk] is derived by the rules. *)
Lemma walk_sound : forall fs md n f d k e cs lk ts fd lg,
  fs_lookup fs k = Some e ->
  walk_runs fs md (mkWSt k cs n f d lk ts fd lg) (walk fs md n f d k e cs lk ts fd lg).
Proof.
  intros fs md n. induction n as [|n IH]; intros f d k e cs lk ts fd lg Hk;
    rewrite walk_unfold; apply walk_comps_runs; try exact Hk.
  - reflexivity.
  - cbn [next_runs walk_next]. eexists; split; [reflexivity|].
    intros f' d' k' e' cs' lk' ts' lg' Hk'. apply IH. exact Hk'.
Qed.

(** A walk standing on a key the image does not hold ends there. *)
Lemma walk_runs_absent : forall fs md s w,
  fs_lookup fs (st_cur s) = None -> walk_runs fs md s w ->
  w = mkWalkRes (RAbsent (st_cur s)) (st_kind s) (st_slash s) (st_followed s) (st_long s).
Proof.
  intros fs md s w Hs H. destruct H as [s w He | s s' w Hst _].
  - destruct He; cbn [st_cur st_kind st_slash st_followed st_long] in *;
      congruence.
  - exfalso. destruct Hst; cbn [st_cur] in Hs; congruence.
Qed.

(** One rule step is one unfolding of the function. *)
Lemma walk_step_fn : forall fs md s s', walk_step fs md s s' ->
  forall e0, fs_lookup fs (st_cur s) = Some e0 ->
  run_fn fs md s e0
  = match fs_lookup fs (st_cur s') with
    | Some e' => run_fn fs md s' e'
    | None => mkWalkRes (RAbsent (st_cur s')) (st_kind s') (st_slash s')
                (st_followed s') (st_long s')
    end.
Proof.
  intros fs md s s' H. destruct H; intros e0 Hk; unfold run_fn;
    cbn [st_budget st_follow st_dir st_cur st_rest st_kind st_slash
         st_followed st_long] in *;
    cbn [walk_comps].
  - rewrite H, H0. cbn [negb]. assert (e0 = e) by congruence. subst. reflexivity.
  - assert (e0 = EDir) by congruence. subst e0.
    rewrite H, H2, H0, H1. cbn [negb]. reflexivity.
  - assert (e0 = EDir) by congruence. subst e0.
    rewrite H, H2, H0. cbn [negb].
    destruct (fs_lookup fs (path_parent k)); reflexivity.
  - assert (e0 = EDir) by congruence. subst e0.
    rewrite H, H2, H0, H3, H4, H5. cbn [negb andb orb].
    destruct e' as [i| |dk|b]; try reflexivity.
    cbn [link_needed] in H6. rewrite H6. reflexivity.
  - assert (e0 = EDir) by congruence. subst e0.
    rewrite H, H2, H0, H3, H4, H5, H6. cbn [negb andb orb walk_next].
    destruct (fs_lookup fs (link_start k b)); [|reflexivity].
    rewrite walk_unfold. reflexivity.
Qed.

(** COMPLETENESS: an answer the rules derive is the function's. *)
Lemma walk_runs_fn : forall fs md s w, walk_runs fs md s w ->
  forall e0, fs_lookup fs (st_cur s) = Some e0 -> run_fn fs md s e0 = w.
Proof.
  intros fs md s w H. induction H as [s w He | s s' w Hst Hrun IH]; intros e0 Hk.
  - destruct He; unfold run_fn;
      cbn [st_budget st_follow st_dir st_cur st_rest st_kind st_slash
           st_followed st_long] in *;
      cbn [walk_comps].
    + congruence.
    + assert (e0 = e) by congruence. subst e0. rewrite H0.
      destruct H1 as [-> | ->]; [destruct e; reflexivity | reflexivity].
    + assert (e0 = e) by congruence. subst e0.
      destruct (mode_parent md); cbn [orb] in H1; [|subst d];
        destruct e; try (exfalso; now apply H0); reflexivity.
    + assert (e0 = EDir) by congruence. subst e0. rewrite H0. reflexivity.
    + rewrite H. cbn [negb]. assert (e0 = e) by congruence. subst e0.
      destruct e; [reflexivity | exfalso; now apply H1 | reflexivity | reflexivity].
    + assert (e0 = EDir) by congruence. subst e0.
      rewrite H, H1, H2. reflexivity.
    + assert (e0 = EDir) by congruence. subst e0.
      rewrite H, H2, H0, H3. reflexivity.
    + assert (e0 = EDir) by congruence. subst e0.
      assert (Hp : mode_parent md = false)
        by (destruct md; cbn [mode_create mode_parent] in *; congruence).
      rewrite H, Hp, H0, H2, H3, H4. reflexivity.
    + assert (e0 = EDir) by congruence. subst e0.
      rewrite H, H2, H0, H3, H4, H5. reflexivity.
    + assert (e0 = EDir) by congruence. subst e0.
      rewrite H, H2, H0, H3, H4, H5, H6. reflexivity.
  - rewrite (walk_step_fn fs md s s' Hst e0 Hk).
    destruct (fs_lookup fs (st_cur s')) as [e'|] eqn:H'.
    + exact (IH e' eq_refl).
    + symmetry. exact (walk_runs_absent fs md s' w H' Hrun).
Qed.

(** DETERMINISM: the rules derive at most one answer from a state. *)
Theorem walk_runs_det : forall fs md s w1 w2,
  walk_runs fs md s w1 -> walk_runs fs md s w2 -> w1 = w2.
Proof.
  intros fs md s w1 w2 H1 H2.
  destruct (fs_lookup fs (st_cur s)) as [e|] eqn:Hk.
  - rewrite <- (walk_runs_fn fs md s w1 H1 e Hk), <- (walk_runs_fn fs md s w2 H2 e Hk).
    reflexivity.
  - rewrite (walk_runs_absent fs md s w1 Hk H1), (walk_runs_absent fs md s w2 Hk H2).
    reflexivity.
Qed.

(** THE SPEC: [walk_from] answers [w] exactly when the rules derive [w]
    from the walk's first state.  The function terminates by its
    structure: each follow spends one unit of the budget, and between
    two follows each step consumes one piece. *)
Theorem walk_from_spec : forall fs md n s p w,
  walk_from fs md n s p = w <-> walk_runs fs md (walk_init md n s p) w.
Proof.
  intros fs md n s p w. unfold walk_from, walk_init.
  destruct (fs_lookup fs s) as [e|] eqn:Hs.
  - split.
    + intros <-. apply walk_sound. exact Hs.
    + intros H. rewrite walk_unfold. exact (walk_runs_fn fs md _ w H e Hs).
  - split.
    + intros <-. apply runs_end. apply we_absent. exact Hs.
    + intros H. apply walk_runs_absent in H; [|exact Hs]. rewrite H. reflexivity.
Qed.

Theorem resolve_spec : forall md fs cwd p w,
  resolve_res md fs cwd p = w
  <-> walk_runs fs md (walk_init md link_max (resolve_start cwd p) p) w.
Proof. intros. apply walk_from_spec. Qed.

(** Two images whose names agree walk alike: the rules read the image
    only through [fs_lookup]. *)
Lemma walk_runs_ext : forall fs fs' md s w,
  (forall q, fs_lookup fs' q = fs_lookup fs q) ->
  walk_runs fs md s w -> walk_runs fs' md s w.
Proof.
  intros fs fs' md s w Heq H.
  induction H as [s w He | s s' w Hst _ IH].
  - apply runs_end.
    destruct He;
      [ eapply we_absent | eapply we_found | eapply we_notdir_end
      | eapply we_parent_root | eapply we_notdir | eapply we_parent
      | eapply we_outside | eapply we_create_slash | eapply we_miss
      | eapply we_loop ];
      rewrite ?Heq; eassumption.
  - apply (runs_step fs' md s s' w); [|exact IH].
    destruct Hst;
      [ eapply ws_skip | eapply ws_dot | eapply ws_dotdot | eapply ws_child
      | eapply ws_link ];
      rewrite ?Heq; eassumption.
Qed.

Lemma walk_from_ext : forall fs fs' md n s p,
  (forall q, fs_lookup fs' q = fs_lookup fs q) ->
  walk_from fs' md n s p = walk_from fs md n s p.
Proof.
  intros fs fs' md n s p Heq. apply walk_from_spec.
  apply (walk_runs_ext fs fs' md _ _ Heq). apply walk_from_spec. reflexivity.
Qed.

(** THE WALK READS NAMES ONLY: a change to the inode or folder-count
    tables leaves every resolution as it was. *)
Lemma resolve_same_tree : forall md fs fs' cwd p,
  fs_tree fs' = fs_tree fs -> resolve md fs' cwd p = resolve md fs cwd p.
Proof.
  intros md fs fs' cwd p Ht. unfold resolve, resolve_res.
  rewrite (walk_from_ext fs fs'); [reflexivity|].
  intros q. unfold fs_lookup. now rewrite Ht.
Qed.

Lemma path_eqb_false_of_neq : forall p q, p <> q -> path_eqb p q = false.
Proof.
  intros p q H. destruct (path_eqb p q) eqn:E; [|reflexivity].
  apply path_eqb_eq in E. contradiction.
Qed.

(* -------------------------------------------------------------------------
   The plain name every collaborator target opens
   ------------------------------------------------------------------------- *)

(** A PLAIN NAME: one nameable component, within [name_max].  Every
    collaborator target opens its input by one ([open(argv[1])]), and
    [Run.valid_argv] keeps the examples' argv entries to this shape. *)
Definition plain_name (a : path) : bool :=
  comp_ok a && negb (Nat.ltb name_max (length a)).

Lemma path_split_plain : forall a,
  comp_ok a = true -> path_split a = [a].
Proof.
  intros a Ha. unfold path_split.
  assert (H := path_split_aux_app_noslash a [] []
                 (fun b Hb => comp_ok_no_slash a b Ha Hb)).
  rewrite !app_nil_r in H. rewrite H.
  cbn [path_split_aux]. rewrite rev_involutive. reflexivity.
Qed.

Lemma comp_ok_not_slash_head : forall a b r,
  comp_ok a = true -> a = b :: r -> bv_eqb b path_slash_byte = false.
Proof.
  intros a b r Ha ->. apply (comp_ok_no_slash (b :: r) b Ha). now left.
Qed.

(** A PLAIN NAME RESOLVES AS ONE LOOKUP.  This is what keeps a harness
    proof over a plain name one rewrite: it never re-derives the walk.
    An absent name is [RMissing] in every working directory, the
    [dev_dir] subtree included.  A link there is the answer only when the
    caller does not follow the last component. *)
Lemma resolve_plain_name : forall md fs cwd a,
  mode_parent md = false -> mode_dir md = false ->
  fs_lookup fs cwd = Some EDir ->
  plain_name a = true ->
  at_outside cwd a = false ->
  (forall b, fs_lookup fs (child_key cwd a) = Some (ELink b) -> mode_follow md = false) ->
  resolve md fs cwd a
  = (match fs_lookup fs (child_key cwd a) with
     | Some e => RFound (child_key cwd a) e
     | None => RMissing cwd a
     end, LastNorm, false).
Proof.
  intros md fs cwd a Hp Hd Hcwd Hplain Hout Hlink.
  unfold plain_name in Hplain. apply Bool.andb_true_iff in Hplain as [Ha _].
  assert (Hne : comp_nonempty a = true) by (apply comp_ok_nonempty; exact Ha).
  assert (Hk : comp_kind a = LastNorm).
  { unfold comp_kind. rewrite (comp_ok_not_dot a Ha), (comp_ok_not_dotdot a Ha).
    reflexivity. }
  assert (Hs : resolve_start cwd a = cwd).
  { destruct a as [|b r]; [discriminate Hne|]. unfold resolve_start, path_absolute.
    now rewrite (comp_ok_not_slash_head _ b r Ha eq_refl). }
  unfold resolve, resolve_res, walk_from.
  rewrite Hs, Hcwd, walk_unfold, (path_split_plain a Ha).
  cbn [walk_comps]. unfold upd_kind, upd_slash. rewrite Hne, Hk, Hout.
  destruct md as [f d | f |]; cbn [mode_parent mode_dir] in Hp, Hd;
    try discriminate; try subst d;
    destruct (fs_lookup fs (child_key cwd a)) as [[i| |dk|b]|] eqn:Hc;
    try reflexivity;
    specialize (Hlink b eq_refl); cbn [mode_follow] in Hlink; subst f; reflexivity.
Qed.

(** "." RESOLVES TO THE WORKING DIRECTORY ITSELF, off nothing but the
    working directory being a directory: [handle_dots] on a [LAST_DOT]
    component is a no-op on the walk's own position (fs/namei.c:2096-2132),
    so a descriptor opened on "." names the working directory.  The last
    kind is [LastDot], which the parent-end arms switch on.  The empty
    pathname never reaches here: every arm answers -ENOENT for it ahead
    of resolution, as [getname_flags] does. *)
Lemma resolve_dot : forall md fs cwd,
  mode_parent md = false ->
  fs_lookup fs cwd = Some EDir ->
  resolve md fs cwd dot_comp = (RFound cwd EDir, LastDot, false).
Proof.
  intros md fs cwd Hp Hcwd. unfold resolve, resolve_res, walk_from.
  change (resolve_start cwd dot_comp) with cwd.
  rewrite Hcwd, walk_unfold.
  change (path_split dot_comp) with [dot_comp].
  cbn [walk_comps]. rewrite !Hp. reflexivity.
Qed.

(** A run the rules derive, read back as the resolution: the way a
    statement about one concrete pathname is proved without unfolding
    the function. *)
Lemma resolve_of_runs : forall md fs cwd p w,
  walk_runs fs md (walk_init md link_max (resolve_start cwd p) p) w ->
  resolve md fs cwd p = (wr_res w, wr_kind w, wr_slash w).
Proof.
  intros md fs cwd p w H. unfold resolve.
  apply resolve_spec in H. now rewrite H.
Qed.

(* -------------------------------------------------------------------------
   Building images
   ------------------------------------------------------------------------- *)

Fixpoint fs_of_list (fs : Fs) (l : list (path * Entry)) : Fs :=
  match l with
  | [] => fs
  | ke :: r => fs_of_list (fs_set fs (fst ke) (snd ke)) r
  end.

Fixpoint fs_add_dirs (fs : Fs) (ds : list path) : Fs :=
  match ds with
  | [] => fs
  | d :: r => fs_add_dirs (fs_set fs d EDir) r
  end.

Lemma fs_of_list_sorted : forall l fs,
  fs_sorted fs = true -> fs_sorted (fs_of_list fs l) = true.
Proof.
  induction l as [|ke l IH]; intros fs H; [exact H|].
  cbn [fs_of_list]. apply IH. now apply fs_set_sorted.
Qed.

Lemma fs_add_dirs_sorted : forall ds fs,
  fs_sorted fs = true -> fs_sorted (fs_add_dirs fs ds) = true.
Proof.
  induction ds as [|d ds IH]; intros fs H; [exact H|].
  cbn [fs_add_dirs]. apply IH. now apply fs_set_sorted.
Qed.

Lemma fs_of_list_keys : forall (P : path -> Prop) l fs,
  Forall (fun ke => P (fst ke)) (fs_tree fs) ->
  Forall (fun ke => P (fst ke)) l ->
  Forall (fun ke => P (fst ke)) (fs_tree (fs_of_list fs l)).
Proof.
  induction l as [|ke l IH]; intros fs Hfs Hl; [exact Hfs|].
  inversion Hl as [|? ? Hke Hl']; subst.
  cbn [fs_of_list]. apply IH; [|exact Hl'].
  now apply tree_set_keys.
Qed.

Lemma fs_add_dirs_keys : forall (P : path -> Prop) ds fs,
  Forall (fun ke => P (fst ke)) (fs_tree fs) ->
  (forall d, In d ds -> P d) ->
  Forall (fun ke => P (fst ke)) (fs_tree (fs_add_dirs fs ds)).
Proof.
  induction ds as [|d ds IH]; intros fs Hfs Hds; [exact Hfs|].
  cbn [fs_add_dirs]. apply IH.
  - apply tree_set_keys; [exact Hfs | apply Hds; now left].
  - intros x Hx. apply Hds. now right.
Qed.

Lemma fs_add_dirs_notin : forall ds fs k,
  ~ In k ds -> fs_lookup (fs_add_dirs fs ds) k = fs_lookup fs k.
Proof.
  induction ds as [|d ds IH]; intros fs k H; [reflexivity|].
  cbn [fs_add_dirs]. rewrite IH by (intros HH; apply H; now right).
  apply fs_lookup_set_neq. apply path_eqb_false_of_neq.
  intros ->. apply H. now left.
Qed.

Lemma fs_add_dirs_in : forall ds fs k,
  In k ds -> fs_lookup (fs_add_dirs fs ds) k = Some EDir.
Proof.
  induction ds as [|d ds IH]; intros fs k H; [contradiction|].
  cbn [fs_add_dirs].
  destruct (in_dec path_eq_dec k ds) as [Hin|Hnin]; [now apply IH|].
  destruct H as [->|H]; [|contradiction].
  rewrite fs_add_dirs_notin by exact Hnin. apply fs_lookup_set_eq.
Qed.

Lemma tree_set_in_keys : forall t p e k,
  In k (map fst (tree_set t p e)) -> k = p \/ In k (map fst t).
Proof.
  induction t as [|[q d] r IH]; intros p e k H.
  - cbn [tree_set map fst] in H. destruct H as [<-|[]]. now left.
  - cbn [tree_set] in H. destruct (path_ltb p q).
    + cbn [map fst] in H. destruct H as [<-|H]; [now left|now right].
    + destruct (path_eqb p q) eqn:Hpq.
      * cbn [map fst] in H. destruct H as [<-|H]; [now left|].
        right. cbn [map fst]. now right.
      * cbn [map fst] in H. destruct H as [<-|H].
        -- right. cbn [map fst]. now left.
        -- destruct (IH p e k H) as [Hl|Hr]; [now left|].
           right. cbn [map fst]. now right.
Qed.

Lemma fs_set_in_keys : forall fs p e k,
  In k (map fst (fs_tree (fs_set fs p e))) -> k = p \/ In k (map fst (fs_tree fs)).
Proof. intros fs p e k H. now apply (tree_set_in_keys (fs_tree fs) p e). Qed.

Lemma fs_of_list_in_keys : forall l fs k,
  In k (map fst (fs_tree (fs_of_list fs l))) ->
  In k (map fst l) \/ In k (map fst (fs_tree fs)).
Proof.
  induction l as [|kv l IH]; intros fs k H; [now right|].
  cbn [fs_of_list] in H.
  destruct (IH _ k H) as [Hl|Hr]; [left; cbn [map]; now right|].
  destruct (fs_set_in_keys fs (fst kv) (snd kv) k Hr) as [->|Hk].
  - left. cbn [map]. now left.
  - now right.
Qed.

Lemma fs_add_dirs_in_keys : forall ds fs k,
  In k (map fst (fs_tree (fs_add_dirs fs ds))) ->
  In k ds \/ In k (map fst (fs_tree fs)).
Proof.
  induction ds as [|d ds IH]; intros fs k H; [now right|].
  cbn [fs_add_dirs] in H.
  destruct (IH _ k H) as [Hl|Hr]; [left; now right|].
  destruct (fs_set_in_keys fs d EDir k Hr) as [->|Hk].
  - left. now left.
  - now right.
Qed.

Lemma fs_inodes_of_list : forall l fs, fs_inodes (fs_of_list fs l) = fs_inodes fs.
Proof. induction l as [|ke l IH]; intros fs; [reflexivity|]. cbn [fs_of_list]. now rewrite IH. Qed.

Lemma fs_inodes_add_dirs : forall ds fs, fs_inodes (fs_add_dirs fs ds) = fs_inodes fs.
Proof. induction ds as [|d ds IH]; intros fs; [reflexivity|]. cbn [fs_add_dirs]. now rewrite IH. Qed.

Lemma fs_dirs_of_list : forall l fs, fs_dirs (fs_of_list fs l) = fs_dirs fs.
Proof. induction l as [|ke l IH]; intros fs; [reflexivity|]. cbn [fs_of_list]. now rewrite IH. Qed.

Lemma fs_dirs_add_dirs : forall ds fs, fs_dirs (fs_add_dirs fs ds) = fs_dirs fs.
Proof. induction ds as [|d ds IH]; intros fs; [reflexivity|]. cbn [fs_add_dirs]. now rewrite IH. Qed.

(* -------------------------------------------------------------------------
   The standard root, and migrating a pre-namespace image
   ------------------------------------------------------------------------- *)

(* [dev_dir] is defined up beside [proc_comp] and [sys_comp], because
   the walk tests it. *)

Definition devnull_key : path :=
  [Z_to_bv 8 47; Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 118;
   Z_to_bv 8 47; Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 108;
   Z_to_bv 8 108].                                                 (* /dev/null *)

Definition urandom_key : path :=
  [Z_to_bv 8 47; Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 118;
   Z_to_bv 8 47; Z_to_bv 8 117; Z_to_bv 8 114; Z_to_bv 8 97;
   Z_to_bv 8 110; Z_to_bv 8 100; Z_to_bv 8 111; Z_to_bv 8 109].  (* /dev/urandom *)

Definition tmp_dir : path :=
  [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112].          (* /tmp *)

(** The working directory a fixture gets when it does not say.  It is the
    harness guest's own working directory on a fresh tmpfs; it is a
    FIXTURE DEFAULT and appears in no theorem. *)
Definition default_cwd : path :=
  [Z_to_bv 8 47; Z_to_bv 8 119; Z_to_bv 8 111; Z_to_bv 8 114;
   Z_to_bv 8 107].                                                     (* /work *)

(** The directories the default image holds: /dev, /tmp and the chain
    down to the working directory, each with every ancestor. *)
Definition standard_dirs (cwd : path) : list path :=
  key_chain dev_dir ++ key_chain tmp_dir ++ key_chain cwd.

(** The image with nothing in it: no name, no inode, no folder row. *)
Definition fs_empty : Fs := mkFs [] [] [].

Definition standard_base : Fs :=
  fs_set (fs_set fs_empty devnull_key (EDev DevNull)) urandom_key (EDev DevUrandom).

(** THE DEFAULT IMAGE: the root, /dev with its two devices, /tmp, and
    the chain down to [cwd].  It is a FIXTURE DEFAULT -- [Run.valid_input]
    names it only through [standard_root_present], and only if the
    maintainer adopts that premise (issue #1011, section 15, question 1).
    It is what every legacy literal is migrated onto, so a fixture that
    opened /dev/null yesterday opens the same device today. *)
Definition standard_root (cwd : path) : Fs :=
  fs_add_dirs standard_base (standard_dirs cwd).

(** WHY A LEGACY KEY IS REFUSED.  The migration REJECTS rather than
    normalises: a key that would have to be rewritten to become a key
    named a file the old model could not have meant, and silently
    renaming it would move a fixture's file without saying so. *)
Inductive MigrateReject :=
  | MrEmptyKey
  | MrAbsoluteKey
  | MrEmptyComponent
  | MrDirRefComponent            (* a "." or ".." component *)
  | MrUnnameableComponent        (* a NUL in a component *)
  | MrShadowedByDirectory        (* "a" beside "a/b": the directory wins *)
  | MrShadowedByDevice.          (* the key is one of the two device keys *)

(** A legacy key the migration accepts: a RELATIVE path whose every
    component is nameable.  A key that is empty, begins with "/", or has
    an empty, "." or ".." component fails this -- the leading "/" and the
    empty key both leave an empty piece in the split. *)
Definition legacy_key_ok (k : path) : bool := forallb comp_ok (path_split k).

Fixpoint first_bad_comp (cs : list path) : option path :=
  match cs with
  | [] => None
  | c :: r => if comp_ok c then first_bad_comp r else Some c
  end.

Definition legacy_reject_reason (k : path) : MigrateReject :=
  match k with
  | [] => MrEmptyKey
  | b :: _ =>
      if bv_eqb b path_slash_byte then MrAbsoluteKey
      else match first_bad_comp (path_split k) with
           | None => MrEmptyKey
           | Some c =>
               if negb (comp_nonempty c) then MrEmptyComponent
               else if path_eqb c dot_comp || path_eqb c dotdot_comp
               then MrDirRefComponent
               else MrUnnameableComponent
           end
  end.

Definition legacy_accepted (legacy : list (path * list byte))
    : list (path * list byte) :=
  List.filter (fun kv => legacy_key_ok (fst kv)) legacy.

Definition legacy_rejected (legacy : list (path * list byte))
    : list (path * list byte) :=
  List.filter (fun kv => negb (legacy_key_ok (fst kv))) legacy.

(** Where a legacy key lands: under the working directory, since that is
    what the flat map's keys were relative to. *)
Definition legacy_abs (cwd k : path) : path :=
  key_of_comps (key_comps cwd ++ path_split k).

(** Number a list from [n]. *)
Fixpoint number_from {A} (n : Z) (l : list A) : list (Z * A) :=
  match l with
  | [] => []
  | x :: r => (n, x) :: number_from (n + 1)%Z r
  end.

Lemma number_from_in : forall {A} (l : list A) n ix,
  In ix (number_from n l) -> In (snd ix) l.
Proof.
  intros A l. induction l as [|x r IH]; intros n ix H; [contradiction|].
  cbn [number_from] in H. destruct H as [<-|H]; [now left|].
  right. exact (IH (n + 1)%Z ix H).
Qed.

(** Each accepted legacy file is an inode of its own, numbered from 1 in
    the order the legacy list gives, with no name outside the image. *)
Definition migrate_files (cwd : path) (legacy : list (path * list byte))
    : list (path * Entry) :=
  map (fun ikv => (legacy_abs cwd (fst (snd ikv)), EFile (fst ikv)))
      (number_from 1 (legacy_accepted legacy)).

Definition migrate_inodes (legacy : list (path * list byte))
    : list (ino * Inode) :=
  map (fun ikv => (fst ikv, mkInode (snd (snd ikv)) 0))
      (number_from 1 (legacy_accepted legacy)).

(** Every directory the migrated image needs: the standard root's, and
    every proper prefix of every accepted key. *)
Definition migrate_dirs (cwd : path) (legacy : list (path * list byte))
    : list path :=
  standard_dirs cwd
  ++ concat (map (fun kv => key_chain (path_parent (legacy_abs cwd (fst kv))))
                 (legacy_accepted legacy)).

(** THE MIGRATION.  Accepted keys become files under the working
    directory, every proper prefix becomes a directory, and the standard
    root is underneath.  The DIRECTORY WINS a file/prefix collision and
    the file is reported; the two DEVICES win over a file at their key
    and that file is reported too.

    Meaning is preserved for images whose keys are plain names, which is
    every harness recording and every Example.  A statement about a
    literal final map is RE-PINNED rather than preserved: the denoted
    image is the migrated one. *)
Definition migrate_image (cwd : path) (legacy : list (path * list byte))
    : Fs * list (path * MigrateReject) :=
  let dirs := migrate_dirs cwd legacy in
  let base := fs_set (fs_set (fs_of_list (mkFs [] (migrate_inodes legacy) [])
                                         (migrate_files cwd legacy))
                             devnull_key (EDev DevNull))
                     urandom_key (EDev DevUrandom) in
  (fs_add_dirs base dirs,
   map (fun kv => (fst kv, legacy_reject_reason (fst kv))) (legacy_rejected legacy)
   ++ map (fun kv => (fst kv, MrShadowedByDirectory))
          (List.filter (fun kv => existsb (path_eqb (legacy_abs cwd (fst kv))) dirs)
                       (legacy_accepted legacy))
   ++ map (fun kv => (fst kv, MrShadowedByDevice))
          (List.filter (fun kv => path_eqb (legacy_abs cwd (fst kv)) devnull_key
                               || path_eqb (legacy_abs cwd (fst kv)) urandom_key)
                       (legacy_accepted legacy))).

(* --- the facts the well-formedness proof is assembled from --- *)

Lemma canonical_dev_dir : canonical_key dev_dir = true.
Proof. reflexivity. Qed.

Lemma canonical_tmp_dir : canonical_key tmp_dir = true.
Proof. reflexivity. Qed.

Lemma canonical_devnull_key : canonical_key devnull_key = true.
Proof. reflexivity. Qed.

Lemma canonical_urandom_key : canonical_key urandom_key = true.
Proof. reflexivity. Qed.

Lemma canonical_default_cwd : canonical_key default_cwd = true.
Proof. reflexivity. Qed.

Lemma parent_devnull_key : path_parent devnull_key = dev_dir.
Proof. reflexivity. Qed.

Lemma parent_urandom_key : path_parent urandom_key = dev_dir.
Proof. reflexivity. Qed.

Lemma standard_dirs_dev : forall cwd, In dev_dir (standard_dirs cwd).
Proof.
  intros cwd. unfold standard_dirs. apply in_or_app. left.
  apply key_chain_self, canonical_dev_dir.
Qed.

Lemma standard_dirs_root : forall cwd, In root (standard_dirs cwd).
Proof.
  intros cwd. unfold standard_dirs. apply in_or_app. left. apply key_chain_root.
Qed.

Lemma standard_dirs_canonical : forall cwd q,
  canonical_key cwd = true -> In q (standard_dirs cwd) -> canonical_key q = true.
Proof.
  intros cwd q Hc Hq. unfold standard_dirs in Hq.
  apply in_app_or in Hq as [Hq|Hq];
    [exact (key_chain_canonical _ _ canonical_dev_dir Hq)|].
  apply in_app_or in Hq as [Hq|Hq];
    [exact (key_chain_canonical _ _ canonical_tmp_dir Hq)
    |exact (key_chain_canonical _ _ Hc Hq)].
Qed.

Lemma standard_dirs_closed : forall cwd q,
  canonical_key cwd = true -> In q (standard_dirs cwd) ->
  In (path_parent q) (standard_dirs cwd).
Proof.
  intros cwd q Hc Hq. unfold standard_dirs in Hq |- *.
  apply in_app_or in Hq as [Hq|Hq].
  { apply in_or_app. left. exact (key_chain_parent _ _ canonical_dev_dir Hq). }
  apply in_app_or in Hq as [Hq|Hq].
  - apply in_or_app. right. apply in_or_app. left.
    exact (key_chain_parent _ _ canonical_tmp_dir Hq).
  - apply in_or_app. right. apply in_or_app. right.
    exact (key_chain_parent _ _ Hc Hq).
Qed.

Lemma legacy_abs_canonical : forall cwd k,
  canonical_key cwd = true -> legacy_key_ok k = true ->
  canonical_key (legacy_abs cwd k) = true.
Proof.
  intros cwd k Hc Hk. unfold legacy_abs. apply canonical_key_of_comps.
  apply Forall_app. split; [now apply key_comps_ok|].
  apply Forall_forall. intros x Hx.
  unfold legacy_key_ok in Hk. rewrite forallb_forall in Hk. now apply Hk.
Qed.

Lemma migrate_dirs_canonical : forall cwd legacy q,
  canonical_key cwd = true -> In q (migrate_dirs cwd legacy) ->
  canonical_key q = true.
Proof.
  intros cwd legacy q Hc Hq. unfold migrate_dirs in Hq.
  apply in_app_or in Hq as [Hq|Hq]; [now apply (standard_dirs_canonical cwd)|].
  apply in_concat in Hq as [l [Hl Hq]].
  apply in_map_iff in Hl as [kv [<- Hkv]].
  refine (key_chain_canonical _ q _ Hq).
  apply canonical_key_parent, legacy_abs_canonical; [exact Hc|].
  unfold legacy_accepted in Hkv. apply filter_In in Hkv as [_ Hok]. exact Hok.
Qed.

Lemma migrate_dirs_closed : forall cwd legacy q,
  canonical_key cwd = true -> In q (migrate_dirs cwd legacy) ->
  In (path_parent q) (migrate_dirs cwd legacy).
Proof.
  intros cwd legacy q Hc Hq. unfold migrate_dirs in Hq |- *.
  apply in_app_or in Hq as [Hq|Hq].
  { apply in_or_app. left. now apply standard_dirs_closed. }
  apply in_concat in Hq as [l [Hl Hq]].
  apply in_map_iff in Hl as [kv [Heq Hkv]].
  apply in_or_app. right. apply in_concat. exists l. split.
  - apply in_map_iff. exists kv. split; [exact Heq|exact Hkv].
  - rewrite <- Heq in Hq |- *.
    apply key_chain_parent; [|exact Hq].
    apply canonical_key_parent, legacy_abs_canonical; [exact Hc|].
    unfold legacy_accepted in Hkv. apply filter_In in Hkv as [_ Hok]. exact Hok.
Qed.

Lemma migrate_dirs_root : forall cwd legacy, In root (migrate_dirs cwd legacy).
Proof.
  intros cwd legacy. unfold migrate_dirs. apply in_or_app. left.
  apply standard_dirs_root.
Qed.

Lemma migrate_dirs_dev : forall cwd legacy, In dev_dir (migrate_dirs cwd legacy).
Proof.
  intros cwd legacy. unfold migrate_dirs. apply in_or_app. left.
  apply standard_dirs_dev.
Qed.

Lemma migrate_files_canonical : forall cwd legacy k,
  canonical_key cwd = true -> In k (map fst (migrate_files cwd legacy)) ->
  canonical_key k = true.
Proof.
  intros cwd legacy k Hc Hk. unfold migrate_files in Hk.
  rewrite map_map in Hk. apply in_map_iff in Hk as [ikv [<- Hikv]].
  apply number_from_in in Hikv.
  apply legacy_abs_canonical; [exact Hc|].
  unfold legacy_accepted in Hikv. apply filter_In in Hikv as [_ Hok]. exact Hok.
Qed.

Lemma migrate_files_parent : forall cwd legacy k,
  canonical_key cwd = true -> In k (map fst (migrate_files cwd legacy)) ->
  In (path_parent k) (migrate_dirs cwd legacy).
Proof.
  intros cwd legacy k Hc Hk. unfold migrate_files in Hk.
  rewrite map_map in Hk. apply in_map_iff in Hk as [ikv [<- Hikv]].
  apply number_from_in in Hikv. cbn [fst].
  unfold migrate_dirs. apply in_or_app. right. apply in_concat.
  exists (key_chain (path_parent (legacy_abs cwd (fst (snd ikv))))). split.
  - apply in_map_iff. exists (snd ikv). split; [reflexivity|exact Hikv].
  - apply key_chain_self.
    apply canonical_key_parent, legacy_abs_canonical; [exact Hc|].
    unfold legacy_accepted in Hikv. apply filter_In in Hikv as [_ Hok]. exact Hok.
Qed.

(** An image assembled files-first, directories-last is well formed as
    soon as the directory list is prefix closed and covers every key's
    parent.  Both images below are assembled that way, which is what
    makes the directory win a collision. *)
Lemma wf_fs_build : forall base dirs,
  fs_sorted base = true ->
  (forall k, In k (map fst (fs_tree base)) -> canonical_key k = true) ->
  (forall q, In q dirs -> canonical_key q = true) ->
  (forall q, In q dirs -> In (path_parent q) dirs) ->
  In root dirs ->
  (forall k, In k (map fst (fs_tree base)) -> In (path_parent k) dirs) ->
  wf_fs (fs_add_dirs base dirs).
Proof.
  intros base dirs Hs Hbk Hdk Hdc Hr Hbp.
  unfold wf_fs. repeat split.
  - now apply fs_add_dirs_sorted.
  - apply Forall_forall. intros ke Hke.
    destruct (fs_add_dirs_in_keys dirs base (fst ke)
                (in_map fst _ _ Hke)) as [H|H];
      [now apply Hdk | now apply Hbk].
  - now apply fs_add_dirs_in.
  - apply Forall_forall. intros ke Hke.
    unfold parent_is_dir.
    assert (Hpar : In (path_parent (fst ke)) dirs).
    { destruct (fs_add_dirs_in_keys dirs base (fst ke)
                  (in_map fst _ _ Hke)) as [H|H];
        [now apply Hdc | now apply Hbp]. }
    rewrite (fs_add_dirs_in dirs base _ Hpar).
    apply Bool.orb_true_r.
Qed.

Lemma standard_base_sorted : fs_sorted standard_base = true.
Proof. reflexivity. Qed.

Lemma standard_base_keys : forall k,
  In k (map fst (fs_tree standard_base)) -> k = devnull_key \/ k = urandom_key.
Proof.
  intros k H. unfold standard_base in H.
  destruct (fs_set_in_keys _ urandom_key (EDev DevUrandom) k H) as [->|H1];
    [now right|].
  destruct (fs_set_in_keys _ devnull_key (EDev DevNull) k H1) as [->|H2];
    [now left|].
  cbn [map fs_tree fs_empty] in H2. contradiction.
Qed.

Lemma standard_root_wf : forall cwd,
  canonical_key cwd = true -> wf_fs (standard_root cwd).
Proof.
  intros cwd Hc. unfold standard_root. apply wf_fs_build.
  - exact standard_base_sorted.
  - intros k Hk. destruct (standard_base_keys k Hk) as [He|He]; rewrite He;
      [exact canonical_devnull_key | exact canonical_urandom_key].
  - intros q Hq. now apply (standard_dirs_canonical cwd).
  - intros q Hq. now apply standard_dirs_closed.
  - apply standard_dirs_root.
  - intros k Hk. destruct (standard_base_keys k Hk) as [He|He]; rewrite He.
    + rewrite parent_devnull_key. apply standard_dirs_dev.
    + rewrite parent_urandom_key. apply standard_dirs_dev.
Qed.

(** THE MIGRATION CONTRACT: whatever the legacy image was, the migrated
    one is a well-formed namespace. *)
Lemma migrate_image_wf : forall cwd legacy,
  canonical_key cwd = true -> wf_fs (fst (migrate_image cwd legacy)).
Proof.
  intros cwd legacy Hc. unfold migrate_image. cbn [fst].
  apply wf_fs_build.
  - apply fs_set_sorted, fs_set_sorted, fs_of_list_sorted. reflexivity.
  - intros k Hk.
    destruct (fs_set_in_keys _ urandom_key (EDev DevUrandom) k Hk) as [->|H1];
      [exact canonical_urandom_key|].
    destruct (fs_set_in_keys _ devnull_key (EDev DevNull) k H1) as [->|H2];
      [exact canonical_devnull_key|].
    destruct (fs_of_list_in_keys _ (mkFs [] (migrate_inodes legacy) []) k H2)
      as [H3|H3];
      [now apply (migrate_files_canonical cwd legacy)|].
    cbn [map fs_tree] in H3. contradiction.
  - intros q Hq. now apply (migrate_dirs_canonical cwd legacy).
  - intros q Hq. now apply migrate_dirs_closed.
  - apply migrate_dirs_root.
  - intros k Hk.
    destruct (fs_set_in_keys _ urandom_key (EDev DevUrandom) k Hk) as [->|H1];
      [rewrite parent_urandom_key; apply migrate_dirs_dev|].
    destruct (fs_set_in_keys _ devnull_key (EDev DevNull) k H1) as [->|H2];
      [rewrite parent_devnull_key; apply migrate_dirs_dev|].
    destruct (fs_of_list_in_keys _ (mkFs [] (migrate_inodes legacy) []) k H2)
      as [H3|H3];
      [now apply (migrate_files_parent cwd legacy)|].
    cbn [map fs_tree] in H3. contradiction.
Qed.

Lemma standard_root_wfb : forall cwd,
  canonical_key cwd = true -> wf_fsb (standard_root cwd) = true.
Proof. intros cwd Hc. apply wf_fsb_iff. now apply standard_root_wf. Qed.

Lemma migrate_image_wfb : forall cwd legacy,
  canonical_key cwd = true -> wf_fsb (fst (migrate_image cwd legacy)) = true.
Proof. intros cwd legacy Hc. apply wf_fsb_iff. now apply migrate_image_wf. Qed.

(** The empty legacy image migrates to exactly the default image. *)
Lemma migrate_image_nil : forall cwd,
  fst (migrate_image cwd []) = standard_root cwd.
Proof.
  intros cwd. unfold migrate_image, standard_root, migrate_dirs,
    migrate_files, migrate_inodes, legacy_accepted.
  cbn [List.filter map concat fst fs_of_list number_from].
  now rewrite app_nil_r.
Qed.

(** THE PREMISE OF QUESTION 1, behind ONE SWITCH.  [Run.valid_input]
    reads [standard_root_present] through
    [valid_input_requires_standard_root]; setting that to [false] is the
    whole of taking the other answer.

    The premise is "this is a Linux with a devtmpfs": the two devices are
    devices, /dev and /tmp are directories.  It is NOT that the image is
    [standard_root] -- any image holding those five entries satisfies it. *)
Definition standard_root_present (fs : Fs) : Prop :=
  fs_lookup fs dev_dir = Some EDir
  /\ fs_lookup fs tmp_dir = Some EDir
  /\ fs_lookup fs devnull_key = Some (EDev DevNull)
  /\ fs_lookup fs urandom_key = Some (EDev DevUrandom).

Definition standard_root_presentb (fs : Fs) : bool :=
  match fs_lookup fs dev_dir, fs_lookup fs tmp_dir,
        fs_lookup fs devnull_key, fs_lookup fs urandom_key with
  | Some EDir, Some EDir, Some (EDev DevNull), Some (EDev DevUrandom) => true
  | _, _, _, _ => false
  end.

Lemma standard_root_presentb_iff : forall fs,
  standard_root_presentb fs = true <-> standard_root_present fs.
Proof.
  intros fs. unfold standard_root_presentb, standard_root_present. split.
  - intros H.
    destruct (fs_lookup fs dev_dir) as [e1|] eqn:E1; [|discriminate].
    destruct e1 as [d1| |k1|b1]; try discriminate.
    destruct (fs_lookup fs tmp_dir) as [e2|] eqn:E2; [|discriminate].
    destruct e2 as [d2| |k2|b2]; try discriminate.
    destruct (fs_lookup fs devnull_key) as [e3|] eqn:E3; [|discriminate].
    destruct e3 as [d3| |k3|b3]; try discriminate.
    destruct k3; [|discriminate].
    destruct (fs_lookup fs urandom_key) as [e4|] eqn:E4; [|discriminate].
    destruct e4 as [d4| |k4|b4]; try discriminate.
    destruct k4; [discriminate|].
    now repeat split.
  - intros [H1 [H2 [H3 H4]]]. now rewrite H1, H2, H3, H4.
Qed.

(** The components of the two device keys, so the derivations below can
    name them. *)
Definition dev_comp : path :=
  [Z_to_bv 8 100; Z_to_bv 8 101; Z_to_bv 8 118].                        (* dev *)
Definition null_comp : path :=
  [Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 108; Z_to_bv 8 108].        (* null *)
Definition urandom_comp : path :=
  [Z_to_bv 8 117; Z_to_bv 8 114; Z_to_bv 8 97; Z_to_bv 8 110;
   Z_to_bv 8 100; Z_to_bv 8 111; Z_to_bv 8 109].                    (* urandom *)

Lemma split_devnull : path_split devnull_key = [[]; dev_comp; null_comp].
Proof. reflexivity. Qed.

Lemma split_urandom : path_split urandom_key = [[]; dev_comp; urandom_comp].
Proof. reflexivity. Qed.

Lemma child_root_dev : child_key root dev_comp = dev_dir.
Proof. reflexivity. Qed.

Lemma child_dev_null : child_key dev_dir null_comp = devnull_key.
Proof. reflexivity. Qed.

Lemma child_dev_urandom : child_key dev_dir urandom_comp = urandom_key.
Proof. reflexivity. Qed.

(** THE DEVICES RESOLVE DETERMINISTICALLY under the standard-root
    premise, from any working directory and for every caller that does
    not stop at the parent or demand a folder.  These two are what turn
    [Fs.standard_root_present] into today's device answers. *)
Lemma resolve_devnull : forall md fs cwd,
  mode_parent md = false -> mode_dir md = false ->
  fs_lookup fs root = Some EDir ->
  fs_lookup fs dev_dir = Some EDir ->
  fs_lookup fs devnull_key = Some (EDev DevNull) ->
  resolve md fs cwd devnull_key = (RFound devnull_key (EDev DevNull), LastNorm, false).
Proof.
  intros md fs cwd Hp Hd Hr Hdev Hn.
  rewrite (resolve_of_runs md fs cwd devnull_key
             (mkWalkRes (RFound devnull_key (EDev DevNull)) LastNorm false false false));
    [reflexivity|].
  change (resolve_start cwd devnull_key) with root. unfold walk_init.
  rewrite split_devnull.
  eapply runs_step; [eapply ws_skip; [reflexivity | exact Hr] |].
  eapply runs_step.
  { eapply ws_child; [reflexivity | reflexivity | exact Hr | rewrite Hp; reflexivity
                     | reflexivity | apply Bool.andb_false_r
                     | rewrite child_root_dev; exact Hdev | reflexivity]. }
  rewrite child_root_dev.
  eapply runs_step.
  { eapply ws_child; [reflexivity | reflexivity | exact Hdev | rewrite Hp; reflexivity
                     | reflexivity | apply Bool.andb_false_r
                     | rewrite child_dev_null; exact Hn | reflexivity]. }
  rewrite child_dev_null.
  apply runs_end. apply we_found; [exact Hn | exact Hp | left; rewrite Hd; reflexivity].
Qed.

Lemma resolve_urandom : forall md fs cwd,
  mode_parent md = false -> mode_dir md = false ->
  fs_lookup fs root = Some EDir ->
  fs_lookup fs dev_dir = Some EDir ->
  fs_lookup fs urandom_key = Some (EDev DevUrandom) ->
  resolve md fs cwd urandom_key
  = (RFound urandom_key (EDev DevUrandom), LastNorm, false).
Proof.
  intros md fs cwd Hp Hd Hr Hdev Hn.
  rewrite (resolve_of_runs md fs cwd urandom_key
             (mkWalkRes (RFound urandom_key (EDev DevUrandom)) LastNorm false false false));
    [reflexivity|].
  change (resolve_start cwd urandom_key) with root. unfold walk_init.
  rewrite split_urandom.
  eapply runs_step; [eapply ws_skip; [reflexivity | exact Hr] |].
  eapply runs_step.
  { eapply ws_child; [reflexivity | reflexivity | exact Hr | rewrite Hp; reflexivity
                     | reflexivity | apply Bool.andb_false_r
                     | rewrite child_root_dev; exact Hdev | reflexivity]. }
  rewrite child_root_dev.
  eapply runs_step.
  { eapply ws_child; [reflexivity | reflexivity | exact Hdev | rewrite Hp; reflexivity
                     | reflexivity | apply Bool.andb_false_r
                     | rewrite child_dev_urandom; exact Hn | reflexivity]. }
  rewrite child_dev_urandom.
  apply runs_end. apply we_found; [exact Hn | exact Hp | left; rewrite Hd; reflexivity].
Qed.

(** A key a lookup answers for IS a key of the tree. *)
Lemma tree_lookup_in : forall t p e, tree_lookup t p = Some e -> In (p, e) t.
Proof.
  induction t as [|[q d] r IH]; intros p e H; [discriminate|].
  cbn [tree_lookup] in H. destruct (path_eqb p q) eqn:Hpq.
  - apply path_eqb_eq in Hpq; subst q. inversion H; subst. now left.
  - right. now apply IH.
Qed.

Lemma fs_lookup_in : forall fs p e,
  fs_lookup fs p = Some e -> In (p, e) (fs_tree fs).
Proof. intros fs p e H. now apply tree_lookup_in. Qed.

(** ... AND SO IT IS CANONICAL, under [wf_fs].  This is what makes a
    RELATIVE pathname unfindable as a key in a well-formed image: a raw
    relative name is never a key, so only [resolve] reaches one. *)
Lemma wf_fs_key_canonical : forall fs p e,
  wf_fs fs -> fs_lookup fs p = Some e -> canonical_key p = true.
Proof.
  intros fs p e [_ [Hall _]] H.
  rewrite Forall_forall in Hall.
  exact (Hall (p, e) (fs_lookup_in fs p e H)).
Qed.

Lemma canonical_key_head_slash : forall p,
  canonical_key p = true -> exists r, p = path_slash_byte :: r.
Proof.
  intros [|b rest] H; [discriminate|].
  cbn [canonical_key] in H. apply Bool.andb_true_iff in H as [Hb _].
  apply bv_eqb_eq in Hb; subst b. now exists rest.
Qed.

(* -------------------------------------------------------------------------
   Preservation: what a writer of the map has to show
   ------------------------------------------------------------------------- *)

(** Is this entry a directory?  The one thing [wf_fs] reads an entry
    for, so the preservation lemmas below are stated over it rather than
    over the constructor. *)
Definition entry_is_dir (e : Entry) : bool :=
  match e with EDir => true | _ => false end.

Lemma tree_remove_in : forall t k ke, In ke (tree_remove t k) -> In ke t.
Proof.
  induction t as [|[q d] r IH]; intros k ke H; [contradiction|].
  cbn [tree_remove] in H. destruct (path_eqb k q).
  - now right.
  - destruct H as [<-|H]; [now left | right; now apply (IH k)].
Qed.

Lemma fs_remove_in : forall fs k ke,
  In ke (fs_tree (fs_remove fs k)) -> In ke (fs_tree fs).
Proof. intros fs k ke H. now apply (tree_remove_in (fs_tree fs) k). Qed.

Lemma tree_lookup_remove_neq : forall t k q,
  path_eqb q k = false -> tree_lookup (tree_remove t k) q = tree_lookup t q.
Proof.
  induction t as [|[a d] r IH]; intros k q Hne; [reflexivity|].
  cbn [tree_remove tree_lookup]. destruct (path_eqb k a) eqn:Hka.
  - apply path_eqb_eq in Hka; subst a.
    rewrite Hne. reflexivity.
  - cbn [tree_lookup]. destruct (path_eqb q a); [reflexivity|]. now apply IH.
Qed.

Lemma fs_lookup_remove_neq : forall fs k q,
  path_eqb q k = false -> fs_lookup (fs_remove fs k) q = fs_lookup fs q.
Proof. intros fs k q H. now apply tree_lookup_remove_neq. Qed.

(** The two projections of [wf_fs] a preservation proof reads. *)
Lemma wf_fs_canonical_of_key : forall fs q,
  wf_fs fs -> In q (map fst (fs_tree fs)) -> canonical_key q = true.
Proof.
  intros fs q [_ [Hall _]] Hin.
  apply in_map_iff in Hin as [ke [<- Hke]].
  rewrite Forall_forall in Hall. now apply Hall.
Qed.

Lemma wf_fs_parent_of_key : forall fs q,
  wf_fs fs -> In q (map fst (fs_tree fs)) -> parent_is_dir fs q = true.
Proof.
  intros fs q [_ [_ [_ Hall]]] Hin.
  apply in_map_iff in Hin as [ke [<- Hke]].
  rewrite Forall_forall in Hall. now apply Hall.
Qed.

Lemma parent_is_dir_lookup : forall fs q,
  parent_is_dir fs q = true -> path_eqb q root = true
  \/ fs_lookup fs (path_parent q) = Some EDir.
Proof.
  intros fs q H. unfold parent_is_dir in H.
  destruct (path_eqb q root); [now left|].
  right. cbn [orb] in H.
  destruct (fs_lookup fs (path_parent q)) as [[d| |dk|lb]|]; congruence.
Qed.

Lemma parent_is_dir_of_lookup : forall fs q,
  fs_lookup fs (path_parent q) = Some EDir -> parent_is_dir fs q = true.
Proof.
  intros fs q H. unfold parent_is_dir. rewrite H. apply Bool.orb_true_r.
Qed.

(** WRITE, PWRITE, WRITEV, FTRUNCATE: replacing an EXISTING key's entry
    with one of the same kind preserves well-formedness, whatever the
    key is.  No canonicity hypothesis is needed -- the key is already in
    the map, so [wf_fs] already says it is one. *)
Lemma wf_fs_set_replace : forall fs k e e',
  wf_fs fs -> fs_lookup fs k = Some e ->
  entry_is_dir e = entry_is_dir e' ->
  wf_fs (fs_set fs k e').
Proof.
  intros fs k e e' Hwf Hlk Hkind.
  assert (Hin : In (k, e) (fs_tree fs)) by (now apply fs_lookup_in).
  assert (Hck : canonical_key k = true).
  { apply (wf_fs_canonical_of_key fs k Hwf).
    change k with (fst (k, e)). now apply in_map. }
  destruct Hwf as (Hs & Hcan & Hroot & Hpar).
  assert (Hwf : wf_fs fs) by (repeat split; assumption).
  (* the parent of any key keeps its directoriness *)
  assert (Hpres : forall q, parent_is_dir fs q = true ->
                            parent_is_dir (fs_set fs k e') q = true).
  { intros q Hq. destruct (parent_is_dir_lookup fs q Hq) as [Hr|Hpq].
    - unfold parent_is_dir. rewrite Hr. reflexivity.
    - apply parent_is_dir_of_lookup.
      destruct (path_eqb (path_parent q) k) eqn:Hpk.
      + apply path_eqb_eq in Hpk. rewrite Hpk in Hpq.
        rewrite Hpq in Hlk. inversion Hlk; subst e.
        cbn [entry_is_dir] in Hkind.
        destruct e' as [d'| |dk'|lb']; try discriminate.
        rewrite Hpk. apply fs_lookup_set_eq.
      + rewrite (fs_lookup_set_neq fs k (path_parent q) e' Hpk). exact Hpq. }
  repeat split.
  - now apply fs_set_sorted.
  - apply (tree_set_keys (fun q => canonical_key q = true));
      [exact Hcan | exact Hck].
  - destruct (path_eqb root k) eqn:Hrk.
    + apply path_eqb_eq in Hrk. rewrite <- Hrk in Hlk.
      rewrite Hroot in Hlk. inversion Hlk; subst e.
      cbn [entry_is_dir] in Hkind.
      destruct e' as [d'| |dk'|lb']; try discriminate.
      rewrite <- Hrk. apply fs_lookup_set_eq.
    + rewrite (fs_lookup_set_neq fs k root e' Hrk). exact Hroot.
  - apply Forall_forall. intros ke Hke. apply Hpres.
    destruct (fs_set_in_keys fs k e' (fst ke) (in_map fst _ _ Hke))
      as [Heq|Hin'].
    + rewrite Heq. apply (wf_fs_parent_of_key fs k Hwf).
      change k with (fst (k, e)). now apply in_map.
    + now apply (wf_fs_parent_of_key fs (fst ke) Hwf).
Qed.

(** UNLINK: removing a NON-DIRECTORY preserves well-formedness.  No key
    can have a non-directory as its parent under [wf_fs], so nothing is
    orphaned, and the root is a directory so it is not the key removed.
    A descriptor on a removed file holds its inode, not the key
    ([fs_unlink_file] keeps the row), so no descriptor is left naming
    something the image lost. *)
Lemma wf_fs_remove_file : forall fs k e,
  wf_fs fs -> fs_lookup fs k = Some e -> entry_is_dir e = false ->
  wf_fs (fs_remove fs k).
Proof.
  intros fs k e Hwf Hlk Hkind.
  assert (Hnotpar : forall q, fs_lookup fs (path_parent q) = Some EDir ->
                              path_eqb (path_parent q) k = false).
  { intros q Hq. destruct (path_eqb (path_parent q) k) eqn:Hpk; [|reflexivity].
    apply path_eqb_eq in Hpk. rewrite Hpk, Hlk in Hq.
    inversion Hq; subst e. discriminate. }
  destruct Hwf as (Hs & Hcan & Hroot & Hpar).
  assert (Hwf : wf_fs fs) by (repeat split; assumption).
  assert (Hrk : path_eqb root k = false).
  { destruct (path_eqb root k) eqn:E; [|reflexivity].
    apply path_eqb_eq in E. rewrite <- E, Hroot in Hlk.
    inversion Hlk; subst e. discriminate. }
  repeat split.
  - now apply fs_remove_sorted.
  - apply Forall_forall. intros ke Hke.
    rewrite Forall_forall in Hcan. apply Hcan. now apply (fs_remove_in fs k).
  - rewrite (fs_lookup_remove_neq fs k root Hrk). exact Hroot.
  - apply Forall_forall. intros ke Hke.
    assert (Hke' : In ke (fs_tree fs)) by (now apply (fs_remove_in fs k)).
    rewrite Forall_forall in Hpar.
    destruct (parent_is_dir_lookup fs (fst ke) (Hpar ke Hke')) as [Hr|Hpq].
    + unfold parent_is_dir. rewrite Hr. reflexivity.
    + apply parent_is_dir_of_lookup.
      rewrite (fs_lookup_remove_neq fs k (path_parent (fst ke))
                 (Hnotpar (fst ke) Hpq)).
      exact Hpq.
Qed.

(** DOES ANY ENTRY SIT DIRECTLY UNDER [k]?  A directory is non-empty
    exactly when some key's parent is it: the image holds every entry
    under its own absolute key, and [wf_fs]'s fourth conjunct says every
    key's parent is a directory in the image, so "has a child" and "has
    an entry whose parent key is [k]" are the same question.

    THE ROOT IS NEVER REPORTED EMPTY, and nothing rests on it:
    [path_parent root] is [root], so the root's own entry makes it its
    own child.  [Sys.Fs.Namei]'s rmdir answers the root -EBUSY off the
    last component's kind before this is reached. *)
Definition fs_has_child (fs : Fs) (k : path) : bool :=
  existsb (fun ke => path_eqb (path_parent (fst ke)) k) (fs_tree fs).

Definition fs_dir_empty (fs : Fs) (k : path) : bool :=
  negb (fs_has_child fs k).

Lemma fs_has_child_false : forall fs k ke,
  fs_has_child fs k = false -> In ke (fs_tree fs) ->
  path_eqb (path_parent (fst ke)) k = false.
Proof.
  intros fs k ke H Hin. unfold fs_has_child in H.
  destruct (path_eqb (path_parent (fst ke)) k) eqn:E; [|reflexivity].
  exfalso. apply Bool.not_true_iff_false in H. apply H.
  apply existsb_exists. exists ke. split; assumption.
Qed.

(** RMDIR: removing an EMPTY DIRECTORY preserves well-formedness.

    EMPTINESS IS EXACTLY WHAT IS NEEDED, and it is needed for two
    different conjuncts at once.  Nothing is orphaned, because a key
    whose parent were [k] would be a child; and the root survives,
    because the root is its own parent and therefore its own child, so
    an empty directory is never the root.  [fs_remove_sorted] carries
    the canonical form and the keys that remain were keys already.

    THE DESCRIPTOR INVARIANT IS NOT PRESERVED BY THIS, exactly as it is
    not by [wf_fs_remove_file]: rmdir can remove a directory an open
    [State.FdDir] names.  [Sys.Fs.Namei.rmdir_spec]'s guard is what
    stands in for it, and it is stated over
    [Sys.Fs.Namei.fd_names_dir] rather than here. *)
Lemma wf_fs_remove_empty_dir : forall fs k,
  wf_fs fs -> fs_lookup fs k = Some EDir ->
  fs_has_child fs k = false ->
  wf_fs (fs_remove fs k).
Proof.
  intros fs k Hwf Hlk Hempty.
  destruct Hwf as (Hs & Hcan & Hroot & Hpar).
  assert (Hrootin : In (root, EDir) (fs_tree fs)) by (now apply fs_lookup_in).
  assert (Hrk : path_eqb root k = false).
  { destruct (path_eqb root k) eqn:E; [|reflexivity].
    exfalso. apply path_eqb_eq in E.
    pose proof (fs_has_child_false fs k (root, EDir) Hempty Hrootin) as Hc.
    cbn [fst] in Hc. rewrite path_parent_root, <- E in Hc.
    rewrite path_eqb_refl in Hc. discriminate. }
  repeat split.
  - now apply fs_remove_sorted.
  - apply Forall_forall. intros ke Hke.
    rewrite Forall_forall in Hcan. apply Hcan. now apply (fs_remove_in fs k).
  - rewrite (fs_lookup_remove_neq fs k root Hrk). exact Hroot.
  - apply Forall_forall. intros ke Hke.
    assert (Hke' : In ke (fs_tree fs)) by (now apply (fs_remove_in fs k)).
    rewrite Forall_forall in Hpar.
    destruct (parent_is_dir_lookup fs (fst ke) (Hpar ke Hke')) as [Hr|Hpq].
    + unfold parent_is_dir. rewrite Hr. reflexivity.
    + apply parent_is_dir_of_lookup.
      rewrite (fs_lookup_remove_neq fs k (path_parent (fst ke))
                 (fs_has_child_false fs k ke Hempty Hke')).
      exact Hpq.
Qed.

(** CREATE: adding a key needs the key CANONICAL and its parent a
    DIRECTORY -- exactly the pair [RMissing] delivers
    ([resolve_missing_parent] below).  The key must be absent, which is
    what makes it a create rather than a replace and what rules out the
    root.

    A creating arm discharges it off [Fs.resolve]'s [RMissing]: the
    key it creates at is the walk's, never the raw pathname a program
    passed.  [State.model_fs_wf_create_at] is the same obligation at
    the level of the model. *)
Lemma wf_fs_set_create : forall fs k e,
  wf_fs fs -> canonical_key k = true ->
  fs_lookup fs k = None ->
  fs_lookup fs (path_parent k) = Some EDir ->
  wf_fs (fs_set fs k e).
Proof.
  intros fs k e Hwf Hck Habs Hparent.
  assert (Hpk : path_eqb (path_parent k) k = false).
  { destruct (path_eqb (path_parent k) k) eqn:E; [|reflexivity].
    apply path_eqb_eq in E. rewrite E, Habs in Hparent. discriminate. }
  assert (Hnotpar : forall q, fs_lookup fs (path_parent q) = Some EDir ->
                              path_eqb (path_parent q) k = false).
  { intros q Hq. destruct (path_eqb (path_parent q) k) eqn:E; [|reflexivity].
    apply path_eqb_eq in E. rewrite E, Habs in Hq. discriminate. }
  destruct Hwf as (Hs & Hcan & Hroot & Hpar).
  assert (Hwf : wf_fs fs) by (repeat split; assumption).
  assert (Hrk : path_eqb root k = false).
  { destruct (path_eqb root k) eqn:E; [|reflexivity].
    apply path_eqb_eq in E. rewrite <- E, Hroot in Habs. discriminate. }
  repeat split.
  - now apply fs_set_sorted.
  - apply (tree_set_keys (fun q => canonical_key q = true));
      [exact Hcan | exact Hck].
  - rewrite (fs_lookup_set_neq fs k root e Hrk). exact Hroot.
  - apply Forall_forall. intros ke Hke.
    destruct (fs_set_in_keys fs k e (fst ke) (in_map fst _ _ Hke))
      as [Heq|Hin'].
    + rewrite Heq. apply parent_is_dir_of_lookup.
      rewrite (fs_lookup_set_neq fs k (path_parent k) e Hpk). exact Hparent.
    + destruct (parent_is_dir_lookup fs (fst ke)
                  (wf_fs_parent_of_key fs (fst ke) Hwf Hin')) as [Hr|Hpq].
      * unfold parent_is_dir. rewrite Hr. reflexivity.
      * apply parent_is_dir_of_lookup.
        rewrite (fs_lookup_set_neq fs k (path_parent (fst ke)) e
                   (Hnotpar (fst ke) Hpq)).
        exact Hpq.
Qed.

(** The writers of the two tables, and the name writers that go with
    them: each keeps [wf_fs] exactly when its name change does, since the
    predicate reads the tree alone. *)
Lemma wf_fs_set_ino_data : forall fs i d,
  wf_fs fs -> wf_fs (fs_set_ino_data fs i d).
Proof. intros fs i d H. exact (wf_fs_same_tree fs _ eq_refl H). Qed.

Lemma wf_fs_create_file : forall fs k d,
  wf_fs fs -> canonical_key k = true -> fs_lookup fs k = None ->
  fs_lookup fs (path_parent k) = Some EDir -> wf_fs (fs_create_file fs k d).
Proof.
  intros fs k d Hwf Hck Habs Hpar. unfold fs_create_file. cbv zeta.
  apply wf_fs_set_create; [|exact Hck|exact Habs|exact Hpar].
  exact (wf_fs_same_tree fs _ eq_refl Hwf).
Qed.

Lemma fs_tree_unlink_file : forall fs k i held,
  fs_tree (fs_unlink_file fs k i held) = fs_tree (fs_remove fs k).
Proof.
  intros fs k i held. unfold fs_unlink_file. cbv zeta.
  destruct (Nat.eqb (fs_ino_names (fs_remove fs k) i) 0); [destruct held|]; reflexivity.
Qed.

Lemma wf_fs_unlink_file : forall fs k i held,
  wf_fs fs -> fs_lookup fs k = Some (EFile i) -> wf_fs (fs_unlink_file fs k i held).
Proof.
  intros fs k i held Hwf Hlk.
  apply (wf_fs_same_tree (fs_remove fs k)); [apply fs_tree_unlink_file|].
  now apply (wf_fs_remove_file fs k (EFile i)).
Qed.

Lemma wf_fs_mkdir : forall fs k,
  wf_fs fs -> canonical_key k = true -> fs_lookup fs k = None ->
  fs_lookup fs (path_parent k) = Some EDir -> wf_fs (fs_mkdir fs k).
Proof.
  intros fs k Hwf Hck Habs Hpar.
  apply (wf_fs_same_tree (fs_set fs k EDir)); [apply fs_tree_mkdir|].
  now apply wf_fs_set_create.
Qed.

Lemma wf_fs_rmdir : forall fs k,
  wf_fs fs -> fs_lookup fs k = Some EDir -> fs_has_child fs k = false ->
  wf_fs (fs_rmdir fs k).
Proof.
  intros fs k Hwf Hlk Hempty.
  apply (wf_fs_same_tree (fs_remove fs k)); [apply fs_tree_rmdir|].
  now apply wf_fs_remove_empty_dir.
Qed.

(* -------------------------------------------------------------------------
   What [RMissing] delivers, and what a create does with it
   ------------------------------------------------------------------------- *)

(** An [RMissing] names a folder the image holds and a normal name with
    nothing at its key. *)
Lemma walk_runs_missing : forall fs md s w, walk_runs fs md s w ->
  forall par nm, wr_res w = RMissing par nm ->
  fs_lookup fs par = Some EDir /\ fs_lookup fs (child_key par nm) = None
  /\ comp_nonempty nm = true /\ comp_kind nm = LastNorm.
Proof.
  intros fs md s w H. induction H as [s w He | s s' w _ _ IH]; [|exact IH].
  intros par nm Hw. destruct He; cbn [wr_res] in Hw; try discriminate.
  destruct (comps_done r); [|discriminate]. injection Hw as <- <-.
  repeat split; assumption.
Qed.

(** THE KEY DISCIPLINE ALONG A WALK: it stands on canonical keys, and
    every normal name it may still look up is nameable. *)
Definition walk_ok (s : WSt) : Prop :=
  canonical_key (st_cur s) = true /\
  (forall c, In c (st_rest s) -> comp_nonempty c = true ->
             comp_kind c = LastNorm -> comp_ok c = true).

Lemma comp_kind_norm_eqb : forall c, comp_kind c = LastNorm ->
  path_eqb c dot_comp = false /\ path_eqb c dotdot_comp = false.
Proof.
  intros c H. unfold comp_kind in H.
  destruct (path_eqb c dot_comp); [discriminate|].
  destruct (path_eqb c dotdot_comp); [discriminate|]. split; reflexivity.
Qed.

(** A link body as the walk reads it holds no NUL. *)
Lemma link_text_nul_free : forall b, path_nul_free (link_text b) = true.
Proof.
  induction b as [|x r IH]; [reflexivity|]. cbn [link_text].
  destruct (bv_eqb x path_nul_byte) eqn:Hx; [reflexivity|].
  unfold path_nul_free in *. cbn [existsb]. rewrite Hx. cbn [orb]. exact IH.
Qed.

Lemma walk_step_ok : forall fs md s s', walk_step fs md s s' -> walk_ok s -> walk_ok s'.
Proof.
  intros fs md s s' H [Hk Hr]. destruct H; cbn [st_cur st_rest] in *; split.
  - exact Hk.
  - intros x Hx. apply Hr. now right.
  - exact Hk.
  - intros x Hx. apply Hr. now right.
  - now apply canonical_key_parent.
  - intros x Hx. apply Hr. now right.
  - apply canonical_key_child; [exact Hk|].
    apply Hr; [now left | assumption | assumption].
  - intros x Hx. apply Hr. now right.
  - unfold link_start. destruct (path_absolute (link_text b)); [reflexivity | exact Hk].
  - intros x Hx Hne Hkind. apply in_app_or in Hx as [Hx|Hx].
    + destruct (comp_kind_norm_eqb x Hkind) as [Hd Hdd].
      exact (comp_ok_of_step (link_text b) x (link_text_nul_free b) Hx Hne Hd Hdd).
    + apply Hr; [now right | exact Hne | exact Hkind].
Qed.

Lemma walk_runs_missing_ok : forall fs md s w, walk_runs fs md s w -> walk_ok s ->
  forall par nm, wr_res w = RMissing par nm ->
  canonical_key par = true /\ comp_ok nm = true.
Proof.
  intros fs md s w H. induction H as [s w He | s s' w Hst _ IH]; intros Hok par nm Hw.
  - destruct Hok as [Hk Hr]. destruct He; cbn [wr_res st_cur st_rest] in *;
      try discriminate.
    destruct (comps_done r); [|discriminate]. injection Hw as <- <-.
    split; [exact Hk|]. apply Hr; [now left | assumption | assumption].
  - exact (IH (walk_step_ok fs md s s' Hst Hok) par nm Hw).
Qed.

(** WHAT A CREATE ARM NEEDS, off one [RMissing]: the parent is a
    canonical key; the name is a nameable component; the child key is
    canonical; its parent is the parent the walk stopped at; the parent
    is a DIRECTORY in the image; and nothing is at the child key yet.
    Together with [wf_fs_set_create] they are the whole of "creating
    under [RMissing] keeps the image well formed".  The name may be a
    followed body's last name: a body is read to its first NUL, so its
    names are nameable too. *)
Lemma resolve_missing_parent : forall md fs cwd p par nm lk ts,
  path_nul_free p = true ->
  canonical_key cwd = true ->
  resolve md fs cwd p = (RMissing par nm, lk, ts) ->
  canonical_key par = true
  /\ comp_ok nm = true
  /\ canonical_key (child_key par nm) = true
  /\ path_parent (child_key par nm) = par
  /\ fs_lookup fs par = Some EDir
  /\ fs_lookup fs (child_key par nm) = None.
Proof.
  intros md fs cwd p par nm lk ts Hnul Hcwd H.
  unfold resolve in H. cbv zeta in H. injection H as Hw _ _.
  assert (Hrun := proj1 (resolve_spec md fs cwd p _) eq_refl).
  assert (Hok : walk_ok (walk_init md link_max (resolve_start cwd p) p)).
  { split; cbn [st_cur st_rest walk_init].
    - unfold resolve_start. destruct (path_absolute p); [reflexivity | exact Hcwd].
    - intros c Hc Hne Hk. destruct (comp_kind_norm_eqb c Hk) as [Hd Hdd].
      exact (comp_ok_of_step p c Hnul Hc Hne Hd Hdd). }
  destruct (walk_runs_missing_ok _ _ _ _ Hrun Hok par nm Hw) as [Hpar Hnm].
  destruct (walk_runs_missing _ _ _ _ Hrun par nm Hw) as (Hlk & Habs & _ & _).
  repeat split; try assumption.
  - now apply canonical_key_child.
  - now apply path_parent_child.
Qed.

(** WHAT THE PARENT END DELIVERS: a folder the image holds, at a
    canonical key, and a last name that is empty (no component) or a
    component whose type the result reports and which, if normal, is
    nameable. *)
Lemma walk_runs_parent_ok : forall fs md s w, walk_runs fs md s w -> walk_ok s ->
  forall dir nm, wr_res w = RParent dir nm ->
  fs_lookup fs dir = Some EDir /\ canonical_key dir = true
  /\ (nm = [] /\ wr_kind w = LastRoot
      \/ wr_kind w = comp_kind nm /\ (comp_kind nm = LastNorm -> comp_ok nm = true)).
Proof.
  intros fs md s w H. induction H as [s w He | s s' w Hst _ IH]; intros Hok dir nm Hw.
  - destruct Hok as [Hk Hr]. destruct He; cbn [wr_res wr_kind st_cur st_rest] in *;
      try discriminate; try (destruct (comps_done r); discriminate);
      injection Hw as <- <-.
    + repeat split; [assumption | assumption | left; split; reflexivity].
    + repeat split; [assumption | assumption |]. right. split; [reflexivity|].
      intros Hn. apply Hr; [now left | assumption | exact Hn].
    + repeat split; [assumption | assumption |]. right. split; [symmetry; assumption|].
      intros Hn. apply Hr; [now left | assumption | exact Hn].
  - exact (IH (walk_step_ok fs md s s' Hst Hok) dir nm Hw).
Qed.

(** The parent end never answers [RMissing]: its last name is not looked
    up by the walk. *)
Lemma walk_runs_parent_no_missing : forall fs s w, walk_runs fs WalkParent s w ->
  forall par nm, wr_res w <> RMissing par nm.
Proof.
  intros fs s w H. induction H as [s w He | s s' w _ _ IH]; [|exact IH].
  intros par nm Hw. destruct He; cbn [wr_res mode_parent andb] in *; try discriminate.
  rewrite H2 in Hw. discriminate.
Qed.

(** ... so the last name a parent-end call creates at is nameable, under
    a canonical folder the image holds, with nothing at its key yet:
    the premises of [wf_fs_mkdir]. *)
Lemma resolve_parent_missing : forall fs cwd p par nm lk ts,
  path_nul_free p = true ->
  canonical_key cwd = true ->
  resolve_parent fs cwd p = (RMissing par nm, lk, ts) ->
  canonical_key par = true
  /\ comp_ok nm = true
  /\ canonical_key (child_key par nm) = true
  /\ path_parent (child_key par nm) = par
  /\ fs_lookup fs par = Some EDir
  /\ fs_lookup fs (child_key par nm) = None.
Proof.
  intros fs cwd p par nm lk ts Hnul Hcwd H.
  unfold resolve_parent, resolve in H. cbv beta iota zeta in H.
  remember (resolve_res WalkParent fs cwd p) as w eqn:Hw.
  assert (Hrun := proj1 (resolve_spec WalkParent fs cwd p w) (eq_sym Hw)).
  assert (Hok : walk_ok (walk_init WalkParent link_max (resolve_start cwd p) p)).
  { split; cbn [st_cur st_rest walk_init].
    - unfold resolve_start. destruct (path_absolute p); [reflexivity | exact Hcwd].
    - intros c Hc Hne Hk. destruct (comp_kind_norm_eqb c Hk) as [Hd Hdd].
      exact (comp_ok_of_step p c Hnul Hc Hne Hd Hdd). }
  injection H as Hr Hlk _.
  unfold parent_last in Hr.
  destruct (wr_res w) as [k e|p0 n0| | | | |dir nm'] eqn:Hres; try discriminate.
  { exfalso. exact (walk_runs_parent_no_missing _ _ _ Hrun p0 n0 Hres). }
  destruct (wr_kind w) eqn:Hkind; try discriminate.
  destruct (at_outside dir nm') eqn:Hout; [discriminate|].
  destruct (fs_lookup fs (child_key dir nm')) eqn:Hc; [discriminate|].
  injection Hr as <- <-.
  destruct (walk_runs_parent_ok _ _ _ _ Hrun Hok dir nm' Hres)
    as (Hdir & Hcan & [[_ Hroot] | [Hk Hnm]]); [congruence|].
  assert (Hok' : comp_ok nm' = true) by (apply Hnm; congruence).
  repeat split; try assumption.
  - now apply canonical_key_child.
  - now apply path_parent_child.
Qed.

(** A step that reads only keys the image holds reads them alike once an
    ABSENT key is set. *)
Lemma lookup_set_other : forall fs t e q x,
  fs_lookup fs q = Some x -> fs_lookup fs t = None ->
  fs_lookup (fs_set fs t e) q = Some x.
Proof.
  intros fs t e q x Hq Ht.
  assert (Hne : path_eqb q t = false).
  { apply path_eqb_false_of_neq. intros ->. congruence. }
  rewrite (fs_lookup_set_neq fs t q e Hne). exact Hq.
Qed.

Lemma walk_step_set_absent : forall fs md s s' t e,
  walk_step fs md s s' -> fs_lookup fs t = None -> walk_step (fs_set fs t e) md s s'.
Proof.
  intros fs md s s' t e H Ht. destruct H;
    [ eapply ws_skip | eapply ws_dot | eapply ws_dotdot | eapply ws_child
    | eapply ws_link ];
    try eassumption; apply lookup_set_other; eassumption.
Qed.

(** Under [O_CREAT] the walk never sets [LOOKUP_DIRECTORY]: a last name
    with a separator stops it first ([we_create_slash]). *)
Lemma walk_step_create_dir : forall fs f s s',
  walk_step fs (WalkCreate f) s s' -> st_dir s = false -> st_dir s' = false.
Proof.
  intros fs f s s' H Hd.
  destruct H; cbn [st_dir mode_create andb] in *; try assumption;
    match goal with Hc : last_slash _ = false |- _ =>
      rewrite Hc, Bool.orb_false_r; assumption end.
Qed.

(** Separators left over walk to nothing. *)
Lemma walk_runs_skip_done : forall fs md k r n f d lk ts fd lg e w,
  comps_done r = true -> fs_lookup fs k = Some e ->
  walk_runs fs md (mkWSt k [] n f d lk ts fd lg) w ->
  walk_runs fs md (mkWSt k r n f d lk ts fd lg) w.
Proof.
  intros fs md k r. induction r as [|c r IH]; intros n f d lk ts fd lg e w Hr He H;
    [exact H|].
  cbn [comps_done forallb] in Hr. apply Bool.andb_true_iff in Hr as [Hc Hr].
  apply Bool.negb_true_iff in Hc.
  eapply runs_step; [eapply ws_skip; [exact Hc | exact He] |].
  eapply IH; eassumption.
Qed.

(** CREATING AT THE MISSING KEY is seen by a later walk of the same
    pathname, through any link that led there. *)
Lemma walk_runs_create_set : forall fs f s w, walk_runs fs (WalkCreate f) s w ->
  st_dir s = false ->
  forall par nm e, wr_res w = RMissing par nm ->
  entry_is_link e = false ->
  walk_runs (fs_set fs (child_key par nm) e) (WalkCreate f) s
    (mkWalkRes (RFound (child_key par nm) e) (wr_kind w) (wr_slash w)
       (wr_followed w) (wr_long w)).
Proof.
  intros fs f s w H. induction H as [s w He | s s' w Hst Hrun IH];
    intros Hd par nm e Hw Hl.
  - destruct He; cbn [wr_res wr_kind wr_slash wr_followed wr_long st_dir] in *;
      try discriminate.
    destruct (comps_done r) eqn:Hdone; [|discriminate]. injection Hw as <- <-.
    assert (Hls : last_slash r = false) by (cbn [mode_create andb] in H4; exact H4).
    assert (Hkk : fs_lookup (fs_set fs (child_key k c) e) k = Some EDir)
      by (apply lookup_set_other; assumption).
    assert (Hkc : fs_lookup (fs_set fs (child_key k c) e) (child_key k c) = Some e)
      by apply fs_lookup_set_eq.
    eapply runs_step.
    { eapply ws_child; try eassumption.
      destruct e as [i| |dk|b];
        [reflexivity | reflexivity | reflexivity | cbn in Hl; discriminate Hl]. }
    eapply walk_runs_skip_done; [exact Hdone | exact Hkc |].
    apply runs_end. apply we_found; [exact Hkc | reflexivity |].
    left. subst d. rewrite Hls. reflexivity.
  - destruct (walk_runs_missing _ _ _ _ Hrun par nm Hw) as (_ & Habs & _ & _).
    eapply runs_step; [exact (walk_step_set_absent fs _ s s' _ e Hst Habs) |].
    apply IH; [exact (walk_step_create_dir fs f s s' Hst Hd) | exact Hw | exact Hl].
Qed.

(** CREATING AT THE MISSING KEY keeps the image well formed AND is seen
    by a later walk of the same pathname.  This is the pair an [O_CREAT]
    arm's soundness proof is built from. *)
Lemma resolve_missing_create : forall f fs cwd p par nm lk ts e,
  wf_fs fs ->
  path_nul_free p = true ->
  canonical_key cwd = true ->
  resolve (WalkCreate f) fs cwd p = (RMissing par nm, lk, ts) ->
  entry_is_link e = false ->
  wf_fs (fs_set fs (child_key par nm) e)
  /\ resolve (WalkCreate f) (fs_set fs (child_key par nm) e) cwd p
     = (RFound (child_key par nm) e, lk, ts).
Proof.
  intros f fs cwd p par nm lk ts e Hwf Hnul Hcwd H Hl.
  destruct (resolve_missing_parent _ fs cwd p par nm lk ts Hnul Hcwd H)
    as (Hpar & Hnm & Hck & Hpp & Hlk & Habs).
  split.
  - apply (wf_fs_set_create fs (child_key par nm) e Hwf Hck Habs).
    rewrite Hpp. exact Hlk.
  - unfold resolve in H. cbv zeta in H. injection H as Hw Hk Hs.
    assert (Hrun := proj1 (resolve_spec (WalkCreate f) fs cwd p _) eq_refl).
    rewrite (resolve_of_runs _ _ cwd p _
               (walk_runs_create_set fs f _ _ Hrun eq_refl par nm e Hw Hl)).
    cbn [wr_res wr_kind wr_slash]. rewrite Hk, Hs. reflexivity.
Qed.
