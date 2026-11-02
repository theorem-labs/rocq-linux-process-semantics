(** * LinuxProcessSem.Checks.AnonAgree — the arms that answer keep an unnamed file's descriptors agreeing

    The contents and the stat pin of an unnamed file are REPLICATED, one
    copy in each of its descriptors ([State.FdAnon]), and
    [State.anon_agree fds id af] says that every [FdAnon] entry of file
    [id] in the table [fds] carries the contents and the pin of [af].
    Every arm that reads an unnamed file's contents or pin declines when
    that test fails: [Fs.ReadWrite]'s read, write, writev, pwrite64,
    pwritev2 and lseek, [Fs.Open]'s ftruncate and "/proc/self/fd/N"
    reopen, and [Fs.Stat]'s fstat.

    The lemmas below are what makes that decline UNREACHABLE FROM A
    LAUNCH.  No launch holds an [FdAnon], so every file id agrees at the
    start ([anon_agree_init_model]), and every table change the
    answering arms make to an unnamed file's descriptors keeps the
    descriptors of each file agreeing:

    - (a) [anon_agree_set_data]: the contents written to every
      descriptor of the file (ftruncate, pwrite64, pwritev2, the
      contents half of write and writev),
      [anon_agree fds id af = true ->
       anon_agree (anon_set_data fds id d) id (af_set_data af d) = true];
    - (b) [anon_agree_write_back]: a transfer through descriptor [fd],
      the contents to every descriptor and the offset to [fd]'s own
      (write, writev),
      [anon_agree fds id af = true ->
       anon_agree (anon_write_back fds fd id af d o) id
         (af_set_off (af_set_data af d) o) = true];
    - (c) [anon_agree_reopen]: a "/proc/self/fd/N" reopen under O_RDONLY
      or O_WRONLY|O_CREAT|O_APPEND, a new descriptor with the contents
      and the pin of the agreeing one,
      [anon_agree fds id af = true ->
       anon_agree (fd_insert fds fd
         (FdAnon id (mkAnonFile (af_data af) o r w a (af_pin af)))) id af = true];
    - (c) [anon_agree_reopen_trunc]: the O_WRONLY|O_CREAT|O_TRUNC reopen,
      the file emptied for every descriptor and a new one on the empty
      file,
      [anon_agree fds id af = true ->
       anon_agree (fd_insert (anon_set_data fds id []) fd
         (FdAnon id (mkAnonFile [] o r w a (af_pin af)))) id
         (af_set_data af []) = true];
    - (d) [anon_agree_fd_remove]: a close removes one entry,
      [anon_agree fds id af = true ->
       anon_agree (fd_remove fds fd) id af = true];
    - (e) [anon_agree_unlink_open]: the removal of a /tmp name open
      descriptors hold ([Fs.Namei.unlink_open_tmp_spec]) gives every
      descriptor it converts the same contents and pin under one fresh
      id, so on EVERY table where that id is not live,
      [anon_id_live fds id = false ->
       anon_agree (map (fun q => (fst q, unlink_open_entry c id data pin (snd q))) fds)
         id (mkAnonFile data o r w a pin) = true],
      whatever offset, access mode and O_APPEND [o r w a] the view
      carries.

    The same argument needs four more steps, stated here too:
    [anon_agree_set_pin], the pin a first fstat writes to every
    descriptor of the file ([State.anon_update]),
    [anon_agree fds id af = true ->
     anon_agree (anon_update fds id (fun a => af_set_pin a bs)) id
       (af_set_pin af bs) = true];
    [anon_agree_set_off], the offset a read or an lseek writes to its own
    descriptor,
    [anon_agree fds id af = true ->
     anon_agree (fd_insert fds fd (FdAnon id (af_set_off af o))) id af = true];
    and, for the OTHER files of the table, [anon_agree_update_other]
    ([id <> id2 -> anon_agree fds id2 af2 = true ->
      anon_agree (anon_update fds id f) id2 af2 = true]) and
    [anon_agree_unlink_open_other] (the same for the removal's map).
    [anon_agree_fd_insert] covers an inserted entry of any kind that
    agrees, which every entry that is not a descriptor of the file does.

    NOT PROVED: that no OTHER arm writes an [FdAnon] entry.  It holds by
    reading the arms: [dup], [dup3], [F_DUPFD] and a [clone] that holds
    one decline ([Fs.File.dup_modeled_entry],
    [Kernel.Fork.clone_no_shared_file_b]), and no other arm makes one.
    The obligation is one named predicate, [State.anon_agree], which all
    nine answering arms call, so a reader of a new arm sees the others
    calling it.

    THE TRIGGER for moving it into a global well-formedness predicate,
    decided by the LPS revision owner (2026-11-01, on
    dispatch://OSSV-287): the FIRST arm found, in review or by a failing
    proof, that reads or writes an [FdAnon] entry WITHOUT calling
    [State.anon_agree].  One such arm, and the predicate moves into
    well-formedness, with its preservation proved for every arm.  Until
    then the per-arm form stands.

    A leaf: nothing in the model or the checker depends on this file. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Fs.Namei.
Import ListNotations.
Open Scope bv_scope.

(* ------------------------------------------------- the entry-level facts *)

Lemma anon_pin_eqb_eq : forall a b, anon_pin_eqb a b = true <-> a = b.
Proof.
  intros [x|] [y|]; cbn; try (split; congruence).
  rewrite path_eqb_eq. split; congruence.
Qed.

Lemma anon_pin_eqb_refl : forall a, anon_pin_eqb a a = true.
Proof. intro a. apply anon_pin_eqb_eq. reflexivity. Qed.

Lemma anon_entry_agrees_anon : forall id af id' af',
  anon_entry_agrees id af (FdAnon id' af')
  = implb (bv_eqb id' id)
      (path_eqb (af_data af') (af_data af) && anon_pin_eqb (af_pin af') (af_pin af)).
Proof. reflexivity. Qed.

(** A descriptor of file [id] whose view has [af]'s contents and pin
    agrees with [af]. *)
Lemma anon_entry_agrees_same : forall id af af',
  af_data af' = af_data af -> af_pin af' = af_pin af ->
  anon_entry_agrees id af (FdAnon id af') = true.
Proof.
  intros id af af' Hd Hp.
  rewrite anon_entry_agrees_anon, (proj2 (bv_eqb_eq id id) eq_refl), Hd, Hp,
    path_eqb_refl, anon_pin_eqb_refl.
  reflexivity.
Qed.

(** A descriptor of another file agrees with any view of [id2]. *)
Lemma anon_entry_agrees_other : forall id2 af2 id x,
  id <> id2 -> anon_entry_agrees id2 af2 (FdAnon id x) = true.
Proof.
  intros id2 af2 id x Hne. rewrite anon_entry_agrees_anon.
  destruct (bv_eqb id id2) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. contradiction.
Qed.

(** Agreement reads only the contents and the pin of the view. *)
Lemma anon_entry_agrees_congr : forall id a b e,
  af_data a = af_data b -> af_pin a = af_pin b ->
  anon_entry_agrees id a e = anon_entry_agrees id b e.
Proof.
  intros id a b e Hd Hp.
  destruct e; try reflexivity.
  rewrite !anon_entry_agrees_anon, Hd, Hp. reflexivity.
Qed.

(** An update of every descriptor of [id] by [f], where [f] maps views
    with the same contents and pin to views with the same contents and
    pin, keeps an entry agreeing with the updated view. *)
Lemma anon_entry_agrees_update : forall id af f e,
  (forall a, af_data a = af_data af -> af_pin a = af_pin af ->
     af_data (f a) = af_data (f af) /\ af_pin (f a) = af_pin (f af)) ->
  anon_entry_agrees id af e = true ->
  anon_entry_agrees id (f af) (anon_entry_update id f e) = true.
Proof.
  intros id af f e Hf H.
  destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |sid side st|ctx|fam|id' af'];
    try reflexivity.
  rewrite anon_entry_agrees_anon in H.
  unfold anon_entry_update. cbv beta iota.
  destruct (bv_eqb id' id) eqn:Hid; cbv iota.
  - cbn [implb] in H. apply andb_true_iff in H as [Hd Hp].
    apply path_eqb_eq in Hd. apply anon_pin_eqb_eq in Hp.
    apply bv_eqb_eq in Hid. subst id'.
    destruct (Hf af' Hd Hp) as [Hd' Hp'].
    apply anon_entry_agrees_same; assumption.
  - rewrite anon_entry_agrees_anon, Hid. reflexivity.
Qed.

(** The same update leaves the entries' agreement with another file. *)
Lemma anon_entry_agrees_update_other : forall id f id2 af2 e,
  id <> id2 -> anon_entry_agrees id2 af2 e = true ->
  anon_entry_agrees id2 af2 (anon_entry_update id f e) = true.
Proof.
  intros id f id2 af2 e Hne H.
  destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |sid side st|ctx|fam|id' af'];
    try reflexivity.
  unfold anon_entry_update. cbv beta iota.
  destruct (bv_eqb id' id) eqn:Hid; cbv iota; [|exact H].
  apply bv_eqb_eq in Hid. subst id'.
  apply anon_entry_agrees_other. exact Hne.
Qed.

(** A descriptor the removal of the name [c] leaves: converted to the
    new file [id] with [data] and [pin], or as it was, and in both
    cases agreeing with the new file's view when it was not a
    descriptor of [id] before. *)
Lemma unlink_open_entry_agrees : forall c id data pin o r w a e,
  match entry_anon_id e with Some id' => bv_eqb id' id | None => false end = false ->
  anon_entry_agrees id (mkAnonFile data o r w a pin)
    (unlink_open_entry c id data pin e) = true.
Proof.
  intros c id data pin o r w a e He.
  destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |sid side st|ctx|fam|id' af'];
    unfold unlink_open_entry; cbv beta iota.
  (* a descriptor of an unnamed file: not of [id], which was not live *)
  14: { cbn [entry_anon_id] in He. rewrite anon_entry_agrees_anon, He. reflexivity. }
  (* the four kinds that hold a name: converted when it is [c] *)
  2-5: (destruct (path_eqb c p); cbv iota;
        [apply anon_entry_agrees_same; reflexivity | reflexivity]).
  (* the kinds that hold no name, left as they were *)
  all: reflexivity.
Qed.

(** ...and agreeing with another file's view as it did before. *)
Lemma unlink_open_entry_agrees_other : forall c id data pin id2 af2 e,
  id <> id2 -> anon_entry_agrees id2 af2 e = true ->
  anon_entry_agrees id2 af2 (unlink_open_entry c id data pin e) = true.
Proof.
  intros c id data pin id2 af2 e Hne H.
  destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid pw|rd wr| |sid side st|ctx|fam|id' af'];
    unfold unlink_open_entry; cbv beta iota; try exact H.
  all: destruct (path_eqb c p); cbv iota;
         [apply anon_entry_agrees_other; exact Hne | exact H].
Qed.

(* ------------------------------------------------- the table-level facts *)

Lemma anon_agree_cons : forall p fds id af,
  anon_agree (p :: fds) id af = (anon_entry_agrees id af (snd p) && anon_agree fds id af)%bool.
Proof. reflexivity. Qed.

Lemma anon_agree_congr : forall fds id a b,
  af_data a = af_data b -> af_pin a = af_pin b ->
  anon_agree fds id a = anon_agree fds id b.
Proof.
  intros fds id a b Hd Hp. induction fds as [|q r IH]; [reflexivity|].
  rewrite !anon_agree_cons, IH, (anon_entry_agrees_congr id a b (snd q) Hd Hp).
  reflexivity.
Qed.

Lemma anon_agree_filter : forall (f : word * FdEntry -> bool) fds id af,
  anon_agree fds id af = true -> anon_agree (List.filter f fds) id af = true.
Proof.
  intros f fds id af. induction fds as [|p r IH]; intros H; [reflexivity|].
  rewrite anon_agree_cons in H. apply andb_true_iff in H as [Hp Hr].
  cbn [List.filter]. destruct (f p); cbv iota.
  - rewrite anon_agree_cons, Hp, (IH Hr). reflexivity.
  - exact (IH Hr).
Qed.

Lemma anon_agree_fd_insert : forall fds fd e id af,
  anon_agree fds id af = true -> anon_entry_agrees id af e = true ->
  anon_agree (fd_insert fds fd e) id af = true.
Proof.
  intros fds fd e id af H He. unfold fd_insert.
  rewrite anon_agree_cons. cbn [snd]. rewrite He. cbn [andb].
  apply anon_agree_filter. exact H.
Qed.

Lemma anon_agree_update : forall fds id af f,
  (forall a, af_data a = af_data af -> af_pin a = af_pin af ->
     af_data (f a) = af_data (f af) /\ af_pin (f a) = af_pin (f af)) ->
  anon_agree fds id af = true ->
  anon_agree (anon_update fds id f) id (f af) = true.
Proof.
  intros fds id af f Hf. induction fds as [|[k e] r IH]; intros H; [reflexivity|].
  rewrite anon_agree_cons in H. apply andb_true_iff in H as [He Hr].
  change (anon_update ((k, e) :: r) id f)
    with ((k, anon_entry_update id f e) :: anon_update r id f).
  rewrite anon_agree_cons. apply andb_true_iff. split.
  - exact (anon_entry_agrees_update id af f e Hf He).
  - exact (IH Hr).
Qed.

(** The start: the launch's descriptors are its three channels, so every
    file id agrees with every view. *)
Lemma anon_agree_init_model : forall reserved brk0 mbase sp lim inp id af,
  anon_agree (m_fds (init_model reserved brk0 mbase sp lim inp)) id af = true.
Proof. reflexivity. Qed.

(* ----------------------------------------- the lemmas the header names *)

(** (a) The contents written to every descriptor of the file. *)
Lemma anon_agree_set_data : forall fds id af d,
  anon_agree fds id af = true ->
  anon_agree (anon_set_data fds id d) id (af_set_data af d) = true.
Proof.
  intros fds id af d H.
  assert (Hf : forall a, af_data a = af_data af -> af_pin a = af_pin af ->
            af_data (af_set_data a d) = af_data (af_set_data af d)
            /\ af_pin (af_set_data a d) = af_pin (af_set_data af d)).
  { intros a _ Hp. split; [reflexivity | exact Hp]. }
  exact (anon_agree_update fds id af (fun a => af_set_data a d) Hf H).
Qed.

(** (b) A transfer through descriptor [fd]: the contents to every
    descriptor, the offset to [fd]'s own. *)
Lemma anon_agree_write_back : forall fds fd id af d o,
  anon_agree fds id af = true ->
  anon_agree (anon_write_back fds fd id af d o) id (af_set_off (af_set_data af d) o) = true.
Proof.
  intros fds fd id af d o H. unfold anon_write_back.
  apply anon_agree_fd_insert.
  - rewrite (anon_agree_congr (anon_set_data fds id d) id
               (af_set_off (af_set_data af d) o) (af_set_data af d)) by reflexivity.
    apply anon_agree_set_data. exact H.
  - apply anon_entry_agrees_same; reflexivity.
Qed.

(** (c) The "/proc/self/fd/N" reopen under O_RDONLY or
    O_WRONLY|O_CREAT|O_APPEND. *)
Lemma anon_agree_reopen : forall fds fd id af o r w a,
  anon_agree fds id af = true ->
  anon_agree (fd_insert fds fd (FdAnon id (mkAnonFile (af_data af) o r w a (af_pin af))))
    id af = true.
Proof.
  intros fds fd id af o r w a H.
  apply anon_agree_fd_insert; [exact H|].
  apply anon_entry_agrees_same; reflexivity.
Qed.

(** (c) The O_WRONLY|O_CREAT|O_TRUNC reopen. *)
Lemma anon_agree_reopen_trunc : forall fds fd id af o r w a,
  anon_agree fds id af = true ->
  anon_agree (fd_insert (anon_set_data fds id []) fd
                (FdAnon id (mkAnonFile [] o r w a (af_pin af))))
    id (af_set_data af []) = true.
Proof.
  intros fds fd id af o r w a H.
  apply anon_agree_fd_insert.
  - apply anon_agree_set_data. exact H.
  - apply anon_entry_agrees_same; reflexivity.
Qed.

(** (d) A close removes one entry and changes no other. *)
Lemma anon_agree_fd_remove : forall fds fd id af,
  anon_agree fds id af = true -> anon_agree (fd_remove fds fd) id af = true.
Proof.
  intros fds fd id af H. unfold fd_remove. apply anon_agree_filter. exact H.
Qed.

(** (e) The removal of a /tmp name open descriptors hold, on any table
    where the new file's id is not live. *)
Lemma anon_agree_unlink_open : forall c id data pin o r w a fds,
  anon_id_live fds id = false ->
  anon_agree (map (fun q => (fst q, unlink_open_entry c id data pin (snd q))) fds)
    id (mkAnonFile data o r w a pin) = true.
Proof.
  intros c id data pin o r w a fds.
  induction fds as [|[k e] rest IH]; intros Hlive; [reflexivity|].
  unfold anon_id_live in Hlive. cbn [existsb] in Hlive.
  apply orb_false_iff in Hlive as [He Hrest].
  cbn [map]. rewrite anon_agree_cons. cbn [fst snd] in He |- *.
  apply andb_true_iff. split.
  - apply unlink_open_entry_agrees. exact He.
  - apply IH. exact Hrest.
Qed.

(* ------------------------------------------ the four further steps *)

(** The pin a first fstat writes to every descriptor of the file. *)
Lemma anon_agree_set_pin : forall fds id af bs,
  anon_agree fds id af = true ->
  anon_agree (anon_update fds id (fun a => af_set_pin a bs)) id (af_set_pin af bs) = true.
Proof.
  intros fds id af bs H.
  assert (Hf : forall a, af_data a = af_data af -> af_pin a = af_pin af ->
            af_data (af_set_pin a bs) = af_data (af_set_pin af bs)
            /\ af_pin (af_set_pin a bs) = af_pin (af_set_pin af bs)).
  { intros a Hd _. split; [exact Hd | reflexivity]. }
  exact (anon_agree_update fds id af (fun a => af_set_pin a bs) Hf H).
Qed.

(** The offset a read or an lseek writes to its own descriptor. *)
Lemma anon_agree_set_off : forall fds fd id af o,
  anon_agree fds id af = true ->
  anon_agree (fd_insert fds fd (FdAnon id (af_set_off af o))) id af = true.
Proof.
  intros fds fd id af o H.
  apply anon_agree_fd_insert; [exact H|].
  apply anon_entry_agrees_same; reflexivity.
Qed.

(** An update of one file's descriptors leaves every other file's
    agreement as it was. *)
Lemma anon_agree_update_other : forall fds id f id2 af2,
  id <> id2 -> anon_agree fds id2 af2 = true ->
  anon_agree (anon_update fds id f) id2 af2 = true.
Proof.
  intros fds id f id2 af2 Hne. induction fds as [|[k e] r IH]; intros H; [reflexivity|].
  rewrite anon_agree_cons in H. apply andb_true_iff in H as [He Hr].
  change (anon_update ((k, e) :: r) id f)
    with ((k, anon_entry_update id f e) :: anon_update r id f).
  rewrite anon_agree_cons. apply andb_true_iff. split.
  - exact (anon_entry_agrees_update_other id f id2 af2 e Hne He).
  - exact (IH Hr).
Qed.

(** The removal of a /tmp name leaves every other file's agreement as it
    was. *)
Lemma anon_agree_unlink_open_other : forall c id data pin id2 af2 fds,
  id <> id2 -> anon_agree fds id2 af2 = true ->
  anon_agree (map (fun q => (fst q, unlink_open_entry c id data pin (snd q))) fds)
    id2 af2 = true.
Proof.
  intros c id data pin id2 af2 fds Hne.
  induction fds as [|[k e] rest IH]; intros H; [reflexivity|].
  rewrite anon_agree_cons in H. apply andb_true_iff in H as [He Hr].
  cbn [map]. rewrite anon_agree_cons. cbn [fst snd] in He |- *.
  apply andb_true_iff. split.
  - apply unlink_open_entry_agrees_other; assumption.
  - apply IH. exact Hr.
Qed.
