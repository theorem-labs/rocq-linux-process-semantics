(** * LinuxProcessSem.Ns.Propagation — mount propagation: the order data and its rules

    A mount's peer group ([mnt_peer]) and the peer group it is a slave of
    ([mnt_master]) are in [Tables.Mount]; the order the kernel keeps of each
    peer group's [mnt_share] ring and of each mount's [mnt_slave_list] is
    [Tables.PropLinks], the state's [ns_prop].  This file states what that
    data must satisfy ([prop_ok], with the checker [prop_okb]) and which
    mounts can receive a mount or unmount event from a peer group that has a
    member outside the tables ([open_reach]).

    Linux v6.18.46 sources: [struct mount] (fs/mount.h:68-71, 95, 103-115);
    [next_peer], [first_slave], [next_slave] (fs/pnode.c:17-30);
    [change_mnt_propagation] and [transfer_propagation] (fs/pnode.c:74-124),
    which keep every member of a peer group on the same master; [clone_mnt]
    (fs/namespace.c:1259-1289), which never makes a mount a slave of its own
    group.

    The rules of the data ([prop_ok]):
    1. a ring entry [(g, l)] lists, without repeating one, exactly the mounts
       of the tables in group [g], and no group has two entries;
    2. a slave-list entry [(k, l)] names a shared mount [k] of the tables,
       and lists only mounts of the tables that are slaves of [k]'s group;
       no mount has two entries, and no mount is in two lists (a mount's
       [mnt_slave] is on one list);
    3. the members of one peer group have the same master group;
    4. no mount is a slave of its own peer group;
    5. an open group ([env_open_groups]) has no ring entry: the order of a
       ring with members outside the tables is not the model's to know.
    Every state whose order data is empty satisfies rules 1, 2 and 5
    ([empty_prop_ok]); rules 3 and 4 hold of every Linux mount tree. *)

From Stdlib Require Import List PArith Bool.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Mount.
Import ListNotations.

(* =========================================================================
   Peer groups
   ========================================================================= *)

(** [m] is a member of peer group [g].  (Not [in_group]: [Files.in_group]
    is [in_group_p], a credential's group.) *)
Definition in_peer_group (g : positive) (m : Mount) : bool :=
  match mnt_peer m with Some h => Pos.eqb h g | None => false end.

(** [m] is a slave of peer group [g]. *)
Definition slave_of_group (g : positive) (m : Mount) : bool :=
  match mnt_master m with Some h => Pos.eqb h g | None => false end.

Lemma in_peer_group_eq : forall g m, in_peer_group g m = true -> mnt_peer m = Some g.
Proof.
  intros g m. unfold in_peer_group.
  destruct (mnt_peer m) as [h|]; cbn; intros H; [|discriminate H].
  apply Pos.eqb_eq in H. subst h. reflexivity.
Qed.

Lemma in_peer_group_of : forall g m, mnt_peer m = Some g -> in_peer_group g m = true.
Proof. intros g m H. unfold in_peer_group. rewrite H. cbn. apply Pos.eqb_refl. Qed.

Lemma slave_of_group_eq : forall g m, slave_of_group g m = true -> mnt_master m = Some g.
Proof.
  intros g m. unfold slave_of_group.
  destruct (mnt_master m) as [h|]; cbn; intros H; [|discriminate H].
  apply Pos.eqb_eq in H. subst h. reflexivity.
Qed.

Lemma slave_of_group_of : forall g m, mnt_master m = Some g -> slave_of_group g m = true.
Proof. intros g m H. unfold slave_of_group. rewrite H. cbn. apply Pos.eqb_refl. Qed.

(** A group the tables use: a mount of the tables is in it or a slave of
    it. *)
Definition live_group (st : NsState) (g : positive) : Prop :=
  exists m, In m (ns_mounts st) /\ (mnt_peer m = Some g \/ mnt_master m = Some g).

Definition live_groupb (st : NsState) (g : positive) : bool :=
  existsb (fun m => in_peer_group g m || slave_of_group g m) (ns_mounts st).

Lemma live_groupb_live : forall st g, live_groupb st g = true -> live_group st g.
Proof.
  intros st g H. unfold live_groupb in H. apply existsb_exists in H.
  destruct H as [m [Hm Hg]]. cbv beta in Hg. exists m. split; [exact Hm|].
  apply orb_true_iff in Hg. destruct Hg as [Hg|Hg].
  - left. exact (in_peer_group_eq g m Hg).
  - right. exact (slave_of_group_eq g m Hg).
Qed.

(** The entry of key [k] in a list of ring or slave-list entries. *)
Fixpoint pl_find (k : positive) (l : list (positive * list positive)) : option (list positive) :=
  match l with
  | [] => None
  | (a, v) :: r => if Pos.eqb a k then Some v else pl_find k r
  end.

(** No element repeats. *)
Fixpoint nodupb (l : list positive) : bool :=
  match l with
  | [] => true
  | x :: r => negb (mem x r) && nodupb r
  end.

Lemma nodupb_nodup : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [|x r IH]; intros H.
  - apply NoDup_nil.
  - cbn [nodupb] in H. apply andb_true_iff in H. destruct H as [Hx Hr].
    apply NoDup_cons.
    + intros Hin. apply negb_true_iff in Hx. unfold mem in Hx.
      assert (Hy : existsb (Pos.eqb x) r = true).
      { apply existsb_exists. exists x. split; [exact Hin | apply Pos.eqb_refl]. }
      rewrite Hy in Hx. discriminate Hx.
    + exact (IH Hr).
Qed.

Definition opt_pos_eqb (a b : option positive) : bool :=
  match a, b with
  | Some x, Some y => Pos.eqb x y
  | None, None => true
  | _, _ => false
  end.

Lemma opt_pos_eqb_eq : forall a b, opt_pos_eqb a b = true -> a = b.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate H; [|reflexivity].
  apply Pos.eqb_eq in H. subst y. reflexivity.
Qed.

(* =========================================================================
   The rules of the order data
   ========================================================================= *)

(** Rule 1, for one entry: [l] lists exactly the members of [g]. *)
Definition ring_entry_ok (T : list Mount) (g : positive) (l : list positive) : Prop :=
  NoDup l
  /\ (forall i, In i l -> exists m, In m T /\ mnt_id m = i /\ mnt_peer m = Some g)
  /\ (forall m, In m T -> mnt_peer m = Some g -> In (mnt_id m) l).

(** Rule 2, for one entry: [k] is a shared mount, and [l] lists slaves of
    its group. *)
Definition slave_entry_ok (T : list Mount) (k : positive) (l : list positive) : Prop :=
  exists mk g, find_mount T k = Some mk /\ mnt_peer mk = Some g
               /\ forall i, In i l -> exists x, In x T /\ mnt_id x = i /\ mnt_master x = Some g.

(** Rules 3 and 4: what every Linux mount tree satisfies. *)
Definition groups_ok (T : list Mount) : Prop :=
  (forall a b g, In a T -> In b T -> mnt_peer a = Some g -> mnt_peer b = Some g ->
                 mnt_master a = mnt_master b)
  /\ (forall m g, In m T -> mnt_peer m = Some g -> mnt_master m <> Some g).

Definition prop_ok (st : NsState) : Prop :=
  let T := ns_mounts st in
  let pl := ns_prop st in
  NoDup (map fst (pl_rings pl))
  /\ (forall g l, In (g, l) (pl_rings pl) -> ring_entry_ok T g l)
  /\ NoDup (map fst (pl_slaves pl))
  /\ NoDup (flat_map snd (pl_slaves pl))
  /\ (forall k l, In (k, l) (pl_slaves pl) -> slave_entry_ok T k l)
  /\ groups_ok T
  /\ (forall g l, In g (env_open_groups (ns_env st)) -> ~ In (g, l) (pl_rings pl)).

(** The checker, rule by rule. *)
Definition ring_entry_okb (T : list Mount) (g : positive) (l : list positive) : bool :=
  nodupb l
  && forallb (fun i => existsb (fun m => Pos.eqb (mnt_id m) i && in_peer_group g m) T) l
  && forallb (fun m => implb (in_peer_group g m) (mem (mnt_id m) l)) T.

Definition slave_entry_okb (T : list Mount) (k : positive) (l : list positive) : bool :=
  match find_mount T k with
  | Some mk =>
      match mnt_peer mk with
      | Some g => forallb (fun i => existsb (fun x => Pos.eqb (mnt_id x) i && slave_of_group g x) T) l
      | None => false
      end
  | None => false
  end.

Definition groups_okb (T : list Mount) : bool :=
  forallb (fun a =>
    match mnt_peer a with
    | Some g =>
        forallb (fun b => implb (in_peer_group g b) (opt_pos_eqb (mnt_master a) (mnt_master b))) T
        && negb (slave_of_group g a)
    | None => true
    end) T.

Definition prop_okb (st : NsState) : bool :=
  let T := ns_mounts st in
  let pl := ns_prop st in
  nodupb (map fst (pl_rings pl))
  && forallb (fun e => ring_entry_okb T (fst e) (snd e)) (pl_rings pl)
  && nodupb (map fst (pl_slaves pl))
  && nodupb (flat_map snd (pl_slaves pl))
  && forallb (fun e => slave_entry_okb T (fst e) (snd e)) (pl_slaves pl)
  && groups_okb T
  && forallb (fun g => negb (existsb (fun e => Pos.eqb (fst e) g) (pl_rings pl)))
             (env_open_groups (ns_env st)).

Lemma ring_entry_okb_ok : forall T g l, ring_entry_okb T g l = true -> ring_entry_ok T g l.
Proof.
  intros T g l H. unfold ring_entry_okb in H.
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  unfold ring_entry_ok.
  split; [exact (nodupb_nodup l H1)|]. split.
  - intros i Hi. rewrite forallb_forall in H2. specialize (H2 i Hi). cbv beta in H2.
    apply existsb_exists in H2. destruct H2 as [m [Hm Hmi]]. cbv beta in Hmi.
    apply andb_true_iff in Hmi. destruct Hmi as [Hid Hg].
    apply Pos.eqb_eq in Hid. exists m. split; [exact Hm|]. split; [exact Hid|].
    exact (in_peer_group_eq g m Hg).
  - intros m Hm Hp. rewrite forallb_forall in H3. specialize (H3 m Hm). cbv beta in H3.
    rewrite (in_peer_group_of g m Hp) in H3.
    change (mem (mnt_id m) l = true) in H3.
    unfold mem in H3. apply existsb_exists in H3. destruct H3 as [i [Hi Hie]].
    apply Pos.eqb_eq in Hie. rewrite Hie. exact Hi.
Qed.

Lemma slave_entry_okb_ok : forall T k l, slave_entry_okb T k l = true -> slave_entry_ok T k l.
Proof.
  intros T k l. unfold slave_entry_okb.
  destruct (find_mount T k) as [mk|] eqn:Hk; cbn; [|intros H; discriminate H].
  destruct (mnt_peer mk) as [g|] eqn:Hg; cbn; [|intros H; discriminate H].
  intros H. unfold slave_entry_ok.
  exists mk, g. split; [exact Hk|]. split; [exact Hg|].
  intros i Hi. rewrite forallb_forall in H. specialize (H i Hi). cbv beta in H.
  apply existsb_exists in H. destruct H as [x [Hx Hxi]]. cbv beta in Hxi.
  apply andb_true_iff in Hxi. destruct Hxi as [Hid Hs].
  apply Pos.eqb_eq in Hid. exists x. split; [exact Hx|]. split; [exact Hid|].
  exact (slave_of_group_eq g x Hs).
Qed.

Lemma groups_okb_ok : forall T, groups_okb T = true -> groups_ok T.
Proof.
  intros T H. unfold groups_okb in H. rewrite forallb_forall in H. unfold groups_ok. split.
  - intros a b g Ha Hb Hpa Hpb. specialize (H a Ha). cbv beta in H. rewrite Hpa in H.
    cbv beta iota in H.
    apply andb_true_iff in H. destruct H as [H _].
    rewrite forallb_forall in H. specialize (H b Hb). cbv beta in H.
    rewrite (in_peer_group_of g b Hpb) in H.
    change (opt_pos_eqb (mnt_master a) (mnt_master b) = true) in H.
    exact (opt_pos_eqb_eq _ _ H).
  - intros m g Hm Hp Hmaster. specialize (H m Hm). cbv beta in H. rewrite Hp in H.
    cbv beta iota in H.
    apply andb_true_iff in H. destruct H as [_ H].
    rewrite (slave_of_group_of g m Hmaster) in H. cbn in H. discriminate H.
Qed.

(** The checker is sound: a state it accepts satisfies the rules. *)
Theorem prop_okb_ok : forall st, prop_okb st = true -> prop_ok st.
Proof.
  intros st H. unfold prop_okb in H. cbv zeta in H.
  apply andb_true_iff in H. destruct H as [H H7].
  apply andb_true_iff in H. destruct H as [H H6].
  apply andb_true_iff in H. destruct H as [H H5].
  apply andb_true_iff in H. destruct H as [H H4].
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  unfold prop_ok. cbv zeta.
  split; [exact (nodupb_nodup _ H1)|].
  split.
  { intros g l Hin. rewrite forallb_forall in H2.
    exact (ring_entry_okb_ok _ _ _ (H2 (g, l) Hin)). }
  split; [exact (nodupb_nodup _ H3)|].
  split; [exact (nodupb_nodup _ H4)|].
  split.
  { intros k l Hin. rewrite forallb_forall in H5.
    exact (slave_entry_okb_ok _ _ _ (H5 (k, l) Hin)). }
  split; [exact (groups_okb_ok _ H6)|].
  intros g l Hg Hin. rewrite forallb_forall in H7. specialize (H7 g Hg). cbv beta in H7.
  apply negb_true_iff in H7.
  assert (Hy : existsb (fun e => Pos.eqb (fst e) g) (pl_rings (ns_prop st)) = true).
  { apply existsb_exists. exists (g, l). split; [exact Hin|]. cbn. apply Pos.eqb_refl. }
  rewrite Hy in H7. discriminate H7.
Qed.

(** A state with no order data satisfies rules 1, 2 and 5; with a Linux
    mount tree (rules 3 and 4), every rule. *)
Theorem empty_prop_ok : forall st,
  pl_rings (ns_prop st) = [] -> pl_slaves (ns_prop st) = [] -> groups_ok (ns_mounts st) ->
  prop_ok st.
Proof.
  intros st Hr Hs Hg. unfold prop_ok. cbv zeta. rewrite Hr, Hs.
  split; [apply NoDup_nil|]. split; [intros g l []|].
  split; [apply NoDup_nil|]. split; [apply NoDup_nil|].
  split; [intros k l []|]. split; [exact Hg|].
  intros g l _ [].
Qed.

Example empty_nsstate_prop_ok : prop_okb empty_nsstate = true := eq_refl.

(* =========================================================================
   Open groups: mount events from outside the tables
   ========================================================================= *)

(** The master group of peer group [g]: [Some] the [mnt_master] of a member
    of [g] in the tables (every member has the same, rule 3), [None] when
    [g] has no member in the tables, where the model does not know it. *)
Definition group_master (T : list Mount) (g : positive) : option (option positive) :=
  match find (in_peer_group g) T with
  | Some m => Some (mnt_master m)
  | None => None
  end.

(** The chain of master groups from [g] up: [g], its master group, that
    group's master group, and so on while the tables know the next one. *)
Fixpoint master_chain (fuel : nat) (T : list Mount) (g : positive) : list positive :=
  match fuel with
  | O => [g]
  | Datatypes.S f => g :: match group_master T g with
                | Some (Some h) => master_chain f T h
                | _ => []
                end
  end.

(** The peer groups whose mount and unmount events reach [m]
    ([propagation_next] visits the peers of a group, their slaves, the
    peers of those, and so on, fs/pnode.c:177-212): its own group, and
    every group of the master chain from its master group.  Each step of
    the chain names a group with a member in the tables, so the number of
    mounts bounds its length. *)
Definition receives_from (T : list Mount) (m : Mount) : list positive :=
  match mnt_peer m with Some g => [g] | None => [] end
  ++ match mnt_master m with Some g => master_chain (length T) T g | None => [] end.

(** [m] can receive a mount or unmount event from an open group: the host
    can add or remove a mount at [m] without a call of the model.  An arm
    whose answer reads such a mount declines. *)
Definition open_reach (st : NsState) (m : Mount) : bool :=
  existsb (fun g => mem g (env_open_groups (ns_env st))) (receives_from (ns_mounts st) m).

(** With no open group, the launch the model names by default
    ([empty_nsenv]), no mount of the tables can receive an event from a
    mount outside them: only calls of the model change the mounts of its
    namespaces. *)
Theorem closed_no_outside_event : forall st m,
  env_open_groups (ns_env st) = [] -> open_reach st m = false.
Proof.
  intros st m H. unfold open_reach. rewrite H.
  generalize (receives_from (ns_mounts st) m) as l.
  induction l as [|g l IH]; [reflexivity | exact IH].
Qed.
