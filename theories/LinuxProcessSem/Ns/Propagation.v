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

(* =========================================================================
   Peer-group keys: mnt_alloc_group_id, mnt_release_group_id
   =========================================================================

   The kernel's group number comes from one IDA for the whole system
   ([mnt_alloc_group_id], fs/namespace.c:239-247; [ida_alloc_min],
   lib/idr.c:382-478), from which mounts outside the tables also take
   numbers, so the number is the environment's ([Tables.mi_group]).  The
   model gives a new group a KEY: one above every key the state names, and
   at least [pl_next_group], which a group that dies raises above its own
   key.  So no key is given twice, and [mi_group] never has to give a new
   group the number of a dead one.  The allocator's refusals (ENOMEM,
   lib/idr.c:470; ENOSPC, lib/idr.c:391, 477) are the environment's: the
   arms' injected rows list them, and a refusal leaves the state as it was
   ([cleanup_group_ids], fs/namespace.c:2439-2447). *)

Definition opt_max (acc : positive) (o : option positive) : positive :=
  match o with Some g => Pos.max acc g | None => acc end.

(** The largest group key the state names: a mount's peer group or master
    group, a ring entry, an open group. *)
Definition max_group_key (st : NsState) : positive :=
  fold_left Pos.max (env_open_groups (ns_env st))
    (fold_left (fun acc e => Pos.max acc (fst e)) (pl_rings (ns_prop st))
       (fold_left (fun acc m => opt_max (opt_max acc (mnt_peer m)) (mnt_master m))
                  (ns_mounts st) 1%positive)).

Definition new_group_key (st : NsState) : positive :=
  Pos.max (pl_next_group (ns_prop st)) (Pos.succ (max_group_key st)).

(** Key [g] given to a new group, or freed by a group that died: no later
    group gets it. *)
Definition key_used (st : NsState) (g : positive) : NsState :=
  with_ns_prop st (pl_with_next_group (ns_prop st)
                     (Pos.max (pl_next_group (ns_prop st)) (Pos.succ g))).

(* =========================================================================
   What the order data knows
   ========================================================================= *)

(** The members of group [g] in the tables, in table order. *)
Definition members (T : list Mount) (g : positive) : list positive :=
  map mnt_id (List.filter (in_peer_group g) T).

(** The slaves of group [g] in the tables, in table order. *)
Definition group_slaves (T : list Mount) (g : positive) : list positive :=
  map mnt_id (List.filter (slave_of_group g) T).

Definition is_open (st : NsState) (g : positive) : bool := mem g (env_open_groups (ns_env st)).

(** The ring of group [g], its members in [next_peer] order, when the model
    knows it: the ring entry, or the members themselves when the tables
    hold at most two (a ring of two has one order).  An open group's ring
    passes through mounts outside the tables. *)
Definition ring_of (st : NsState) (g : positive) : option (list positive) :=
  if is_open st g then None
  else match pl_find g (pl_rings (ns_prop st)) with
       | Some l => Some l
       | None => let l := members (ns_mounts st) g in
                 if Nat.leb (length l) 2 then Some l else None
       end.

(** The element after [i] in the cycle [l] whose first element is
    [first]. *)
Fixpoint after_in (i first : positive) (l : list positive) : option positive :=
  match l with
  | [] => None
  | x :: r => if Pos.eqb x i then Some (match r with y :: _ => y | [] => first end)
              else after_in i first r
  end.

Definition ring_next (l : list positive) (i : positive) : option positive :=
  match l with [] => None | x :: _ => after_in i x l end.

(** [next_peer] of mount [i] of group [g] (fs/pnode.c:17-20), when known. *)
Definition next_peer_of (st : NsState) (g i : positive) : option positive :=
  match ring_of st g with Some l => ring_next l i | None => None end.

(** The slaves of mount [k] in the tables, head first, when the model knows
    them: the slave-list entry of [k]; none, when [k] is not shared or no
    mount of the tables is a slave of [k]'s group; the one slave of the
    group, when [k] is the group's one member in the tables and the group
    is not open.  (Slaves outside the tables are on the kernel's list too;
    no mount of the tables receives through one of them.) *)
Definition slave_list (st : NsState) (k : positive) : option (list positive) :=
  match pl_find k (pl_slaves (ns_prop st)) with
  | Some l => Some l
  | None =>
      match find_mount (ns_mounts st) k with
      | Some mk =>
          match mnt_peer mk with
          | Some g =>
              match group_slaves (ns_mounts st) g, members (ns_mounts st) g with
              | [], _ => Some []
              | [x], [_] => if is_open st g then None else Some [x]
              | _, _ => None
              end
          | None => Some []
          end
      | None => None
      end
  end.

(** The key of the slave list that holds [i]. *)
Fixpoint holder (i : positive) (l : list (positive * list positive)) : option positive :=
  match l with
  | [] => None
  | (k, s) :: r => if mem i s then Some k else holder i r
  end.

(** The master mount of [m] ([mnt_master], fs/mount.h:71), when the model
    knows it: the mount whose slave list holds [m], or the one member of
    [m]'s master group when the tables hold one and the group is not
    open. *)
Definition master_mount (st : NsState) (m : Mount) : option positive :=
  match mnt_master m with
  | None => None
  | Some h =>
      match holder (mnt_id m) (pl_slaves (ns_prop st)) with
      | Some k => Some k
      | None => match members (ns_mounts st) h with
                | [k] => if is_open st h then None else Some k
                | _ => None
                end
      end
  end.

(* =========================================================================
   Changing the order data
   ========================================================================= *)

(** The slave list of [k] set to [l], or removed ([None]: not known). *)
Definition set_slaves (pl : PropLinks) (k : positive) (o : option (list positive)) : PropLinks :=
  let rest := List.filter (fun e => negb (Pos.eqb (fst e) k)) (pl_slaves pl) in
  pl_with_slaves pl (match o with Some l => (k, l) :: rest | None => rest end).

(** The ring entry of [g] set to [l], or removed. *)
Definition set_ring (pl : PropLinks) (g : positive) (o : option (list positive)) : PropLinks :=
  let rest := List.filter (fun e => negb (Pos.eqb (fst e) g)) (pl_rings pl) in
  pl_with_rings pl (match o with Some l => (g, l) :: rest | None => rest end).

(** [i] taken out of every slave list ([hlist_del_init (&m->mnt_slave)]). *)
Definition unlist (pl : PropLinks) (i : positive) : PropLinks :=
  pl_with_slaves pl (map (fun e => (fst e, List.filter (fun x => negb (Pos.eqb x i)) (snd e)))
                         (pl_slaves pl)).

(** The slave lists of the mounts [cs] forgotten: one of them changed in a
    way the model does not know. *)
Definition forget_lists (pl : PropLinks) (cs : list positive) : PropLinks :=
  pl_with_slaves pl (List.filter (fun e => negb (mem (fst e) cs)) (pl_slaves pl)).

(** Where a mount's slaves go when it stops being shared, and where it goes
    itself when it becomes a slave: a mount of the tables; no mount of the
    tables (NULL, or a mount outside them); or one of [cands], the model
    does not know which. *)
Inductive Dest := DTo (k : positive) | DOut | DSome (cands : list positive).

(** [change_mnt_propagation] (fs/pnode.c:95, 101-111): the next peer of [m]
    while its group has another member, else [m]'s master mount. *)
Definition change_dest (st : NsState) (m : Mount) : Dest :=
  let T := ns_mounts st in
  let i := mnt_id m in
  let via_master :=
    match mnt_master m with
    | None => DOut
    | Some h => match master_mount st m with
                | Some k => DTo k
                | None => match members T h with [] => DOut | cs => DSome cs end
                end
    end in
  match mnt_peer m with
  | Some g =>
      match List.filter (fun x => negb (Pos.eqb x i)) (members T g) with
      | [] => if is_open st g then DOut else via_master
      | _ => match next_peer_of st g i with Some k => DTo k | None => DSome (members T g) end
      end
  | None => via_master
  end.

(** The four propagation types ([flags_to_propagation_type],
    fs/namespace.c:2840-2851). *)
Inductive PropType := PShared | PSlave | PPrivate | PUnbindable.

(** [change_mnt_propagation (m, type)] (fs/pnode.c:93-124) on the order
    data, read in the state [st] before the change:
    - MS_SHARED: nothing ([set_mnt_shared] keeps every link; a new group has
      one member and needs no ring entry);
    - else, when [m] is shared: [m] leaves its ring; its slaves go, in their
      order, to the head of the slave list of [change_dest]
      ([transfer_propagation], fs/pnode.c:74-88); a group whose last member
      in the tables [m] was ends, and its key is not given again;
    - [m] leaves its master's slave list (fs/pnode.c:112);
    - MS_SLAVE: [m] goes to the head of [change_dest]'s slave list, before
      the slaves it handed over (fs/pnode.c:113-116).
    A list the model does not know stays unknown, and a list that changed
    at a mount the model cannot name is forgotten. *)
Definition change_one_links (st : NsState) (k : PropType) (m : Mount) : PropLinks :=
  let pl := ns_prop st in
  let i := mnt_id m in
  let not_i := fun x => negb (Pos.eqb x i) in
  match k with
  | PShared => pl
  | _ =>
      let d := change_dest st m in
      let mine := match mnt_peer m with Some _ => slave_list st i | None => Some [] end in
      let pl1 := match mnt_peer m with
                 | Some g =>
                     let pl0 := match pl_find g (pl_rings pl) with
                                | Some l => set_ring pl g
                                              (match List.filter not_i l with
                                               | [] => None
                                               | l' => Some l'
                                               end)
                                | None => pl
                                end in
                     match List.filter not_i (members (ns_mounts st) g) with
                     | [] => pl_with_next_group pl0 (Pos.max (pl_next_group pl0) (Pos.succ g))
                     | _ => pl0
                     end
                 | None => pl
                 end in
      let pl2 := set_slaves (unlist pl1 i) i None in
      let moved := match k with PSlave => option_map (cons i) mine | _ => mine end in
      match d with
      | DTo t => set_slaves pl2 t
                   (match moved, slave_list st t with
                    | Some a, Some b => Some (a ++ List.filter not_i b)
                    | _, _ => None
                    end)
      | DOut => pl2
      | DSome cs => match moved with Some [] => pl2 | _ => forget_lists pl2 cs end
      end
  end.

(** [set_mnt_shared] (fs/pnode.h:33-37) on mount [i]: it keeps its group, or
    takes group [g] that [invent_group_ids] gave it (fs/namespace.c:2449-
    2464); it keeps its master and loses the unbindable mark (T_SHARED_MASK,
    fs/mount.h:115). *)
Definition share_one (T : list Mount) (g i : positive) : list Mount :=
  map (fun x => if Pos.eqb (mnt_id x) i
                then mnt_with_unbindable
                       (mnt_with_peer x (match mnt_peer x with Some h => Some h | None => Some g end))
                       false
                else x) T.

(** [change_mnt_propagation] on the mount table: MS_SLAVE and MS_PRIVATE are
    [Mount.change_one]; MS_UNBINDABLE is MS_PRIVATE with the unbindable mark
    set (fs/pnode.c:117-123). *)
Definition change_type_table (k : PropType) (T : list Mount) (g i : positive) : list Mount :=
  match k with
  | PShared => share_one T g i
  | PSlave => change_one PropSlave T i
  | PPrivate => change_one PropPrivate T i
  | PUnbindable => map (fun x => if Pos.eqb (mnt_id x) i then mnt_with_unbindable x true else x)
                       (change_one PropPrivate T i)
  end.

(** The propagation change of one mount, on the table and the order data.
    A mount with no group that becomes shared takes [new_group_key]. *)
Definition change_type_one (k : PropType) (st : NsState) (i : positive) : NsState :=
  match find_mount (ns_mounts st) i with
  | None => st
  | Some m =>
      let g := new_group_key st in
      let T' := change_type_table k (ns_mounts st) g i in
      match k with
      | PShared =>
          match mnt_peer m with
          | Some _ => with_mounts st T'
          | None => key_used (with_mounts st T') g
          end
      | _ => with_ns_prop (with_mounts st T') (change_one_links st k m)
      end
  end.

(** [do_change_type]'s loop (fs/namespace.c:2877-2884): with MS_REC every
    mount of the subtree in pre-order, each against the state the earlier
    ones left.  With MS_SHARED, [invent_group_ids] gives the mounts with no
    group their groups before the loop; each new group has one member and
    the loop changes no other mount's group, so giving each its key when
    the loop reaches it is the same.  The checks before the loop belong to
    the arm ([MountArms.mount_change_type]). *)
Definition change_type (k : PropType) (st : NsState) (r : positive) (recursive : bool) : NsState :=
  fold_left (change_type_one k) (setattr_targets (ns_mounts st) r recursive) st.

Lemma change_type_one_mounts : forall k k0 st i,
  (k = PSlave /\ k0 = PropSlave) \/ (k = PPrivate /\ k0 = PropPrivate) ->
  ns_mounts (change_type_one k st i) = change_one k0 (ns_mounts st) i.
Proof.
  intros k k0 st i Hk. unfold change_type_one.
  destruct (find_mount (ns_mounts st) i) as [m|] eqn:Hf.
  - destruct Hk as [[Hk Hk0]|[Hk Hk0]]; subst k k0; reflexivity.
  - unfold change_one. rewrite Hf. reflexivity.
Qed.

Lemma change_type_fold_mounts : forall k k0 targets st,
  (k = PSlave /\ k0 = PropSlave) \/ (k = PPrivate /\ k0 = PropPrivate) ->
  ns_mounts (fold_left (change_type_one k) targets st)
  = fold_left (change_one k0) targets (ns_mounts st).
Proof.
  intros k k0 targets. induction targets as [|i rest IH]; intros st Hk; [reflexivity|].
  cbn [fold_left]. rewrite (IH _ Hk). rewrite (change_type_one_mounts k k0 st i Hk).
  reflexivity.
Qed.

(** On the mount table, MS_SLAVE and MS_PRIVATE give what the published
    [Mount.change_propagation] gives. *)
Theorem change_type_group_level : forall k k0 st r rec,
  (k = PSlave /\ k0 = PropSlave) \/ (k = PPrivate /\ k0 = PropPrivate) ->
  change_propagation (ns_mounts st) r rec k0
  = match find_mount (ns_mounts st) r with
    | None => MErr EINVAL
    | Some _ => MOk (ns_mounts (change_type k st r rec))
    end.
Proof.
  intros k k0 st r rec Hk. unfold change_propagation, change_type.
  destruct (find_mount (ns_mounts st) r); [|reflexivity].
  rewrite (change_type_fold_mounts k k0 _ st Hk). reflexivity.
Qed.
