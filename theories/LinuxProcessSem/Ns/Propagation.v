(** * LinuxProcessSem.Ns.Propagation — mount propagation: the order data and its rules

    A mount's peer group ([mnt_peer]) and the peer group it is a slave of
    ([mnt_master]) are in [Tables.Mount]; the order the kernel keeps of each
    peer group's [mnt_share] ring and of each mount's [mnt_slave_list] is
    [Tables.PropLinks], the state's [ns_prop].  This file states what that
    data must satisfy ([prop_ok], with the checker [prop_okb]), which
    mounts can receive a mount or unmount event from a peer group that has a
    member outside the tables ([open_reach]), how a propagation type changes
    a mount ([change_type]), what a copy of a mount links ([clone_links]),
    how a tree attached on a shared mount propagates ([propagate_copies],
    [attach_tree]), what an MNT_DETACH unmount removes and changes
    ([umount_detach_prop]), and which group a slave's mountinfo line names
    as [propagate_from] ([dominating_id]).

    Linux v6.18.46 sources: [struct mount] (fs/mount.h:68-71, 95, 103-115);
    [next_peer], [first_slave], [next_slave] (fs/pnode.c:17-30);
    [change_mnt_propagation] and [transfer_propagation] (fs/pnode.c:74-124),
    which keep every member of a peer group on the same master; [clone_mnt]
    (fs/namespace.c:1246-1296), which never makes a mount a slave of its own
    group; [next_group], [need_secondary], [find_master] and
    [propagate_mnt] (fs/pnode.c:228-366); [copy_tree], [lock_mnt_tree],
    [invent_group_ids], [count_mounts] and [attach_recursive_mnt]
    (fs/namespace.c:2157-2230, 2412-2437, 2449-2487, 2559-2673);
    [umount_tree] (fs/namespace.c:1771-1838), [bulk_make_private]
    (fs/pnode.c:126-175), [propagate_mount_unlock] and [propagate_umount]
    (fs/pnode.c:466-687; Documentation/filesystems/propagate_umount.txt);
    [get_peer_under_root] and [get_dominating_id] (fs/pnode.c:33-67).

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

From Stdlib Require Import List PArith ZArith Bool.
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

(* =========================================================================
   Copies: clone_mnt's links
   ========================================================================= *)

(** [l] with [ys] put right after [x] ([list_add] after [x] in a ring,
    [hlist_add_behind] after [x] in a slave list); [l] when [x] is not in
    it. *)
Fixpoint ins_after (x : positive) (ys l : list positive) : list positive :=
  match l with
  | [] => []
  | a :: r => if Pos.eqb a x then a :: ys ++ r else a :: ins_after x ys r
  end.

(** The ring entry of [g], or the slave-list entry of [k], changed by [f]
    where the order data has one: an order the model does not know stays
    unknown. *)
Definition upd_ring (pl : PropLinks) (g : positive) (f : list positive -> list positive)
    : PropLinks :=
  match pl_find g (pl_rings pl) with
  | Some l => set_ring pl g (Some (f l))
  | None => pl
  end.

Definition upd_slaves (pl : PropLinks) (k : positive) (f : list positive -> list positive)
    : PropLinks :=
  match pl_find k (pl_slaves pl) with
  | Some l => set_slaves pl k (Some (f l))
  | None => pl
  end.

(** What [ring_of] and [slave_list] know in [st] of group [g]'s ring and of
    shared mount [k]'s slave list, written as an entry of [pl] where [pl]
    has none.  Their inference from the members holds only while a group
    keeps its members and slaves, so a call that adds one writes the
    entries first. *)
Definition pin_ring (st : NsState) (pl : PropLinks) (g : positive) : PropLinks :=
  match pl_find g (pl_rings pl), ring_of st g with
  | None, Some l => set_ring pl g (Some l)
  | _, _ => pl
  end.

Definition pin_slaves (st : NsState) (pl : PropLinks) (k : positive) : PropLinks :=
  match pl_find k (pl_slaves pl), slave_list st k with
  | None, Some l => if is_shared (ns_mounts st) k then set_slaves pl k (Some l) else pl
  | _, _ => pl
  end.

(** [clone_mnt]'s links (fs/namespace.c:1259-1288) for copies of mounts of
    [st]: each pair is a mount of the tables and the key of its copy, in
    the order the copies are made, with clone flags 0 ([do_loopback],
    [copy_mnt_ns] into a namespace of the same owner) or CL_SLAVE
    ([copy_mnt_ns] into a namespace of another owner, fs/namespace.c:
    4134-4136; [cl_slave]):
    - without CL_SLAVE, the copy of a shared mount joins its group right
      after it in the ring (1259-1262, 1280-1281) and has no slave; the copy
      of a slave goes right after it in its master's slave list, a slave of
      the same master (1286-1288);
    - with CL_SLAVE, the copy of a shared mount is a slave of it, at the
      head of its slave list (1283-1285); the copy of a slave in no group
      as without.
    The rings and lists the copies change are first written as entries
    where the model knows them ([pin_ring], [pin_slaves]). *)
Definition clone_links (st : NsState) (cl_slave : bool) (pairs : list (Mount * positive))
    : PropLinks :=
  let T := ns_mounts st in
  let gs := flat_map (fun p => match mnt_peer (fst p) with Some g => [g] | None => [] end) pairs in
  let ks := flat_map (members T) gs
            ++ flat_map (fun p => match master_mount st (fst p) with Some k => [k] | None => [] end)
                        pairs in
  let pl0 := fold_left (pin_slaves st) ks (fold_left (pin_ring st) gs (ns_prop st)) in
  fold_left
    (fun pl p =>
       let i := mnt_id (fst p) in
       let y := snd p in
       let behind := fun pl' : PropLinks =>
                       match master_mount st (fst p) with
                       | Some k => upd_slaves pl' k (ins_after i [y])
                       | None => pl'
                       end in
       match mnt_peer (fst p) with
       | Some g =>
           if cl_slave then upd_slaves pl i (cons y)
           else behind (set_slaves (upd_ring pl g (ins_after i [y])) y (Some []))
       | None => behind pl
       end)
    pairs pl0.

(** Each mount of [l] and the key of its copy: [base] plus its place in
    [l] counted from 1, the keys [Mount.copies] and [Mount.copy_mnt_ns]
    give. *)
Definition copy_pairs (base : positive) (l : list Mount) : list (Mount * positive) :=
  map (fun p => (snd p, (base + Pos.of_succ_nat (fst p))%positive)) (combine (seq 0 (length l)) l).

(** The pairs of a bind [Mount.bind_mount] accepts: its source mounts
    ([Mount.bind_sources]) and their copies.  None for a bind it refuses. *)
Definition bind_pairs (st : NsState) (src : positive) (below : positive -> bool) (recursive : bool)
    : list (Mount * positive) :=
  match find_mount (ns_mounts st) src with
  | Some s => match bind_sources (ns_mounts st) s below recursive with
              | Some l => copy_pairs (max_mount_id (ns_mounts st)) l
              | None => []
              end
  | None => []
  end.

(** The order data after a bind onto a mount that is not shared: each copy
    keeps its source's group and master (clone flags 0, [__do_loopback],
    fs/namespace.c:2954-2971). *)
Definition bind_links (st : NsState) (src : positive) (bp : BindPaths) (recursive : bool)
    : PropLinks :=
  clone_links st false (bind_pairs st src (bp_below bp) recursive).

(** The order data after [copy_mnt_ns] (fs/namespace.c:4108-4178) of the
    namespace whose root mount is [root]: the copies [Mount.copy_mnt_ns]
    makes, with CL_SLAVE into a namespace of another owner. *)
Definition copy_ns_links (st : NsState) (root : positive) (other_userns : bool) : PropLinks :=
  clone_links st other_userns
    (copy_pairs (max_mount_id (ns_mounts st)) (subtree_mounts (ns_mounts st) root)).

(* =========================================================================
   Open groups at the arms
   ========================================================================= *)

(** [open_reach] of mount [i], computed only when the launch names an open
    group: with none it is false ([closed_no_outside_event]), and a path
    walk pays nothing for it. *)
Definition open_mount (st : NsState) (i : positive) : bool :=
  match env_open_groups (ns_env st) with
  | [] => false
  | _ => match find_mount (ns_mounts st) i with
         | Some m => open_reach st m
         | None => false
         end
  end.

(** Mount namespace [n] holds a mount that can receive an event from an
    open group: the host can add mounts to it or remove mounts from it, so
    the number of its mounts, which [count_mounts] reads, is not the
    tables'. *)
Definition ns_open (st : NsState) (n : positive) : bool :=
  match env_open_groups (ns_env st) with
  | [] => false
  | _ => existsb (fun m => Pos.eqb (mnt_ns m) n && open_reach st m) (ns_mounts st)
  end.

(** The mounts besides [m] that [change_mnt_propagation (m, k)]
    (fs/pnode.c:93-124) reads and changes, in the state [st] before the
    change.  MS_SHARED: none ([set_mnt_shared] changes [m] alone).  Else:
    - when [m] is shared, the slaves it hands over
      ([transfer_propagation], fs/pnode.c:74-88, sets the master of each):
      its slave list while its group keeps another member and the list is
      known, else every slave of its group in the tables;
    - the mount [change_dest] names, whose slave list takes those slaves
      and an MS_SLAVE [m] (every candidate, when the model does not know
      which);
    - the master whose slave list [m] leaves (fs/pnode.c:112; every member
      of [m]'s master group, when the model does not know which). *)
Definition change_reads (k : PropType) (st : NsState) (m : Mount) : list positive :=
  match k with
  | PShared => []
  | _ =>
      let T := ns_mounts st in
      let i := mnt_id m in
      let moved :=
        match mnt_peer m with
        | Some g =>
            match List.filter (fun x => negb (Pos.eqb x i)) (members T g), slave_list st i with
            | _ :: _, Some l => l
            | _, _ => group_slaves T g
            end
        | None => []
        end in
      let dest := match change_dest st m with DTo t => [t] | DOut => [] | DSome cs => cs end in
      let old := match master_mount st m with
                 | Some t => [t]
                 | None => match mnt_master m with Some h => members T h | None => [] end
                 end in
      moved ++ dest ++ old
  end.

(** The mounts a propagation change of the mounts [l] reads, one mount
    after another as [change_type]'s fold changes them: each mount of [l],
    and what its change reads ([change_reads]) in the state the earlier
    changes left. *)
Fixpoint change_type_reads (k : PropType) (st : NsState) (l : list positive) : list positive :=
  match l with
  | [] => []
  | i :: r =>
      let here := match find_mount (ns_mounts st) i with
                  | Some m => change_reads k st m
                  | None => []
                  end in
      i :: here ++ change_type_reads k (change_type_one k st i) r
  end.

(** A propagation change to type [k] ([Some k]) or a [mount_setattr]
    ([None] when it changes no propagation) of mount [r] reads a mount
    that can receive an event from an open group: a mount it selects ([r],
    and with [recursive] its subtree) or, for a change, a mount
    [change_type_reads] lists.  The arm then has no answer: the host can
    mount or unmount at such a mount at any time, and
    [change_mnt_propagation] of a mount in an open group takes the next
    peer among all members of the group, those outside the tables
    included, and makes an MS_SLAVE mount a slave of that peer
    (fs/pnode.c:101-116), which the tables cannot name.  The test reads
    the state [st] at the start of the call: no host event comes during a
    propagation change, which holds [namespace_sem] for writing
    ([do_change_type], fs/namespace.c:2871; [do_mount_setattr] when it
    changes propagation, 4798-4835; [namespace_lock], 1727-1730), and a change
    moves a slave only to a member of its master group or of the group
    above, makes an MS_SLAVE mount a slave of the group it leaves or of
    its master group, and gives a new group a key above every open group
    ([new_group_key]), so no mount comes to receive from an open group.
    Computed only when the launch names an open group, as [open_mount]. *)
Definition targets_open (st : NsState) (k : option PropType) (r : positive) (recursive : bool)
    : bool :=
  match env_open_groups (ns_env st) with
  | [] => false
  | _ =>
      let ts := setattr_targets (ns_mounts st) r recursive in
      existsb (open_mount st) (match k with Some k => change_type_reads k st ts | None => ts end)
  end.

(** With no open group, the default launch, no mount is open: the arms
    answer as they do without the test. *)
Theorem targets_open_closed : forall st k r recursive,
  env_open_groups (ns_env st) = [] -> targets_open st k r recursive = false.
Proof.
  intros st k r recursive H. unfold targets_open. rewrite H. reflexivity.
Qed.

(* =========================================================================
   The walk of a propagation tree: next_group
   ========================================================================= *)

(** [l] split before [e]: a ring read from [e] is the second part, then the
    first ([l] itself when [e] is not in it). *)
Fixpoint split_ring (e : positive) (l : list positive) : list positive * list positive :=
  match l with
  | [] => ([], [])
  | x :: r => if Pos.eqb x e then ([], l)
              else let p := split_ring e r in (x :: fst p, snd p)
  end.

Definition rotate (l : list positive) (e : positive) : list positive :=
  snd (split_ring e l) ++ fst (split_ring e l).

(** The units of a slave list, in its order.  [propagate_mnt] visits a peer
    group at once, and a slave in no group alone (fs/pnode.c:321-356); the
    members of a slave group are one run of their master's list
    (fs/pnode.c:199), and [next_group] enters the group at the first of
    them (fs/pnode.c:235-236, 248-249).  A unit is its group's key, or
    [None] for a slave in no group, and the mount the walk enters it at. *)
Definition units_of (T : list Mount) (l : list positive) : list (option positive * positive) :=
  fold_left
    (fun acc i =>
       match find_mount T i with
       | Some x =>
           match mnt_peer x with
           | Some h => if existsb (fun u => opt_pos_eqb (fst u) (Some h)) acc then acc
                       else acc ++ [(Some h, i)]
           | None => acc ++ [(None, i)]
           end
       | None => acc
       end)
    l [].

(** The units that receive from group [g] directly: its slaves in the
    tables, in table order. *)
Definition kid_units (T : list Mount) (g : positive) : list (option positive * positive) :=
  units_of T (group_slaves T g).

(** The units of a propagation tree in the order [propagate_mnt] visits
    them ([next_group], fs/pnode.c:228-258, from fs/pnode.c:321): a unit,
    its members in the order of its ring from where the walk entered it,
    then, for each member in that order, the units of its slave list, each
    with the units below it.  [ring] gives a unit's members and [kids] the
    units below a group, each with whether it took an order the model does
    not know; the result says whether one did.  Each unit has a member, so
    the number of mounts bounds the depth; a unit met twice, which no Linux
    mount tree has, shows as a member met twice, and the arm declines. *)
Fixpoint walk_units (fuel : nat)
    (ring : option positive -> positive -> list positive * bool)
    (kids : positive -> list positive -> list (option positive * positive) * bool)
    (u : option positive * positive) : list (option positive * list positive) * bool :=
  match fuel with
  | O => ([], false)
  | Datatypes.S f =>
      let ms := ring (fst u) (snd u) in
      match fst u with
      | None => ([(None, fst ms)], snd ms)
      | Some g =>
          let ks := kids g (fst ms) in
          fold_left
            (fun acc k => let r := walk_units f ring kids k in (fst acc ++ fst r, snd acc || snd r))
            (fst ks) ([(Some g, fst ms)], snd ms || snd ks)
      end
  end.

(** The order of the tables: a ring in table order, a group's slaves in
    table order.  It is no order the kernel keeps. *)
Definition canon_ring (T : list Mount) (og : option positive) (e : positive)
    : list positive * bool :=
  match og with
  | Some g => (rotate (members T g) e, false)
  | None => ([e], false)
  end.

Definition canon_kids (T : list Mount) (g : positive) (_ : list positive)
    : list (option positive * positive) * bool :=
  (kid_units T g, false).

(** The order the kernel keeps, as far as the order data knows it: a ring
    from [ring_of]; the units below a group from its members' slave lists,
    member by member ([slave_list]).  Where the model does not know it, the
    table order and the flag. *)
Definition walk_ring (st : NsState) (og : option positive) (e : positive)
    : list positive * bool :=
  match og with
  | Some g => match ring_of st g with
              | Some l => (rotate l e, false)
              | None => (rotate (members (ns_mounts st) g) e, true)
              end
  | None => ([e], false)
  end.

Definition same_unit (u v : option positive * positive) : bool :=
  match fst u, fst v with
  | Some a, Some b => Pos.eqb a b
  | None, None => Pos.eqb (snd u) (snd v)
  | _, _ => false
  end.

Definition walk_kids (st : NsState) (g : positive) (ms : list positive)
    : list (option positive * positive) * bool :=
  let T := ns_mounts st in
  let canon := kid_units T g in
  let lists := map (slave_list st) ms in
  if forallb (fun o => match o with Some _ => true | None => false end) lists then
    let ks := units_of T (flat_map (fun o => match o with Some l => l | None => [] end) lists) in
    if Nat.eqb (length ks) (length canon) && forallb (fun u => existsb (same_unit u) ks) canon
    then (ks, false) else (canon, true)
  else (canon, true).

(** The units of the propagation tree of mount [tgt] of group [g]: in table
    order, read from the tables alone ([plan_units]); in the kernel's order
    as far as the order data knows it, with the flag ([walked_units]).  The
    first unit is [g]. *)
Definition plan_units (T : list Mount) (g tgt : positive) : list (option positive * list positive) :=
  fst (walk_units (Datatypes.S (length T)) (canon_ring T) (canon_kids T) (Some g, tgt)).

Definition walked_units (st : NsState) (g tgt : positive)
    : list (option positive * list positive) * bool :=
  walk_units (Datatypes.S (length (ns_mounts st))) (walk_ring st) (walk_kids st) (Some g, tgt).

(* =========================================================================
   propagate_mnt: which mounts get a secondary
   ========================================================================= *)

(** [need_secondary] (fs/pnode.c:260-272): the target dentry [td] is below
    [n]'s root ([is_subdir]; [below root d] is the test, which the caller
    gives).  A mount of the tables is not new, and the model has no
    anonymous namespace. *)
Definition need_secondary (T : list Mount) (below : positive -> positive -> bool) (td n : positive)
    : bool :=
  match find_mount T n with
  | Some m => below (mnt_root m) td
  | None => false
  end.

(** The secondaries of the units [us]: each mount that gets one, with the
    index of its unit in [us].  The target itself gets the source tree, not
    a secondary (fs/pnode.c:322-327). *)
Definition plan_secs (T : list Mount) (below : positive -> positive -> bool) (tgt td : positive)
    (us : list (option positive * list positive)) : list (positive * nat) :=
  flat_map (fun p => map (fun n => (n, fst p))
                         (List.filter (fun n => negb (Pos.eqb n tgt) && need_secondary T below td n)
                                      (snd (snd p))))
           (combine (seq 0 (length us)) us).

(** [P] in the order of the mounts [s], then the rest of [P]. *)
Definition reorder (P : list (positive * nat)) (s : list positive) : list (positive * nat) :=
  flat_map (fun n => List.filter (fun x => Pos.eqb (fst x) n) P) s
  ++ List.filter (fun x => negb (mem (fst x) s)) P.

Lemma reorder_in : forall P s x, In x (reorder P s) <-> In x P.
Proof.
  intros P s x. unfold reorder. split.
  - intros H. apply in_app_or in H. destruct H as [H|H].
    + apply in_flat_map in H. destruct H as [n [_ Hn]]. cbv beta in Hn.
      apply filter_In in Hn. exact (proj1 Hn).
    + apply filter_In in H. exact (proj1 H).
  - intros H. apply in_or_app.
    destruct (mem (fst x) s) eqn:Hm.
    + left. apply in_flat_map. exists (fst x). split.
      * unfold mem in Hm. apply existsb_exists in Hm. destruct Hm as [y [Hy Hxy]].
        apply Pos.eqb_eq in Hxy. rewrite Hxy. exact Hy.
      * cbv beta. apply filter_In. split; [exact H|]. cbv beta. apply Pos.eqb_refl.
    + right. apply filter_In. split; [exact H|]. cbv beta. rewrite Hm. reflexivity.
Qed.

(** [propagate_mnt]'s secondaries (fs/pnode.c:311-366) for a tree attached
    on mount [tgt] of group [g] at dentry [td], in the order it makes them:
    each is the mount it sits on and its unit in [plan_units].  Which
    mounts get one, and so each one's unit, comes from the tables alone;
    the order of the walk ([walked_units]) only orders them. *)
Definition propagate_copies (st : NsState) (below : positive -> positive -> bool)
    (g tgt td : positive) : list (positive * nat) :=
  reorder (plan_secs (ns_mounts st) below tgt td (plan_units (ns_mounts st) g tgt))
          (flat_map snd (fst (walked_units st g tgt))).

(** The order data changes the order of the secondaries only: with any
    other order data, the same mounts get secondaries, each in the same
    unit, so with the same group and the same master group per position of
    the tree ([unit_group], [unit_master_at] read the units alone).  This
    is the claim of the order-data rule: an order the model does not know
    decides an answer only through the order of two secondaries in one
    namespace. *)
Theorem propagate_group_level_order_free : forall st pl below g tgt td x,
  In x (propagate_copies (with_ns_prop st pl) below g tgt td)
  <-> In x (propagate_copies st below g tgt td).
Proof.
  intros st pl below g tgt td x. unfold propagate_copies.
  pose proof (reorder_in (plan_secs (ns_mounts st) below tgt td (plan_units (ns_mounts st) g tgt))
                         (flat_map snd (fst (walked_units (with_ns_prop st pl) g tgt))) x) as H1.
  pose proof (reorder_in (plan_secs (ns_mounts st) below tgt td (plan_units (ns_mounts st) g tgt))
                         (flat_map snd (fst (walked_units st g tgt))) x) as H2.
  exact (iff_trans H1 (iff_sym H2)).
Qed.

(* =========================================================================
   The groups of the copies: invent_group_ids, clone_mnt, find_master
   ========================================================================= *)

Definition unit_shared (us : list (option positive * list positive)) (ui : nat) : bool :=
  match nth_error us ui with
  | Some (Some _, _) => true
  | _ => false
  end.

(** A unit that gets copies: the target's (the source) or one with a
    secondary. *)
Definition productive (secs : list (positive * nat)) (ui : nat) : bool :=
  Nat.eqb ui 0 || existsb (fun s => Nat.eqb (snd s) ui) secs.

(** The groups other than the target's that get secondaries: each gets a
    new group per position of the tree. *)
Definition new_units (us : list (option positive * list positive)) (secs : list (positive * nat))
    : list nat :=
  List.filter (fun ui => negb (Nat.eqb ui 0) && productive secs ui && unit_shared us ui)
              (seq 0 (length us)).

Fixpoint pos_in (x : nat) (l : list nat) : option nat :=
  match l with
  | [] => None
  | y :: r => if Nat.eqb x y then Some O else option_map Datatypes.S (pos_in x r)
  end.

Fixpoint unit_index (g : positive) (us : list (option positive * list positive)) : option nat :=
  match us with
  | [] => None
  | u :: r => if opt_pos_eqb (fst u) (Some g) then Some O else option_map Datatypes.S (unit_index g r)
  end.

(** The group a unit receives from: its members' master group. *)
Definition unit_master (T : list Mount) (u : option positive * list positive) : option positive :=
  match snd u with
  | i :: _ => match find_mount T i with Some m => mnt_master m | None => None end
  | [] => None
  end.

(** The nearest unit above unit [ui] that gets copies.  [find_master]
    (fs/pnode.c:274-297) climbs from the new secondary's mount to the first
    master marked as the master of a mount that got one (fs/pnode.c:316-
    317, 347-348), and returns the copy made last in the unit below it:
    so, per position of the tree, the first secondary of a unit is a slave
    of the last copy made in the nearest unit above it that has copies,
    and the secondaries after it in the unit are its peers (CL_MAKE_SHARED,
    fs/pnode.c:354).  The target's unit (index 0) has the source. *)
Fixpoint up_productive (fuel : nat) (T : list Mount) (us : list (option positive * list positive))
    (prod : nat -> bool) (ui : nat) : nat :=
  match fuel with
  | O => O
  | Datatypes.S f =>
      match nth_error us ui with
      | Some u =>
          match unit_master T u with
          | Some h =>
              match unit_index h us with
              | Some pi => if prod pi then pi else up_productive f T us prod pi
              | None => O
              end
          | None => O
          end
      | None => O
      end
  end.

(** The [n]-th new group key from [k0] on. *)
Definition key_at (k0 : positive) (n : nat) : positive :=
  Pos.pred (k0 + Pos.of_succ_nat n)%positive.

(** How many source mounts before position [j] have no group:
    [invent_group_ids] gives each a new one, in the tree's order
    (fs/namespace.c:2449-2464), before [propagate_mnt] makes any. *)
Definition inv_rank (src : list Mount) (j : nat) : nat :=
  length (List.filter (fun m => match mnt_peer m with Some _ => false | None => true end)
                      (firstn j src)).

(** The group of the source mount [s] at position [j]: its own, or the new
    one [invent_group_ids] gives it. *)
Definition src_group (k0 : positive) (src : list Mount) (j : nat) (s : Mount) : positive :=
  match mnt_peer s with Some h => h | None => key_at k0 (inv_rank src j) end.

(** The group of the secondaries of unit [ui] at position [j] of the tree
    ([s] the source mount there): the target's group copies the source
    with CL_MAKE_SHARED, so its secondaries join the source's groups
    (fs/pnode.c:322-327, fs/namespace.c:1259-1262); another shared unit's
    first secondary is a CL_SLAVE | CL_MAKE_SHARED copy, a new group, which
    the later ones join (fs/pnode.c:329-333, 354; fs/namespace.c:1264-
    1268); a slave in no group gets a copy in no group (CL_SLAVE). *)
Definition unit_group (k0 : positive) (src : list Mount) (us : list (option positive * list positive))
    (nu : list nat) (ui j : nat) (s : Mount) : option positive :=
  if Nat.eqb ui 0 then Some (src_group k0 src j s)
  else match pos_in ui nu with
       | Some r => Some (key_at k0 (inv_rank src (length src) + r * length src + j))
       | None => None
       end.

(** The master group of those secondaries: the source's master for the
    target's group (a CL_MAKE_SHARED copy of a slave is a slave of its
    master, fs/namespace.c:1286-1288); else the group of the copies of the
    nearest unit above that has copies ([up_productive]; CL_SLAVE,
    fs/namespace.c:1283-1285). *)
Definition unit_master_at (T : list Mount) (k0 : positive) (src : list Mount)
    (us : list (option positive * list positive)) (nu : list nat) (psecs : list (positive * nat))
    (ui j : nat) (s : Mount) : option positive :=
  if Nat.eqb ui 0 then mnt_master s
  else unit_group k0 src us nu (up_productive (length us) T us (productive psecs) ui) j s.

(* =========================================================================
   The secondary trees: copy_tree, lock_mnt_tree, the overmount
   ========================================================================= *)

(** The copy at position [j] of the secondary tree on mount [n]: [copy_tree]
    (fs/namespace.c:2157-2230) of the source tree [src] (each secondary is
    a copy of the one before, which is a copy of the source), its root on
    [n] at the target dentry [td] (fs/pnode.c:346), each other copy on the
    copy of its parent at its own mount point; the flags and locks of the
    source mount (fs/namespace.c:1256-1257), no MNT_LOCKED on the root and
    the source's on a child (2208-2209), never unbindable; the group
    [peer] and master group [master].  Into a namespace whose owner is not
    the owner of the caller's mount namespace ([cross]), [lock_mnt_tree]
    (fs/namespace.c:2412-2437, from 2637-2639) locks every flag a copy has
    and sets MNT_LOCKED on every copy but the root.  [key i] is the key of
    the copy at position [i]. *)
Definition sec_mount (src : list Mount) (key : nat -> positive) (cross : bool) (td : positive)
    (n : Mount) (j : nat) (s : Mount) (peer master : option positive) : Mount :=
  let parent := if Nat.eqb j 0 then Some (mnt_id n)
                else match mnt_parent s with
                     | Some p => match index_of p src with
                                 | Some i => Some (key i)
                                 | None => Some (mnt_id n)
                                 end
                     | None => Some (mnt_id n)
                     end in
  let m1 := mnt_with_place (mnt_with_ns (mnt_with_id s (key j)) (mnt_ns n)) parent
                           (if Nat.eqb j 0 then td else mnt_mountpoint s) in
  let m2 := mnt_with_lock_flags m1 (if cross then flags_or (mnt_lock_flags s) (mnt_flags s)
                                    else mnt_lock_flags s) in
  let m3 := mnt_with_locked m2 (if Nat.eqb j 0 then false else mnt_locked s || cross) in
  mnt_with_master (mnt_with_peer (mnt_with_unbindable m3 false) peer) master.

Fixpoint index_where (p : Mount -> bool) (l : list Mount) : option nat :=
  match l with
  | [] => None
  | m :: r => if p m then Some O else option_map Datatypes.S (index_where p r)
  end.

(** [topmost_overmount] (fs/mount.h:243-248) within the source tree: from
    position [j], the copy on the root of the copy there, and so on up;
    its position and mount. *)
Fixpoint top_of (fuel : nat) (src : list Mount) (j : nat) (s : Mount) : nat * Mount :=
  match fuel with
  | O => (j, s)
  | Datatypes.S f =>
      match index_where (fun c => is_child_of (mnt_id s) c && Pos.eqb (mnt_mountpoint c) (mnt_root s))
                        src with
      | Some j' => match nth_error src j' with
                   | Some c => top_of f src j' c
                   | None => (j, s)
                   end
      | None => (j, s)
      end
  end.

(** [__lookup_mnt]: the mount of [T] on mount [p] at dentry [d]. *)
Definition mount_at (T : list Mount) (p d : positive) : option Mount :=
  find (fun m => match mnt_parent m with
                 | Some q => Pos.eqb q p && Pos.eqb (mnt_mountpoint m) d
                 | None => false
                 end) T.

Definition mntns_owner_of (st : NsState) (n : positive) : option positive :=
  match find (fun x => Pos.eqb (mntns_id x) n) (ns_mntns st) with
  | Some x => Some (mntns_owner x)
  | None => None
  end.

(* =========================================================================
   attach_recursive_mnt onto a shared mount
   ========================================================================= *)

(** The namespaces of the secondaries, one entry per secondary. *)
Definition sec_namespaces (T : list Mount) (secs : list (positive * nat)) : list positive :=
  flat_map (fun s => match find_mount T (fst s) with Some n => [mnt_ns n] | None => [] end) secs.

Definition occ (n : positive) (l : list positive) : nat := length (List.filter (Pos.eqb n) l).

(** [count_mounts] for each namespace that gets secondaries (fs/pnode.c:351;
    fs/namespace.c:2466-2487): the mounts it has, plus the source tree in
    the target's namespace [ns0] (fs/namespace.c:2588-2592), plus each
    secondary tree it gets, above the limit [mx].  Each call adds to the
    namespace's [pending_mounts], so a namespace over the limit refuses the
    call in every order of the walk. *)
Definition prop_enospc (T : list Mount) (mx : Z) (ns0 : positive) (size : nat) (nss : list positive)
    : bool :=
  existsb (fun n => (mx <? Z.of_nat (ns_mount_count T n + (if Pos.eqb n ns0 then size else 0)
                                     + size * occ n nss))%Z)
          nss.

(** The checks of a tree of [size] mounts attached on mount [tgt] of group
    [g] in namespace [ns0], at dentry [td], before any change: [None] when
    the call goes on; [Some (Some e)] the tables' errno; [Some None] when
    the tables do not decide it:
    - the order data breaks a rule ([prop_okb]), or the walk meets a mount
      twice (no Linux mount tree does);
    - a mount of the propagation tree can receive an event from an open
      group, or a namespace the call adds mounts to holds one: the host
      can mount or unmount there at any time, which changes the tree and
      the counts, so the call has no answer;
    - a namespace that gets a secondary is not in the tables;
    - [count_mounts] refuses ([prop_enospc]): ENOSPC, the tables' answer
      (fs/pnode.c:351);
    - the walk read, anywhere in the propagation tree, a ring or slave
      list whose order the model does not know, and some namespace gets
      two or more secondaries: the creation order of those secondaries,
      which mountinfo shows, may then be unknown.  The test declines
      whenever both hold, also when the unknown order cannot change the
      order of those secondaries (for example an unknown slave list whose
      groups get no secondary).  It is conservative: a bind or a new mount
      onto a shared mount had no answer before propagation was modelled,
      so no answer the model gave before is lost.
    The allocators' refusals (ENOMEM from [clone_mnt] and
    [get_mountpoint], ENOMEM and ENOSPC from [mnt_alloc_group_id], ENOSPC
    from [count_mounts] of a namespace outside the tables) are the
    environment's ([MountArms.mount40_injected]). *)
Definition attach_check (st : NsState) (below : positive -> positive -> bool) (size : nat)
    (ns0 g tgt td : positive) : option (option Z) :=
  let T := ns_mounts st in
  let us := plan_units T g tgt in
  let wk := walked_units st g tgt in
  let nss := sec_namespaces T (plan_secs T below tgt td us) in
  if negb (prop_okb st) then Some None
  else if negb (nodupb (flat_map snd us)) || negb (nodupb (flat_map snd (fst wk))) then Some None
  else if existsb (open_mount st) (flat_map snd us) || existsb (ns_open st) (ns0 :: nss)
  then Some None
  else if negb (forallb (fun n => match mntns_owner_of st n with Some _ => true | None => false end)
                        nss)
  then Some None
  else if prop_enospc T (env_mount_max (ns_env st)) ns0 size nss then Some (Some ENOSPC)
  else if snd wk && existsb (fun n => Nat.ltb 1 (occ n nss)) nss then Some None
  else None.

Fixpoint dedup_nat (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: r => x :: List.filter (fun y => negb (Nat.eqb y x)) (dedup_nat r)
  end.

(** The order data after the attach.  [ksecs] are the secondaries in the
    order they are made, each with its index; [skey k j] is the key of the
    copy at position [j] of the [k]-th.
    - The source copies' own links ([clone_links], for a bind).
    - The target unit's secondaries join the source mounts' groups right
      after each source mount, in the order they are made, and after it in
      its master's slave list (fs/namespace.c:1280-1281, 1286-1288); a new
      group of the source has them as its ring.
    - Every new shared mount has no slave yet.  Each other unit's
      secondaries at a position: a new group whose ring is them in the
      order made, at the head of the slave list of the last copy made at
      that position in the nearest unit above with copies (CL_SLAVE,
      fs/namespace.c:1283-1285, then each behind the one before,
      1286-1288).
    When the walk took an order the model does not know ([guessed]; the
    call then puts at most one secondary in each namespace), the order of
    the copies is not known: the new mounts and groups get no entry, and a
    ring or list that got two or more of them loses its entry.
    [pl_next_group] moves past the new group keys. *)
Definition attach_links (st : NsState) (pairs : list (Mount * positive)) (src : list Mount)
    (us : list (option positive * list positive)) (psecs : list (positive * nat))
    (ksecs : list (nat * (positive * nat))) (guessed : bool) (k0 : positive) (nu : list nat)
    (skey : nat -> nat -> positive) : PropLinks :=
  let T := ns_mounts st in
  let sz := length src in
  let jsrc := combine (seq 0 sz) src in
  let keys_of := fun ui j => map (fun ks => skey (fst ks) j)
                                 (List.filter (fun ks => Nat.eqb (snd (snd ks)) ui) ksecs) in
  let pl1 :=
    fold_left
      (fun pl p =>
         let j := fst p in
         let y := mnt_id (snd p) in
         let cs := keys_of O j in
         let mk := match nth_error pairs j with
                   | Some x => master_mount st (fst x)
                   | None => None
                   end in
         if guessed && Nat.ltb 1 (length cs) then
           let pl' := match mnt_peer (snd p) with Some h => set_ring pl h None | None => pl end in
           match mk with Some k => set_slaves pl' k None | None => pl' end
         else
           let pl' := match mnt_peer (snd p) with
                      | Some h => upd_ring pl h (ins_after y cs)
                      | None => if guessed then pl
                                else set_ring pl (src_group k0 src j (snd p)) (Some (y :: cs))
                      end in
           match mk with Some k => upd_slaves pl' k (ins_after y cs) | None => pl' end)
      jsrc (clone_links st false pairs) in
  let cnt := inv_rank src sz + length nu * sz in
  let pl_end := fun pl : PropLinks =>
                  if Nat.eqb cnt 0 then pl
                  else pl_with_next_group pl (Pos.max (pl_next_group pl) (key_at k0 cnt)) in
  if guessed then pl_end (fold_left (fun pl s => set_slaves pl (mnt_id s) None) src pl1)
  else
    let shared_keys := map mnt_id src
                       ++ flat_map (fun ks => if unit_shared us (snd (snd ks))
                                              then map (skey (fst ks)) (seq 0 sz) else [])
                                   ksecs in
    let pl2 := fold_left (fun pl k => set_slaves pl k (Some [])) shared_keys pl1 in
    let order := List.filter (fun ui => negb (Nat.eqb ui 0))
                             (dedup_nat (map (fun ks => snd (snd ks)) ksecs)) in
    let pl3 :=
      fold_left
        (fun pl ui =>
           let a := up_productive (length us) T us (productive psecs) ui in
           fold_left
             (fun pl' p =>
                let j := fst p in
                let cs := keys_of ui j in
                let f := match rev (keys_of a j) with k :: _ => k | [] => mnt_id (snd p) end in
                let pl'' := upd_slaves pl' f (fun l => cs ++ l) in
                match unit_group k0 src us nu ui j (snd p) with
                | Some ng => set_ring pl'' ng (Some cs)
                | None => pl''
                end)
             jsrc pl)
        order pl2 in
    pl_end pl3.

(** The attach itself, after [attach_check] (fs/namespace.c:2594-2651):
    the source tree [src] (root [s0], already on mount [tgt] of group [g] at
    dentry [td]) takes its groups ([invent_group_ids]) and becomes shared
    (2604-2607); the secondaries ([propagate_copies]) follow it in the
    table, in the order made, each tree in the source's order; a mount [q]
    already on a secondary's mount at [td] moves onto the topmost copy of
    that secondary tree, at its root, and keeps MNT_LOCKED (2640-2650; v7.1
    hands MNT_LOCKED over, v6.18.46 does not).  [owner] is the owner of the
    caller's mount namespace ([lock_mnt_tree], 2637-2639); [pairs] the
    source mounts' originals, for a bind. *)
Definition attach_build (st : NsState) (below : positive -> positive -> bool) (owner : positive)
    (pairs : list (Mount * positive)) (src : list Mount) (s0 : Mount) (g tgt td : positive)
    : NsState :=
  let T := ns_mounts st in
  let us := plan_units T g tgt in
  let psecs := plan_secs T below tgt td us in
  let wk := walked_units st g tgt in
  let secs := reorder psecs (flat_map snd (fst wk)) in
  let ksecs := combine (seq 0 (length secs)) secs in
  let k0 := new_group_key st in
  let nu := new_units us psecs in
  let sz := length src in
  let base := max_mount_id (T ++ src) in
  let skey := fun k j => (base + Pos.of_succ_nat (k * sz + j))%positive in
  let tp := top_of sz src 0 s0 in
  let moves := flat_map (fun ks => match mount_at T (fst (snd ks)) td with
                                    | Some q => [(mnt_id q, skey (fst ks) (fst tp))]
                                    | None => []
                                    end) ksecs in
  let T1 := map (fun m => match find (fun mv => Pos.eqb (fst mv) (mnt_id m)) moves with
                          | Some mv => mnt_with_place m (Some (snd mv)) (mnt_root (snd tp))
                          | None => m
                          end) T in
  let srcs := map (fun p => mnt_with_unbindable
                              (mnt_with_peer (snd p) (Some (src_group k0 src (fst p) (snd p)))) false)
                  (combine (seq 0 sz) src) in
  let made := flat_map (fun ks =>
                 match find_mount T (fst (snd ks)) with
                 | Some n =>
                     let ui := snd (snd ks) in
                     let cross := negb (opt_pos_eqb (mntns_owner_of st (mnt_ns n)) (Some owner)) in
                     map (fun p => sec_mount src (skey (fst ks)) cross td n (fst p) (snd p)
                                     (unit_group k0 src us nu ui (fst p) (snd p))
                                     (unit_master_at T k0 src us nu psecs ui (fst p) (snd p)))
                         (combine (seq 0 sz) src)
                 | None => []
                 end) ksecs in
  with_ns_prop (with_mounts st (T1 ++ srcs ++ made))
               (attach_links st pairs src us psecs ksecs (snd wk) k0 nu skey).

(** What a call that attaches a tree answers: the new state, an errno of
    the tables, or no answer from the tables. *)
Inductive Attach :=
  | ADone (st : NsState)
  | AErr (e : Z)
  | AOver.

(** [attach_recursive_mnt] (fs/namespace.c:2559-2673) of the source tree
    [src] on a shared mount [tgt] at dentry [td], after the caller's own
    checks ([graft_tree], [do_loopback], [do_add_mount]) and the count of
    the target's namespace (2588-2592): [attach_check], then
    [attach_build].  A target that is not shared does not propagate, and
    [Mount.bind_mount] and [NewMount.new_mount] answer for it. *)
Definition attach_tree (st : NsState) (below : positive -> positive -> bool) (owner : positive)
    (pairs : list (Mount * positive)) (src : list Mount) (tgt td : positive) : Attach :=
  match find_mount (ns_mounts st) tgt, src with
  | Some t, s0 :: _ =>
      match mnt_peer t with
      | Some g =>
          match attach_check st below (length src) (mnt_ns t) g tgt td with
          | Some (Some e) => AErr e
          | Some None => AOver
          | None => ADone (attach_build st below owner pairs src s0 g tgt td)
          end
      | None => AOver
      end
  | _, _ => AOver
  end.

(** A bind onto a shared mount: the bind [Mount.bind_mount] leaves
    undecided after all its checks because the target is shared (its
    source is in the caller's namespace [ns]).  The source copies are
    [Mount.copies]; [owner] is the owner of [ns]. *)
Definition bind_mount_shared (st : NsState) (ns owner : positive)
    (below : positive -> positive -> bool) (src : positive) (bp : BindPaths) (recursive : bool)
    (tgt td : positive) : Attach :=
  let T := ns_mounts st in
  match bind_mount T ns (env_mount_max (ns_env st)) src bp recursive tgt td, find_mount T src with
  | None, Some s =>
      if negb (Pos.eqb (mnt_ns s) ns) then AOver
      else match bind_sources T s (bp_below bp) recursive with
           | Some l =>
               attach_tree st below owner (copy_pairs (max_mount_id T) l)
                           (copies (max_mount_id T) l src (bp_src_dentry bp) tgt td ns) tgt td
           | None => AOver
           end
  | _, _ => AOver
  end.

(* =========================================================================
   Unmount: propagate_mount_unlock, propagate_umount, bulk_make_private
   ========================================================================= *)

(** The mounts that receive the mount and unmount events of mount [p]
    ([propagation_next (p, p)], fs/pnode.c:177-212): every mount of the
    units of its propagation tree but [p] itself; none for a mount in no
    group, which has no slave. *)
Definition receivers (T : list Mount) (p : positive) : list positive :=
  match find_mount T p with
  | Some m =>
      match mnt_peer m with
      | Some g => List.filter (fun q => negb (Pos.eqb q p)) (flat_map snd (plan_units T g p))
      | None => []
      end
  | None => []
  end.

(** The mounts at dentry [d] of the receivers of mount [p] ([__lookup_mnt]
    on each, fs/pnode.c:473-478, 510-513). *)
Definition received_children (T : list Mount) (p d : positive) : list positive :=
  flat_map (fun q => match mount_at T q d with Some c => [mnt_id c] | None => [] end)
           (receivers T p).

(** [propagate_mount_unlock] (fs/pnode.c:466-479), the first step of
    [umount_tree] with UMOUNT_PROPAGATE (fs/namespace.c:1776-1777): the
    mount at [x]'s mount point on each receiver of [x]'s parent loses
    MNT_LOCKED, before anything is decided. *)
Definition unlock_propagated (T : list Mount) (x : Mount) : list Mount :=
  match mnt_parent x with
  | Some p =>
      let cs := received_children T p (mnt_mountpoint x) in
      map (fun m => if mem (mnt_id m) cs then mnt_with_locked m false else m) T
  | None => T
  end.

Fixpoint dedup_pos (l : list positive) : list positive :=
  match l with
  | [] => []
  | x :: r => x :: List.filter (fun y => negb (Pos.eqb y x)) (dedup_pos r)
  end.

(** The candidates of [propagate_umount] for the subtree [U]
    ([gather_candidates], fs/pnode.c:500-535; propagate_umount.txt:51-62):
    for each mount of [U], the mount at its mount point on each receiver of
    its parent, when that mount is not in [U]. *)
Definition umount_candidates (T : list Mount) (U : list positive) : list positive :=
  dedup_pos (List.filter (fun c => negb (mem c U))
    (flat_map (fun i => match find_mount T i with
                        | Some m => match mnt_parent m with
                                    | Some p => received_children T p (mnt_mountpoint m)
                                    | None => []
                                    end
                        | None => []
                        end) U)).

(** Mount [x] is forbidden in the set [kept] (propagate_umount.txt:12-14,
    107-111): a subtree mounted strictly inside [x], that is on a child of
    [x] that does not sit on [x]'s root, holds a mount outside [kept]. *)
Definition forbidden (T : list Mount) (kept : list positive) (x : Mount) : bool :=
  existsb (fun c => is_child_of (mnt_id x) c && negb (Pos.eqb (mnt_mountpoint c) (mnt_root x))
                    && negb (forallb (fun i => mem i kept) (subtree T (mnt_id c)))) T.

(** The largest non-shifting subset of [U] and the candidates [C]
    (propagate_umount.txt:107-197; [trim_one], [trim_ancestors],
    fs/pnode.c:542-595): every forbidden candidate goes, again until none
    is.  A mount forbidden in a set is forbidden in each subset of it, so
    the order of removal does not matter.  [U] is a whole subtree, so none
    of it is forbidden.  Each round that removes nothing ends, so [C]'s
    length bounds the rounds. *)
Fixpoint trim_shifting (fuel : nat) (T : list Mount) (U C : list positive) : list positive :=
  match fuel with
  | O => C
  | Datatypes.S f =>
      let C' := List.filter (fun i => match find_mount T i with
                                      | Some x => negb (forbidden T (U ++ C) x)
                                      | None => false
                                      end) C in
      if Nat.eqb (length C') (length C) then C else trim_shifting f T U C'
  end.

(** The largest non-revealing subset (propagate_umount.txt:16-17, 349-413;
    [handle_locked], fs/pnode.c:597-616): every MNT_LOCKED candidate whose
    parent is not in the set goes, again until none does. *)
Fixpoint trim_revealing (fuel : nat) (T : list Mount) (U C : list positive) : list positive :=
  match fuel with
  | O => C
  | Datatypes.S f =>
      let C' := List.filter (fun i => match find_mount T i with
                                      | Some x => negb (mnt_locked x)
                                                  || match mnt_parent x with
                                                     | Some p => mem p (U ++ C)
                                                     | None => false
                                                     end
                                      | None => false
                                      end) C in
      if Nat.eqb (length C') (length C) then C else trim_revealing f T U C'
  end.

(** The candidates [propagate_umount] adds to the subtree of mount [i]
    (fs/pnode.c:658-687): those in the largest non-shifting, non-revealing
    subset of the subtree and its candidates.  That subset is unique
    (propagate_umount.txt:43-47), so the kernel's list surgery reaches it
    in every order of its lists. *)
Definition umount_added (T : list Mount) (i : positive) : list positive :=
  let U := subtree T i in
  let C0 := umount_candidates T U in
  let C1 := trim_shifting (Datatypes.S (length C0)) T U C0 in
  trim_revealing (Datatypes.S (length C1)) T U C1.

(** Every mount MNT_DETACH of mount [i] removes: its subtree
    ([umount_tree], fs/namespace.c:1780-1785) and the candidates
    [propagate_umount] adds (fs/namespace.c:1793-1794). *)
Definition umount_set (T : list Mount) (i : positive) : list positive :=
  subtree T i ++ umount_added T i.

(** The set reads the mount table alone: the order data never decides it,
    so the arm answers whatever the model knows of the order. *)
Theorem umount_set_order_free : forall st pl i,
  umount_set (ns_mounts (with_ns_prop st pl)) i = umount_set (ns_mounts st) i.
Proof. reflexivity. Qed.

(** Where a mount that stays on the root of a removed candidate [m] goes
    ([reparent], fs/pnode.c:631-643, from 679-683): down the stack of
    removed mounts under it, onto the first ancestor that stays, at the
    mount point the bottom of the stack had there. *)
Fixpoint stack_base (fuel : nat) (T : list Mount) (R : list positive) (m : Mount)
    : option (positive * positive) :=
  match fuel with
  | O => None
  | Datatypes.S f =>
      match mnt_parent m with
      | Some p => if mem p R
                  then match find_mount T p with
                       | Some pm => stack_base f T R pm
                       | None => None
                       end
                  else Some (p, mnt_mountpoint m)
      | None => None
      end
  end.

(** Each mount that stays on the root of a removed candidate of [C] (its
    [overmount], fs/mount.h:99), with its new parent and mount point. *)
Definition reparents (T : list Mount) (R C : list positive) : list (positive * (positive * positive)) :=
  flat_map (fun i => match find_mount T i with
                     | Some m =>
                         match mount_at T i (mnt_root m) with
                         | Some o => if mem (mnt_id o) R then []
                                     else match stack_base (length T) T R m with
                                          | Some b => [(mnt_id o, b)]
                                          | None => []
                                          end
                         | None => []
                         end
                     | None => []
                     end) C.

(** The group a slave of group [g] receives from once the mounts [R] are
    gone ([bulk_make_private], [trace_transfers], [set_destinations],
    fs/pnode.c:126-175: from a removed mount to its next peer that stays,
    else to its master, and on up): [g] while a member stays, or when [g]
    has no member in the tables (none is removed); else the first group up
    the chain of master groups with a member that stays; none when the
    chain ends ([transfer_propagation] to NULL, fs/pnode.c:79-82). *)
Fixpoint dest_group (fuel : nat) (T : list Mount) (R : list positive) (g : positive)
    : option positive :=
  match fuel with
  | O => None
  | Datatypes.S f =>
      if existsb (fun m => in_peer_group g m && negb (mem (mnt_id m) R)) T
         || negb (existsb (in_peer_group g) T)
      then Some g
      else match group_master T g with
           | Some (Some h) => dest_group f T R h
           | _ => None
           end
  end.

Definition new_master (T : list Mount) (R : list positive) (o : option positive) : option positive :=
  match o with
  | Some g => dest_group (Datatypes.S (length T)) T R g
  | None => None
  end.

(** The groups with a member in [R] and none outside it: they end, and
    their keys are not given again ([mnt_release_group_id] in
    [trace_transfers], fs/pnode.c:136-137). *)
Definition dead_groups (T : list Mount) (R : list positive) : list positive :=
  dedup_pos (flat_map (fun m => match mnt_peer m with
                                | Some g =>
                                    if mem (mnt_id m) R
                                       && negb (existsb (fun x => in_peer_group g x
                                                                 && negb (mem (mnt_id x) R)) T)
                                    then [g] else []
                                | None => []
                                end) T).

(** The order data once the mounts [R] are gone: they leave every ring and
    slave list ([list_del_init], [hlist_del_init], fs/pnode.c:132, 140),
    and their own lists go; a group that ends loses its entry and its key.
    The slaves of a removed mount go, in their order, to the head of the
    slave list of the mount [trace_transfers] reaches ([transfer_propagation],
    fs/pnode.c:74-88, 170-171), which ring and list orders choose: the
    slave lists of the members of each group that receives them become
    unknown. *)
Definition umount_links (st : NsState) (T : list Mount) (R : list positive) : PropLinks :=
  let pl := ns_prop st in
  let keep := fun l => List.filter (fun i => negb (mem i R)) l in
  let rings := flat_map (fun e => match keep (snd e) with [] => [] | l => [(fst e, l)] end)
                        (pl_rings pl) in
  let slaves := flat_map (fun e => if mem (fst e) R then [] else [(fst e, keep (snd e))])
                         (pl_slaves pl) in
  let gets := flat_map (fun m =>
                 if mem (mnt_id m) R then []
                 else match mnt_master m with
                      | Some g =>
                          if existsb (fun x => in_peer_group g x && mem (mnt_id x) R) T
                          then match new_master T R (Some g) with Some h => [h] | None => [] end
                          else []
                      | None => []
                      end) T in
  let pl1 := forget_lists (pl_with_slaves (pl_with_rings pl rings) slaves)
                          (flat_map (members T) (dedup_pos gets)) in
  pl_with_next_group pl1 (fold_left (fun acc g => Pos.max acc (Pos.succ g)) (dead_groups T R)
                                    (pl_next_group pl1)).

(** The mounts an MNT_DETACH of mount [i] reads: its subtree, the
    candidates, and the parent of each mount of the subtree with that
    parent's receivers. *)
Definition umount_reads (T : list Mount) (i : positive) : list positive :=
  let U := subtree T i in
  U ++ umount_candidates T U
  ++ flat_map (fun j => match find_mount T j with
                        | Some m => match mnt_parent m with Some p => p :: receivers T p | None => [] end
                        | None => []
                        end) U.

(** [umount_tree (X, UMOUNT_PROPAGATE)] of mount [i] (fs/namespace.c:
    1771-1838), which do_umount runs for every MNT_DETACH
    (fs/namespace.c:1948-1950), after the arm's checks: MNT_LOCKED cleared
    on the propagated mounts ([unlock_propagated], fs/namespace.c:
    1776-1777); the subtree and the candidates [propagate_umount] adds
    leave the tables (fs/namespace.c:1793-1794; fs/pnode.c:505-531 gathers
    them); a mount on the root of a removed candidate moves down
    ([reparents]); the slaves of removed mounts pass on
    ([bulk_make_private], fs/namespace.c:1796).  [None] when a mount it
    reads can receive an event from an open group: the host can mount or
    unmount there at any time, so a call whose answer reads such a mount
    has no answer. *)
Definition umount_detach_prop (st : NsState) (i : positive) : option NsState :=
  let T0 := ns_mounts st in
  match find_mount T0 i with
  | None => None
  | Some x =>
      if existsb (open_mount st) (umount_reads T0 i) then None
      else
        let T := unlock_propagated T0 x in
        let R := umount_set T i in
        let mv := reparents T R (umount_added T i) in
        let T2 := map (fun m =>
                         let m' := mnt_with_master m (new_master T R (mnt_master m)) in
                         match find (fun e => Pos.eqb (fst e) (mnt_id m)) mv with
                         | Some e => mnt_with_place m' (Some (fst (snd e))) (snd (snd e))
                         | None => m'
                         end)
                      (List.filter (fun m => negb (mem (mnt_id m) R)) T) in
        Some (with_ns_prop (with_mounts st T2) (umount_links st T R))
  end.

(** The mounts after an unmount do not depend on the order data: other
    order data gives the same table, or no answer in both. *)
Theorem umount_detach_prop_order_free : forall st pl i,
  option_map ns_mounts (umount_detach_prop (with_ns_prop st pl) i)
  = option_map ns_mounts (umount_detach_prop st i).
Proof.
  intros st pl i.
  assert (HT : ns_mounts (with_ns_prop st pl) = ns_mounts st) by reflexivity.
  assert (HO : open_mount (with_ns_prop st pl) = open_mount st) by reflexivity.
  unfold umount_detach_prop. rewrite HO, HT. cbv zeta.
  destruct (find_mount (ns_mounts st) i) as [x|]; [|reflexivity].
  destruct (existsb (open_mount st) (umount_reads (ns_mounts st) i)); reflexivity.
Qed.

(* =========================================================================
   mountinfo: get_dominating_id
   ========================================================================= *)

(** What [get_dominating_id] (fs/pnode.c:56-67) gives for a slave: the
    group of the first master up the chain that has a member in the
    slave's mount namespace whose root the reader's root reaches
    ([get_peer_under_root], fs/pnode.c:33-48); 0 when the chain ends
    without one; or [DomOut]: the chain leaves the tables at a group with
    no member in them, whose master and members outside the tables the
    model does not know. *)
Inductive DomId := DomGroup (g : positive) | DomZero | DomOut.

(** The chain from group [g] up, for a slave in mount namespace [ns].
    [reach d] is [is_path_reachable] of mount [d]'s root from the
    reader's root (fs/namespace.c:4514-4522), [None] when the tables do
    not decide it.  Every member of a group gives the group's number, so
    which member [get_peer_under_root] meets first does not matter.
    [None]: a test the tables do not decide.  A chain longer than the
    table loops, which no Linux mount tree does; it gives [DomOut]. *)
Fixpoint dom_chain (fuel : nat) (T : list Mount) (reach : Mount -> option bool) (ns g : positive)
    : option DomId :=
  match fuel with
  | O => Some DomOut
  | Datatypes.S f =>
      let cands := List.filter (fun d => in_peer_group g d && Pos.eqb (mnt_ns d) ns) T in
      if existsb (fun d => match reach d with Some true => true | _ => false end) cands
      then Some (DomGroup g)
      else if existsb (fun d => match reach d with None => true | _ => false end) cands then None
      else match group_master T g with
           | Some (Some h) => dom_chain f T reach ns h
           | Some None => Some DomZero
           | None => Some DomOut
           end
  end.

(** [get_dominating_id] of mount [m] (fs/pnode.c:56-67): [DomZero] for a
    mount that is not a slave. *)
Definition dominating_id (T : list Mount) (reach : Mount -> option bool) (m : Mount) : option DomId :=
  match mnt_master m with
  | Some g => dom_chain (Datatypes.S (length T)) T reach (mnt_ns m) g
  | None => Some DomZero
  end.
