(** * LinuxProcessSem.Ns.Userns — user namespaces and their id maps

    Pure functions over the table of user namespaces.

    Linux 6.18.44 sources:
    - an id seen through a map: [map_id_range_down] over the extents of
      [struct uid_gid_map], kernel/user_namespace.c;
    - the rules a written map must pass, before any permission check: one to
      [UID_GID_MAP_MAX_EXTENTS] (340) lines, a count above zero, no range
      that wraps 32 bits, and no two lines whose first ranges or lower ranges
      overlap ([map_write], [mappings_overlap], kernel/user_namespace.c);
      the permission checks ([new_idmap_permitted]) read the writer's
      credentials and belong to the arm that answers the write;
    - a new user namespace: [create_user_ns] refuses a parent above level 32
      with ENOSPC (kernel/user_namespace.c:91-93), starts with no maps, and
      copies the parent's flags, so the setgroups state
      (kernel/user_namespace.c:150).  The per-user count limit (95-97) and the
      chrooted and unmapped-owner refusals (105-107, 113-116) read state this
      table does not hold and belong to the arm. *)

From Stdlib Require Import List PArith ZArith Bool.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.
Import ListNotations.
Local Open Scope Z_scope.

Inductive NsResult (A : Type) :=
  | NsOk  (x : A)
  | NsErr (e : Z).
Arguments NsOk {A} x.
Arguments NsErr {A} e.

(** The id [x] maps to, through the first extent that holds it. *)
Fixpoint map_id (exts : list IdExtent) (x : Z) : option Z :=
  match exts with
  | [] => None
  | e :: r =>
      if (ext_first e <=? x) && (x <? ext_first e + ext_count e)
      then Some (ext_lower e + (x - ext_first e))
      else map_id r x
  end.

Definition extent_ok (e : IdExtent) : bool :=
  (0 <? ext_count e) && (0 <=? ext_first e) && (0 <=? ext_lower e)
  && (ext_first e + ext_count e <=? 4294967296)
  && (ext_lower e + ext_count e <=? 4294967296).

Definition ranges_overlap (a1 n1 a2 n2 : Z) : bool := (a1 <? a2 + n2) && (a2 <? a1 + n1).

Definition extents_overlap (a b : IdExtent) : bool :=
  ranges_overlap (ext_first a) (ext_count a) (ext_first b) (ext_count b)
  || ranges_overlap (ext_lower a) (ext_count a) (ext_lower b) (ext_count b).

Fixpoint no_overlap (l : list IdExtent) : bool :=
  match l with
  | [] => true
  | e :: r => forallb (fun f => negb (extents_overlap e f)) r && no_overlap r
  end.

Definition map_extents_ok (l : list IdExtent) : bool :=
  Nat.leb 1%nat (length l) && Nat.leb (length l) 340%nat && forallb extent_ok l && no_overlap l.

(** One extent whose ranges fit and whose count is positive always passes. *)
Theorem map_extents_ok_one : forall e, extent_ok e = true -> map_extents_ok [e] = true.
Proof.
  intros e He. unfold map_extents_ok. cbn [length Nat.leb forallb no_overlap].
  rewrite He. reflexivity.
Qed.

Definition find_userns (U : list UserNs) (i : positive) : option UserNs :=
  find (fun u => Pos.eqb (uns_id u) i) U.

Definition max_userns_id (U : list UserNs) : positive :=
  fold_left (fun acc u => Pos.max acc (uns_id u)) U 1%positive.

Definition create_user_ns (U : list UserNs) (parent : positive) (owner : Z)
    : NsResult (positive * list UserNs) :=
  match find_userns U parent with
  | None => NsErr EINVAL
  | Some p =>
      if Nat.ltb 32%nat (uns_level p) then NsErr ENOSPC
      else NsOk (Pos.succ (max_userns_id U),
                 mkUserNs (Pos.succ (max_userns_id U)) (Some parent)
                          (Datatypes.S (uns_level p)) owner None None
                          (uns_setgroups_allowed p) :: U)
  end.

(** A created namespace is a child of the parent, one level below it, owned
    by the creator, with no maps, and with the parent's setgroups state. *)
Theorem create_user_ns_child : forall U parent owner i U',
  create_user_ns U parent owner = NsOk (i, U') ->
  exists p, find_userns U parent = Some p
    /\ find_userns U' i
       = Some (mkUserNs i (Some parent) (Datatypes.S (uns_level p)) owner None None
                        (uns_setgroups_allowed p)).
Proof.
  intros U parent owner i U'. unfold create_user_ns.
  destruct (find_userns U parent) as [p|]; [|intros Hc; discriminate Hc].
  destruct (Nat.ltb 32%nat (uns_level p)); [intros Hc; discriminate Hc|].
  intros H. injection H as Hi HU. subst i U'.
  exists p. split; [reflexivity|].
  unfold find_userns. cbn [find uns_id]. rewrite Pos.eqb_refl. reflexivity.
Qed.

(** A parent above level 32 gets ENOSPC. *)
Theorem create_user_ns_too_deep : forall U parent owner p,
  find_userns U parent = Some p -> (32 < uns_level p)%nat ->
  create_user_ns U parent owner = NsErr ENOSPC.
Proof.
  intros U parent owner p Hf Hl. unfold create_user_ns. rewrite Hf. cbv iota.
  apply Nat.ltb_lt in Hl. rewrite Hl. reflexivity.
Qed.
