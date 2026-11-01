(** * LinuxProcessSem.Ns.UserArms — unshare of a user namespace

    [unshare] (97) with CLONE_NEWUSER, from Linux 6.18.44 kernel/fork.c
    ([ksys_unshare], [check_unshare_flags]), kernel/user_namespace.c
    ([unshare_userns], [create_user_ns], [set_cred_user_ns]),
    kernel/ucount.c ([inc_ucount]), fs/namespace.c ([current_chrooted])
    and kernel/cred.c ([commit_creds], [cred_cap_issubset]).

    The answers, in the kernel's order: a bit outside the flags [unshare]
    knows, EINVAL; the task is single-threaded and its fs_struct is its own
    (the model makes no thread and no CLONE_FS sharing), so CLONE_THREAD
    and CLONE_FS, which CLONE_NEWUSER adds, change nothing; a parent above
    level 32, ENOSPC; [inc_ucount]: a charge over the limit of a sealed
    namespace, ENOSPC, and at a namespace that is not sealed ENOSPC or not
    ([Userns.ucount_check]); a chrooted task ([current_chrooted]: its root
    is not the root of the topmost mount on its mount namespace's root),
    EPERM; an owner or group the parent does not map, EPERM; then a
    security module's refusal ([security_create_user_ns], any errno from 1
    to 4095), an allocation failure (ENOMEM) and [set_cred_ucounts]'
    EAGAIN, all the environment's; else the new namespace, the task in it
    with every capability in its permitted, effective and bounding sets,
    none inheritable or ambient, and securebits cleared.  [commit_creds]
    resets neither the parent-death signal nor the dumpable mode: the new
    namespace is a child of the old one owned by the task's euid, so
    [cred_cap_issubset] holds.

    Any other flag set declines.  Kind: exact inside the tree; over at a
    namespace that is not sealed and for the environment's refusals. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Ext Mount Userns Walk Arm.
Import ListNotations.
Local Open Scope Z_scope.

Definition CLONE_VM : Z := 256.
Definition CLONE_FS : Z := 512.
Definition CLONE_FILES : Z := 1024.
Definition CLONE_SIGHAND : Z := 2048.
Definition CLONE_NEWTIME : Z := 128.
Definition CLONE_THREAD : Z := 65536.
Definition CLONE_NEWNS : Z := 131072.
Definition CLONE_SYSVSEM : Z := 262144.
Definition CLONE_NEWCGROUP : Z := 33554432.
Definition CLONE_NEWUTS : Z := 67108864.
Definition CLONE_NEWIPC : Z := 134217728.
Definition CLONE_NEWUSER : Z := 268435456.
Definition CLONE_NEWPID : Z := 536870912.
Definition CLONE_NEWNET : Z := 1073741824.

(** The flags [check_unshare_flags] accepts. *)
Definition unshare_valid : Z :=
  fold_left Z.lor [CLONE_THREAD; CLONE_FS; CLONE_NEWNS; CLONE_SIGHAND; CLONE_VM; CLONE_FILES;
                   CLONE_SYSVSEM; CLONE_NEWUTS; CLONE_NEWIPC; CLONE_NEWNET; CLONE_NEWUSER;
                   CLONE_NEWPID; CLONE_NEWCGROUP; CLONE_NEWTIME] 0.

Definition CAP_FULL_SET : Z := 2 ^ 41 - 1.

(** [topmost_overmount]: from mount [m], the mount on its root dentry, and
    so on up. *)
Fixpoint topmost_fuel (fuel : nat) (st : NsState) (m : Mount) : Mount :=
  match fuel with
  | O => m
  | S f => match mount_on st (mnt_id m) (mnt_root m) with
           | Some m' => topmost_fuel f st m'
           | None => m
           end
  end.

(** [current_chrooted]: the task's root is not the root dentry of the
    topmost mount on its mount namespace's root mount.  [None] when the
    tables do not list that namespace or mount. *)
Definition current_chrooted (st : NsState) (ctx : NsCtx) : option bool :=
  match find (fun n => Pos.eqb (mntns_id n) (cx_mount ctx)) (ns_mntns st) with
  | None => None
  | Some n =>
      match find_mount (ns_mounts st) (mntns_root n) with
      | None => None
      | Some r =>
          let top := topmost_fuel (length (ns_mounts st)) st r in
          Some (negb (Pos.eqb (fst (cx_root ctx)) (mnt_id top) && Pos.eqb (snd (cx_root ctx)) (mnt_root top)))
      end
  end.

(** The task in a new user namespace [n]: every capability permitted,
    effective and bounding, none inheritable or ambient, securebits 0
    ([set_cred_user_ns]). *)
Definition in_new_userns (ctx : NsCtx) (n : positive) : NsCtx :=
  mkNsCtx n (cx_mount ctx) (cx_pidns ctx) (cx_net ctx) (cx_pids ctx) (cx_root ctx) (cx_cwd ctx)
          (cx_umask ctx) (mkCaps CAP_FULL_SET CAP_FULL_SET 0 CAP_FULL_SET 0) 0 (cx_cloexec ctx)
          (cx_no_new_privs ctx) (cx_pdeathsig ctx) (cx_dumpable ctx).

(** The environment's refusals after the flag checks: [prepare_creds] and
    the namespace's allocation (ENOMEM), [alloc_ucounts] (ENOSPC through
    [inc_user_namespaces]), [set_cred_ucounts] (EAGAIN) and
    [security_create_user_ns] (any errno from 1 to 4095).  [user_injected]
    lists them for the forced-only filter. *)
Definition env_refusal (o : ext_outcome) (m : Model) (ctx : NsCtx) (st : NsState) : Prop :=
  exists e, 1 <= e <= 4095 /\ o = ns_errno e m ctx st.

Definition user_injected : list NsInjected :=
  [mkNsInjected 97 [(fun e => (e =? ENOMEM) || (e =? ENOSPC) || (e =? EAGAIN), FamAlloc);
                    (fun e => (1 <=? e) && (e <=? 4095), FamCred)]].

(** What [create_user_ns] answers from the tables, in its order, once the
    environment refuses nothing. *)
Definition unshare_exact (p : UserNs) (chrooted : bool) (m : Model) (ctx : NsCtx) (st : NsState)
    (o : ext_outcome) : Prop :=
  let euid := bv_unsigned (cr_euid (m_creds m)) in
  let egid := bv_unsigned (cr_egid (m_creds m)) in
  let after :=
    if chrooted then o = ns_errno EPERM m ctx st
    else if negb (kid_has_mapping (uns_uid_map p) euid && kid_has_mapping (uns_gid_map p) egid)
    then o = ns_errno EPERM m ctx st
    else match create_user_ns (ns_userns st) (cx_user ctx) euid
                              (Z.testbit (cap_effective (cx_caps ctx)) CAP_SETFCAP) with
         | NsOk (n, U') => o = ns_ret (Z_to_bv 64 0) m (in_new_userns ctx n) (with_userns st U')
         | NsErr e => o = ns_errno e m ctx st
         end in
  if Nat.ltb 32 (uns_level p) then o = ns_errno ENOSPC m ctx st
  else match ucount_check (ns_userns st) p euid with
       | ChargeFull => o = ns_errno ENOSPC m ctx st
       | ChargeEither => o = ns_errno ENOSPC m ctx st \/ after
       | ChargeOk => after
       end.

Definition unshare_arm : NsArm := fun i m ctx st o =>
  let f := bv_unsigned (in_arg i 0) in
  if negb (Z.land f (Z.lnot unshare_valid) =? 0) then o = ns_errno EINVAL m ctx st
  else if negb (f =? CLONE_NEWUSER) then o = EUnmodeled
  else
    match find_userns (ns_userns st) (cx_user ctx), current_chrooted st ctx with
    | Some p, Some chrooted => unshare_exact p chrooted m ctx st o \/ env_refusal o m ctx st
    | _, _ => o = EUnmodeled
    end.

(** For CLONE_NEWUSER alone, from a namespace and a mount namespace the
    tables hold, the answers are the tables' answer or the environment's. *)
Lemma unshare_arm_newuser : forall i m ctx st o p c,
  bv_unsigned (in_arg i 0) = CLONE_NEWUSER ->
  find_userns (ns_userns st) (cx_user ctx) = Some p ->
  current_chrooted st ctx = Some c ->
  unshare_arm i m ctx st o <-> unshare_exact p c m ctx st o \/ env_refusal o m ctx st.
Proof.
  intros i m ctx st o p c Hf Hp Hc. unfold unshare_arm. cbv zeta. rewrite Hf.
  replace (Z.land CLONE_NEWUSER (Z.lnot unshare_valid) =? 0) with true by reflexivity.
  replace (CLONE_NEWUSER =? CLONE_NEWUSER) with true by reflexivity.
  cbn [negb]. rewrite Hp, Hc. reflexivity.
Qed.

Definition user_arms : list (Z * NsArm) := [(97, unshare_arm)].
