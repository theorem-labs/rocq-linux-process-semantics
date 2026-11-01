(** * LinuxProcessSem.Checks.Cases.Ns.UsernsCases — user namespaces and id maps

    Each example runs one operation of [Ns.Userns] and states its exact
    result: an id mapped through one extent; how a written map is parsed
    and refused; who may write a map and what it then holds; the setgroups
    file; and the namespace a creation makes or the errno it gives. *)

From Stdlib Require Import List PArith ZArith Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables Userns.
Import ListNotations.
Open Scope Z_scope.

Example map_one_extent : map_id [mkExtent 0 1000 1] 0 = Some 1000 := eq_refl.
Example map_outside_extent : map_id [mkExtent 0 1000 1] 1 = None := eq_refl.
Example map_second_extent : map_id [mkExtent 0 1000 1; mkExtent 5 2000 3] 6 = Some 2001 := eq_refl.

(** The bytes of a string, and the newline and NUL bytes. *)
Definition zs (s : string) : list Z := map (fun c => Z.of_nat (nat_of_ascii c)) (list_ascii_of_string s).
Definition NL : list Z := [10].
Definition NUL : list Z := [0].

Definition one : list IdExtent := [mkExtent 0 1000 1].

(** [map_write]'s parse: three decimal numbers per line, separated by any
    white space, the count last and nothing after it. *)
Example parse_one : parse_map (zs "0 1000 1") = Some one := eq_refl.
Example parse_trailing_newline : parse_map (zs "0 1000 1" ++ NL) = Some one := eq_refl.
Example parse_spaces : parse_map (zs "  0   1000 1  " ++ NL) = Some one := eq_refl.
Example parse_tabs : parse_map (zs "0" ++ [9] ++ zs "1000" ++ [9] ++ zs "1") = Some one := eq_refl.
Example parse_two_lines :
  parse_map (zs "0 1000 1" ++ NL ++ zs "1 2000 1" ++ NL)
  = Some [mkExtent 0 1000 1; mkExtent 1 2000 1] := eq_refl.

(** What the parse refuses (EINVAL). *)
Example parse_empty : parse_map [] = None := eq_refl.
Example parse_missing_count : parse_map (zs "0 1000") = None := eq_refl.
Example parse_zero_count : parse_map (zs "0 1000 0") = None := eq_refl.
Example parse_first_minus_one : parse_map (zs "4294967295 0 1") = None := eq_refl.
Example parse_wraps : parse_map (zs "4294967294 0 2") = None := eq_refl.
Example parse_last_id : parse_map (zs "4294967294 0 1") = Some [mkExtent 4294967294 0 1] := eq_refl.
Example parse_junk : parse_map (zs "0 1000 1x") = None := eq_refl.
Example parse_fourth_number : parse_map (zs "0 1000 1 2") = None := eq_refl.
Example parse_no_digits : parse_map (zs "x 1000 1") = None := eq_refl.
Example parse_blank_line : parse_map (zs "0 1000 1" ++ NL ++ NL) = None := eq_refl.
Example parse_overlap_upper :
  parse_map (zs "0 1000 2" ++ NL ++ zs "1 2000 1") = None := eq_refl.
Example parse_overlap_lower :
  parse_map (zs "0 1000 2" ++ NL ++ zs "5 1001 1") = None := eq_refl.

(** A number is read as an unsigned long and stored in 32 bits, and a NUL
    ends what the parse reads. *)
Example parse_truncates : parse_map (zs "4294967296 1000 1") = Some one := eq_refl.
Example parse_nul_ends : parse_map (zs "0 1000 1" ++ NUL ++ zs "junk") = Some one := eq_refl.

(** At most 340 lines. *)
Fixpoint dec_rev (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => []
  | S f => if n <? 10 then [48 + n] else (48 + n mod 10) :: dec_rev f (n / 10)
  end.
Definition dec (n : Z) : list Z := rev (dec_rev 20 n).
Definition lines (k : nat) : list Z :=
  flat_map (fun i => dec (Z.of_nat i) ++ zs " " ++ dec (100000 + Z.of_nat i) ++ zs " 1" ++ NL)
           (seq 0 k).

Example parse_340_lines : option_map (@List.length IdExtent) (parse_map (lines 340)) = Some 340%nat.
Proof. vm_compute. reflexivity. Qed.
Example parse_341_lines : parse_map (lines 341) = None.
Proof. vm_compute. reflexivity. Qed.

(** The namespaces: 1 is the initial one, whose maps are the identity; 2 is
    a child of 1 owned by kuid 1000 with no map written; 3 is a child of 2
    owned by kuid 1000.  [all] is every capability. *)
Definition full : list IdExtent := [mkExtent 0 0 4294967295].
Definition all : Z := 2 ^ 41 - 1.

Definition root_ns : UserNs := mkUserNs 1%positive None 0%nat 0 (Some full) (Some full) true true.
Definition ns2 (setgroups : bool) : UserNs :=
  mkUserNs 2%positive (Some 1%positive) 1%nat 1000 None None setgroups false.
Definition ns2_mapped : UserNs :=
  mkUserNs 2%positive (Some 1%positive) 1%nat 1000 (Some one) (Some one) false false.
Definition ns3 (could_setfcap : bool) : UserNs :=
  mkUserNs 3%positive (Some 2%positive) 2%nat 1000 None None false could_setfcap.

(** A task inside namespace [n] with euid and egid 1000 and the given
    effective set there. *)
Definition inside (n : positive) (caps : Z) : IdCred := mkIdCred n 1000 1000 caps.

Definition uid_map_of (r : NsResult (list UserNs)) (n : positive) : option (option (list IdExtent)) :=
  match r with NsOk u => option_map uns_uid_map (find_userns u n) | NsErr _ => None end.
Definition gid_map_of (r : NsResult (list UserNs)) (n : positive) : option (option (list IdExtent)) :=
  match r with NsOk u => option_map uns_gid_map (find_userns u n) | NsErr _ => None end.
Definition err_of {A} (r : NsResult A) : option Z := match r with NsErr e => Some e | NsOk _ => None end.

(** The owner of a new namespace maps its own uid to 0 there. *)
Example owner_maps_own_uid :
  uid_map_of (map_write [root_ns; ns2 true] 2 UidMap (inside 2 all) (inside 2 all) 0
                        (zs "0 1000 1" ++ NL)) 2
  = Some (Some one) := eq_refl.

(** A map is written once. *)
Example second_write_refused :
  err_of (map_write [root_ns; ns2_mapped] 2 UidMap (inside 2 all) (inside 2 all) 0
                    (zs "0 1000 1")) = Some 1 := eq_refl.

(** A gid map by the owner alone needs setgroups denied first. *)
Example gid_map_needs_setgroups_deny :
  err_of (map_write [root_ns; ns2 true] 2 GidMap (inside 2 all) (inside 2 all) 0
                    (zs "0 1000 1")) = Some 1 := eq_refl.
Example gid_map_after_deny :
  gid_map_of (map_write [root_ns; ns2 false] 2 GidMap (inside 2 all) (inside 2 all) 0
                        (zs "0 1000 1")) 2
  = Some (Some one) := eq_refl.

(** Mapping another kernel id needs CAP_SETUID over the parent. *)
Example other_uid_refused :
  err_of (map_write [root_ns; ns2 true] 2 UidMap (inside 2 all) (inside 2 all) 0
                    (zs "0 0 1")) = Some 1 := eq_refl.

(** A privileged task of the parent may write any range it maps. *)
Example parent_privileged_writes_range :
  uid_map_of (map_write [root_ns; ns2 true] 2 UidMap (inside 1 all) (inside 1 all) 0
                        (zs "0 5000 10")) 2
  = Some (Some [mkExtent 0 5000 10]) := eq_refl.

(** The lower ids are read in the parent and stored as kernel ids: 0 in
    namespace 2 is kuid 1000.  Mapping lower id 0 needs the creator of
    namespace 3 to have had CAP_SETFCAP. *)
Example lower_ids_translated :
  uid_map_of (map_write [root_ns; ns2_mapped; ns3 true] 3 UidMap (inside 3 all) (inside 3 all) 0
                        (zs "0 0 1")) 3
  = Some (Some one) := eq_refl.
Example root_map_needs_setfcap :
  err_of (map_write [root_ns; ns2_mapped; ns3 false] 3 UidMap (inside 3 all) (inside 3 all) 0
                    (zs "0 0 1")) = Some 1 := eq_refl.

(** A lower id the parent does not map is refused. *)
Example unmapped_lower_refused :
  err_of (map_write [root_ns; ns2_mapped; ns3 true] 3 UidMap (inside 2 all) (inside 2 all) 0
                    (zs "0 1 1")) = Some 1 := eq_refl.

(** The checks before the parse. *)
Example initial_ns_map_refused :
  err_of (map_write [root_ns] 1 UidMap (inside 1 all) (inside 1 all) 0 (zs "0 0 1")) = Some 1
  := eq_refl.
Example opener_elsewhere_refused :
  err_of (map_write [root_ns; ns2_mapped; ns3 true] 3 UidMap (inside 1 all) (inside 1 all) 0
                    (zs "0 0 1")) = Some 1 := eq_refl.
Example offset_refused :
  err_of (map_write [root_ns; ns2 true] 2 UidMap (inside 2 all) (inside 2 all) 1
                    (zs "0 1000 1")) = Some 22 := eq_refl.
Example page_refused :
  err_of (map_write [root_ns; ns2 true] 2 UidMap (inside 2 all) (inside 2 all) 0
                    (repeat 32 4096)) = Some 22.
Proof. vm_compute. reflexivity. Qed.
Example opener_without_sys_admin_refused :
  err_of (map_write [root_ns; ns2 true] 2 UidMap (inside 2 0) (inside 2 all) 0
                    (zs "0 1000 1")) = Some 1 := eq_refl.
Example malformed_after_permission :
  err_of (map_write [root_ns; ns2 true] 2 UidMap (inside 2 all) (inside 2 all) 0
                    (zs "0 1000")) = Some 22 := eq_refl.

(** The setgroups file. *)
Definition sg_of (r : NsResult (list UserNs)) (n : positive) : option bool :=
  match r with NsOk u => option_map uns_setgroups_allowed (find_userns u n) | NsErr _ => None end.

Example setgroups_deny : sg_of (setgroups_write [root_ns; ns2 true] 2 0 (zs "deny")) 2 = Some false
  := eq_refl.
Example setgroups_deny_newline :
  sg_of (setgroups_write [root_ns; ns2 true] 2 0 (zs "deny" ++ NL)) 2 = Some false := eq_refl.
Example setgroups_allow_after_deny_refused :
  err_of (setgroups_write [root_ns; ns2 false] 2 0 (zs "allow")) = Some 1 := eq_refl.
Example setgroups_deny_after_gid_map_refused :
  err_of (setgroups_write [root_ns; ns2_mapped] 2 0 (zs "deny")) = Some 1 := eq_refl.
Example setgroups_junk_refused :
  err_of (setgroups_write [root_ns; ns2 true] 2 0 (zs "denyx")) = Some 22 := eq_refl.
Example setgroups_long_refused :
  err_of (setgroups_write [root_ns; ns2 true] 2 0 (zs "deny    ")) = Some 22 := eq_refl.
Example setgroups_offset_refused :
  err_of (setgroups_write [root_ns; ns2 true] 2 3 (zs "deny")) = Some 22 := eq_refl.

Definition level_of (r : NsResult (positive * list UserNs)) : option nat :=
  match r with
  | NsOk (i, u) => option_map uns_level (find_userns u i)
  | NsErr _ => None
  end.

(** A new user namespace is one level below its parent and has no maps yet. *)
Example create_child_level :
  level_of (create_user_ns [root_ns] 1%positive 1000 true) = Some 1%nat := eq_refl.

Example create_child_unmapped :
  match create_user_ns [root_ns] 1%positive 1000 true with
  | NsOk (i, u) => option_map uns_uid_map (find_userns u i)
  | NsErr _ => None
  end = Some None := eq_refl.

(** The new namespace records whether its creator held CAP_SETFCAP. *)
Example create_records_setfcap :
  match create_user_ns [root_ns] 1%positive 1000 false with
  | NsOk (i, u) => option_map uns_parent_could_setfcap (find_userns u i)
  | NsErr _ => None
  end = Some false := eq_refl.

(** A parent at level 33 can have no child: ENOSPC. *)
Definition deep : UserNs := mkUserNs 1%positive None 33%nat 0 None None true true.
Example create_too_deep : create_user_ns [deep] 1%positive 1000 true = NsErr 28 := eq_refl.

(** A parent at level 32 still can. *)
Definition level32 : UserNs := mkUserNs 1%positive None 32%nat 0 None None true true.
Example create_at_level_32 :
  level_of (create_user_ns [level32] 1%positive 1000 true) = Some 33%nat := eq_refl.

Example create_missing_parent : create_user_ns [root_ns] 2%positive 1000 true = NsErr 22 := eq_refl.

(** A child copies the parent's setgroups state. *)
Definition denied : UserNs := mkUserNs 1%positive None 0%nat 0 None None false true.
Example create_inherits_setgroups_deny :
  match create_user_ns [denied] 1%positive 1000 true with
  | NsOk (i, u) => option_map uns_setgroups_allowed (find_userns u i)
  | NsErr _ => None
  end = Some false := eq_refl.
