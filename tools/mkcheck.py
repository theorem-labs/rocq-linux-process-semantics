#!/usr/bin/env python3
"""Regenerate theories/LinuxProcessSem/ProcsCheck.v from Procs.v.

tools/check_one.py compiles one file against the INSTALLED library, and
Ns/Tables.v is a new file on this branch, so its two records are inlined
into a scratch copy.  The copy is for the one-second check only and is
never committed; the records below must match Ns/Tables.v exactly.
"""
import sys

INLINE = '''
(* SCRATCH ONLY -- see tools/mkcheck.py.  Must match Ns/Tables.v. *)
Record MountFlags := mkMountFlags {
  mf_ro : bool; mf_nosuid : bool; mf_nodev : bool; mf_noexec : bool }.
Record Mount := mkMount {
  mnt_id : positive; mnt_ns : positive; mnt_parent : option positive;
  mnt_mountpoint : positive; mnt_root : positive; mnt_sb : positive;
  mnt_flags : MountFlags; mnt_lock_flags : MountFlags;
  mnt_locked : bool; mnt_unbindable : bool }.
Record IdExtent := mkExtent {
  ext_first : Z; ext_lower : Z; ext_count : Z }.
Record UserNs := mkUserNs {
  uns_id : positive; uns_parent : option positive; uns_level : nat;
  uns_owner : Z; uns_uid_map : option (list IdExtent);
  uns_gid_map : option (list IdExtent); uns_setgroups_allowed : bool }.
Record NsState := mkNsState {
  ns_mounts : list Mount; ns_userns : list UserNs }.
Record NsCtx := mkNsCtx {
  cx_user : positive; cx_mount : positive;
  cx_root : positive * positive; cx_cwd : positive * positive }.
'''

IMPORT = '''(** [NsState] and [NsCtx].  This file DEPENDS ON [Ns/Tables.v] and does not
    vendor it: two representations of one thing are what diverge. *)
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Tables.
'''

ANCHOR = 'Local Open Scope bool_scope.'

src = open('theories/LinuxProcessSem/Procs.v').read()
if IMPORT not in src:
    sys.exit('mkcheck.py: the Ns/Tables import block is not where expected')
out = src.replace(IMPORT, '').replace(ANCHOR, ANCHOR + '\n' + INLINE, 1)
open('theories/LinuxProcessSem/ProcsCheck.v', 'w').write(out)
print('ProcsCheck.v regenerated')
