# A4 transcription brief — LPS start-state model (branch `revision/entry`)

All paths relative to `theories/LinuxProcessSem/`. Citations are `file:line`. `SL`=StackLayout.v, `ST`=State.v, `RN`=Run.v, `BV`=BvBase.v.
Conventions: `word = bv 64`, `byte = bv 8`. `Z_to_bv n z = z mod 2^n` and `bv_extract lo len v = (unsigned(v) >> lo) mod 2^len` (stdpp `bv`; these two are imported from `Riscv/Prelude`, NOT defined in the three files, and I did not read their source — standard stdpp semantics). All address arithmetic on `word` (`+`, `-`) wraps mod 2^64 (never wraps in practice). `[Z]`/`nat` arithmetic below is exact.

## 0. Findings you must know first

1. **`vdso_images` DOES NOT EXIST on this branch** (grep over whole repo incl. ignored files: no match for `vdso_images`, `vdso_image`, or any table of vDSO bytes). The model holds NO vDSO bytes. It only holds a vDSO *size in pages*: `vdso_text_pages kb = 1 + (kb_vdso mod 16)` (ST:3217). `ST:3215` says "a lane that gives the model a table of MEASURED images replaces this body alone"; `ST:3160-3162` says the image's content "belongs to the vDSO rules". `State.v` also does not define the hwcap constants (they are in StackLayout.v, SL:103-104).
2. This brief was written before `reports/` existed on the branch, by an agent whose write tool could not create it.
3. The build-stack function takes **11 args** in this branch: `build_stack_bytes la ph entry sp top argv envp execfn uid gid hwcap draw` (SL:451). (Many `Common/*.v` files still use the old 7-arg form; they're stale vs. this file.)
4. Fixture sanity numbers (Checks/Cases/EntryLaunch.v:26-30): argv=["a"], envp=[], execfn="a", RSEQ on → auxv 29 entries, items=4, C=512, L=4.

---

## 1. Primitive encoders

### 1.1 `word_le8` (BV:66-69)
```coq
Definition word_le8 (v : word) : list byte :=
  [ bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v;
    bv_extract 24 8 v; bv_extract 32 8 v; bv_extract 40 8 v;
    bv_extract 48 8 v; bv_extract 56 8 v ].
```
Python: `word_le8(v) = (v % 2**64).to_bytes(8,'little')`.

### 1.2 `len_word`, `nat_to_word` (BV:31-32, 36)
```coq
Definition len_word {A} (l : list A) : word := Z_to_bv 64 (Z.of_nat (length l)).
Definition nat_to_word (n : nat) : word := Z_to_bv 64 (Z.of_nat n).
```
Python: `len_word(l)=len(l) mod 2**64`; `nat_to_word(n)=n mod 2**64`.

### 1.3 `at_random_bytes` (SL:343-351)
```coq
Definition at_random_bytes (rnd : bv 128) : list byte :=
  [ bv_extract 0 8 rnd;    bv_extract 8 8 rnd;
    bv_extract 16 8 rnd;   bv_extract 24 8 rnd;
    bv_extract 32 8 rnd;   bv_extract 40 8 rnd;
    bv_extract 48 8 rnd;   bv_extract 56 8 rnd;
    bv_extract 64 8 rnd;   bv_extract 72 8 rnd;
    bv_extract 80 8 rnd;   bv_extract 88 8 rnd;
    bv_extract 96 8 rnd;   bv_extract 104 8 rnd;
    bv_extract 112 8 rnd;  bv_extract 120 8 rnd ].
```
Python: `at_random_bytes(rnd) = rnd.to_bytes(16,'little')` — i.e. the 16 recorded AT_RANDOM bytes b[0..15] give `rnd = int.from_bytes(b,'little')`; byte i of memory = byte i of b.

### 1.4 `string_addrs`, `flatten_strings` (SL:46-54, 56-57)
```coq
Fixpoint string_addrs (base : word) (strs : list (list byte))
    : list word * word :=
  match strs with
  | [] => ([], base)
  | s :: rest =>
    let next := base + len_word s + 1 in
    let '(ptrs, final) := string_addrs next rest in
    (base :: ptrs, final)
  end.

Definition flatten_strings (strs : list (list byte)) : list byte :=
  flat_map (fun s => s ++ [Z_to_bv 8 0]) strs.
```
Python: `ptrs=[]; a=base; for s in strs: ptrs.append(a); a+=len(s)+1; return (ptrs, a)`. `flatten_strings = b''.join(s+b'\0' for s in strs)`. (Elements of `s` are used as-is; `len(s)` counts bytes, a NUL inside s would still count — no special-casing.)

---

## 2. StackLayout.v definitions

### 2.1 Auxv tag constants (SL:64-92) — all `Z_to_bv 64 N`
```coq
Definition AT_NULL    : word := Z_to_bv 64 0.
Definition AT_PHDR    : word := Z_to_bv 64 3.
Definition AT_PHENT   : word := Z_to_bv 64 4.
Definition AT_PHNUM   : word := Z_to_bv 64 5.
Definition AT_PAGESZ  : word := Z_to_bv 64 6.
Definition AT_BASE    : word := Z_to_bv 64 7.
Definition AT_FLAGS   : word := Z_to_bv 64 8.
Definition AT_ENTRY   : word := Z_to_bv 64 9.
Definition AT_UID     : word := Z_to_bv 64 11.
Definition AT_EUID    : word := Z_to_bv 64 12.
Definition AT_GID     : word := Z_to_bv 64 13.
Definition AT_EGID    : word := Z_to_bv 64 14.
Definition AT_HWCAP   : word := Z_to_bv 64 16.
Definition AT_CLKTCK  : word := Z_to_bv 64 17.
Definition AT_SECURE  : word := Z_to_bv 64 23.
Definition AT_RANDOM  : word := Z_to_bv 64 25.
Definition AT_RSEQ_FEATURE_SIZE : word := Z_to_bv 64 27.
Definition AT_RSEQ_ALIGN        : word := Z_to_bv 64 28.
Definition AT_EXECFN  : word := Z_to_bv 64 31.
Definition AT_SYSINFO_EHDR      : word := Z_to_bv 64 33.
Definition AT_L1I_CACHESIZE     : word := Z_to_bv 64 40.
Definition AT_L1I_CACHEGEOMETRY : word := Z_to_bv 64 41.
Definition AT_L1D_CACHESIZE     : word := Z_to_bv 64 42.
Definition AT_L1D_CACHEGEOMETRY : word := Z_to_bv 64 43.
Definition AT_L2_CACHESIZE      : word := Z_to_bv 64 44.
Definition AT_L2_CACHEGEOMETRY  : word := Z_to_bv 64 45.
Definition AT_L3_CACHESIZE      : word := Z_to_bv 64 46.
Definition AT_L3_CACHEGEOMETRY  : word := Z_to_bv 64 47.
Definition AT_MINSIGSTKSZ       : word := Z_to_bv 64 51.
```
Python: `AT = dict(NULL=0,PHDR=3,PHENT=4,PHNUM=5,PAGESZ=6,BASE=7,FLAGS=8,ENTRY=9,UID=11,EUID=12,GID=13,EGID=14,HWCAP=16,CLKTCK=17,SECURE=23,RANDOM=25,RSEQ_FEATURE_SIZE=27,RSEQ_ALIGN=28,EXECFN=31,SYSINFO_EHDR=33,L1I_CACHESIZE=40,L1I_CACHEGEOMETRY=41,L1D_CACHESIZE=42,L1D_CACHEGEOMETRY=43,L2_CACHESIZE=44,L2_CACHEGEOMETRY=45,L3_CACHESIZE=46,L3_CACHEGEOMETRY=47,MINSIGSTKSZ=51)`.
Not emitted (SL:~110-130 comment): AT_HWCAP2/3/4, AT_PLATFORM, AT_BASE_PLATFORM, AT_EXECFD, AT_NOTELF, AT_IGNORE.

### 2.2 hwcap constants (SL:103-104)
```coq
Definition hwcap_rv64gc  : word := Z_to_bv 64 0x112D.
Definition hwcap_rv64gcv : word := Z_to_bv 64 0x20112D.
```
Python: `HWCAP_RV64GC=0x112D; HWCAP_RV64GCV=0x20112D` (differ only by bit 21, V). `valid_hwcap h := h=gc \/ h=gcv` (RN:3360-3361). `in_hwcap` is an *input* (ST ProcInput field, §3.8).

### 2.3 `CacheWords`, `cache_words_zero` (SL:120-132)
```coq
Record CacheWords := mkCacheWords {
  cw_l1i_size : word;  cw_l1i_geom : word;
  cw_l1d_size : word;  cw_l1d_geom : word;
  cw_l2_size  : word;  cw_l2_geom  : word;
  cw_l3_size  : word;  cw_l3_geom  : word
}.
Definition cache_words_zero : CacheWords :=
  let z := Z_to_bv 64 0 in mkCacheWords z z z z z z z z.
```
(field layout was reconstructed from SL:120-129; the 8 fields in this exact order: l1i_size, l1i_geom, l1d_size, l1d_geom, l2_size, l2_geom, l3_size, l3_geom — confirmed by `launch_cache_words` argument order, RN:940-947.)

### 2.4 `LaunchAuxv` (SL:156-161)
```coq
Record LaunchAuxv := mkLaunchAuxv {
  la_sysinfo_ehdr : word;
  la_cache        : CacheWords;
  la_minsigstksz  : word;
  la_rseq         : bool
}.
```

### 2.5 `auxv_entries` (SL:228-261) — EXACT order, tags, value expressions
```coq
Definition auxv_entries (la : LaunchAuxv) (ph : PhdrInfo) (entry : word)
    (uid gid hwcap at_random at_execfn : word) : list (word * word) :=
  let c := la_cache la in
  [ (AT_SYSINFO_EHDR,      la_sysinfo_ehdr la);
    (AT_L1I_CACHESIZE,     cw_l1i_size c);
    (AT_L1I_CACHEGEOMETRY, cw_l1i_geom c);
    (AT_L1D_CACHESIZE,     cw_l1d_size c);
    (AT_L1D_CACHEGEOMETRY, cw_l1d_geom c);
    (AT_L2_CACHESIZE,      cw_l2_size c);
    (AT_L2_CACHEGEOMETRY,  cw_l2_geom c);
    (AT_L3_CACHESIZE,      cw_l3_size c);
    (AT_L3_CACHEGEOMETRY,  cw_l3_geom c);
    (AT_MINSIGSTKSZ,       la_minsigstksz la);
    (AT_HWCAP,  hwcap);
    (AT_PAGESZ, Z_to_bv 64 4096);
    (AT_CLKTCK, Z_to_bv 64 100);
    (AT_PHDR,   Z_to_bv 64 (Z.of_N (ph_addr ph)));
    (AT_PHENT,  Z_to_bv 64 (Z.of_N (ph_ent ph)));
    (AT_PHNUM,  Z_to_bv 64 (Z.of_N (ph_num ph)));
    (AT_BASE,   Z_to_bv 64 0);
    (AT_FLAGS,  Z_to_bv 64 0);
    (AT_ENTRY,  entry);
    (AT_UID,    uid);
    (AT_EUID,   uid);
    (AT_GID,    gid);
    (AT_EGID,   gid);
    (AT_SECURE, Z_to_bv 64 0);
    (AT_RANDOM, at_random);
    (AT_EXECFN, at_execfn) ]
  ++ (if la_rseq la
      then [ (AT_RSEQ_FEATURE_SIZE, Z_to_bv 64 28);
             (AT_RSEQ_ALIGN,        Z_to_bv 64 32) ]
      else [])
  ++ [ (AT_NULL, Z_to_bv 64 0) ].
```
Python (index: (tag, value)):
```
 0 (33 SYSINFO_EHDR, vdso_text_base)
 1 (40, l1i_size)   2 (41, l1i_geom)   3 (42, l1d_size)   4 (43, l1d_geom)
 5 (44, l2_size)    6 (45, l2_geom)    7 (46, l3_size)    8 (47, l3_geom)
 9 (51 MINSIGSTKSZ, min_sigframe_size)
10 (16 HWCAP, hwcap)         11 (6 PAGESZ, 4096)        12 (17 CLKTCK, 100)
13 (3 PHDR, ph_addr)         14 (4 PHENT, ph_ent)       15 (5 PHNUM, ph_num)
16 (7 BASE, 0)               17 (8 FLAGS, 0)            18 (9 ENTRY, entry)
19 (11 UID, uid) 20 (12 EUID, uid) 21 (13 GID, gid) 22 (14 EGID, gid)
23 (23 SECURE, 0)            24 (25 RANDOM, at_random_ptr)   25 (31 EXECFN, at_execfn_ptr)
[if rseq: 26 (27, 28)  27 (28, 32)]
last: (0 NULL, 0)           # index 26 without rseq, index 28 with rseq
```
Total 27 entries without RSEQ, 29 with. `entry` = initial pc (in `init_machine_state`: `Z_to_bv 64 (Z.of_N mi_init_pc)`, RN:~1040; = ELF e_entry, ET_EXEC static). `uid`,`gid` = `in_uid`,`in_gid`; `hwcap`=`in_hwcap`. AT_BASE=0, AT_FLAGS=0, AT_SECURE=0 literal. The AT_RANDOM value = *address* of the 16 bytes (§2.9); AT_EXECFN value = *address* of exec name (§2.8). Note: no AT_PLATFORM, no AT_HWCAP2, and order has ARCH_DLINFO (10 entries) first.

### 2.6 `build_auxv`, `auxv_bytes` (SL:264-269)
```coq
Definition build_auxv (entries : list (word * word)) : list byte :=
  flat_map (fun e => word_le8 (fst e) ++ word_le8 (snd e)) entries.
Definition auxv_bytes (la) (ph) (entry) (uid gid hwcap at_random at_execfn : word) : list byte :=
  build_auxv (auxv_entries la ph entry uid gid hwcap at_random at_execfn).
```
Python: `b''.join(le8(tag)+le8(val) for tag,val in entries)` — 16 bytes per entry, tag first.

### 2.7 `auxv_count`, `auxv_size` (SL:275-276)
```coq
Definition auxv_count (rseq : bool) : nat := if rseq then 29%nat else 27%nat.
Definition auxv_size (rseq : bool) : nat := (16 * auxv_count rseq)%nat.
```
Python: `auxv_count = 29 if rseq else 27`; `auxv_size = 16*auxv_count` (= 464 / 432). (Lemma `length_auxv_bytes`, SL:278-280, proves `len(auxv_bytes)=auxv_size(la_rseq)`.)

### 2.8 `EntryDraw` (SL:333-337)
```coq
Record EntryDraw := mkDraw {
  ed_random : bv 128;
  ed_top    : word;
  ed_vdso   : nat -> list word -> list byte -> word -> (list word * list byte)
}.
```
`ed_random` = the 16 AT_RANDOM bytes (§1.3). `ed_top` = the stack VMA's `vm_end` (top of the block; page-aligned; every byte from `sp` to `ed_top` is laid out). `ed_vdso` = a vDSO-call choice, NOT read by the start-state bytes. (`ed_slack` no longer exists.)
Python: `top = ed_top` ; `draw_random = ed_random`.

### 2.9 Block measurements (SL:363-364, 377-379, 384-387)
```coq
Definition block_items (argv envp : list (list byte)) : nat :=
  (length argv + length envp + 3)%nat.

Definition block_head_size (rseq : bool) (argv envp : list (list byte)) : nat :=
  let items := block_items argv envp in
  (8 * items + auxv_size rseq + 8 * (items mod 2) + 16)%nat.

Definition launch_string_bytes (argv envp : list (list byte))
    (execfn : list byte) : nat :=
  (length (flatten_strings argv) + length (flatten_strings envp)
   + length execfn + 1)%nat.
```
Python:
```
items = len(argv)+len(envp)+3
C = 8*items + 16*auxv_count(rseq) + 8*(items%2) + 16        # block_head_size
L = sum(len(s)+1 for s in argv) + sum(len(s)+1 for s in envp) + len(execfn) + 1   # launch_string_bytes
```
(`length (flatten_strings x) = sum(len(s)+1)`.)

### 2.10 Address functions (SL:392-394, 399-400, 403-405)
```coq
(* lowest string byte = argv[0] *)
Definition string_base_addr (top : word) (argv envp : list (list byte))
    (execfn : list byte) : word :=
  top - nat_to_word (8 + launch_string_bytes argv envp execfn).

(* AT_EXECFN *)
Definition at_execfn_ptr (top : word) (execfn : list byte) : word :=
  top - nat_to_word (8 + length execfn + 1).

(* AT_RANDOM: bottom of the sixteen bytes *)
Definition at_random_ptr (sp : word) (rseq : bool)
    (argv envp : list (list byte)) : word :=
  sp + nat_to_word (block_head_size rseq argv envp - 16).
```
Python:
```
addr_argv0   = top - (8 + L)                       # string_base_addr; = &argv[0][0]
addr_argv[k] = addr_argv0 + sum(len(argv[j])+1 for j<k)           # string_addrs
addr_envp[k] = addr_argv0 + sum(len(a)+1 for a in argv) + sum(len(envp[j])+1 for j<k)
addr_execfn  = top - (8 + len(execfn) + 1)         # at_execfn_ptr  (= addr_argv0 + sum_argv + sum_envp)
addr_random  = sp + C - 16                         # at_random_ptr
```
Consistency: `top - (8+L) + sum_argv + sum_envp = top - 8 - len(execfn) - 1` ✓. (`C-16` is nat subtraction; C≥16 always.)

### 2.11 `block_pad_len` (SL:417-422)
```coq
Definition block_pad_len (rseq : bool) (sp top : word)
    (argv envp : list (list byte)) (execfn : list byte) : nat :=
  Z.to_nat (bv_unsigned top - 8
            - Z.of_nat (launch_string_bytes argv envp execfn)
            - bv_unsigned sp
            - Z.of_nat (block_head_size rseq argv envp)).
```
Python: `pad = max(0, top - 8 - L - sp - C)`. Under `entry_launch_ok_va` it is in [0,4095] and the image length is exactly `top - sp`. (Lines 417-422 verbatim: the final subtract line was read as `- Z.of_nat (block_head_size rseq argv envp))` at SL:~421; the tool's display elided that one line — it is certain from `length_build_stack_bytes` SL:501-505 which sums `block_head_size + block_pad_len + launch_string_bytes + 8`.)

### 2.12 `build_stack_bytes` (SL:451-471) — THE layout
```coq
Definition build_stack_bytes (la : LaunchAuxv) (ph : PhdrInfo) (entry : word)
    (sp top : word) (argv envp : list (list byte)) (execfn : list byte)
    (uid gid hwcap : word) (draw : EntryDraw) : list byte :=
  let items := block_items argv envp in
  let sbase := string_base_addr top argv envp execfn in
  let '(argv_ptrs, env_str_base) := string_addrs sbase argv in
  let '(envp_ptrs, _) := string_addrs env_str_base envp in
  let auxv :=
    auxv_bytes la ph entry uid gid hwcap
      (at_random_ptr sp (la_rseq la) argv envp)
      (at_execfn_ptr top execfn) in
  let head :=
    word_le8 (len_word argv)
    ++ flat_map word_le8 argv_ptrs
    ++ word_le8 (Z_to_bv 64 0)
    ++ flat_map word_le8 envp_ptrs
    ++ word_le8 (Z_to_bv 64 0)
    ++ auxv
    ++ repeat (Z_to_bv 8 0) (8 * (items mod 2))
    ++ at_random_bytes (ed_random draw) in
  let strs :=
    flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] in
  let pad := block_pad_len (la_rseq la) sp top argv envp execfn in
  head ++ repeat (Z_to_bv 8 0) pad ++ strs ++ repeat (Z_to_bv 8 0) 8.
```
Python (the image occupies memory addresses `[sp, top)` when pad is in range, byte 0 at `sp`):
```
img = le8(len(argv))                                   # argc @ sp+0
    + b''.join(le8(p) for p in argv_ptrs) + le8(0)      # argv[0..argc-1], NULL
    + b''.join(le8(p) for p in envp_ptrs) + le8(0)      # envp[..], NULL
    + auxv_bytes(...)                                   # at sp + 8*items; 16*n_aux bytes
    + b'\0' * (8*(items%2))                             # zero gap -> random 16-aligned
    + at_random_bytes(rnd)                              # 16 bytes @ sp + C - 16
    + b'\0' * pad                                       # arch_align_stack pad, zeros
    + flat(argv) + flat(envp) + execfn + b'\0'          # string area; argv[0] first (lowest)
    + b'\0' * 8                                         # slot create_init_stack_vma skipped
```
Offsets from `sp`: argc 0; argv ptrs 8..8+8*argc; NULL; envp ptrs; NULL (end of those = 8*items); auxv `[8*items, 8*items+16*n_aux)`; gap 0|8; AT_RANDOM `[C-16, C)`; pad `[C, C+pad)`; strings from `C+pad` (== top-8-L-sp); the exec name is the last string before the trailing NUL, then 8 zero bytes ending at `top`. Strings order low→high: argv strings, envp strings, execfn. Pads/gaps/slot are all ZERO. The auxv holds *addresses* computed from `top` and `sp` (§2.10); `sbase` for pointers uses `top`, not `sp`. Total length (lemma SL:501-505) `= C + pad + L + 8`.
Only `ed_random` of the draw is read (SL:564-577 `build_stack_bytes_split_random`).

### 2.13 `stack_to_mem` (SL:583-591)
```coq
Definition stack_to_mem (base : word) (bytes : list byte) : word -> option byte :=
  fun addr =>
    if Z.leb (bv_unsigned base) (bv_unsigned addr) then
      let off := (bv_unsigned addr - bv_unsigned base)%Z in
      if Z.ltb off (Z.of_nat (length bytes)) then nth_error bytes (Z.to_nat off) else None
    else None.
```
Python: `mem(addr) = img[addr-sp] if sp <= addr < sp+len(img) else None`.

---

## 3. State.v definitions

### 3.1 `page_size`, rounding, window constants
```coq
Definition page_size : Z := 4096%Z.                                    (* ST:34 *)
Definition page_round_up_Z (n : Z) : Z := ((n + page_size - 1) / page_size * page_size)%Z.   (* ST:39-40 *)
Definition page_round_down_Z (n : Z) : Z := (n / page_size * page_size)%Z.                    (* ST:41-42 *)
Definition stack_max_size : Z := (8 * 1024 * 1024)%Z.                  (* ST:128 *)
Definition sp_window_lo : Z := 0x7fff80000000%Z.                       (* ST:160 *)
Definition sp_window_hi : Z := 0x800000000000%Z.                       (* ST:161 *)
Definition mmap_base_min : Z := 0x154555557000%Z.                      (* ST:320 *)
Definition TASK_SIZE : Z := 0x800000000000%Z.                          (* ST:~437 (after comment block ST:339-436) *)
```
Python: `PAGE=4096`; `SP_WINDOW_HI=0x800000000000`; `STACK_MAX=8<<20`.

### 3.2 `VaSize`, `va_stack_top` etc. (ST:472, 483-501, 503-510)
```coq
Inductive VaSize := Sv39 | Sv48 | Sv57.                                   (* ST:472 *)
Definition sv39_task_size : Z := 0x4000000000%Z.                          (* ST:476-477 region; value 2^38 *)
Definition sv57_task_size : Z := 0x100000000000000%Z.                     (* 2^56 *)
Definition va_task_size (v : VaSize) : Z := match v with Sv39 => sv39_task_size | Sv48 => TASK_SIZE | Sv57 => sv57_task_size end.   (* ST:483-488 *)
Definition va_stack_top (v : VaSize) : Z :=                               (* ST:492-497 *)
  match v with
  | Sv39 => sv39_task_size
  | Sv48 => sp_window_hi
  | Sv57 => sp_window_hi
  end.
Definition va_sp_window_hi (v : VaSize) : Z := va_stack_top v.            (* ST:499 *)
Definition va_sp_window_lo (v : VaSize) : Z := (va_stack_top v - 2 * 1024 * 1024 * 1024)%Z.   (* ST:500-501 *)
Definition va_mmap_base_max (v : VaSize) : Z := (va_stack_top v - 128 * 1024 * 1024)%Z.        (* ST:503-504 *)
Definition va_mmap_base_min (v : VaSize) : Z := match v with Sv39 => 0%Z | Sv48 => mmap_base_min | Sv57 => mmap_base_min end.  (* ST:505-510 *)
```
Python: `va_stack_top = {Sv39:2**38, Sv48:0x800000000000, Sv57:0x800000000000}`. For the Linux v6.18.46 rv64 run in question, Sv48 or Sv57 boot ⇒ `va_stack_top = 0x800000000000 = 2**47`. NOTE: `in_va_size` is pinned to `Sv48` by `valid_input`; `entry_launch_ok_va` takes the VaSize `v` explicitly. QEMU `virt` boots Sv57 by default (ST comment ~ST:395-405) — stack top is identical for Sv48/Sv57 (2^47) but `kb_rnd_bits` max is 33 for both.

### 3.3 `CacheLeaf` (ST:3072-3077), `CacheView` (ST:3083-3088), absents
```coq
Record CacheLeaf := mkCacheLeaf {
  cl_acpi  : bool;
  cl_size  : N;
  cl_assoc : N;
  cl_line  : N
}.
Definition cache_leaf_absent : CacheLeaf := mkCacheLeaf false 0%N 0%N 0%N.    (* ST:3079 *)
Record CacheView := mkCacheView {
  cv_l1i : CacheLeaf;  cv_l1d : CacheLeaf;  cv_l2 : CacheLeaf;  cv_l3 : CacheLeaf
}.
Definition cache_view_absent : CacheView := mkCacheView cache_leaf_absent cache_leaf_absent cache_leaf_absent cache_leaf_absent.   (* ST:3090-3092 *)
```
Meaning: `cl_acpi` picks firmware path. Devicetree: `cl_assoc` = NUMBER OF SETS. ACPI: `cl_assoc` = PPTT 8-bit associativity. `cl_size` = bytes. `cl_line` = line size. Order L1I, L1D, L2, L3 (= auxv order 40..47).

### 3.4 Cache helpers (ST:3103-3115, 3122-3126)
```coq
Definition cache_ways (l : CacheLeaf) : N :=
  if cl_acpi l then (cl_assoc l mod 2 ^ 8)%N
  else if andb (negb (N.eqb (cl_assoc l) 1))
               (andb (negb (N.eqb (cl_assoc l) 0))
                     (andb (negb (N.eqb (cl_size l) 0))
                           (negb (N.eqb (cl_line l) 0))))
       then ((cl_size l / cl_assoc l) / cl_line l)%N
       else 0%N.
Definition cache_line (l : CacheLeaf) : N :=
  if cl_acpi l then (cl_line l mod 2 ^ 16)%N else cl_line l.
Definition cache_size_word (l : CacheLeaf) : Z :=
  (Z.of_N (cl_size l) mod 2 ^ 32)%Z.
Definition cache_geometry_word (l : CacheLeaf) : Z :=
  (Z.lor (Z.of_N (cache_ways l) * 2 ^ 16) (Z.of_N (cache_line l))
   mod 2 ^ 32)%Z.
```
Python:
```
def cache_ways(l): 
    if l.acpi: return l.assoc % 256
    if l.assoc not in (0,1) and l.size != 0 and l.line != 0: return (l.size // l.assoc) // l.line
    return 0
def cache_line(l): return l.line % 65536 if l.acpi else l.line
cache_size_word(l)     = l.size % 2**32
cache_geometry_word(l) = ((cache_ways(l) * 2**16) | cache_line(l)) % 2**32
```
(N division: floor; `x/0=0` in Rocq but guarded here by assoc≠0.) Note `ways*2^16 | line` is evaluated before the `mod 2^32` (the `mod` binds to the `Z.lor` result).

### 3.5 `launch_cache_words` (RN:940-947) — mapping CacheView → auxv words
```coq
Definition launch_cache_words (kb : KernelBuild) : CacheWords :=
  let w := fun l => Z_to_bv 64 (cache_size_word l) in
  let g := fun l => Z_to_bv 64 (cache_geometry_word l) in
  let c := kb_cache kb in
  mkCacheWords (w (cv_l1i c)) (g (cv_l1i c))
               (w (cv_l1d c)) (g (cv_l1d c))
               (w (cv_l2 c))  (g (cv_l2 c))
               (w (cv_l3 c))  (g (cv_l3 c)).
```
Python: auxv[1..8] = `[size_word(l1i), geom_word(l1i), size_word(l1d), geom_word(l1d), size_word(l2), geom_word(l2), size_word(l3), geom_word(l3)]`.

### 3.6 `KernelBuild` (ST:3148-3197) — all fields
```coq
Record KernelBuild := mkKernelBuild {
  kb_thp : bool;        (* CONFIG_TRANSPARENT_HUGEPAGE; mmap only, not in start-state bytes *)
  kb_vdso : N;          (* which vDSO image; only used for SIZE via vdso_text_pages *)
  kb_aslr : bool;       (* PF_RANDOMIZE: launch randomizes stack top / mmap base / mmap gap pad *)
  kb_guard : N;         (* stack_guard_gap boot param, in PAGES (default 256) *)
  kb_rnd_bits : N;      (* vm.mmap_rnd_bits, wrapped by mmap_rnd_bits *)
  kb_rseq : bool;       (* CONFIG_RSEQ: 29 vs 27 auxv entries *)
  kb_vlenb : N;         (* VLENB CSR; feeds AT_MINSIGSTKSZ through launch_vlenb *)
  kb_cache : CacheView  (* four cache leaves -> eight auxv words *)
}.
```
Constructor argument order: `kb_thp kb_vdso kb_aslr kb_guard kb_rnd_bits kb_rseq kb_vlenb kb_cache`.
```coq
Definition default_kernel : KernelBuild :=
  mkKernelBuild false 1%N true 256%N 0%N true 0%N cache_view_absent.      (* ST:3268-3269 *)
```

### 3.7 Decoders of `kb_*` fields
```coq
Definition vdso_vvar_pages : Z := 4.                                       (* ST:3203 *)
Definition vdso_text_pages (kb : KernelBuild) : Z := (1 + Z.of_N (kb_vdso kb) mod 16)%Z.   (* ST:3217-3218 *)
Definition vdso_len (kb : KernelBuild) : Z := ((vdso_vvar_pages + vdso_text_pages kb) * page_size)%Z.   (* ST:3233-3234 *)

Definition stack_guard_gap_pages (kb : KernelBuild) : Z := Z.of_N (kb_guard kb mod 0x4aba6a2ac).   (* ST:3283-3284 *)
Definition stack_guard_gap_bytes (kb : KernelBuild) : Z := (page_size * stack_guard_gap_pages kb)%Z. (* ST:3285-3286 *)

Definition mmap_rnd_bits_max (v : VaSize) : Z := match v with Sv39 => 24%Z | Sv48 => 33%Z | Sv57 => 33%Z end.  (* ST:3316-3317 *)
Definition mmap_rnd_bits (v : VaSize) (kb : KernelBuild) : Z :=
  (18 + Z.of_N (kb_rnd_bits kb mod Z.to_N (mmap_rnd_bits_max v - 17)))%Z.                                    (* ST:3318-3319 *)

Definition hwcap_has_v (h : word) : bool := Z.testbit (bv_unsigned h) 21.                                    (* ST: just above launch_vlenb, ~3357 *)
Definition launch_vlenb (kb : KernelBuild) (hwcap : word) : Z :=
  if hwcap_has_v hwcap then (16 * 2 ^ Z.of_N (kb_vlenb kb mod 10))%Z
  else if N.eqb (kb_vlenb kb) 0 then 0%Z
  else (1 + Z.of_N ((kb_vlenb kb - 1) mod (2 ^ 32 - 1)))%Z.                                                  (* ST:3359-3362 *)

Definition rt_sigframe_size : Z := 1088%Z.                                                                    (* ST: just above min_sigframe_size, ~3386 *)
Definition min_sigframe_size (kb : KernelBuild) (hwcap : word) : Z :=
  let v := launch_vlenb kb hwcap in
  let vsz := if Z.eqb v 0 then 0%Z else (8 + 48 + 32 * v)%Z in
  ((rt_sigframe_size + vsz + 15) / 16 * 16)%Z.                                                                (* ST:3388-3391 *)
```
(`rt_sigframe_size` and `hwcap_has_v` line numbers are approximate: both definitions are immediately adjacent to the cited ones in the ST:3330-3390 block I read; their bodies are verbatim.)
Python:
```
vdso_text_pages = 1 + kb_vdso % 16              # 1..16 ; default kb_vdso=1 -> 2
vdso_len        = (4 + vdso_text_pages) * 4096
guard_pages     = kb_guard % 0x4aba6a2ac ; guard_bytes = 4096*guard_pages          # default 256 pages = 1 MiB
rnd_bits(v)     = 18 + kb_rnd_bits % (max_bits(v) - 17)    # Sv48/Sv57: max 33 -> modulus 16 ; Sv39: max 24 -> modulus 7
hwcap_has_v(h)  = (h >> 21) & 1
def launch_vlenb(kb, hwcap):
    if hwcap_has_v(hwcap): return 16 * 2**(kb_vlenb % 10)
    if kb_vlenb == 0: return 0
    return 1 + (kb_vlenb - 1) % (2**32 - 1)
def min_sigframe_size(kb, hwcap):
    v = launch_vlenb(kb, hwcap); vsz = 0 if v == 0 else 8 + 48 + 32*v
    return (1088 + vsz + 15) // 16 * 16        # AT_MINSIGSTKSZ
```
Examples: no vector → `(1088+15)//16*16 = 1088`. vlenb=32 (with V or not): `vsz=8+48+1024=1080`, → `(1088+1080+15)//16*16 = 2176`. (`kb_vlenb` encoding: with V bit set in hwcap, `kb_vlenb = k` ⇒ vlenb = 16*2^(k mod 10); without V bit, `kb_vlenb = 0` ⇒ none, else `kb_vlenb = vlenb` for 1 ≤ vlenb ≤ 2^32-1.) **`rnd_bits` cannot encode a value > 33; `kb_guard` encodes pages directly (mod); `kb_vdso` encodes (pages − 1) mod 16.**

### 3.8 `vdso_text_base` and `launch_auxv` (RN:949-957)
```coq
Definition vdso_text_base (kb : KernelBuild) (mbase : word) : word :=
  Z_to_bv 64 (bv_unsigned mbase - vdso_text_pages kb * page_size).

Definition launch_auxv (inp : ProcInput) (mbase : word) : LaunchAuxv :=
  let kb := in_kernel inp in
  mkLaunchAuxv (vdso_text_base kb mbase)
               (launch_cache_words kb)
               (Z_to_bv 64 (min_sigframe_size kb (in_hwcap inp)))
               (kb_rseq kb).
```
Python: `AT_SYSINFO_EHDR = (mbase - vdso_text_pages*4096) mod 2**64` (**the vDSO text starts `text_pages` pages below `mmap_base`; vvar (4 pages) is below the text**: `vdso_reserved kb top` ST:5001-5007 gives vvar `[top-vdso_len, top-vdso_len+4*4096)`, text `[top-text_pages*4096, top)` with `top = page_round_down(mmap_top)`-ish; for the launch `top = mbase`); `AT_MINSIGSTKSZ = min_sigframe_size(kb,hwcap)`; `la_rseq = kb_rseq`.

### 3.9 `ProcInput` (ST:5734-~5873) — fields in order
```coq
Record ProcInput := mkProcInput_full {
  in_argv  : list (list byte);
  in_envp  : list (list byte);
  in_image_fs : Fs.Fs;
  in_stdin : InputStream;
  in_uid   : word;
  in_gid   : word;
  in_groups : list word;
  in_net   : NetQueue;
  in_nofile : word;
  in_sigmask : word;
  in_hwcap : word;                 (* AT_HWCAP *)
  in_abort_terminal : bool;
  in_va_size : VaSize;             (* pinned Sv48 by valid_input *)
  in_urandom : InputStream;
  in_tmp   : Fs.Fs;
  in_kernel : KernelBuild;
  in_execfn : list byte            (* bprm->filename WITHOUT NUL; default "a" = [97] *)
}.
```
Start-state-relevant: `in_argv`, `in_envp` (lists of byte lists, NULs not included), `in_uid`, `in_gid`, `in_hwcap`, `in_kernel`, `in_execfn`, `in_va_size`. `default_execfn := [Z_to_bv 8 97]` (ST:~3395). `mkProcInput` (ST:5923-5927) fills defaults `default_kernel`, `default_execfn`.

---

## 4. Run.v definitions

### 4.1 `PhdrInfo` (MemImageType.v:64-68)
```coq
Record PhdrInfo := mkPhdrInfo {
  ph_addr : N;   (** AT_PHDR  — run-time address of the phdr table *)
  ph_ent  : N;   (** AT_PHENT — e_phentsize (56 on ELF64) *)
  ph_num  : N    (** AT_PHNUM — e_phnum *)
}.
```

### 4.2 `ExecEntry` (RN:1095-1100)
```coq
Record ExecEntry := mkEntry {
  en_sp        : word;
  en_brk       : word;
  en_mmap_base : word;
  en_draw      : EntryDraw
}.
```
Python: `sp = en_sp` (initial sp register, x2), `mbase = en_mmap_base`, `top = en_draw.ed_top`, `brk = en_brk`.

### 4.3 `align_down16`, `stack_rnd_max` (RN:2904, ~2907-2909)
```coq
Definition align_down16 (x : Z) : Z := (x - x mod 16)%Z.
Definition stack_rnd_max : Z := 0x3ffff000%Z.
```
Python: `align_down16(x) = x & ~15`; `STACK_RND_MAX=0x3ffff000`.

### 4.4 Rule 1 — `valid_stack_top_va` (RN:2939-2945)
```coq
Definition valid_stack_top_va (v : VaSize) (aslr : bool) (top : word) : Prop :=
  (bv_unsigned top mod page_size = 0)%Z
  /\ (bv_unsigned top <= va_stack_top v)%Z
  /\ (va_stack_top v
      - (if aslr then stack_rnd_max + page_size else page_size)
      <= bv_unsigned top)%Z.
```
Python: `top % 4096 == 0 and top <= STACK_TOP and STACK_TOP - ((0x3ffff000 + 4096) if aslr else 4096) <= top`, with `STACK_TOP=0x800000000000` (Sv48/Sv57), `aslr = kb_aslr`. I.e. `top ∈ [STACK_TOP-0x40000000, STACK_TOP]` page aligned (aslr), or `[STACK_TOP-4096, STACK_TOP]` (no aslr). `ed_top` ⇒ `top`.

### 4.5 Rule 2 — `launch_sp_hi/lo`, `valid_launch_sp` (RN:2970-2987)
```coq
Definition launch_sp_hi (top : word) (inp : ProcInput) : Z :=
  (align_down16 (bv_unsigned top - 8
                 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                                 (in_execfn inp)))
   - Z.of_nat (block_head_size (kb_rseq (in_kernel inp))
                               (in_argv inp) (in_envp inp)))%Z.

Definition launch_sp_lo (top : word) (inp : ProcInput) : Z :=
  (align_down16 (bv_unsigned top - 8
                 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                                 (in_execfn inp))
                 - 4095)
   - Z.of_nat (block_head_size (kb_rseq (in_kernel inp))
                               (in_argv inp) (in_envp inp)))%Z.

Definition valid_launch_sp (top : word) (inp : ProcInput) (sp : word) : Prop :=
  (bv_unsigned sp mod 16 = 0)%Z
  /\ (launch_sp_lo top inp <= bv_unsigned sp <= launch_sp_hi top inp)%Z.
```
Python:
```
sp_hi = align_down16(top - 8 - L) - C
sp_lo = align_down16(top - 8 - L - 4095) - C
valid_launch_sp: sp % 16 == 0 and sp_lo <= sp <= sp_hi
```
with `L = launch_string_bytes(argv,envp,execfn)`, `C = block_head_size(kb_rseq, argv, envp)`. Equivalent: `sp = align_down16(top-8-L-r) - C`, r∈[0,4095]. Then `pad = top-8-L-sp-C ∈ [0,4095]` (pad = `(top-8-L) mod 16 + 16*m`, i.e. up to 4095+15…; exact pad range is what the sp window induces: `pad = (top-8-L) - align_down16(top-8-L-r)`).

### 4.6 Rule 3 — `valid_launch_base` (RN:2995-3041)
```coq
Definition mmap_min_gap : Z := (128 * 1024 * 1024)%Z.
Definition mmap_max_gap (v : VaSize) : Z := (va_stack_top v / 6 * 5)%Z.

Definition mmap_gap (v : VaSize) (kb : KernelBuild) : Z :=
  let rlim := stack_max_size in
  let pad := (stack_guard_gap_bytes kb
              + if kb_aslr kb then stack_rnd_max else 0)%Z in
  let g := if ((rlim + pad) mod two_pow_64 >? rlim)%Z then (rlim + pad)%Z
           else rlim in
  if andb (g <? mmap_min_gap)%Z (mmap_min_gap <? mmap_max_gap v)%Z
  then mmap_min_gap
  else if (g >? mmap_max_gap v)%Z then mmap_max_gap v else g.

Definition mmap_base_of (v : VaSize) (kb : KernelBuild) (rnd : Z) : Z :=
  page_round_up_Z (va_stack_top v - mmap_gap v kb - rnd).

Definition valid_launch_base (v : VaSize) (kb : KernelBuild) (mbase : word) : Prop :=
  exists r : Z,
    (0 <= r)%Z
    /\ (kb_aslr kb = true -> r < 2 ^ mmap_rnd_bits v kb)%Z
    /\ (kb_aslr kb = false -> r = 0%Z)
    /\ bv_unsigned mbase = mmap_base_of v kb (page_size * r).
```
Python:
```
MIN_GAP = 128<<20 ; MAX_GAP(v) = va_stack_top(v)//6*5
pad = guard_bytes + (0x3ffff000 if aslr else 0)
g = rlim+pad if ((rlim+pad) % 2**64) > rlim else rlim ; rlim = 8<<20
if g < MIN_GAP and MIN_GAP < MAX_GAP: gap = MIN_GAP
elif g > MAX_GAP: gap = MAX_GAP
else: gap = g
mmap_base_of(rnd) = page_round_up(STACK_TOP - gap - rnd)
valid_launch_base: exists r>=0 with (aslr => r < 2**mmap_rnd_bits(v,kb)), (not aslr => r == 0), mbase == mmap_base_of(4096*r)
```
Default kernel (Sv48, aslr, guard 256 pages=0x100000, rnd_bits 18): `pad=0x100000+0x3ffff000=0x400ff000`; `g=0x800000+0x400ff000=0x408ff000` (> MIN_GAP, < MAX_GAP) ⇒ `mbase = page_round_up(0x800000000000 - 0x408ff000 - 4096*r) = 0x7fffbf701000 - 4096*r`, `r<2**18`. (Line numbers: header comment RN:2989-3028; the three defs `mmap_min_gap`..`valid_launch_base` precede RN:3030; `valid_launch_base` itself is RN:3030-3037.) The vDSO text (and so `AT_SYSINFO_EHDR`) lies directly below `mbase` per §3.8.

### 4.7 `entry_launch_ok_va` (RN:3052-3060)
```coq
Definition entry_launch_ok_va (v : VaSize) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match en with
  | mkEntry sp _ mbase draw =>
    valid_stack_top_va v (kb_aslr (in_kernel inp)) (ed_top draw)
    /\ valid_launch_sp (ed_top draw) inp sp
    /\ valid_launch_base v (in_kernel inp) mbase
  end.
```
Python: `valid_stack_top_va(v, kb_aslr, top) and valid_launch_sp(top, inp, sp) and valid_launch_base(v, kb, mbase)`. It is the fifth conjunct of `valid_entry_va` (RN:~3062-3068), which also asserts `valid_sp_va`, `valid_brk`, `valid_mmap_base_va`, `entry_stack_fits_va`:
```coq
Definition valid_sp_va v sp := (va_sp_window_lo v <= sp)%Z /\ (sp <= va_sp_window_hi v)%Z /\ (sp mod 16 = 0)%Z.            (* RN:2502-2505 *)
Definition valid_mmap_base_va v mbase := (va_mmap_base_min v <= mbase)%Z /\ (mbase <= va_mmap_base_max v)%Z /\ (mbase mod page_size = 0)%Z.  (* RN:2507-2510 *)
```

### 4.8 `entry_stack_image` (RN:977-980)
```coq
Definition entry_stack_image (inp : ProcInput) (mbase : word)
    (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw) : list byte :=
  build_stack_bytes (launch_auxv inp mbase) ph entry sp (ed_top draw)
    (in_argv inp) (in_envp inp) (in_execfn inp)
    (in_uid inp) (in_gid inp) (in_hwcap inp) draw.
```
Python: `entry_stack_image = build_stack_bytes(launch_auxv(inp, mbase), ph, entry_pc, sp, top, argv, envp, execfn, uid, gid, hwcap, draw)`. The mapped stack memory in `init_machine_state` (RN:~1030-1062): bytes of the image at `[sp, sp+len)`; otherwise a zero byte for `stack_window_lo <= addr < sp`; else unmapped.
```coq
Definition stack_window_lo (kb : KernelBuild) (mbase : word) (draw : EntryDraw) : Z :=
  Z.max (bv_unsigned (ed_top draw) - stack_max_size)
        (bv_unsigned mbase + stack_guard_gap_bytes kb).            (* RN:1012-1015 *)
```
Python: `stack_window_lo = max(top - 8*MiB, mbase + guard_bytes)`. Initial regs: sp = `en_sp`, a0 = 0, all else 0; pc = `e_entry`; fcsr = 0.

### 4.9 `valid_launch` (RN:2710-2715), `valid_execfn` (RN:2670-2680), `e2big_limit` (RN:2708)
```coq
Definition e2big_limit : Z := 2097152%Z.
Definition launch_bytes (inp : ProcInput) : Z :=
  (Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))
   + 8 * (Z.of_nat (length (in_argv inp)) + Z.of_nat (length (in_envp inp))))%Z.
Definition valid_launch (inp : ProcInput) : Prop :=
  valid_execfn (in_execfn inp) /\ (launch_bytes inp <= e2big_limit)%Z.
```
Python: `launch_bytes = L + 8*(argc+envc) <= 2097152` and `valid_execfn(execfn)`:
```coq
Definition valid_execfn (fn : list byte) : Prop :=
  valid_path_name fn
  \/ (exists ds, fn = dev_fd_prefix ++ ds /\ valid_fd_digits ds)
  \/ (exists ds rest, fn = dev_fd_prefix ++ ds ++ [path_byte] ++ rest
        /\ valid_fd_digits ds /\ valid_path_name rest /\ hd path_byte rest <> path_byte).
Definition valid_path_name (p : list byte) : Prop := (1 <= Z.of_nat (length p) <= 4095)%Z /\ ~ In (Z_to_bv 8 0) p.
```
(`dev_fd_prefix = "/dev/fd/"`, `path_byte = '/'`.) The execfn is `bprm->filename` as passed to execve (e.g. `./prog`), no NUL in the model.

---

## 5. Python transcription skeleton (derived directly from the above)

```python
def le8(v): return (v % 2**64).to_bytes(8,'little')
def flat(strs): return b''.join(s+b'\0' for s in strs)
def build(sp, top, argv, envp, execfn, uid, gid, hwcap, ph, entry, rnd16, kb, mbase):
    rseq = kb.rseq
    items = len(argv)+len(envp)+3
    n_aux = 29 if rseq else 27
    C = 8*items + 16*n_aux + 8*(items%2) + 16
    L = len(flat(argv)) + len(flat(envp)) + len(execfn) + 1
    sbase = top - (8 + L)
    argv_ptrs=[]; a=sbase
    for s in argv: argv_ptrs.append(a); a+=len(s)+1
    envp_ptrs=[]
    for s in envp: envp_ptrs.append(a); a+=len(s)+1
    at_random = sp + C - 16
    at_execfn = top - (8 + len(execfn) + 1)
    ents = [(33, mbase - vdso_text_pages(kb)*4096)] + cache_pairs(kb) + [(51, min_sigframe_size(kb,hwcap))] + \
           [(16,hwcap),(6,4096),(17,100),(3,ph.addr),(4,ph.ent),(5,ph.num),(7,0),(8,0),(9,entry),
            (11,uid),(12,uid),(13,gid),(14,gid),(23,0),(25,at_random),(31,at_execfn)] + \
           ([(27,28),(28,32)] if rseq else []) + [(0,0)]
    auxv = b''.join(le8(t)+le8(v) for t,v in ents)
    pad = max(0, top - 8 - L - sp - C)
    return (le8(len(argv)) + b''.join(le8(p) for p in argv_ptrs) + le8(0)
            + b''.join(le8(p) for p in envp_ptrs) + le8(0) + auxv
            + b'\0'*(8*(items%2)) + rnd16 + b'\0'*pad
            + flat(argv) + flat(envp) + execfn + b'\0' + b'\0'*8)
# image occupies [sp, top) when pad is in range.
```
where `cache_pairs(kb) = [(40,size(l1i)),(41,geom(l1i)),(42,size(l1d)),(43,geom(l1d)),(44,size(l2)),(45,geom(l2)),(46,size(l3)),(47,geom(l3))]`.

## 6. Where things live (quick index)
- Address of argv[0]: `string_base_addr` SL:392-394 (= first element of `string_addrs sbase argv`, SL:46-54).
- Address of AT_RANDOM bytes: `at_random_ptr` SL:403-405 (value of the AT_RANDOM auxv entry, SL:228-261; the 16 bytes sit at offset `C-16` in the image, SL:451-471).
- Address of exec file name: `at_execfn_ptr` SL:399-400 (value of AT_EXECFN auxv entry).
- Trailing 8-byte slot: last `repeat 0 8` in `build_stack_bytes`, SL:471 (`top-8 .. top`), skipped by `create_initstack_vma`; execfn NUL is at `top-9`.
- Kernel facts about each: SL:1-44 header, SL:134-155 (launch facts), RN:2939-3060 (rules).
- vDSO bytes: NOT IN MODEL (see §0.1).
