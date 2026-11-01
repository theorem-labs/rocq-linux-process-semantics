/* probe.c — the placement conformance probe.
 *
 * Asks a real Linux kernel to place mappings, and writes what it answered as
 * JSON lines.  tools/placement_conformance/log_to_rocq.py turns a log into a
 * Rocq replay that the LPS checker must accept, so the model's placement rule
 * (Sys/Mm/Mmap.linux_place) is read against the kernel, not against a reading
 * of the kernel's source.
 *
 * It runs as init (rdinit=/probe) in an initramfs on qemu-system-riscv64, and
 * also under qemu-riscv64 in user mode, where the answers are QEMU's and not
 * Linux's.  It is built static, non-PIE, for rv64g against musl 1.2.6, and it
 * makes every call with a raw ecall: no libc wrapper may add a flag, round a
 * length or retry, because the log is evidence about the kernel.  It allocates
 * nothing: every buffer is static, so no malloc of libc's can map a page this
 * log does not name.
 *
 * THE FIRST LINE is the launch: the whole of /proc/self/maps, the initial
 * stack pointer (field 28 of /proc/self/stat, mm->start_stack), the initial
 * break, the mmu the kernel runs, and /proc/sys/vm/mmap_min_addr — which shows
 * dac_mmap_min_addr only, not the effective minimum (Linux v6.18.46, commit
 * 1f99e9ab748f, security/min_addr.c, mmap_min_addr_handler).  The effective
 * minimum is read off the 0x8000 hint below instead.
 *
 * EVERY OTHER LINE is one call: {"sysno":222|215|216|214,"args":[…],"ret":…}.
 * Every number is the 64-bit register value as a SIGNED decimal, so a hint of
 * 2^64-1 reads -1 and an error return reads -12; log_to_rocq.py takes each
 * modulo 2^64.
 *
 * The sequence, in order:
 *   64 one-page PROT_NONE grants           they pack down from the vDSO pair
 *   a 2 MiB and an 8 MiB grant             PMD multiples: THP shows here
 *   munmap of a middle page, and of 4 MiB  two holes
 *   a grant of exactly the hole            the highest fit is the 4 KiB hole
 *   hints 1, 0x1001, 0x8000, 0x80000000,   round_hint_to_min, mmap_min_addr,
 *     an occupied address, 2^64-1            the hint that cannot fit
 *   MAP_FIXED_NOREPLACE over the vvar      -EEXIST
 *   three mremap grows                     blocked by the vDSO, room, no room
 *   two brk grows                          1 page and 1 MiB
 *
 * THE START-STATE MODE (acceptance item A4 of the start-state
 * specification).  With "pc_mode=startstate" on the boot
 * command line -- which the kernel hands to init in its environment (Linux
 * v6.18.46, commit 1f99e9ab748f, init/main.c, unknown_bootoption) -- the
 * probe makes no placement call at all.  As init it forks twice and execs
 * "a" (the same binary under a second name in the initramfs): once with argv
 * ["a"] and an empty environment, once with a long argv and a long envp.
 * Each child writes ONE launch line that holds, besides the five keys above,
 * the bytes of its own entry block, its auxiliary vector, the end of its
 * [stack] mapping, its own ELF header ("elf") and the facts that decide
 * them.  The parent then powers the machine off.
 * tools/placement_conformance/start_state_to_rocq.py turns each line into a
 * Rocq file whose lemmas the model has to close by computation, and
 * check_start_state.py reads the same line against a Python transcription
 * of the model.
 *
 * The probe is built -nostartfiles, so _start below is the process's entry
 * point and its first instructions store the kernel's x2 to sp_at_start.  No
 * libc start-up code runs, and the stack pointer that main sees is not the
 * one the kernel chose.
 */

typedef unsigned long u64;
typedef long i64;

/* ---------------------------------------------------------------- entry -- */

/* x2 as the kernel set it at the process entry point.  _start's first two
   instructions compute the address of this word; neither touches the stack,
   so the third instruction stores the value the kernel chose (Linux v6.18.46,
   commit 1f99e9ab748f, fs/binfmt_elf.c, create_elf_tables: sp points at
   argc).  main runs on its own frame, below this address. */
u64 sp_at_start;

void start_c(u64 *sp);

__asm__(".text\n"
        ".globl _start\n"
        ".type _start, @function\n"
        "_start:\n"
        "  la    t0, sp_at_start\n"
        "  sd    sp, 0(t0)\n"
        "  mv    a0, sp\n"
        "  andi  sp, sp, -16\n"
        "  tail  start_c\n"
        ".size _start, .-_start\n");

/* ---------------------------------------------------------------- calls -- */

/* asm-generic syscall numbers, which riscv64 uses. */
#define SYS_mount       40
#define SYS_openat      56
#define SYS_close       57
#define SYS_read        63
#define SYS_write       64
#define SYS_exit_group  94
#define SYS_reboot     142
#define SYS_brk        214
#define SYS_munmap     215
#define SYS_mremap     216
#define SYS_mmap       222
#define SYS_clone      220
#define SYS_execve     221
#define SYS_wait4      260

static long rsys(long n, long x0, long x1, long x2, long x3, long x4, long x5)
{
  register long a0 __asm__("a0") = x0;
  register long a1 __asm__("a1") = x1;
  register long a2 __asm__("a2") = x2;
  register long a3 __asm__("a3") = x3;
  register long a4 __asm__("a4") = x4;
  register long a5 __asm__("a5") = x5;
  register long a7 __asm__("a7") = n;
  __asm__ __volatile__("ecall"
                       : "+r"(a0)
                       : "r"(a1), "r"(a2), "r"(a3), "r"(a4), "r"(a5), "r"(a7)
                       : "memory");
  return a0;
}

#define PROT_NONE   0
#define PROT_READ   1
#define PROT_WRITE  2
#define MAP_PRIVATE          0x02
#define MAP_ANONYMOUS        0x20
#define MAP_FIXED            0x10
#define MAP_FIXED_NOREPLACE  0x100000
#define MREMAP_MAYMOVE       1
#define AT_FDCWD   (-100)
#define PAGE       4096UL
#define MB         (1024UL * 1024UL)
#define ANON       (MAP_PRIVATE | MAP_ANONYMOUS)
#define RW         (PROT_READ | PROT_WRITE)

/* --------------------------------------------------------------- output -- */

static char ob[1 << 13];
static unsigned long obn;

static void oflush(void)
{
  unsigned long done = 0;
  while (done < obn) {
    long r = rsys(SYS_write, 1, (long)(ob + done), (long)(obn - done), 0, 0, 0);
    if (r <= 0) break;
    done += (unsigned long)r;
  }
  obn = 0;
}

static void pc(char c)
{
  if (obn == sizeof ob) oflush();
  ob[obn++] = c;
}

static void ps(const char *s) { while (*s) pc(*s++); }

static void pu(u64 v)
{
  char t[24];
  int k = 0;
  if (!v) { pc('0'); return; }
  while (v) { t[k++] = (char)('0' + (int)(v % 10)); v /= 10; }
  while (k) pc(t[--k]);
}

static void pi(i64 v)
{
  if (v < 0) { pc('-'); pu((u64)(-v)); } else pu((u64)v);
}

static void pjstr(const char *s, unsigned long n)
{
  static const char hex[] = "0123456789abcdef";
  unsigned long i;
  pc('"');
  for (i = 0; i < n; i++) {
    unsigned char c = (unsigned char)s[i];
    if (c == '"' || c == '\\') { pc('\\'); pc((char)c); }
    else if (c == '\n') { pc('\\'); pc('n'); }
    else if (c == '\t') { pc('\\'); pc('t'); }
    else if (c < 0x20 || c == 0x7f) {
      ps("\\u00"); pc(hex[(c >> 4) & 0xf]); pc(hex[c & 0xf]);
    } else pc((char)c);
  }
  pc('"');
}

static void log_call(long sysno, const i64 *args, int nargs, i64 ret)
{
  int i;
  ps("{\"sysno\":"); pi(sysno); ps(",\"args\":[");
  for (i = 0; i < nargs; i++) { if (i) pc(','); pi(args[i]); }
  ps("],\"ret\":"); pi(ret); ps("}\n");
  oflush();
}

/* ------------------------------------------------------------- the calls -- */

static u64 do_mmap(u64 addr, u64 len, long prot, long flags)
{
  long r = rsys(SYS_mmap, (long)addr, (long)len, prot, flags, -1, 0);
  i64 a[6] = { (i64)addr, (i64)len, prot, flags, -1, 0 };
  log_call(SYS_mmap, a, 6, r);
  return (u64)r;
}

static long do_munmap(u64 addr, u64 len)
{
  long r = rsys(SYS_munmap, (long)addr, (long)len, 0, 0, 0, 0);
  i64 a[6] = { (i64)addr, (i64)len, 0, 0, 0, 0 };
  log_call(SYS_munmap, a, 6, r);
  return r;
}

static u64 do_mremap(u64 addr, u64 old_len, u64 new_len, long flags)
{
  long r = rsys(SYS_mremap, (long)addr, (long)old_len, (long)new_len, flags, 0, 0);
  i64 a[6] = { (i64)addr, (i64)old_len, (i64)new_len, flags, 0, 0 };
  log_call(SYS_mremap, a, 6, r);
  return (u64)r;
}

static u64 do_brk(u64 addr)
{
  long r = rsys(SYS_brk, (long)addr, 0, 0, 0, 0, 0);
  i64 a[6] = { (i64)addr, 0, 0, 0, 0, 0 };
  log_call(SYS_brk, a, 6, r);
  return (u64)r;
}

/* -------------------------------------------------------------- /proc io -- */

static long read_file(const char *path, char *buf, long cap)
{
  long fd = rsys(SYS_openat, AT_FDCWD, (long)path, 0 /* O_RDONLY */, 0, 0, 0);
  long n = 0;
  if (fd < 0) { buf[0] = 0; return fd; }
  for (;;) {
    long r = rsys(SYS_read, fd, (long)(buf + n), cap - 1 - n, 0, 0, 0);
    if (r <= 0) break;
    n += r;
    if (n >= cap - 1) break;
  }
  rsys(SYS_close, fd, 0, 0, 0, 0, 0);
  buf[n] = 0;
  return n;
}

static int starts(const char *s, const char *pre)
{
  while (*pre) { if (*s++ != *pre++) return 0; }
  return 1;
}

/* The first line of [buf] that ends with [tag], or 0. */
static const char *line_with(const char *buf, const char *tag)
{
  const char *line = buf;
  while (*line) {
    const char *p = line;
    while (*p && *p != '\n') {
      if (starts(p, tag)) return line;
      p++;
    }
    if (!*p) return 0;
    line = p + 1;
  }
  return 0;
}

static u64 hex_at(const char *p, const char **end)
{
  u64 v = 0;
  for (;;) {
    char c = *p;
    int d;
    if (c >= '0' && c <= '9') d = c - '0';
    else if (c >= 'a' && c <= 'f') d = c - 'a' + 10;
    else if (c >= 'A' && c <= 'F') d = c - 'A' + 10;
    else break;
    v = v * 16 + (u64)d;
    p++;
  }
  if (end) *end = p;
  return v;
}

static u64 dec_at(const char *p, const char **end)
{
  u64 v = 0;
  while (*p >= '0' && *p <= '9') { v = v * 10 + (u64)(*p - '0'); p++; }
  if (end) *end = p;
  return v;
}

/* Field 28 of /proc/self/stat (mm->start_stack): the comm field is in
   parentheses and may hold spaces, so counting starts after the last ')'. */
static u64 start_stack(const char *stat)
{
  const char *p = stat, *last = 0;
  int field;
  while (*p) { if (*p == ')') last = p; p++; }
  if (!last) return 0;
  p = last + 1;
  /* the token after ')' is field 3; field 28 is 25 tokens later */
  for (field = 3; ; field++) {
    while (*p == ' ') p++;
    if (!*p || *p == '\n') return 0;
    if (field == 28) return dec_at(p, 0);
    while (*p && *p != ' ' && *p != '\n') p++;
  }
}

/* The value after the colon of the "mmu" line of /proc/cpuinfo. */
static void put_mmu(const char *cpuinfo)
{
  const char *l = cpuinfo;
  while (*l) {
    if (starts(l, "mmu")) {
      const char *p = l;
      while (*p && *p != '\n' && *p != ':') p++;
      if (*p == ':') {
        const char *s;
        p++;
        while (*p == ' ' || *p == '\t') p++;
        s = p;
        while (*p && *p != '\n') p++;
        pjstr(s, (unsigned long)(p - s));
        return;
      }
    }
    while (*l && *l != '\n') l++;
    if (*l) l++;
  }
  pjstr("", 0);
}

/* ------------------------------------------------------------------ main -- */

static char maps[1 << 15];
static char statb[1 << 11];
static char cpub[1 << 13];
static char minaddr[64];
static u64 pages[64];

static void placement_run(void)
{
  long maps_n;
  u64 brk0, vvar_lo = 0, m8, sc, top, room, crowd;
  const char *vvar;
  int i;

  /* The probe is init, so nothing has mounted /proc yet.  Under qemu-user
     the call fails and the host's /proc answers; neither changes a mapping. */
  rsys(SYS_mount, (long)"proc", (long)"/proc", (long)"proc", 0, 0, 0);

  maps_n = read_file("/proc/self/maps", maps, sizeof maps);
  if (maps_n < 0) maps_n = 0;
  read_file("/proc/self/stat", statb, sizeof statb);
  read_file("/proc/cpuinfo", cpub, sizeof cpub);
  read_file("/proc/sys/vm/mmap_min_addr", minaddr, sizeof minaddr);
  brk0 = (u64)rsys(SYS_brk, 0, 0, 0, 0, 0, 0);

  ps("{\"maps\":");
  pjstr(maps, (unsigned long)maps_n);
  ps(",\"startstack\":"); pu(start_stack(statb));
  ps(",\"brk0\":"); pu(brk0);
  ps(",\"mmu\":"); put_mmu(cpub);
  ps(",\"dac_mmap_min_addr\":"); pu(dec_at(minaddr, 0));
  ps("}\n");
  oflush();

  vvar = line_with(maps, "[vvar]");
  if (vvar) vvar_lo = hex_at(vvar, 0);

  /* 64 one-page PROT_NONE grants: they pack downwards from the vDSO pair. */
  for (i = 0; i < 64; i++) pages[i] = do_mmap(0, PAGE, PROT_NONE, ANON);

  /* A 2 MiB and an 8 MiB grant.  Both lengths are PMD multiples, so on a
     CONFIG_TRANSPARENT_HUGEPAGE kernel each takes the padded search and the
     2 MiB alignment (mm/huge_memory.c, __thp_get_unmapped_area). */
  do_mmap(0, 2 * MB, RW, ANON);
  m8 = do_mmap(0, 8 * MB, RW, ANON);

  /* A middle page of the packed block, and the top half of the 8 MiB grant. */
  do_munmap(pages[31], PAGE);
  do_munmap(m8 + 4 * MB, 4 * MB);

  /* The highest fit for one page is now that 4 KiB hole, and nothing else. */
  do_mmap(0, PAGE, PROT_NONE, ANON);

  /* The hints.  1 rounds down to 0, so it is no hint at all and a 2 MiB
     length reaches the THP path; 0x1001 rounds to 0x1000; 0x8000 is granted
     at 0x8000 when mmap_min_addr is 4096 and at 0x10000 when it is 65536;
     an occupied hint and 2^64-1 both fall back to the search. */
  do_mmap(1, 2 * MB, RW, ANON);
  do_mmap(0x1001, PAGE, RW, ANON);
  do_mmap(0x8000, PAGE, RW, ANON);
  do_mmap(0x80000000UL, PAGE, RW, ANON);
  do_mmap(pages[0], PAGE, RW, ANON);
  do_mmap(~0UL, PAGE, RW, ANON);

  /* MAP_FIXED_NOREPLACE over the first page of the vvar mapping: -EEXIST.
     The protection is PROT_READ|PROT_WRITE, not PROT_READ: Linux answers
     -EEXIST whatever the protection, and a read-only anonymous mapping is a
     shape the model does not cover (see README.md, "Why no PROT_READ-only
     mapping").  Do not change it back. */
  if (vvar_lo)
    do_mmap(vvar_lo, PAGE, RW, ANON | MAP_FIXED_NOREPLACE);

  /* The three mremap grows.  A scratch region is taken and released so the
     last two subjects can be placed with MAP_FIXED: their answers then do
     not depend on what the hints above happened to take. */
  sc = do_mmap(0, 16 * MB, PROT_NONE, ANON);
  do_munmap(sc, 16 * MB);

  /* The topmost mapping, directly below the vvar: in place is blocked by the
     vDSO pair, so Linux moves it. */
  do_munmap(pages[0], PAGE);
  top = do_mmap(pages[0], PAGE, RW, ANON | MAP_FIXED);
  do_mremap(top, PAGE, 2 * PAGE, MREMAP_MAYMOVE);

  /* An interior mapping with a free page above it: it grows in place. */
  room = do_mmap(sc, PAGE, RW, ANON | MAP_FIXED);
  do_mremap(room, PAGE, 2 * PAGE, MREMAP_MAYMOVE);

  /* And one with a neighbour directly above it: it moves. */
  crowd = do_mmap(sc + 0x10000, PAGE, RW, ANON | MAP_FIXED);
  do_mmap(sc + 0x11000, PAGE, RW, ANON | MAP_FIXED);
  do_mremap(crowd, PAGE, 2 * PAGE, MREMAP_MAYMOVE);

  /* Two brk grows. */
  do_brk(brk0 + PAGE);
  do_brk(brk0 + PAGE + MB);

  oflush();
}

/* ----------------------------------------------------- the start state -- */

/* Auxiliary vector tags (Linux v6.18.46, commit 1f99e9ab748f,
   include/uapi/linux/auxvec.h and arch/riscv/include/uapi/asm/hwcap.h). */
#define AT_HWCAP          16
#define AT_EXECFN         31
#define AT_SYSINFO_EHDR   33
#define COMPAT_HWCAP_ISA_V (1UL << ('V' - 'A'))   /* 0x200000 */

#define CLONE_SIGCHLD   17   /* clone(SIGCHLD, 0, ...) is fork */

static char auxvb[1 << 12];
static char rndbitsb[64];
static u64 rndmax;
static char randvab[64];
static char lbuf[1 << 13];
static char *largv[40];
static char *lenvp[24];

static void phexmem(const unsigned char *p, u64 n)
{
  static const char hex[] = "0123456789abcdef";
  u64 i;
  pc('"');
  for (i = 0; i < n; i++) { pc(hex[p[i] >> 4]); pc(hex[p[i] & 0xf]); }
  pc('"');
}

static unsigned long slen(const char *s)
{
  unsigned long n = 0;
  while (s[n]) n++;
  return n;
}

static long write_file(const char *path, const char *buf, long n)
{
  long fd = rsys(SYS_openat, AT_FDCWD, (long)path, 1 /* O_WRONLY */, 0, 0, 0);
  long r;
  if (fd < 0) return fd;
  r = rsys(SYS_write, fd, (long)buf, n, 0, 0, 0);
  rsys(SYS_close, fd, 0, 0, 0, 0, 0);
  return r;
}

static int dec_str(u64 v, char *out)
{
  char t[24];
  int k = 0, i = 0;
  if (!v) t[k++] = '0';
  while (v) { t[k++] = (char)('0' + (int)(v % 10)); v /= 10; }
  while (k) out[i++] = t[--k];
  out[i++] = '\n';
  return i;
}

/* The ceiling the kernel puts on vm.mmap_rnd_bits.  There is no
   mmap_rnd_bits_max file, so the ceiling is measured: the largest candidate
   the sysctl accepts is mmap_rnd_bits_max (Linux v6.18.46, commit
   1f99e9ab748f, kernel/sysctl.c, vm_table, whose extra2 is
   &mmap_rnd_bits_max, and arch/riscv/mm/init.c, set_mmap_rnd_bits_max).
   This process's own launch is already over, and the value the launch used
   is written back, so the next execve sees the value it would have seen. */
static u64 probe_rnd_bits_max(u64 cur)
{
  static char tmp[64];
  char dec[24];
  u64 k, best = cur;
  int n;
  for (k = 40; k > cur; k--) {
    n = dec_str(k, dec);
    if (write_file("/proc/sys/vm/mmap_rnd_bits", dec, n) < 0) continue;
    read_file("/proc/sys/vm/mmap_rnd_bits", tmp, sizeof tmp);
    if (dec_at(tmp, 0) == k) { best = k; break; }
  }
  n = dec_str(cur, dec);
  write_file("/proc/sys/vm/mmap_rnd_bits", dec, n);
  return best;
}


/* The start and the end of the first mapping of [buf] whose line carries
   [tag].  /proc/self/maps lines begin "start-end ". */
static int range_of(const char *buf, const char *tag, u64 *lo, u64 *hi)
{
  const char *l = line_with(buf, tag), *p;
  if (!l) return 0;
  *lo = hex_at(l, &p);
  if (*p != '-') return 0;
  *hi = hex_at(p + 1, 0);
  return 1;
}

/* THE PROBE'S OWN ELF HEADER, read out of its own mapped image.

   AT_PHDR, AT_PHENT, AT_PHNUM and AT_ENTRY are four entries the kernel
   copies out of this header.  A check that reads them back out of the
   auxiliary vector and feeds them to the model checks nothing about those
   four, so the probe publishes the header itself and the check compares the
   two.

   The header is at the start of the first PT_LOAD.  This binary is static
   ET_EXEC built -no-pie, so that segment is the lowest mapping
   /proc/self/maps shows, and its start is also the image base; the magic is
   verified before anything is read, and a line that does not carry an ELF
   header leaves ok = 0 and the launch says "elf": null.  Nothing here opens
   a file.

   The offsets are Elf64_Ehdr's (include/uapi/linux/elf.h, Linux v6.18.46,
   commit 1f99e9ab748f): e_entry at 0x18, e_phoff at 0x20, e_phentsize at
   0x36, e_phnum at 0x38.  The base is page-aligned, so each is aligned. */
struct elf_facts { u64 base, phoff, phentsize, phnum, entry; int ok; };

static void read_elf_facts(const char *buf, struct elf_facts *e)
{
  const unsigned char *h;
  const char *p;
  e->ok = 0;
  e->base = 0; e->phoff = 0; e->phentsize = 0; e->phnum = 0; e->entry = 0;
  e->base = hex_at(buf, &p);
  if (*p != '-' || !e->base) return;
  h = (const unsigned char *)e->base;
  if (h[0] != 0x7f || h[1] != 'E' || h[2] != 'L' || h[3] != 'F') return;
  e->entry     = *(const u64 *)(const void *)(h + 0x18);
  e->phoff     = *(const u64 *)(const void *)(h + 0x20);
  e->phentsize = *(const unsigned short *)(const void *)(h + 0x36);
  e->phnum     = *(const unsigned short *)(const void *)(h + 0x38);
  e->ok = 1;
}

/* vlenb, the vector register width in bytes (arch/riscv/kernel/vector.c,
   riscv_v_setup_vsize).  The CSR is read ONLY when AT_HWCAP carries the V
   bit: on a hart without V the read traps, and a trap in init panics the
   kernel. */
static u64 read_vlenb(void)
{
  u64 v;
  __asm__ __volatile__("csrr %0, 0xc22" : "=r"(v));
  return v;
}

static void pstrings(char *const *v)
{
  int i;
  pc('[');
  for (i = 0; v && v[i]; i++) { if (i) pc(','); pjstr(v[i], slen(v[i])); }
  pc(']');
}

/* ONE launch line: the five keys of the placement log, then the launch
   facts and the bytes of this process's own entry block. */
static void record_run(const char *run, char *const *argv, char *const *envp)
{
  long maps_n, auxv_n;
  u64 brk0, stack_lo = 0, stack_hi = 0, vvar_lo = 0, vvar_hi = 0;
  u64 vdso_lo = 0, vdso_hi = 0, ehdr = 0, hwcap = 0, execfn = 0;
  const u64 *av;
  struct elf_facts ef;
  long i;

  rsys(SYS_mount, (long)"proc", (long)"/proc", (long)"proc", 0, 0, 0);
  maps_n = read_file("/proc/self/maps", maps, sizeof maps);
  if (maps_n < 0) maps_n = 0;
  read_elf_facts(maps, &ef);
  read_file("/proc/self/stat", statb, sizeof statb);
  read_file("/proc/cpuinfo", cpub, sizeof cpub);
  read_file("/proc/sys/vm/mmap_min_addr", minaddr, sizeof minaddr);
  read_file("/proc/sys/vm/mmap_rnd_bits", rndbitsb, sizeof rndbitsb);
  rndmax = probe_rnd_bits_max(dec_at(rndbitsb, 0));
  read_file("/proc/sys/kernel/randomize_va_space", randvab, sizeof randvab);
  auxv_n = read_file("/proc/self/auxv", auxvb, sizeof auxvb);
  if (auxv_n < 0) auxv_n = 0;
  brk0 = (u64)rsys(SYS_brk, 0, 0, 0, 0, 0, 0);

  range_of(maps, "[stack]", &stack_lo, &stack_hi);
  range_of(maps, "[vvar]", &vvar_lo, &vvar_hi);
  range_of(maps, "[vdso]", &vdso_lo, &vdso_hi);

  av = (const u64 *)(const void *)auxvb;
  for (i = 0; (i + 1) * 16 <= auxv_n && av[2 * i]; i++) {
    if (av[2 * i] == AT_HWCAP) hwcap = av[2 * i + 1];
    else if (av[2 * i] == AT_SYSINFO_EHDR) ehdr = av[2 * i + 1];
    else if (av[2 * i] == AT_EXECFN) execfn = av[2 * i + 1];
  }

  ps("{\"maps\":");
  pjstr(maps, (unsigned long)maps_n);
  ps(",\"startstack\":"); pu(start_stack(statb));
  ps(",\"brk0\":"); pu(brk0);
  ps(",\"mmu\":"); put_mmu(cpub);
  ps(",\"dac_mmap_min_addr\":"); pu(dec_at(minaddr, 0));
  ps(",\"run\":"); pjstr(run, slen(run));
  ps(",\"argv\":"); pstrings(argv);
  ps(",\"envp\":"); pstrings(envp);
  ps(",\"execfn\":");
  if (execfn) pjstr((const char *)execfn, slen((const char *)execfn));
  else pjstr("", 0);
  ps(",\"mmap_rnd_bits\":"); pu(dec_at(rndbitsb, 0));
  ps(",\"mmap_rnd_bits_max\":"); pu(rndmax);
  ps(",\"randomize_va_space\":"); pu(dec_at(randvab, 0));
  ps(",\"vlenb\":");
  if (hwcap & COMPAT_HWCAP_ISA_V) pu(read_vlenb()); else ps("null");
  /* The image's own ELF header: the four values the kernel turned into
     AT_PHDR, AT_PHENT, AT_PHNUM and AT_ENTRY, plus the base they are
     relative to.  "phdr" is base + phoff, the run-time address of the
     program-header table, so a reader compares it with AT_PHDR without
     adding anything.  base and phoff are both written because they differ
     the day this binary is built PIE. */
  ps(",\"elf\":");
  if (ef.ok) {
    ps("{\"base\":"); pu(ef.base);
    ps(",\"phoff\":"); pu(ef.phoff);
    ps(",\"phdr\":"); pu(ef.base + ef.phoff);
    ps(",\"phentsize\":"); pu(ef.phentsize);
    ps(",\"phnum\":"); pu(ef.phnum);
    ps(",\"entry\":"); pu(ef.entry);
    pc('}');
  } else {
    ps("null");
  }
  ps(",\"sp_at_start\":"); pu(sp_at_start);
  ps(",\"stack_end\":"); pu(stack_hi);
  ps(",\"vvar_start\":"); pu(vvar_lo);
  ps(",\"auxv\":"); phexmem((const unsigned char *)auxvb, (u64)auxv_n);
  ps(",\"stack_bytes\":");
  if (stack_hi > sp_at_start && stack_hi - sp_at_start <= 1 * MB)
    phexmem((const unsigned char *)sp_at_start, stack_hi - sp_at_start);
  else pjstr("", 0);
  ps(",\"vdso_image\":");
  if (ehdr && vdso_hi > ehdr && vdso_hi - ehdr <= 1 * MB)
    phexmem((const unsigned char *)ehdr, vdso_hi - ehdr);
  else pjstr("", 0);
  ps("}\n");
  oflush();
}

/* A long argv and a long envp, built in place: the probe allocates nothing. */
static void build_long(void)
{
  unsigned long o = 0;
  int i, j;
  largv[0] = lbuf; lbuf[o++] = 'a'; lbuf[o++] = 0;
  for (i = 0; i < 32; i++) {
    largv[i + 1] = lbuf + o;
    lbuf[o++] = 'A';
    lbuf[o++] = (char)('0' + i / 10);
    lbuf[o++] = (char)('0' + i % 10);
    lbuf[o++] = '-';
    for (j = 0; j < 16 + i * 3; j++) lbuf[o++] = 'x';
    lbuf[o++] = 0;
  }
  largv[33] = 0;
  for (i = 0; i < 16; i++) {
    lenvp[i] = lbuf + o;
    lbuf[o++] = 'V';
    lbuf[o++] = (char)('0' + i / 10);
    lbuf[o++] = (char)('0' + i % 10);
    lbuf[o++] = '=';
    for (j = 0; j < 24 + i * 7; j++) lbuf[o++] = 'y';
    lbuf[o++] = 0;
  }
  lenvp[16] = 0;
}

/* execve("a", ...): the exec file name is the relative name "a", so
   AT_EXECFN is "a" (Linux v6.18.46, fs/exec.c, do_execveat_common, and
   fs/namei.c, getname_flags). */
static void spawn(char *const *argv, char *const *envp)
{
  long pid;
  oflush();
  pid = rsys(SYS_clone, CLONE_SIGCHLD, 0, 0, 0, 0, 0);
  if (pid == 0) {
    rsys(SYS_execve, (long)"a", (long)argv, (long)envp, 0, 0, 0);
    ps("{\"error\":\"execve of /a failed\"}\n");
    oflush();
    rsys(SYS_exit_group, 1, 0, 0, 0, 0, 0);
  }
  if (pid > 0) rsys(SYS_wait4, pid, 0, 0, 0, 0, 0);
}

static char *fixture_argv[] = { (char *)"a", 0 };
static char *fixture_envp[] = { 0 };

int main(int argc, char **argv, char **envp)
{
  const char *mode = 0;
  int i;

  for (i = 0; envp && envp[i]; i++)
    if (starts(envp[i], "pc_mode=")) mode = envp[i] + 8;

  /* A child of the start-state driver: this process's own launch is the
     record.  Only the driver's children are called "a". */
  if (argc >= 1 && argv[0][0] == 'a' && argv[0][1] == 0) {
    record_run(argc > 1 ? "long" : "fixture", argv, envp);
    rsys(SYS_exit_group, 0, 0, 0, 0, 0, 0);
  }

  if (mode && starts(mode, "startstate")) {
    rsys(SYS_mount, (long)"proc", (long)"/proc", (long)"proc", 0, 0, 0);
    spawn(fixture_argv, fixture_envp);
    build_long();
    spawn(largv, lenvp);
  } else {
    placement_run();
  }

  /* As init, exiting panics the kernel; power the machine off instead.  In
     user mode the call is refused and the exit below ends the run. */
  rsys(SYS_reboot, (long)0xfee1deadL, 672274793L, (long)0x4321fedcL, 0, 0, 0);
  rsys(SYS_exit_group, 0, 0, 0, 0, 0, 0);
  return 0;
}

/* The C half of _start: argc, argv and envp are the words at the kernel's
   stack pointer (Linux v6.18.46, fs/binfmt_elf.c, create_elf_tables). */
void start_c(u64 *sp)
{
  int argc = (int)sp[0];
  char **argv = (char **)(void *)(sp + 1);
  char **envp = argv + argc + 1;
  main(argc, argv, envp);
  rsys(SYS_exit_group, 0, 0, 0, 0, 0, 0);
  for (;;) { }
}
