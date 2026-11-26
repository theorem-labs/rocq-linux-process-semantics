/* modprint: print argc modulo a runtime-loaded divisor as one decimal
   digit followed by a newline, then exit 0.

   With argc = length(argv), the whole observable behavior is a single
   write(1, ".\n", 2) of the digit '0' + (argc mod 7), then exit 0.
   There is no input-dependent control flow at all: no operand is read,
   no string is scanned, every execution takes the same straight line.
   argc mod 7 is always in [0, 6], so the rendering is always one digit.

   This is the smallest complete "write buffers, then exit" example
   (Common/CatSim) in the tree, and it exists to keep two Common step
   lemmas exercised: SeqExec.step_lw_zero (an `lw` of an all-zero .bss
   word) and SeqExec.v_remu_small (the bridge from the machine's `remu`
   to Z.modulo).

   The `volatile` on `modulus_base` is load-bearing, not decoration.
   Without it both compilers constant-fold `modulus_base + 7` to the
   literal 7 and then strength-reduce the modulo into a multiply-and-
   shift sequence, so the binaries would contain neither the `lw` from
   .bss nor the `remu` that this example exists to cover.  The qualifier
   forces exactly one 32-bit load of the all-zero .bss word and a real
   64-bit `remu` in both binaries.  It is declared `int` (not `unsigned`)
   so the load stays a sign-extending `lw` rather than an `lwu`. */
#include <unistd.h>

/* .bss: four zero bytes in the loaded image.  See the note above on why
   this is volatile. */
static volatile int modulus_base;

/* .data: the output buffer, patched in place with the rendered digit. */
static char out[2] = {'0', '\n'};

int main(int argc, char **argv) {
    unsigned long d, r;

    (void)argv;
    d = (unsigned long)(modulus_base + 7);
    r = (unsigned long)argc % d;
    out[0] = (char)('0' + r);
    write(1, out, 2);
    return 0;
}
