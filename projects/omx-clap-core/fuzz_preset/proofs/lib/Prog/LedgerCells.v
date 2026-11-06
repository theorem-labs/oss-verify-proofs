(* GENERATED FILE: do not edit; regenerate with
     python3 gen_ledger_cells.py gen --build plain --twin fuzz_preset.plain
       --pin fuzz_preset.plain --out <this file>
   generator  gen_ledger_cells.py sha256 720d7c83fe77a6b29969dd74afe2e55a72236b67b19769358f4dcbbfb215d156
   twin       fuzz_preset.plain sha256 c8f4d6b8e567b0b1ea729885f933b66e2d8a297445c1e8ae00904c41e0e1dd6c (unstripped; .symtab read with pyelftools)
   pin        fuzz_preset.plain sha256 805604bb0907ae1b70854fb641c3d34299c9d2daf97d8429cb817e232626df99
              (its 4 PT_LOAD equal to the twin's except 25 bytes: e_shoff / e_shnum / e_shstrndx and the
              .note.gnu.build-id descriptor, which stripping changes; checked)
   module     lib/Prog/LedgerCells.v
   The plain build's ledger cells, keyed by SYMBOL. A cell is (address, size rounded up to 8): the object and the
   alignment padding after it; the generator checked that the padding holds no byte of another .symtab object,
   that each cell stays in its section and that no two cells overlap.
     order  symbol          STT_FILE        section  address    size  cell  name
     1      g_live          alloc.c         .bss     0x347b0    8     8     GL_LIVE
     2      g_peak          alloc.c         .bss     0x347b8    8     8     GL_PEAK
     3      g_count         alloc.c         .bss     0x347c0    8     8     GL_COUNT
     4      g_fail_at       alloc.c         .data    0x24520    8     8     GL_FAIL
     5      g_ran_out       alloc.c         .bss     0x347a8    1     8     GL_RAN_OUT
     6      g_most          alloc.c         .data    0x24528    8     8     GL_MOST
     7      g_own_ran_out   fuzz_preset.c   .bss     0x347a0    1     8     GL_OWN_RAN_OUT
   GL_cells is in the order the proofs need: the four Ledger.alloc_words words (Ledger.v names them G_LIVE,
   G_PEAK, G_COUNT, G_FAIL), then g_ran_out, in the prh_pst order by symbol (lib/A/PRH_Base.v:308-310), then
   the #102 cells. GL_cells_over takes the four words' names as arguments, so GIInit.v can state the same list
   over Ledger.v's names. GL_runs: the cells merged into maximal runs of adjacent cells, in address order
   (the range-list form of fuzz_free.v's globals_free list at base 9d764437e6be). *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition GL_LIVE : Z := 0x347b0.   (* g_live, alloc.c .bss *)
Definition GL_PEAK : Z := 0x347b8.   (* g_peak, alloc.c .bss *)
Definition GL_COUNT : Z := 0x347c0.   (* g_count, alloc.c .bss *)
Definition GL_FAIL : Z := 0x24520.   (* g_fail_at, alloc.c .data *)
Definition GL_RAN_OUT : Z := 0x347a8.   (* g_ran_out, alloc.c .bss *)
Definition GL_MOST : Z := 0x24528.   (* g_most, alloc.c .data *)
Definition GL_OWN_RAN_OUT : Z := 0x347a0.   (* g_own_ran_out, fuzz_preset.c .bss *)

Definition GZ_LIVE : Z := 8.   (* g_live: .symtab st_size *)
Definition GZ_PEAK : Z := 8.   (* g_peak: .symtab st_size *)
Definition GZ_COUNT : Z := 8.   (* g_count: .symtab st_size *)
Definition GZ_FAIL : Z := 8.   (* g_fail_at: .symtab st_size *)
Definition GZ_RAN_OUT : Z := 1.   (* g_ran_out: .symtab st_size *)
Definition GZ_MOST : Z := 8.   (* g_most: .symtab st_size *)
Definition GZ_OWN_RAN_OUT : Z := 1.   (* g_own_ran_out: .symtab st_size *)

Definition GL_cells_over (g_live g_peak g_count g_fail_at : Z) : list (Z * Z) :=
  [(g_live, 8); (g_peak, 8); (g_count, 8); (g_fail_at, 8); (GL_RAN_OUT, 8); (GL_MOST, 8); (GL_OWN_RAN_OUT, 8)].

Definition GL_cells : list (Z * Z) := GL_cells_over GL_LIVE GL_PEAK GL_COUNT GL_FAIL.

Definition GL_runs : list (Z * Z) := [(GL_FAIL, 16); (GL_OWN_RAN_OUT, 40)].
