(* GENERATED FILE: do not edit; regenerate with
     python3 gen_ledger_cells.py gen --build ubsan --twin fuzz_preset.ubsan
       --pin fuzz_preset.ubsan --out <this file>
   generator  gen_ledger_cells.py sha256 720d7c83fe77a6b29969dd74afe2e55a72236b67b19769358f4dcbbfb215d156
   twin       fuzz_preset.ubsan sha256 27566683952ebd54716c69a144e701ca8fd67c84ff98628dcf731b1613261ea6 (unstripped; .symtab read with pyelftools)
   pin        fuzz_preset.ubsan sha256 45b0357d18ff66cd5a4ef336de96441316bb734a3da5ca99ba774808384beb58
              (its 4 PT_LOAD equal to the twin's except 25 bytes: e_shoff / e_shnum / e_shstrndx and the
              .note.gnu.build-id descriptor, which stripping changes; checked)
   module     lib/U/Prog/LedgerCells.v
   The ubsan build's ledger cells, keyed by SYMBOL. A cell is (address, size rounded up to 8): the object and the
   alignment padding after it; the generator checked that the padding holds no byte of another .symtab object,
   that each cell stays in its section and that no two cells overlap.
     order  symbol          STT_FILE        section  address    size  cell  name
     1      g_live          alloc.c         .bss     0x35260    8     8     GL_LIVE
     2      g_peak          alloc.c         .bss     0x35268    8     8     GL_PEAK
     3      g_count         alloc.c         .bss     0x35270    8     8     GL_COUNT
     4      g_fail_at       alloc.c         .data    0x24fd8    8     8     GL_FAIL
     5      g_ran_out       alloc.c         .bss     0x35258    1     8     GL_RAN_OUT
     6      g_most          alloc.c         .data    0x24fe0    8     8     GL_MOST
     7      g_own_ran_out   fuzz_preset.c   .bss     0x35250    1     8     GL_OWN_RAN_OUT
   GL_cells is in the order the proofs need: the four Ledger.alloc_words words (Ledger.v names them G_LIVE,
   G_PEAK, G_COUNT, G_FAIL), then g_ran_out, in the prh_pst order by symbol (lib/A/PRH_Base.v:308-310), then
   the #102 cells. GL_cells_over takes the four words' names as arguments, so GIInit.v can state the same list
   over Ledger.v's names. GL_runs: the cells merged into maximal runs of adjacent cells, in address order
   (the range-list form of fuzz_free.v's globals_free list at base 9d764437e6be). *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition GL_LIVE : Z := 0x35260.   (* g_live, alloc.c .bss *)
Definition GL_PEAK : Z := 0x35268.   (* g_peak, alloc.c .bss *)
Definition GL_COUNT : Z := 0x35270.   (* g_count, alloc.c .bss *)
Definition GL_FAIL : Z := 0x24fd8.   (* g_fail_at, alloc.c .data *)
Definition GL_RAN_OUT : Z := 0x35258.   (* g_ran_out, alloc.c .bss *)
Definition GL_MOST : Z := 0x24fe0.   (* g_most, alloc.c .data *)
Definition GL_OWN_RAN_OUT : Z := 0x35250.   (* g_own_ran_out, fuzz_preset.c .bss *)

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
