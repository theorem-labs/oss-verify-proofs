(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdGlob.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): cmd_ -> seg_, CMD_ -> SEG_, GI_cmdA -> GI_segA; the program's writable statics are fuzz_segconf.asan's one, LLVMFuzzerTestOneInput.longl (twin .symtab 0x5de680, nm size 160 with the redzone; 121 bytes, asan_globals descriptor 87 and fuzz_segconf.c:594 `static char longl[121]`), in place of g_rec, record.spill and g_quitting; the global invariant is the plain proof's GI (lib/Prog/SlotFR.v GIb: longl[120] = 0) at that address; the read-only range 0xa5740..0xa7108 -> 0xa14a0..0xa3748 (.data.rel.ro start, .got end; PT_GNU_RELRO 0xa1468 size 0x2b98). *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/SegGlob.v for fuzz_segconf.asan-ubsan: module paths; and the image-B values named in the commit message. *)
(* The program's own writable statics on fuzz_command.asan, and the global invariant over them.

   These are image addresses, independent of the program interface, so they live apart from lib/A/ACfn.v (which
   re-exports this file): every per-function contract needs them, and none of those contracts needs the interface.
   Addresses: the pinned image's symbols (g_rec 0x5e3740, record.spill 0x5e3be0, g_quitting 0x5e3c60), the object
   sizes from the program's DWARF (960, 56, 4; nm's 0x4a0 / 0x60 / 0x20 include the redzones). GI_cmdA is
   fuzz_command's plain lib/Prog/Slot.v:19-21 GI_cmd at these addresses, over the ASan side's reader. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
Import ListNotations.
Local Open Scope Z_scope.
Definition A_LONGL : Z := 0x5dee40.
Definition seg_PG : list (Z * Z) :=
[(A_LONGL, A_LONGL + 121)].
(* The read-only range after relocation (RELRO's file part, .data.rel.ro and .got): the statements' arodata_okP is
   over this range, fixed here rather than left as a free variable, so that every fact about it (in the image,
   apart from the program's statics, below the ofl head) is a fact about two numbers (MEASURED: the PT_GNU_RELRO
   header at 0xa5700, file size 0x1a08; .data.rel.ro starts at 0xa5740). *)
Definition SEG_RLO : Z := 0xa1c60.
Definition SEG_RHI : Z := 0xa3f08.
Definition zero_atA (rd : reader) (a n : Z) : Prop := forall i, 0 <= i < n -> rd (a + i) = Some 0.
Definition GI_segA (j : nat) (rd : reader) : Prop :=
zero_atA rd (A_LONGL + 120) 1.
