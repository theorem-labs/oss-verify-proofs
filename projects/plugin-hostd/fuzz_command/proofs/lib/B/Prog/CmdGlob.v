(* The program's own writable statics on fuzz_command.asan-ubsan, and the global invariant over them.

   These are image addresses, independent of the program interface, so they live apart from lib/B/YCfn.v (which
   re-exports this file): every per-function contract needs them, and none of those contracts needs the interface.
   Addresses: the pinned image's symbols (g_rec 0x5e32c0, record.spill 0x5e3760, g_quitting 0x5e37e0), the object
   sizes from the program's DWARF (960, 56, 4; nm's 0x4a0 / 0x60 / 0x20 include the redzones). GI_cmdA is
   fuzz_command's plain lib/Prog/Slot.v:19-21 GI_cmd at these addresses, over the ASan side's reader. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f.
Import ListNotations.
Local Open Scope Z_scope.
Definition A_G_REC : Z := 0x5e32c0.
Definition A_REC_SPILL : Z := 0x5e3760.
Definition A_G_QUITTING : Z := 0x5e37e0.
Definition cmd_PG : list (Z * Z) :=
[(A_G_REC, A_G_REC + 960); (A_REC_SPILL, A_REC_SPILL + 56); (A_G_QUITTING, A_G_QUITTING + 4)].
(* The read-only range after relocation (RELRO's file part, .data.rel.ro and .got): the statements' arodata_okP is
   over this range, fixed here rather than left as a free variable, so that every fact about it (in the image,
   apart from the program's statics, below the ofl head) is a fact about two numbers (MEASURED on
   fuzz_command.asan-ubsan: the PT_GNU_RELRO header at 0xa5258, file size 0x1a10, so it ends at 0xa6c68, the end of
   .got; .data.rel.ro starts at 0xa52a0). *)
Definition CMD_RLO : Z := 0xa52a0.
Definition CMD_RHI : Z := 0xa6c68.
Definition zero_atA (rd : reader) (a n : Z) : Prop := forall i, 0 <= i < n -> rd (a + i) = Some 0.
Definition GI_cmdA (j : nat) (rd : reader) : Prop :=
zero_atA rd (A_G_REC + 8) 4 /\ zero_atA rd (A_G_REC + 912) 12 /\ zero_atA rd (A_G_REC + 928) 16 /\
zero_atA rd A_REC_SPILL 8 /\ zero_atA rd A_G_QUITTING 4.
