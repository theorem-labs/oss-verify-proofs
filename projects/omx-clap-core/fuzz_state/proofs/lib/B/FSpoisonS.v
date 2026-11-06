(* fs.asan-ubsan (build B): the contracts of __asan_poison_memory_region (h, 16) and __asan_unpoison_memory_region
   (h, 16), STATEMENTS ONLY; lib/B/FSpoisonW.v proves them (tfib_poison16 / tfib_unpoison16).
   Ported from: a working branch 52efd1c871f7 proofs/omx-clap-core/fuzz_manifest/lib/A/FMpoisonS.v:20-45 via
   lib/A/FSpoisonS.v (this branch): the shapes apoison16_realizes / aunpoison16_realizes are A/FSpoisonS.v's, generic in
   the entry pc and stated once for both builds; this file instantiates them at B's entries, FSH_Base.PC_poison 0x54904
   and FSH_Base.PC_unpoison 0x54aa4 (lib/B/FSH_Base.v). Changed from the donor: the instantiation at B's names, and the
   shapes' last conjunct `(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)`: A/FSpoisonS.v's text is ONE
   CONJUNCT STRONGER than a Theorem Labs lane's FMpoisonS.v (global presence monotonicity, which the walk kit's fsw_intrin_atU,
   a working branch 259ea2daea9, consumes; A/FSpoisonS.v's header says why), and B's two statements below
   carry it through the shared definitions.
   Disassembly of the pinned fs.asan-ubsan (sha256 5ac5ce0954f8..., capstone 5.0.7): 0x54904 and 0x54aa4 are each
   `addi sp,sp,-0x40`; the two bodies (104 resp. 96 instructions) equal A's at 0x54894 / 0x54a34 instruction for
   instruction except the auipc/ld GOT offsets and the string operands of the dead Printf / CHECK paths; B calls them
   from own() (`jal` 0x82b58 -> 0x54904), fuzz_realloc (0x82c54 -> 0x54aa4) and fuzz_free (0x82e00 -> 0x54aa4).
   What B's walk will read (same disassembly): MemToShadow 0x547c8 (79 instructions, A's 0x54758 modulo GOT offsets),
   musl memset 0x99340 (62 instructions, the same mnemonics and operands as A's 0x98e24), the flags GOT slot 0x9fc08
   (-> 0xa5c38), current_verbosity's GOT slot 0x9fc60 (-> 0x137ed8), REAL(memset)'s GOT slot 0x9fc30 (-> 0xa1a90,
   holding 0x99340).
   The proof: lib/B/FSpoisonR.v + lib/B/FSpoisonW.v (tfib_poison16 / tfib_unpoison16), lib/A/FSpoisonR.v +
   lib/A/FSpoisonW.v over RELOC-B's lib/B core at B's addresses (each address's disassembly in lib/B/FSpoisonR.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSpoisonS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base.
Import ListNotations.
Local Open Scope Z_scope.
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
(* B's poison / unpoison contracts: A/FSpoisonS.v's text at B's entries. *)
Definition fs_poison16 : Prop := apoison16_realizes segs B PC_poison.
Definition fs_unpoison16 : Prop := aunpoison16_realizes segs B PC_unpoison.
End u.
