(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/DecodeCallocTbl.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B; lib/Lib/DecodeCallocKit.v to its image-B copy lib/B/DecodeCallocKit.v) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The decoded instruction table of libreac/fuzz_decode's calloc chain, for the walk of
   lib/A/DecodeCallocWalk.v: the trampoline, ___interceptor_calloc and __asan::asan_calloc of each ASan image.
   The words are read out of the image itself ([build_table] over the unit's loaded segments, [Eval vm_compute]),
   so no instruction word is written here; [table_ok] says every entry is the image's word at that pc.

   Ranges (start, instruction count), measured with capstone on the ORIGINAL unstripped binaries
   (fuzz_decode.asan and fuzz_decode.asan-ubsan), and matched to the symbol
   table (lib/A/DecodeCalloc.v's address table):
     image A: 0x51f68 (1), 0x52364 (92), 0x31bd4 (56)
     image B: 0x51fb4 (1), 0x523b0 (92), 0x31c20 (56)
   The callees the walk does not step through (TryAsanInitFromRtl, GetMallocContextSize, GetCurrentPc,
   UnwindImpl, Allocate, real_memset, SetErrnoToENOMEM) are not in the table: the walk uses their contracts. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import DecodeCallocKit.
Import ListNotations.
Open Scope Z_scope.

(* Image A (fuzz_decode.asan). *)
Definition calloc_ranges_A : list (Z * nat) :=
[ (0x56cc4, 1%nat); (0x570c0, 92%nat); (0x33b2c, 56%nat) ].
Definition tbl_calloc_A : ctable := Eval vm_compute in build_ranges tfibsegs calloc_ranges_A TEmpty.
Lemma tbl_calloc_A_eq : tbl_calloc_A = build_ranges tfibsegs calloc_ranges_A TEmpty.
Proof. vm_cast_no_check (@eq_refl ctable tbl_calloc_A). Qed.
Lemma tbl_calloc_A_ok : table_ok tfibsegs tbl_calloc_A.
Proof.
rewrite tbl_calloc_A_eq. apply build_ranges_ok; [repeat constructor; cbn; discriminate | apply table_ok_empty].
Qed.
