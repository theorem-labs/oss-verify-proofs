(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x67f000 <= s1 -> no_image bsegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells bsegs m 0xd1390 [C8 (Z_to_bv 64 0x16b6a8); C8 (Z_to_bv 64 0xd7378); C8 (Z_to_bv 64 0xd9b78);
                              C8 (Z_to_bv 64 0xda868); C8 (Z_to_bv 64 0xda870); C8 (Z_to_bv 64 0xda860)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells bsegs m 0xd1f08 [C8 (Z_to_bv 64 0xda859)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells bsegs m 0xd9b78 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells bsegs m 0xda858 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells bsegs m 0xda860 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells bsegs m 0xd3250 [C8 (Z_to_bv 64 0xc76dc); C8 (Z_to_bv 64 0xc7ae0)]).
Notation rt_real_wcslen m := (rw_cells bsegs m 0xd3110 [C8 (Z_to_bv 64 0xc75e0)]).
Notation rt_real_read m := (rw_cells bsegs m 0xd3120 [C8 (Z_to_bv 64 0xccde0)]).
Notation rt_real_printf m := (rw_cells bsegs m 0xd3140 [C8 (Z_to_bv 64 0xc7028); C8 (Z_to_bv 64 0xc3f18)]).
