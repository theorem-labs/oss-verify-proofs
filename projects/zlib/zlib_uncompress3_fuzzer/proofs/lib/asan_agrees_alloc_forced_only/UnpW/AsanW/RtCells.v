(* reloc-zl14c a01b137199410f9a01e172b1bca22880 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma no_image_asan : forall s1 s2, 0x67e000 <= s1 -> no_image asegs s1 s2.
Proof. intros s1 s2 H z Hz. apply ref_find_segment_none; lia. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation rt_got m :=
  (rw_cells asegs m 0xd0168 [C8 (Z_to_bv 64 0x16a4a8); C8 (Z_to_bv 64 0xd6178); C8 (Z_to_bv 64 0xd8978);
                              C8 (Z_to_bv 64 0xd9668); C8 (Z_to_bv 64 0xd9670); C8 (Z_to_bv 64 0xd9660)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells asegs m 0xd0ce0 [C8 (Z_to_bv 64 0xd9659)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells asegs m 0xd8978 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells asegs m 0xd9658 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells asegs m 0xd9660 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells asegs m 0xd2028 [C8 (Z_to_bv 64 0xc64b0); C8 (Z_to_bv 64 0xc68b4)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0xd1ee8 [C8 (Z_to_bv 64 0xc63b4)]).
Notation rt_real_read m := (rw_cells asegs m 0xd1ef8 [C8 (Z_to_bv 64 0xcbbb4)]).
Notation rt_real_printf m := (rw_cells asegs m 0xd1f18 [C8 (Z_to_bv 64 0xc5dfc); C8 (Z_to_bv 64 0xc2cec)]).
