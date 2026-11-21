(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  (rw_cells asegs m 0xcfe08 [C8 (Z_to_bv 64 0x16a128); C8 (Z_to_bv 64 0xd5df8); C8 (Z_to_bv 64 0xd85f8);
                              C8 (Z_to_bv 64 0xd92e8); C8 (Z_to_bv 64 0xd92f0); C8 (Z_to_bv 64 0xd92e0)]).
(* [comment removed for export] *)
Notation rt_got_ric m := (rw_cells asegs m 0xd0980 [C8 (Z_to_bv 64 0xd92d9)]).
(* [comment removed for export] *)
Notation rt_shbase m := (rw_cells asegs m 0xd85f8 [C8 (Z_to_bv 64 0x7fff8000)]).
(* [comment removed for export] *)
Notation rt_inited m := (rw_cells asegs m 0xd92d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]).
(* [comment removed for export] *)
Notation rt_layout m := (rw_cells asegs m 0xd92e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
(* [comment removed for export] *)
Notation rt_real_mem m := (rw_cells asegs m 0xd1cc8 [C8 (Z_to_bv 64 0xc6150); C8 (Z_to_bv 64 0xc6554)]).
Notation rt_real_wcslen m := (rw_cells asegs m 0xd1b88 [C8 (Z_to_bv 64 0xc6054)]).
Notation rt_real_read m := (rw_cells asegs m 0xd1b98 [C8 (Z_to_bv 64 0xcb854)]).
Notation rt_real_printf m := (rw_cells asegs m 0xd1bb8 [C8 (Z_to_bv 64 0xc5a9c); C8 (Z_to_bv 64 0xc298c)]).
