(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8a3c8 : bv 32 := 0x000e0517.
Lemma F_8a3c8 : fetch_word Asan.M.loaded_segments (0x8a418 : word) = Some W_8a3c8.
Proof. vm_refl. Qed.
Lemma D_8a3c8 : decode_any W_8a3c8 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3cc : bv 32 := 0x7e452503.
Lemma F_8a3cc : fetch_word Asan.M.loaded_segments (0x8a41c : word) = Some W_8a3cc.
Proof. vm_refl. Qed.
Lemma D_8a3cc : decode_any W_8a3cc = Some (Load SZ4 true 10 10 2020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3d0 : bv 32 := 0x0230000f.
Lemma F_8a3d0 : fetch_word Asan.M.loaded_segments (0x8a420 : word) = Some W_8a3d0.
Proof. vm_refl. Qed.
Lemma D_8a3d0 : decode_any W_8a3d0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3d4 : bv 32 := 0x00008067.
Lemma F_8a3d4 : fetch_word Asan.M.loaded_segments (0x8a424 : word) = Some W_8a3d4.
Proof. vm_refl. Qed.
Lemma D_8a3d4 : decode_any W_8a3d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3d8 : bv 32 := 0xfb010113.
Lemma F_8a3d8 : fetch_word Asan.M.loaded_segments (0x8a428 : word) = Some W_8a3d8.
Proof. vm_refl. Qed.
Lemma D_8a3d8 : decode_any W_8a3d8 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3dc : bv 32 := 0x04113423.
Lemma F_8a3dc : fetch_word Asan.M.loaded_segments (0x8a42c : word) = Some W_8a3dc.
Proof. vm_refl. Qed.
Lemma D_8a3dc : decode_any W_8a3dc = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3e0 : bv 32 := 0x04813023.
Lemma F_8a3e0 : fetch_word Asan.M.loaded_segments (0x8a430 : word) = Some W_8a3e0.
Proof. vm_refl. Qed.
Lemma D_8a3e0 : decode_any W_8a3e0 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3e4 : bv 32 := 0x02913c23.
Lemma F_8a3e4 : fetch_word Asan.M.loaded_segments (0x8a434 : word) = Some W_8a3e4.
Proof. vm_refl. Qed.
Lemma D_8a3e4 : decode_any W_8a3e4 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3e8 : bv 32 := 0x03213823.
Lemma F_8a3e8 : fetch_word Asan.M.loaded_segments (0x8a438 : word) = Some W_8a3e8.
Proof. vm_refl. Qed.
Lemma D_8a3e8 : decode_any W_8a3e8 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3ec : bv 32 := 0x03313423.
Lemma F_8a3ec : fetch_word Asan.M.loaded_segments (0x8a43c : word) = Some W_8a3ec.
Proof. vm_refl. Qed.
Lemma D_8a3ec : decode_any W_8a3ec = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3f0 : bv 32 := 0x03413023.
Lemma F_8a3f0 : fetch_word Asan.M.loaded_segments (0x8a440 : word) = Some W_8a3f0.
Proof. vm_refl. Qed.
Lemma D_8a3f0 : decode_any W_8a3f0 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3f4 : bv 32 := 0x01513c23.
Lemma F_8a3f4 : fetch_word Asan.M.loaded_segments (0x8a444 : word) = Some W_8a3f4.
Proof. vm_refl. Qed.
Lemma D_8a3f4 : decode_any W_8a3f4 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3f8 : bv 32 := 0x01613823.
Lemma F_8a3f8 : fetch_word Asan.M.loaded_segments (0x8a448 : word) = Some W_8a3f8.
Proof. vm_refl. Qed.
Lemma D_8a3f8 : decode_any W_8a3f8 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a3fc : bv 32 := 0x01713423.
Lemma F_8a3fc : fetch_word Asan.M.loaded_segments (0x8a44c : word) = Some W_8a3fc.
Proof. vm_refl. Qed.
Lemma D_8a3fc : decode_any W_8a3fc = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a400 : bv 32 := 0x01813023.
Lemma F_8a400 : fetch_word Asan.M.loaded_segments (0x8a450 : word) = Some W_8a400.
Proof. vm_refl. Qed.
Lemma D_8a400 : decode_any W_8a400 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a404 : bv 32 := 0x00078493.
Lemma F_8a404 : fetch_word Asan.M.loaded_segments (0x8a454 : word) = Some W_8a404.
Proof. vm_refl. Qed.
Lemma D_8a404 : decode_any W_8a404 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a408 : bv 32 := 0x00070a93.
Lemma F_8a408 : fetch_word Asan.M.loaded_segments (0x8a458 : word) = Some W_8a408.
Proof. vm_refl. Qed.
Lemma D_8a408 : decode_any W_8a408 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a40c : bv 32 := 0x00068a13.
Lemma F_8a40c : fetch_word Asan.M.loaded_segments (0x8a45c : word) = Some W_8a40c.
Proof. vm_refl. Qed.
Lemma D_8a40c : decode_any W_8a40c = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a410 : bv 32 := 0x00060413.
Lemma F_8a410 : fetch_word Asan.M.loaded_segments (0x8a460 : word) = Some W_8a410.
Proof. vm_refl. Qed.
Lemma D_8a410 : decode_any W_8a410 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a414 : bv 32 := 0x00058913.
Lemma F_8a414 : fetch_word Asan.M.loaded_segments (0x8a464 : word) = Some W_8a414.
Proof. vm_refl. Qed.
Lemma D_8a414 : decode_any W_8a414 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a418 : bv 32 := 0x00050993.
Lemma F_8a418 : fetch_word Asan.M.loaded_segments (0x8a468 : word) = Some W_8a418.
Proof. vm_refl. Qed.
Lemma D_8a418 : decode_any W_8a418 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a41c : bv 32 := 0x00052423.
Lemma F_8a41c : fetch_word Asan.M.loaded_segments (0x8a46c : word) = Some W_8a41c.
Proof. vm_refl. Qed.
Lemma D_8a41c : decode_any W_8a41c = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a420 : bv 32 := 0xb10fe0ef.
Lemma F_8a420 : fetch_word Asan.M.loaded_segments (0x8a470 : word) = Some W_8a420.
Proof. vm_refl. Qed.
Lemma D_8a420 : decode_any W_8a420 = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a424 : bv 32 := 0x0c050a63.
Lemma F_8a424 : fetch_word Asan.M.loaded_segments (0x8a474 : word) = Some W_8a424.
Proof. vm_refl. Qed.
Lemma D_8a424 : decode_any W_8a424 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a428 : bv 32 := 0x219010ef.
Lemma F_8a428 : fetch_word Asan.M.loaded_segments (0x8a478 : word) = Some W_8a428.
Proof. vm_refl. Qed.
Lemma D_8a428 : decode_any W_8a428 = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a42c : bv 32 := 0x04050a63.
Lemma F_8a42c : fetch_word Asan.M.loaded_segments (0x8a47c : word) = Some W_8a42c.
Proof. vm_refl. Qed.
Lemma D_8a42c : decode_any W_8a42c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a430 : bv 32 := 0x7ff50c13.
Lemma F_8a430 : fetch_word Asan.M.loaded_segments (0x8a480 : word) = Some W_8a430.
Proof. vm_refl. Qed.
Lemma D_8a430 : decode_any W_8a430 = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a434 : bv 32 := 0x461c4583.
Lemma F_8a434 : fetch_word Asan.M.loaded_segments (0x8a484 : word) = Some W_8a434.
Proof. vm_refl. Qed.
Lemma D_8a434 : decode_any W_8a434 = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a438 : bv 32 := 0x00100613.
Lemma F_8a438 : fetch_word Asan.M.loaded_segments (0x8a488 : word) = Some W_8a438.
Proof. vm_refl. Qed.
Lemma D_8a438 : decode_any W_8a438 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a43c : bv 32 := 0x46cc00a3.
Lemma F_8a43c : fetch_word Asan.M.loaded_segments (0x8a48c : word) = Some W_8a43c.
Proof. vm_refl. Qed.
Lemma D_8a43c : decode_any W_8a43c = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a440 : bv 32 := 0x0a059a63.
Lemma F_8a440 : fetch_word Asan.M.loaded_segments (0x8a490 : word) = Some W_8a440.
Proof. vm_refl. Qed.
Lemma D_8a440 : decode_any W_8a440 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a444 : bv 32 := 0x00050b93.
Lemma F_8a444 : fetch_word Asan.M.loaded_segments (0x8a494 : word) = Some W_8a444.
Proof. vm_refl. Qed.
Lemma D_8a444 : decode_any W_8a444 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a448 : bv 32 := 0x3bd010ef.
Lemma F_8a448 : fetch_word Asan.M.loaded_segments (0x8a498 : word) = Some W_8a448.
Proof. vm_refl. Qed.
Lemma D_8a448 : decode_any W_8a448 = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a44c : bv 32 := 0x00050b13.
Lemma F_8a44c : fetch_word Asan.M.loaded_segments (0x8a49c : word) = Some W_8a44c.
Proof. vm_refl. Qed.
Lemma D_8a44c : decode_any W_8a44c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a450 : bv 32 := 0x000b8513.
Lemma F_8a450 : fetch_word Asan.M.loaded_segments (0x8a4a0 : word) = Some W_8a450.
Proof. vm_refl. Qed.
Lemma D_8a450 : decode_any W_8a450 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a454 : bv 32 := 0x409010ef.
Lemma F_8a454 : fetch_word Asan.M.loaded_segments (0x8a4a4 : word) = Some W_8a454.
Proof. vm_refl. Qed.
Lemma D_8a454 : decode_any W_8a454 = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a458 : bv 32 := 0x00050813.
Lemma F_8a458 : fetch_word Asan.M.loaded_segments (0x8a4a8 : word) = Some W_8a458.
Proof. vm_refl. Qed.
Lemma D_8a458 : decode_any W_8a458 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a45c : bv 32 := 0x060a8c63.
Lemma F_8a45c : fetch_word Asan.M.loaded_segments (0x8a4ac : word) = Some W_8a45c.
Proof. vm_refl. Qed.
Lemma D_8a45c : decode_any W_8a45c = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a460 : bv 32 := 0x00100893.
Lemma F_8a460 : fetch_word Asan.M.loaded_segments (0x8a4b0 : word) = Some W_8a460.
Proof. vm_refl. Qed.
Lemma D_8a460 : decode_any W_8a460 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a464 : bv 32 := 0x00098513.
Lemma F_8a464 : fetch_word Asan.M.loaded_segments (0x8a4b4 : word) = Some W_8a464.
Proof. vm_refl. Qed.
Lemma D_8a464 : decode_any W_8a464 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a468 : bv 32 := 0x00048593.
Lemma F_8a468 : fetch_word Asan.M.loaded_segments (0x8a4b8 : word) = Some W_8a468.
Proof. vm_refl. Qed.
Lemma D_8a468 : decode_any W_8a468 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a46c : bv 32 := 0x00090613.
Lemma F_8a46c : fetch_word Asan.M.loaded_segments (0x8a4bc : word) = Some W_8a46c.
Proof. vm_refl. Qed.
Lemma D_8a46c : decode_any W_8a46c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a470 : bv 32 := 0x00040693.
Lemma F_8a470 : fetch_word Asan.M.loaded_segments (0x8a4c0 : word) = Some W_8a470.
Proof. vm_refl. Qed.
Lemma D_8a470 : decode_any W_8a470 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a474 : bv 32 := 0x00000713.
Lemma F_8a474 : fetch_word Asan.M.loaded_segments (0x8a4c4 : word) = Some W_8a474.
Proof. vm_refl. Qed.
Lemma D_8a474 : decode_any W_8a474 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a478 : bv 32 := 0x000b0793.
Lemma F_8a478 : fetch_word Asan.M.loaded_segments (0x8a4c8 : word) = Some W_8a478.
Proof. vm_refl. Qed.
Lemma D_8a478 : decode_any W_8a478 = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a47c : bv 32 := 0x0740006f.
Lemma F_8a47c : fetch_word Asan.M.loaded_segments (0x8a4cc : word) = Some W_8a47c.
Proof. vm_refl. Qed.
Lemma D_8a47c : decode_any W_8a47c = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a4f0 : bv 32 := 0x018190ef.
Lemma F_8a4f0 : fetch_word Asan.M.loaded_segments (0x8a540 : word) = Some W_8a4f0.
Proof. vm_refl. Qed.
Lemma D_8a4f0 : decode_any W_8a4f0 = Some (Jal 1 102424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a4f4 : bv 32 := 0x460c00a3.
Lemma F_8a4f4 : fetch_word Asan.M.loaded_segments (0x8a544 : word) = Some W_8a4f4.
Proof. vm_refl. Qed.
Lemma D_8a4f4 : decode_any W_8a4f4 = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a4f8 : bv 32 := 0x04813083.
Lemma F_8a4f8 : fetch_word Asan.M.loaded_segments (0x8a548 : word) = Some W_8a4f8.
Proof. vm_refl. Qed.
Lemma D_8a4f8 : decode_any W_8a4f8 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a4fc : bv 32 := 0x04013403.
Lemma F_8a4fc : fetch_word Asan.M.loaded_segments (0x8a54c : word) = Some W_8a4fc.
Proof. vm_refl. Qed.
Lemma D_8a4fc : decode_any W_8a4fc = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a500 : bv 32 := 0x03813483.
Lemma F_8a500 : fetch_word Asan.M.loaded_segments (0x8a550 : word) = Some W_8a500.
Proof. vm_refl. Qed.
Lemma D_8a500 : decode_any W_8a500 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a504 : bv 32 := 0x03013903.
Lemma F_8a504 : fetch_word Asan.M.loaded_segments (0x8a554 : word) = Some W_8a504.
Proof. vm_refl. Qed.
Lemma D_8a504 : decode_any W_8a504 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a508 : bv 32 := 0x02813983.
Lemma F_8a508 : fetch_word Asan.M.loaded_segments (0x8a558 : word) = Some W_8a508.
Proof. vm_refl. Qed.
Lemma D_8a508 : decode_any W_8a508 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a50c : bv 32 := 0x02013a03.
Lemma F_8a50c : fetch_word Asan.M.loaded_segments (0x8a55c : word) = Some W_8a50c.
Proof. vm_refl. Qed.
Lemma D_8a50c : decode_any W_8a50c = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a510 : bv 32 := 0x01813a83.
Lemma F_8a510 : fetch_word Asan.M.loaded_segments (0x8a560 : word) = Some W_8a510.
Proof. vm_refl. Qed.
Lemma D_8a510 : decode_any W_8a510 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a514 : bv 32 := 0x01013b03.
Lemma F_8a514 : fetch_word Asan.M.loaded_segments (0x8a564 : word) = Some W_8a514.
Proof. vm_refl. Qed.
Lemma D_8a514 : decode_any W_8a514 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a518 : bv 32 := 0x00813b83.
Lemma F_8a518 : fetch_word Asan.M.loaded_segments (0x8a568 : word) = Some W_8a518.
Proof. vm_refl. Qed.
Lemma D_8a518 : decode_any W_8a518 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a51c : bv 32 := 0x00013c03.
Lemma F_8a51c : fetch_word Asan.M.loaded_segments (0x8a56c : word) = Some W_8a51c.
Proof. vm_refl. Qed.
Lemma D_8a51c : decode_any W_8a51c = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a520 : bv 32 := 0x05010113.
Lemma F_8a520 : fetch_word Asan.M.loaded_segments (0x8a570 : word) = Some W_8a520.
Proof. vm_refl. Qed.
Lemma D_8a520 : decode_any W_8a520 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8a524 : bv 32 := 0x00008067.
Lemma F_8a524 : fetch_word Asan.M.loaded_segments (0x8a574 : word) = Some W_8a524.
Proof. vm_refl. Qed.
Lemma D_8a524 : decode_any W_8a524 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

