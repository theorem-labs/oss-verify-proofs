(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1c440 : bv 32 := 0xfa010113.
Lemma F_1c440 : fetch_word Ubsan.M.loaded_segments (0x1c440 : word) = Some W_1c440.
Proof. vm_refl. Qed.
Lemma D_1c440 : decode_any W_1c440 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c444 : bv 32 := 0x04113c23.
Lemma F_1c444 : fetch_word Ubsan.M.loaded_segments (0x1c444 : word) = Some W_1c444.
Proof. vm_refl. Qed.
Lemma D_1c444 : decode_any W_1c444 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c448 : bv 32 := 0x04813823.
Lemma F_1c448 : fetch_word Ubsan.M.loaded_segments (0x1c448 : word) = Some W_1c448.
Proof. vm_refl. Qed.
Lemma D_1c448 : decode_any W_1c448 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c44c : bv 32 := 0x04913423.
Lemma F_1c44c : fetch_word Ubsan.M.loaded_segments (0x1c44c : word) = Some W_1c44c.
Proof. vm_refl. Qed.
Lemma D_1c44c : decode_any W_1c44c = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c450 : bv 32 := 0x05213023.
Lemma F_1c450 : fetch_word Ubsan.M.loaded_segments (0x1c450 : word) = Some W_1c450.
Proof. vm_refl. Qed.
Lemma D_1c450 : decode_any W_1c450 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c454 : bv 32 := 0x03313c23.
Lemma F_1c454 : fetch_word Ubsan.M.loaded_segments (0x1c454 : word) = Some W_1c454.
Proof. vm_refl. Qed.
Lemma D_1c454 : decode_any W_1c454 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c458 : bv 32 := 0x03413823.
Lemma F_1c458 : fetch_word Ubsan.M.loaded_segments (0x1c458 : word) = Some W_1c458.
Proof. vm_refl. Qed.
Lemma D_1c458 : decode_any W_1c458 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c45c : bv 32 := 0x03513423.
Lemma F_1c45c : fetch_word Ubsan.M.loaded_segments (0x1c45c : word) = Some W_1c45c.
Proof. vm_refl. Qed.
Lemma D_1c45c : decode_any W_1c45c = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c460 : bv 32 := 0x03613023.
Lemma F_1c460 : fetch_word Ubsan.M.loaded_segments (0x1c460 : word) = Some W_1c460.
Proof. vm_refl. Qed.
Lemma D_1c460 : decode_any W_1c460 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c464 : bv 32 := 0x01713c23.
Lemma F_1c464 : fetch_word Ubsan.M.loaded_segments (0x1c464 : word) = Some W_1c464.
Proof. vm_refl. Qed.
Lemma D_1c464 : decode_any W_1c464 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c468 : bv 32 := 0x24050463.
Lemma F_1c468 : fetch_word Ubsan.M.loaded_segments (0x1c468 : word) = Some W_1c468.
Proof. vm_refl. Qed.
Lemma D_1c468 : decode_any W_1c468 = Some (Branch BC_EQ 10 0 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c46c : bv 32 := 0x00070413.
Lemma F_1c46c : fetch_word Ubsan.M.loaded_segments (0x1c46c : word) = Some W_1c46c.
Proof. vm_refl. Qed.
Lemma D_1c46c : decode_any W_1c46c = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c470 : bv 32 := 0x00068493.
Lemma F_1c470 : fetch_word Ubsan.M.loaded_segments (0x1c470 : word) = Some W_1c470.
Proof. vm_refl. Qed.
Lemma D_1c470 : decode_any W_1c470 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c474 : bv 32 := 0x00060913.
Lemma F_1c474 : fetch_word Ubsan.M.loaded_segments (0x1c474 : word) = Some W_1c474.
Proof. vm_refl. Qed.
Lemma D_1c474 : decode_any W_1c474 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c478 : bv 32 := 0x00058993.
Lemma F_1c478 : fetch_word Ubsan.M.loaded_segments (0x1c478 : word) = Some W_1c478.
Proof. vm_refl. Qed.
Lemma D_1c478 : decode_any W_1c478 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c47c : bv 32 := 0x01410593.
Lemma F_1c47c : fetch_word Ubsan.M.loaded_segments (0x1c47c : word) = Some W_1c47c.
Proof. vm_refl. Qed.
Lemma D_1c47c : decode_any W_1c47c = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c480 : bv 32 := 0x01010613.
Lemma F_1c480 : fetch_word Ubsan.M.loaded_segments (0x1c480 : word) = Some W_1c480.
Proof. vm_refl. Qed.
Lemma D_1c480 : decode_any W_1c480 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c484 : bv 32 := 0x00050a13.
Lemma F_1c484 : fetch_word Ubsan.M.loaded_segments (0x1c484 : word) = Some W_1c484.
Proof. vm_refl. Qed.
Lemma D_1c484 : decode_any W_1c484 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c488 : bv 32 := 0x00000693.
Lemma F_1c488 : fetch_word Ubsan.M.loaded_segments (0x1c488 : word) = Some W_1c488.
Proof. vm_refl. Qed.
Lemma D_1c488 : decode_any W_1c488 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c48c : bv 32 := 0xeacfd0ef.
Lemma F_1c48c : fetch_word Ubsan.M.loaded_segments (0x1c48c : word) = Some W_1c48c.
Proof. vm_refl. Qed.
Lemma D_1c48c : decode_any W_1c48c = Some (Jal 1 2086572, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c490 : bv 32 := 0x01412503.
Lemma F_1c490 : fetch_word Ubsan.M.loaded_segments (0x1c490 : word) = Some W_1c490.
Proof. vm_refl. Qed.
Lemma D_1c490 : decode_any W_1c490 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c494 : bv 32 := 0x1f354463.
Lemma F_1c494 : fetch_word Ubsan.M.loaded_segments (0x1c494 : word) = Some W_1c494.
Proof. vm_refl. Qed.
Lemma D_1c494 : decode_any W_1c494 = Some (Branch BC_LT 10 19 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c498 : bv 32 := 0x1f254263.
Lemma F_1c498 : fetch_word Ubsan.M.loaded_segments (0x1c498 : word) = Some W_1c498.
Proof. vm_refl. Qed.
Lemma D_1c498 : decode_any W_1c498 = Some (Branch BC_LT 10 18 484, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c49c : bv 32 := 0x01012503.
Lemma F_1c49c : fetch_word Ubsan.M.loaded_segments (0x1c49c : word) = Some W_1c49c.
Proof. vm_refl. Qed.
Lemma D_1c49c : decode_any W_1c49c = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4a0 : bv 32 := 0x1c954e63.
Lemma F_1c4a0 : fetch_word Ubsan.M.loaded_segments (0x1c4a0 : word) = Some W_1c4a0.
Proof. vm_refl. Qed.
Lemma D_1c4a0 : decode_any W_1c4a0 = Some (Branch BC_LT 10 9 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4a4 : bv 32 := 0x1c854c63.
Lemma F_1c4a4 : fetch_word Ubsan.M.loaded_segments (0x1c4a4 : word) = Some W_1c4a4.
Proof. vm_refl. Qed.
Lemma D_1c4a4 : decode_any W_1c4a4 = Some (Branch BC_LT 10 8 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4a8 : bv 32 := 0x000a0513.
Lemma F_1c4a8 : fetch_word Ubsan.M.loaded_segments (0x1c4a8 : word) = Some W_1c4a8.
Proof. vm_refl. Qed.
Lemma D_1c4a8 : decode_any W_1c4a8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4ac : bv 32 := 0x00098593.
Lemma F_1c4ac : fetch_word Ubsan.M.loaded_segments (0x1c4ac : word) = Some W_1c4ac.
Proof. vm_refl. Qed.
Lemma D_1c4ac : decode_any W_1c4ac = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4b0 : bv 32 := 0x00090613.
Lemma F_1c4b0 : fetch_word Ubsan.M.loaded_segments (0x1c4b0 : word) = Some W_1c4b0.
Proof. vm_refl. Qed.
Lemma D_1c4b0 : decode_any W_1c4b0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4b4 : bv 32 := 0x00048693.
Lemma F_1c4b4 : fetch_word Ubsan.M.loaded_segments (0x1c4b4 : word) = Some W_1c4b4.
Proof. vm_refl. Qed.
Lemma D_1c4b4 : decode_any W_1c4b4 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4b8 : bv 32 := 0x00040713.
Lemma F_1c4b8 : fetch_word Ubsan.M.loaded_segments (0x1c4b8 : word) = Some W_1c4b8.
Proof. vm_refl. Qed.
Lemma D_1c4b8 : decode_any W_1c4b8 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4bc : bv 32 := 0x00000793.
Lemma F_1c4bc : fetch_word Ubsan.M.loaded_segments (0x1c4bc : word) = Some W_1c4bc.
Proof. vm_refl. Qed.
Lemma D_1c4bc : decode_any W_1c4bc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4c0 : bv 32 := 0xc85ff0ef.
Lemma F_1c4c0 : fetch_word Ubsan.M.loaded_segments (0x1c4c0 : word) = Some W_1c4c0.
Proof. vm_refl. Qed.
Lemma D_1c4c0 : decode_any W_1c4c0 = Some (Jal 1 2096260, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4c4 : bv 32 := 0x00050a13.
Lemma F_1c4c4 : fetch_word Ubsan.M.loaded_segments (0x1c4c4 : word) = Some W_1c4c4.
Proof. vm_refl. Qed.
Lemma D_1c4c4 : decode_any W_1c4c4 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4c8 : bv 32 := 0x05305863.
Lemma F_1c4c8 : fetch_word Ubsan.M.loaded_segments (0x1c4c8 : word) = Some W_1c4c8.
Proof. vm_refl. Qed.
Lemma D_1c4c8 : decode_any W_1c4c8 = Some (Branch BC_GE 0 19 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4cc : bv 32 := 0x00000b13.
Lemma F_1c4cc : fetch_word Ubsan.M.loaded_segments (0x1c4cc : word) = Some W_1c4cc.
Proof. vm_refl. Qed.
Lemma D_1c4cc : decode_any W_1c4cc = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4d0 : bv 32 := 0xfff98a9b.
Lemma F_1c4d0 : fetch_word Ubsan.M.loaded_segments (0x1c4d0 : word) = Some W_1c4d0.
Proof. vm_refl. Qed.
Lemma D_1c4d0 : decode_any W_1c4d0 = Some (OpImm32 21 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4d4 : bv 32 := 0xfff00b93.
Lemma F_1c4d4 : fetch_word Ubsan.M.loaded_segments (0x1c4d4 : word) = Some W_1c4d4.
Proof. vm_refl. Qed.
Lemma D_1c4d4 : decode_any W_1c4d4 = Some (OpImm ALU_ADD 23 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4d8 : bv 32 := 0x016988b3.
Lemma F_1c4d8 : fetch_word Ubsan.M.loaded_segments (0x1c4d8 : word) = Some W_1c4d8.
Proof. vm_refl. Qed.
Lemma D_1c4d8 : decode_any W_1c4d8 = Some (Op ALU_ADD 17 19 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4dc : bv 32 := 0x0169853b.
Lemma F_1c4dc : fetch_word Ubsan.M.loaded_segments (0x1c4dc : word) = Some W_1c4dc.
Proof. vm_refl. Qed.
Lemma D_1c4dc : decode_any W_1c4dc = Some (Op32 ALU_ADD 10 19 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4e0 : bv 32 := 0x25151c63.
Lemma F_1c4e0 : fetch_word Ubsan.M.loaded_segments (0x1c4e0 : word) = Some W_1c4e0.
Proof. vm_refl. Qed.
Lemma D_1c4e0 : decode_any W_1c4e0 = Some (Branch BC_NE 10 17 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4e4 : bv 32 := 0x01012703.
Lemma F_1c4e4 : fetch_word Ubsan.M.loaded_segments (0x1c4e4 : word) = Some W_1c4e4.
Proof. vm_refl. Qed.
Lemma D_1c4e4 : decode_any W_1c4e4 = Some (Load SZ4 true 14 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4e8 : bv 32 := 0x0008889b.
Lemma F_1c4e8 : fetch_word Ubsan.M.loaded_segments (0x1c4e8 : word) = Some W_1c4e8.
Proof. vm_refl. Qed.
Lemma D_1c4e8 : decode_any W_1c4e8 = Some (OpImm32 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4ec : bv 32 := 0x00100693.
Lemma F_1c4ec : fetch_word Ubsan.M.loaded_segments (0x1c4ec : word) = Some W_1c4ec.
Proof. vm_refl. Qed.
Lemma D_1c4ec : decode_any W_1c4ec = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4f0 : bv 32 := 0x00c00793.
Lemma F_1c4f0 : fetch_word Ubsan.M.loaded_segments (0x1c4f0 : word) = Some W_1c4f0.
Proof. vm_refl. Qed.
Lemma D_1c4f0 : decode_any W_1c4f0 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4f4 : bv 32 := 0x00913023.
Lemma F_1c4f4 : fetch_word Ubsan.M.loaded_segments (0x1c4f4 : word) = Some W_1c4f4.
Proof. vm_refl. Qed.
Lemma D_1c4f4 : decode_any W_1c4f4 = Some (Store SZ8 2 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4f8 : bv 32 := 0x000a0513.
Lemma F_1c4f8 : fetch_word Ubsan.M.loaded_segments (0x1c4f8 : word) = Some W_1c4f8.
Proof. vm_refl. Qed.
Lemma D_1c4f8 : decode_any W_1c4f8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c4fc : bv 32 := 0x000a8593.
Lemma F_1c4fc : fetch_word Ubsan.M.loaded_segments (0x1c4fc : word) = Some W_1c4fc.
Proof. vm_refl. Qed.
Lemma D_1c4fc : decode_any W_1c4fc = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c500 : bv 32 := 0x00048613.
Lemma F_1c500 : fetch_word Ubsan.M.loaded_segments (0x1c500 : word) = Some W_1c500.
Proof. vm_refl. Qed.
Lemma D_1c500 : decode_any W_1c500 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c504 : bv 32 := 0x000a0813.
Lemma F_1c504 : fetch_word Ubsan.M.loaded_segments (0x1c504 : word) = Some W_1c504.
Proof. vm_refl. Qed.
Lemma D_1c504 : decode_any W_1c504 = Some (OpImm ALU_ADD 16 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c508 : bv 32 := 0x6e90a0ef.
Lemma F_1c508 : fetch_word Ubsan.M.loaded_segments (0x1c508 : word) = Some W_1c508.
Proof. vm_refl. Qed.
Lemma D_1c508 : decode_any W_1c508 = Some (Jal 1 44776, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c50c : bv 32 := 0xfffa8a9b.
Lemma F_1c50c : fetch_word Ubsan.M.loaded_segments (0x1c50c : word) = Some W_1c50c.
Proof. vm_refl. Qed.
Lemma D_1c50c : decode_any W_1c50c = Some (OpImm32 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c510 : bv 32 := 0x001b0b1b.
Lemma F_1c510 : fetch_word Ubsan.M.loaded_segments (0x1c510 : word) = Some W_1c510.
Proof. vm_refl. Qed.
Lemma D_1c510 : decode_any W_1c510 = Some (OpImm32 22 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c514 : bv 32 := 0xfd7a92e3.
Lemma F_1c514 : fetch_word Ubsan.M.loaded_segments (0x1c514 : word) = Some W_1c514.
Proof. vm_refl. Qed.
Lemma D_1c514 : decode_any W_1c514 = Some (Branch BC_NE 21 23 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c518 : bv 32 := 0x07205463.
Lemma F_1c518 : fetch_word Ubsan.M.loaded_segments (0x1c518 : word) = Some W_1c518.
Proof. vm_refl. Qed.
Lemma D_1c518 : decode_any W_1c518 = Some (Branch BC_GE 0 18 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c51c : bv 32 := 0x00000a93.
Lemma F_1c51c : fetch_word Ubsan.M.loaded_segments (0x1c51c : word) = Some W_1c51c.
Proof. vm_refl. Qed.
Lemma D_1c51c : decode_any W_1c51c = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c520 : bv 32 := 0x01412583.
Lemma F_1c520 : fetch_word Ubsan.M.loaded_segments (0x1c520 : word) = Some W_1c520.
Proof. vm_refl. Qed.
Lemma D_1c520 : decode_any W_1c520 = Some (Load SZ4 true 11 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c524 : bv 32 := 0x00b98533.
Lemma F_1c524 : fetch_word Ubsan.M.loaded_segments (0x1c524 : word) = Some W_1c524.
Proof. vm_refl. Qed.
Lemma D_1c524 : decode_any W_1c524 = Some (Op ALU_ADD 10 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c528 : bv 32 := 0x00b985bb.
Lemma F_1c528 : fetch_word Ubsan.M.loaded_segments (0x1c528 : word) = Some W_1c528.
Proof. vm_refl. Qed.
Lemma D_1c528 : decode_any W_1c528 = Some (Op32 ALU_ADD 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c52c : bv 32 := 0x20a59663.
Lemma F_1c52c : fetch_word Ubsan.M.loaded_segments (0x1c52c : word) = Some W_1c52c.
Proof. vm_refl. Qed.
Lemma D_1c52c : decode_any W_1c52c = Some (Branch BC_NE 11 10 524, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c530 : bv 32 := 0x0005061b.
Lemma F_1c530 : fetch_word Ubsan.M.loaded_segments (0x1c530 : word) = Some W_1c530.
Proof. vm_refl. Qed.
Lemma D_1c530 : decode_any W_1c530 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c534 : bv 32 := 0x015605bb.
Lemma F_1c534 : fetch_word Ubsan.M.loaded_segments (0x1c534 : word) = Some W_1c534.
Proof. vm_refl. Qed.
Lemma D_1c534 : decode_any W_1c534 = Some (Op32 ALU_ADD 11 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c538 : bv 32 := 0x015606b3.
Lemma F_1c538 : fetch_word Ubsan.M.loaded_segments (0x1c538 : word) = Some W_1c538.
Proof. vm_refl. Qed.
Lemma D_1c538 : decode_any W_1c538 = Some (Op ALU_ADD 13 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c53c : bv 32 := 0x1ed59e63.
Lemma F_1c53c : fetch_word Ubsan.M.loaded_segments (0x1c53c : word) = Some W_1c53c.
Proof. vm_refl. Qed.
Lemma D_1c53c : decode_any W_1c53c = Some (Branch BC_NE 11 13 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c540 : bv 32 := 0xfff5051b.
Lemma F_1c540 : fetch_word Ubsan.M.loaded_segments (0x1c540 : word) = Some W_1c540.
Proof. vm_refl. Qed.
Lemma D_1c540 : decode_any W_1c540 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c544 : bv 32 := 0x1ec55a63.
Lemma F_1c544 : fetch_word Ubsan.M.loaded_segments (0x1c544 : word) = Some W_1c544.
Proof. vm_refl. Qed.
Lemma D_1c544 : decode_any W_1c544 = Some (Branch BC_GE 10 12 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c548 : bv 32 := 0x415508b3.
Lemma F_1c548 : fetch_word Ubsan.M.loaded_segments (0x1c548 : word) = Some W_1c548.
Proof. vm_refl. Qed.
Lemma D_1c548 : decode_any W_1c548 = Some (Op ALU_SUB 17 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c54c : bv 32 := 0x4155053b.
Lemma F_1c54c : fetch_word Ubsan.M.loaded_segments (0x1c54c : word) = Some W_1c54c.
Proof. vm_refl. Qed.
Lemma D_1c54c : decode_any W_1c54c = Some (Op32 ALU_SUB 10 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c550 : bv 32 := 0x1f151463.
Lemma F_1c550 : fetch_word Ubsan.M.loaded_segments (0x1c550 : word) = Some W_1c550.
Proof. vm_refl. Qed.
Lemma D_1c550 : decode_any W_1c550 = Some (Branch BC_NE 10 17 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c554 : bv 32 := 0x01012703.
Lemma F_1c554 : fetch_word Ubsan.M.loaded_segments (0x1c554 : word) = Some W_1c554.
Proof. vm_refl. Qed.
Lemma D_1c554 : decode_any W_1c554 = Some (Load SZ4 true 14 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c558 : bv 32 := 0x0008889b.
Lemma F_1c558 : fetch_word Ubsan.M.loaded_segments (0x1c558 : word) = Some W_1c558.
Proof. vm_refl. Qed.
Lemma D_1c558 : decode_any W_1c558 = Some (OpImm32 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c55c : bv 32 := 0x00100693.
Lemma F_1c55c : fetch_word Ubsan.M.loaded_segments (0x1c55c : word) = Some W_1c55c.
Proof. vm_refl. Qed.
Lemma D_1c55c : decode_any W_1c55c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c560 : bv 32 := 0x00c00793.
Lemma F_1c560 : fetch_word Ubsan.M.loaded_segments (0x1c560 : word) = Some W_1c560.
Proof. vm_refl. Qed.
Lemma D_1c560 : decode_any W_1c560 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c564 : bv 32 := 0x00913023.
Lemma F_1c564 : fetch_word Ubsan.M.loaded_segments (0x1c564 : word) = Some W_1c564.
Proof. vm_refl. Qed.
Lemma D_1c564 : decode_any W_1c564 = Some (Store SZ8 2 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c568 : bv 32 := 0x000a0513.
Lemma F_1c568 : fetch_word Ubsan.M.loaded_segments (0x1c568 : word) = Some W_1c568.
Proof. vm_refl. Qed.
Lemma D_1c568 : decode_any W_1c568 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c56c : bv 32 := 0x00048613.
Lemma F_1c56c : fetch_word Ubsan.M.loaded_segments (0x1c56c : word) = Some W_1c56c.
Proof. vm_refl. Qed.
Lemma D_1c56c : decode_any W_1c56c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c570 : bv 32 := 0x000a0813.
Lemma F_1c570 : fetch_word Ubsan.M.loaded_segments (0x1c570 : word) = Some W_1c570.
Proof. vm_refl. Qed.
Lemma D_1c570 : decode_any W_1c570 = Some (OpImm ALU_ADD 16 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c574 : bv 32 := 0x67d0a0ef.
Lemma F_1c574 : fetch_word Ubsan.M.loaded_segments (0x1c574 : word) = Some W_1c574.
Proof. vm_refl. Qed.
Lemma D_1c574 : decode_any W_1c574 = Some (Jal 1 44668, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c578 : bv 32 := 0x001a8a9b.
Lemma F_1c578 : fetch_word Ubsan.M.loaded_segments (0x1c578 : word) = Some W_1c578.
Proof. vm_refl. Qed.
Lemma D_1c578 : decode_any W_1c578 = Some (OpImm32 21 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c57c : bv 32 := 0xfb5912e3.
Lemma F_1c57c : fetch_word Ubsan.M.loaded_segments (0x1c57c : word) = Some W_1c57c.
Proof. vm_refl. Qed.
Lemma D_1c57c : decode_any W_1c57c = Some (Branch BC_NE 18 21 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c580 : bv 32 := 0x06905863.
Lemma F_1c580 : fetch_word Ubsan.M.loaded_segments (0x1c580 : word) = Some W_1c580.
Proof. vm_refl. Qed.
Lemma D_1c580 : decode_any W_1c580 = Some (Branch BC_GE 0 9 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c584 : bv 32 := 0x00000b13.
Lemma F_1c584 : fetch_word Ubsan.M.loaded_segments (0x1c584 : word) = Some W_1c584.
Proof. vm_refl. Qed.
Lemma D_1c584 : decode_any W_1c584 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c588 : bv 32 := 0xfff48a9b.
Lemma F_1c588 : fetch_word Ubsan.M.loaded_segments (0x1c588 : word) = Some W_1c588.
Proof. vm_refl. Qed.
Lemma D_1c588 : decode_any W_1c588 = Some (OpImm32 21 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c58c : bv 32 := 0xfff00b93.
Lemma F_1c58c : fetch_word Ubsan.M.loaded_segments (0x1c58c : word) = Some W_1c58c.
Proof. vm_refl. Qed.
Lemma D_1c58c : decode_any W_1c58c = Some (OpImm ALU_ADD 23 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c590 : bv 32 := 0x01412583.
Lemma F_1c590 : fetch_word Ubsan.M.loaded_segments (0x1c590 : word) = Some W_1c590.
Proof. vm_refl. Qed.
Lemma D_1c590 : decode_any W_1c590 = Some (Load SZ4 true 11 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c594 : bv 32 := 0x00b98533.
Lemma F_1c594 : fetch_word Ubsan.M.loaded_segments (0x1c594 : word) = Some W_1c594.
Proof. vm_refl. Qed.
Lemma D_1c594 : decode_any W_1c594 = Some (Op ALU_ADD 10 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c598 : bv 32 := 0x00b985bb.
Lemma F_1c598 : fetch_word Ubsan.M.loaded_segments (0x1c598 : word) = Some W_1c598.
Proof. vm_refl. Qed.
Lemma D_1c598 : decode_any W_1c598 = Some (Op32 ALU_ADD 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c59c : bv 32 := 0x18a59e63.
Lemma F_1c59c : fetch_word Ubsan.M.loaded_segments (0x1c59c : word) = Some W_1c59c.
Proof. vm_refl. Qed.
Lemma D_1c59c : decode_any W_1c59c = Some (Branch BC_NE 11 10 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5a0 : bv 32 := 0x0005051b.
Lemma F_1c5a0 : fetch_word Ubsan.M.loaded_segments (0x1c5a0 : word) = Some W_1c5a0.
Proof. vm_refl. Qed.
Lemma D_1c5a0 : decode_any W_1c5a0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5a4 : bv 32 := 0x012506bb.
Lemma F_1c5a4 : fetch_word Ubsan.M.loaded_segments (0x1c5a4 : word) = Some W_1c5a4.
Proof. vm_refl. Qed.
Lemma D_1c5a4 : decode_any W_1c5a4 = Some (Op32 ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5a8 : bv 32 := 0x01250533.
Lemma F_1c5a8 : fetch_word Ubsan.M.loaded_segments (0x1c5a8 : word) = Some W_1c5a8.
Proof. vm_refl. Qed.
Lemma D_1c5a8 : decode_any W_1c5a8 = Some (Op ALU_ADD 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5ac : bv 32 := 0x18a69663.
Lemma F_1c5ac : fetch_word Ubsan.M.loaded_segments (0x1c5ac : word) = Some W_1c5ac.
Proof. vm_refl. Qed.
Lemma D_1c5ac : decode_any W_1c5ac = Some (Branch BC_NE 13 10 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5b0 : bv 32 := 0x01648533.
Lemma F_1c5b0 : fetch_word Ubsan.M.loaded_segments (0x1c5b0 : word) = Some W_1c5b0.
Proof. vm_refl. Qed.
Lemma D_1c5b0 : decode_any W_1c5b0 = Some (Op ALU_ADD 10 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5b4 : bv 32 := 0x016485bb.
Lemma F_1c5b4 : fetch_word Ubsan.M.loaded_segments (0x1c5b4 : word) = Some W_1c5b4.
Proof. vm_refl. Qed.
Lemma D_1c5b4 : decode_any W_1c5b4 = Some (Op32 ALU_ADD 11 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5b8 : bv 32 := 0x18a59063.
Lemma F_1c5b8 : fetch_word Ubsan.M.loaded_segments (0x1c5b8 : word) = Some W_1c5b8.
Proof. vm_refl. Qed.
Lemma D_1c5b8 : decode_any W_1c5b8 = Some (Branch BC_NE 11 10 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5bc : bv 32 := 0x0005051b.
Lemma F_1c5bc : fetch_word Ubsan.M.loaded_segments (0x1c5bc : word) = Some W_1c5bc.
Proof. vm_refl. Qed.
Lemma D_1c5bc : decode_any W_1c5bc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5c0 : bv 32 := 0x00100713.
Lemma F_1c5c0 : fetch_word Ubsan.M.loaded_segments (0x1c5c0 : word) = Some W_1c5c0.
Proof. vm_refl. Qed.
Lemma D_1c5c0 : decode_any W_1c5c0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5c4 : bv 32 := 0x00c00793.
Lemma F_1c5c4 : fetch_word Ubsan.M.loaded_segments (0x1c5c4 : word) = Some W_1c5c4.
Proof. vm_refl. Qed.
Lemma D_1c5c4 : decode_any W_1c5c4 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5c8 : bv 32 := 0x00a13023.
Lemma F_1c5c8 : fetch_word Ubsan.M.loaded_segments (0x1c5c8 : word) = Some W_1c5c8.
Proof. vm_refl. Qed.
Lemma D_1c5c8 : decode_any W_1c5c8 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5cc : bv 32 := 0x000a0513.
Lemma F_1c5cc : fetch_word Ubsan.M.loaded_segments (0x1c5cc : word) = Some W_1c5cc.
Proof. vm_refl. Qed.
Lemma D_1c5cc : decode_any W_1c5cc = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5d0 : bv 32 := 0x00000593.
Lemma F_1c5d0 : fetch_word Ubsan.M.loaded_segments (0x1c5d0 : word) = Some W_1c5d0.
Proof. vm_refl. Qed.
Lemma D_1c5d0 : decode_any W_1c5d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5d4 : bv 32 := 0x000a8613.
Lemma F_1c5d4 : fetch_word Ubsan.M.loaded_segments (0x1c5d4 : word) = Some W_1c5d4.
Proof. vm_refl. Qed.
Lemma D_1c5d4 : decode_any W_1c5d4 = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5d8 : bv 32 := 0x000a0813.
Lemma F_1c5d8 : fetch_word Ubsan.M.loaded_segments (0x1c5d8 : word) = Some W_1c5d8.
Proof. vm_refl. Qed.
Lemma D_1c5d8 : decode_any W_1c5d8 = Some (OpImm ALU_ADD 16 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5dc : bv 32 := 0x00000893.
Lemma F_1c5dc : fetch_word Ubsan.M.loaded_segments (0x1c5dc : word) = Some W_1c5dc.
Proof. vm_refl. Qed.
Lemma D_1c5dc : decode_any W_1c5dc = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5e0 : bv 32 := 0x6110a0ef.
Lemma F_1c5e0 : fetch_word Ubsan.M.loaded_segments (0x1c5e0 : word) = Some W_1c5e0.
Proof. vm_refl. Qed.
Lemma D_1c5e0 : decode_any W_1c5e0 = Some (Jal 1 44560, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5e4 : bv 32 := 0xfffa8a9b.
Lemma F_1c5e4 : fetch_word Ubsan.M.loaded_segments (0x1c5e4 : word) = Some W_1c5e4.
Proof. vm_refl. Qed.
Lemma D_1c5e4 : decode_any W_1c5e4 = Some (OpImm32 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5e8 : bv 32 := 0x001b0b1b.
Lemma F_1c5e8 : fetch_word Ubsan.M.loaded_segments (0x1c5e8 : word) = Some W_1c5e8.
Proof. vm_refl. Qed.
Lemma D_1c5e8 : decode_any W_1c5e8 = Some (OpImm32 22 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5ec : bv 32 := 0xfb7a92e3.
Lemma F_1c5ec : fetch_word Ubsan.M.loaded_segments (0x1c5ec : word) = Some W_1c5ec.
Proof. vm_refl. Qed.
Lemma D_1c5ec : decode_any W_1c5ec = Some (Branch BC_NE 21 23 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5f0 : bv 32 := 0x10805c63.
Lemma F_1c5f0 : fetch_word Ubsan.M.loaded_segments (0x1c5f0 : word) = Some W_1c5f0.
Proof. vm_refl. Qed.
Lemma D_1c5f0 : decode_any W_1c5f0 = Some (Branch BC_GE 0 8 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5f4 : bv 32 := 0x00000a93.
Lemma F_1c5f4 : fetch_word Ubsan.M.loaded_segments (0x1c5f4 : word) = Some W_1c5f4.
Proof. vm_refl. Qed.
Lemma D_1c5f4 : decode_any W_1c5f4 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5f8 : bv 32 := 0x01012583.
Lemma F_1c5f8 : fetch_word Ubsan.M.loaded_segments (0x1c5f8 : word) = Some W_1c5f8.
Proof. vm_refl. Qed.
Lemma D_1c5f8 : decode_any W_1c5f8 = Some (Load SZ4 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5fc : bv 32 := 0x00b48533.
Lemma F_1c5fc : fetch_word Ubsan.M.loaded_segments (0x1c5fc : word) = Some W_1c5fc.
Proof. vm_refl. Qed.
Lemma D_1c5fc : decode_any W_1c5fc = Some (Op ALU_ADD 10 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c600 : bv 32 := 0x00b485bb.
Lemma F_1c600 : fetch_word Ubsan.M.loaded_segments (0x1c600 : word) = Some W_1c600.
Proof. vm_refl. Qed.
Lemma D_1c600 : decode_any W_1c600 = Some (Op32 ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c604 : bv 32 := 0x12a59a63.
Lemma F_1c604 : fetch_word Ubsan.M.loaded_segments (0x1c604 : word) = Some W_1c604.
Proof. vm_refl. Qed.
Lemma D_1c604 : decode_any W_1c604 = Some (Branch BC_NE 11 10 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c608 : bv 32 := 0x0005059b.
Lemma F_1c608 : fetch_word Ubsan.M.loaded_segments (0x1c608 : word) = Some W_1c608.
Proof. vm_refl. Qed.
Lemma D_1c608 : decode_any W_1c608 = Some (OpImm32 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c60c : bv 32 := 0x0155863b.
Lemma F_1c60c : fetch_word Ubsan.M.loaded_segments (0x1c60c : word) = Some W_1c60c.
Proof. vm_refl. Qed.
Lemma D_1c60c : decode_any W_1c60c = Some (Op32 ALU_ADD 12 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c610 : bv 32 := 0x015586b3.
Lemma F_1c610 : fetch_word Ubsan.M.loaded_segments (0x1c610 : word) = Some W_1c610.
Proof. vm_refl. Qed.
Lemma D_1c610 : decode_any W_1c610 = Some (Op ALU_ADD 13 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c614 : bv 32 := 0x12d61263.
Lemma F_1c614 : fetch_word Ubsan.M.loaded_segments (0x1c614 : word) = Some W_1c614.
Proof. vm_refl. Qed.
Lemma D_1c614 : decode_any W_1c614 = Some (Branch BC_NE 12 13 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c618 : bv 32 := 0x01412703.
Lemma F_1c618 : fetch_word Ubsan.M.loaded_segments (0x1c618 : word) = Some W_1c618.
Proof. vm_refl. Qed.
Lemma D_1c618 : decode_any W_1c618 = Some (Load SZ4 true 14 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c61c : bv 32 := 0x00e986b3.
Lemma F_1c61c : fetch_word Ubsan.M.loaded_segments (0x1c61c : word) = Some W_1c61c.
Proof. vm_refl. Qed.
Lemma D_1c61c : decode_any W_1c61c = Some (Op ALU_ADD 13 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c620 : bv 32 := 0x00e9873b.
Lemma F_1c620 : fetch_word Ubsan.M.loaded_segments (0x1c620 : word) = Some W_1c620.
Proof. vm_refl. Qed.
Lemma D_1c620 : decode_any W_1c620 = Some (Op32 ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c624 : bv 32 := 0x10d71a63.
Lemma F_1c624 : fetch_word Ubsan.M.loaded_segments (0x1c624 : word) = Some W_1c624.
Proof. vm_refl. Qed.
Lemma D_1c624 : decode_any W_1c624 = Some (Branch BC_NE 14 13 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c628 : bv 32 := 0x0006871b.
Lemma F_1c628 : fetch_word Ubsan.M.loaded_segments (0x1c628 : word) = Some W_1c628.
Proof. vm_refl. Qed.
Lemma D_1c628 : decode_any W_1c628 = Some (OpImm32 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c62c : bv 32 := 0x012706bb.
Lemma F_1c62c : fetch_word Ubsan.M.loaded_segments (0x1c62c : word) = Some W_1c62c.
Proof. vm_refl. Qed.
Lemma D_1c62c : decode_any W_1c62c = Some (Op32 ALU_ADD 13 14 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c630 : bv 32 := 0x01270733.
Lemma F_1c630 : fetch_word Ubsan.M.loaded_segments (0x1c630 : word) = Some W_1c630.
Proof. vm_refl. Qed.
Lemma D_1c630 : decode_any W_1c630 = Some (Op ALU_ADD 14 14 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c634 : bv 32 := 0x10e69263.
Lemma F_1c634 : fetch_word Ubsan.M.loaded_segments (0x1c634 : word) = Some W_1c634.
Proof. vm_refl. Qed.
Lemma D_1c634 : decode_any W_1c634 = Some (Branch BC_NE 13 14 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c638 : bv 32 := 0xfff5071b.
Lemma F_1c638 : fetch_word Ubsan.M.loaded_segments (0x1c638 : word) = Some W_1c638.
Proof. vm_refl. Qed.
Lemma D_1c638 : decode_any W_1c638 = Some (OpImm32 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c63c : bv 32 := 0x0eb75e63.
Lemma F_1c63c : fetch_word Ubsan.M.loaded_segments (0x1c63c : word) = Some W_1c63c.
Proof. vm_refl. Qed.
Lemma D_1c63c : decode_any W_1c63c = Some (Branch BC_GE 14 11 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c640 : bv 32 := 0x41570533.
Lemma F_1c640 : fetch_word Ubsan.M.loaded_segments (0x1c640 : word) = Some W_1c640.
Proof. vm_refl. Qed.
Lemma D_1c640 : decode_any W_1c640 = Some (Op ALU_SUB 10 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c644 : bv 32 := 0x415705bb.
Lemma F_1c644 : fetch_word Ubsan.M.loaded_segments (0x1c644 : word) = Some W_1c644.
Proof. vm_refl. Qed.
Lemma D_1c644 : decode_any W_1c644 = Some (Op32 ALU_SUB 11 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c648 : bv 32 := 0x0ea59863.
Lemma F_1c648 : fetch_word Ubsan.M.loaded_segments (0x1c648 : word) = Some W_1c648.
Proof. vm_refl. Qed.
Lemma D_1c648 : decode_any W_1c648 = Some (Branch BC_NE 11 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c64c : bv 32 := 0x0005051b.
Lemma F_1c64c : fetch_word Ubsan.M.loaded_segments (0x1c64c : word) = Some W_1c64c.
Proof. vm_refl. Qed.
Lemma D_1c64c : decode_any W_1c64c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c650 : bv 32 := 0x00100713.
Lemma F_1c650 : fetch_word Ubsan.M.loaded_segments (0x1c650 : word) = Some W_1c650.
Proof. vm_refl. Qed.
Lemma D_1c650 : decode_any W_1c650 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c654 : bv 32 := 0x00c00793.
Lemma F_1c654 : fetch_word Ubsan.M.loaded_segments (0x1c654 : word) = Some W_1c654.
Proof. vm_refl. Qed.
Lemma D_1c654 : decode_any W_1c654 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c658 : bv 32 := 0x00a13023.
Lemma F_1c658 : fetch_word Ubsan.M.loaded_segments (0x1c658 : word) = Some W_1c658.
Proof. vm_refl. Qed.
Lemma D_1c658 : decode_any W_1c658 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c65c : bv 32 := 0x000a0513.
Lemma F_1c65c : fetch_word Ubsan.M.loaded_segments (0x1c65c : word) = Some W_1c65c.
Proof. vm_refl. Qed.
Lemma D_1c65c : decode_any W_1c65c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c660 : bv 32 := 0x00000593.
Lemma F_1c660 : fetch_word Ubsan.M.loaded_segments (0x1c660 : word) = Some W_1c660.
Proof. vm_refl. Qed.
Lemma D_1c660 : decode_any W_1c660 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c664 : bv 32 := 0x000a0813.
Lemma F_1c664 : fetch_word Ubsan.M.loaded_segments (0x1c664 : word) = Some W_1c664.
Proof. vm_refl. Qed.
Lemma D_1c664 : decode_any W_1c664 = Some (OpImm ALU_ADD 16 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c668 : bv 32 := 0x00000893.
Lemma F_1c668 : fetch_word Ubsan.M.loaded_segments (0x1c668 : word) = Some W_1c668.
Proof. vm_refl. Qed.
Lemma D_1c668 : decode_any W_1c668 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c66c : bv 32 := 0x5850a0ef.
Lemma F_1c66c : fetch_word Ubsan.M.loaded_segments (0x1c66c : word) = Some W_1c66c.
Proof. vm_refl. Qed.
Lemma D_1c66c : decode_any W_1c66c = Some (Jal 1 44420, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c670 : bv 32 := 0x001a8a9b.
Lemma F_1c670 : fetch_word Ubsan.M.loaded_segments (0x1c670 : word) = Some W_1c670.
Proof. vm_refl. Qed.
Lemma D_1c670 : decode_any W_1c670 = Some (OpImm32 21 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c674 : bv 32 := 0xf95412e3.
Lemma F_1c674 : fetch_word Ubsan.M.loaded_segments (0x1c674 : word) = Some W_1c674.
Proof. vm_refl. Qed.
Lemma D_1c674 : decode_any W_1c674 = Some (Branch BC_NE 8 21 8068, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c678 : bv 32 := 0x0900006f.
Lemma F_1c678 : fetch_word Ubsan.M.loaded_segments (0x1c678 : word) = Some W_1c678.
Proof. vm_refl. Qed.
Lemma D_1c678 : decode_any W_1c678 = Some (Jal 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c67c : bv 32 := 0x00029517.
Lemma F_1c67c : fetch_word Ubsan.M.loaded_segments (0x1c67c : word) = Some W_1c67c.
Proof. vm_refl. Qed.
Lemma D_1c67c : decode_any W_1c67c = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c680 : bv 32 := 0x81c53503.
Lemma F_1c680 : fetch_word Ubsan.M.loaded_segments (0x1c680 : word) = Some W_1c680.
Proof. vm_refl. Qed.
Lemma D_1c680 : decode_any W_1c680 = Some (Load SZ8 true 10 10 2076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c684 : bv 32 := 0x00052503.
Lemma F_1c684 : fetch_word Ubsan.M.loaded_segments (0x1c684 : word) = Some W_1c684.
Proof. vm_refl. Qed.
Lemma D_1c684 : decode_any W_1c684 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c688 : bv 32 := 0x00500593.
Lemma F_1c688 : fetch_word Ubsan.M.loaded_segments (0x1c688 : word) = Some W_1c688.
Proof. vm_refl. Qed.
Lemma D_1c688 : decode_any W_1c688 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c68c : bv 32 := 0x06a5cc63.
Lemma F_1c68c : fetch_word Ubsan.M.loaded_segments (0x1c68c : word) = Some W_1c68c.
Proof. vm_refl. Qed.
Lemma D_1c68c : decode_any W_1c68c = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c690 : bv 32 := 0xffff6517.
Lemma F_1c690 : fetch_word Ubsan.M.loaded_segments (0x1c690 : word) = Some W_1c690.
Proof. vm_refl. Qed.
Lemma D_1c690 : decode_any W_1c690 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c694 : bv 32 := 0xffff4597.
Lemma F_1c694 : fetch_word Ubsan.M.loaded_segments (0x1c694 : word) = Some W_1c694.
Proof. vm_refl. Qed.
Lemma D_1c694 : decode_any W_1c694 = Some (Auipc 11 1048564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c698 : bv 32 := 0xbd950513.
Lemma F_1c698 : fetch_word Ubsan.M.loaded_segments (0x1c698 : word) = Some W_1c698.
Proof. vm_refl. Qed.
Lemma D_1c698 : decode_any W_1c698 = Some (OpImm ALU_ADD 10 10 3033, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c69c : bv 32 := 0xd1b58593.
Lemma F_1c69c : fetch_word Ubsan.M.loaded_segments (0x1c69c : word) = Some W_1c69c.
Proof. vm_refl. Qed.
Lemma D_1c69c : decode_any W_1c69c = Some (OpImm ALU_ADD 11 11 3355, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6a0 : bv 32 := 0x00000613.
Lemma F_1c6a0 : fetch_word Ubsan.M.loaded_segments (0x1c6a0 : word) = Some W_1c6a0.
Proof. vm_refl. Qed.
Lemma D_1c6a0 : decode_any W_1c6a0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6a4 : bv 32 := 0x821fb0ef.
Lemma F_1c6a4 : fetch_word Ubsan.M.loaded_segments (0x1c6a4 : word) = Some W_1c6a4.
Proof. vm_refl. Qed.
Lemma D_1c6a4 : decode_any W_1c6a4 = Some (Jal 1 2078752, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6a8 : bv 32 := 0x00050a13.
Lemma F_1c6a8 : fetch_word Ubsan.M.loaded_segments (0x1c6a8 : word) = Some W_1c6a8.
Proof. vm_refl. Qed.
Lemma D_1c6a8 : decode_any W_1c6a8 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6ac : bv 32 := 0x05c0006f.
Lemma F_1c6ac : fetch_word Ubsan.M.loaded_segments (0x1c6ac : word) = Some W_1c6ac.
Proof. vm_refl. Qed.
Lemma D_1c6ac : decode_any W_1c6ac = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6b0 : bv 32 := 0x00028517.
Lemma F_1c6b0 : fetch_word Ubsan.M.loaded_segments (0x1c6b0 : word) = Some W_1c6b0.
Proof. vm_refl. Qed.
Lemma D_1c6b0 : decode_any W_1c6b0 = Some (Auipc 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6b4 : bv 32 := 0x7e853503.
Lemma F_1c6b4 : fetch_word Ubsan.M.loaded_segments (0x1c6b4 : word) = Some W_1c6b4.
Proof. vm_refl. Qed.
Lemma D_1c6b4 : decode_any W_1c6b4 = Some (Load SZ8 true 10 10 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6b8 : bv 32 := 0x00052503.
Lemma F_1c6b8 : fetch_word Ubsan.M.loaded_segments (0x1c6b8 : word) = Some W_1c6b8.
Proof. vm_refl. Qed.
Lemma D_1c6b8 : decode_any W_1c6b8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6bc : bv 32 := 0x00500593.
Lemma F_1c6bc : fetch_word Ubsan.M.loaded_segments (0x1c6bc : word) = Some W_1c6bc.
Proof. vm_refl. Qed.
Lemma D_1c6bc : decode_any W_1c6bc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6c0 : bv 32 := 0x04a5c263.
Lemma F_1c6c0 : fetch_word Ubsan.M.loaded_segments (0x1c6c0 : word) = Some W_1c6c0.
Proof. vm_refl. Qed.
Lemma D_1c6c0 : decode_any W_1c6c0 = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6c4 : bv 32 := 0xffff4517.
Lemma F_1c6c4 : fetch_word Ubsan.M.loaded_segments (0x1c6c4 : word) = Some W_1c6c4.
Proof. vm_refl. Qed.
Lemma D_1c6c4 : decode_any W_1c6c4 = Some (Auipc 10 1048564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6c8 : bv 32 := 0xffff4597.
Lemma F_1c6c8 : fetch_word Ubsan.M.loaded_segments (0x1c6c8 : word) = Some W_1c6c8.
Proof. vm_refl. Qed.
Lemma D_1c6c8 : decode_any W_1c6c8 = Some (Auipc 11 1048564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6cc : bv 32 := 0xbf050513.
Lemma F_1c6cc : fetch_word Ubsan.M.loaded_segments (0x1c6cc : word) = Some W_1c6cc.
Proof. vm_refl. Qed.
Lemma D_1c6cc : decode_any W_1c6cc = Some (OpImm ALU_ADD 10 10 3056, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6d0 : bv 32 := 0xce758593.
Lemma F_1c6d0 : fetch_word Ubsan.M.loaded_segments (0x1c6d0 : word) = Some W_1c6d0.
Proof. vm_refl. Qed.
Lemma D_1c6d0 : decode_any W_1c6d0 = Some (OpImm ALU_ADD 11 11 3303, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6d4 : bv 32 := 0x00000613.
Lemma F_1c6d4 : fetch_word Ubsan.M.loaded_segments (0x1c6d4 : word) = Some W_1c6d4.
Proof. vm_refl. Qed.
Lemma D_1c6d4 : decode_any W_1c6d4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6d8 : bv 32 := 0x05813083.
Lemma F_1c6d8 : fetch_word Ubsan.M.loaded_segments (0x1c6d8 : word) = Some W_1c6d8.
Proof. vm_refl. Qed.
Lemma D_1c6d8 : decode_any W_1c6d8 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6dc : bv 32 := 0x05013403.
Lemma F_1c6dc : fetch_word Ubsan.M.loaded_segments (0x1c6dc : word) = Some W_1c6dc.
Proof. vm_refl. Qed.
Lemma D_1c6dc : decode_any W_1c6dc = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6e0 : bv 32 := 0x04813483.
Lemma F_1c6e0 : fetch_word Ubsan.M.loaded_segments (0x1c6e0 : word) = Some W_1c6e0.
Proof. vm_refl. Qed.
Lemma D_1c6e0 : decode_any W_1c6e0 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6e4 : bv 32 := 0x04013903.
Lemma F_1c6e4 : fetch_word Ubsan.M.loaded_segments (0x1c6e4 : word) = Some W_1c6e4.
Proof. vm_refl. Qed.
Lemma D_1c6e4 : decode_any W_1c6e4 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6e8 : bv 32 := 0x03813983.
Lemma F_1c6e8 : fetch_word Ubsan.M.loaded_segments (0x1c6e8 : word) = Some W_1c6e8.
Proof. vm_refl. Qed.
Lemma D_1c6e8 : decode_any W_1c6e8 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6ec : bv 32 := 0x03013a03.
Lemma F_1c6ec : fetch_word Ubsan.M.loaded_segments (0x1c6ec : word) = Some W_1c6ec.
Proof. vm_refl. Qed.
Lemma D_1c6ec : decode_any W_1c6ec = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6f0 : bv 32 := 0x02813a83.
Lemma F_1c6f0 : fetch_word Ubsan.M.loaded_segments (0x1c6f0 : word) = Some W_1c6f0.
Proof. vm_refl. Qed.
Lemma D_1c6f0 : decode_any W_1c6f0 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6f4 : bv 32 := 0x02013b03.
Lemma F_1c6f4 : fetch_word Ubsan.M.loaded_segments (0x1c6f4 : word) = Some W_1c6f4.
Proof. vm_refl. Qed.
Lemma D_1c6f4 : decode_any W_1c6f4 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6f8 : bv 32 := 0x01813b83.
Lemma F_1c6f8 : fetch_word Ubsan.M.loaded_segments (0x1c6f8 : word) = Some W_1c6f8.
Proof. vm_refl. Qed.
Lemma D_1c6f8 : decode_any W_1c6f8 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6fc : bv 32 := 0x06010113.
Lemma F_1c6fc : fetch_word Ubsan.M.loaded_segments (0x1c6fc : word) = Some W_1c6fc.
Proof. vm_refl. Qed.
Lemma D_1c6fc : decode_any W_1c6fc = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c700 : bv 32 := 0xfc4fb06f.
Lemma F_1c700 : fetch_word Ubsan.M.loaded_segments (0x1c700 : word) = Some W_1c700.
Proof. vm_refl. Qed.
Lemma D_1c700 : decode_any W_1c700 = Some (Jal 0 2078660, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c704 : bv 32 := 0x00000a13.
Lemma F_1c704 : fetch_word Ubsan.M.loaded_segments (0x1c704 : word) = Some W_1c704.
Proof. vm_refl. Qed.
Lemma D_1c704 : decode_any W_1c704 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c708 : bv 32 := 0x000a0513.
Lemma F_1c708 : fetch_word Ubsan.M.loaded_segments (0x1c708 : word) = Some W_1c708.
Proof. vm_refl. Qed.
Lemma D_1c708 : decode_any W_1c708 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c70c : bv 32 := 0x05813083.
Lemma F_1c70c : fetch_word Ubsan.M.loaded_segments (0x1c70c : word) = Some W_1c70c.
Proof. vm_refl. Qed.
Lemma D_1c70c : decode_any W_1c70c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c710 : bv 32 := 0x05013403.
Lemma F_1c710 : fetch_word Ubsan.M.loaded_segments (0x1c710 : word) = Some W_1c710.
Proof. vm_refl. Qed.
Lemma D_1c710 : decode_any W_1c710 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c714 : bv 32 := 0x04813483.
Lemma F_1c714 : fetch_word Ubsan.M.loaded_segments (0x1c714 : word) = Some W_1c714.
Proof. vm_refl. Qed.
Lemma D_1c714 : decode_any W_1c714 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c718 : bv 32 := 0x04013903.
Lemma F_1c718 : fetch_word Ubsan.M.loaded_segments (0x1c718 : word) = Some W_1c718.
Proof. vm_refl. Qed.
Lemma D_1c718 : decode_any W_1c718 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c71c : bv 32 := 0x03813983.
Lemma F_1c71c : fetch_word Ubsan.M.loaded_segments (0x1c71c : word) = Some W_1c71c.
Proof. vm_refl. Qed.
Lemma D_1c71c : decode_any W_1c71c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c720 : bv 32 := 0x03013a03.
Lemma F_1c720 : fetch_word Ubsan.M.loaded_segments (0x1c720 : word) = Some W_1c720.
Proof. vm_refl. Qed.
Lemma D_1c720 : decode_any W_1c720 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c724 : bv 32 := 0x02813a83.
Lemma F_1c724 : fetch_word Ubsan.M.loaded_segments (0x1c724 : word) = Some W_1c724.
Proof. vm_refl. Qed.
Lemma D_1c724 : decode_any W_1c724 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c728 : bv 32 := 0x02013b03.
Lemma F_1c728 : fetch_word Ubsan.M.loaded_segments (0x1c728 : word) = Some W_1c728.
Proof. vm_refl. Qed.
Lemma D_1c728 : decode_any W_1c728 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c72c : bv 32 := 0x01813b83.
Lemma F_1c72c : fetch_word Ubsan.M.loaded_segments (0x1c72c : word) = Some W_1c72c.
Proof. vm_refl. Qed.
Lemma D_1c72c : decode_any W_1c72c = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c730 : bv 32 := 0x06010113.
Lemma F_1c730 : fetch_word Ubsan.M.loaded_segments (0x1c730 : word) = Some W_1c730.
Proof. vm_refl. Qed.
Lemma D_1c730 : decode_any W_1c730 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c734 : bv 32 := 0x00008067.
Lemma F_1c734 : fetch_word Ubsan.M.loaded_segments (0x1c734 : word) = Some W_1c734.
Proof. vm_refl. Qed.
Lemma D_1c734 : decode_any W_1c734 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c738 : bv 32 := 0xc0001073.
Lemma F_1c738 : fetch_word Ubsan.M.loaded_segments (0x1c738 : word) = Some W_1c738.
Proof. vm_refl. Qed.
Lemma D_1c738 : decode_any W_1c738 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
