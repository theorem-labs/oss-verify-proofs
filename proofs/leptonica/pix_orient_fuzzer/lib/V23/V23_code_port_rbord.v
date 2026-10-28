(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6e2a4 : bv 32 := 0x0035f713.
Lemma F_6e2a4 : fetch_word Ubsan.M.loaded_segments (0x6e2a4 : word) = Some W_6e2a4.
Proof. vm_refl. Qed.
Lemma D_6e2a4 : decode_any W_6e2a4 = Some (OpImm ALU_AND 14 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2a8 : bv 32 := 0x00058663.
Lemma F_6e2a8 : fetch_word Ubsan.M.loaded_segments (0x6e2a8 : word) = Some W_6e2a8.
Proof. vm_refl. Qed.
Lemma D_6e2a8 : decode_any W_6e2a8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2ac : bv 32 := 0x0a071863.
Lemma F_6e2ac : fetch_word Ubsan.M.loaded_segments (0x6e2ac : word) = Some W_6e2ac.
Proof. vm_refl. Qed.
Lemma D_6e2ac : decode_any W_6e2ac = Some (Branch BC_NE 14 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b0 : bv 32 := 0x0005a023.
Lemma F_6e2b0 : fetch_word Ubsan.M.loaded_segments (0x6e2b0 : word) = Some W_6e2b0.
Proof. vm_refl. Qed.
Lemma D_6e2b0 : decode_any W_6e2b0 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b4 : bv 32 := 0x00367793.
Lemma F_6e2b4 : fetch_word Ubsan.M.loaded_segments (0x6e2b4 : word) = Some W_6e2b4.
Proof. vm_refl. Qed.
Lemma D_6e2b4 : decode_any W_6e2b4 = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b8 : bv 32 := 0x00060663.
Lemma F_6e2b8 : fetch_word Ubsan.M.loaded_segments (0x6e2b8 : word) = Some W_6e2b8.
Proof. vm_refl. Qed.
Lemma D_6e2b8 : decode_any W_6e2b8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2bc : bv 32 := 0x0a079063.
Lemma F_6e2bc : fetch_word Ubsan.M.loaded_segments (0x6e2bc : word) = Some W_6e2bc.
Proof. vm_refl. Qed.
Lemma D_6e2bc : decode_any W_6e2bc = Some (Branch BC_NE 15 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c0 : bv 32 := 0x00062023.
Lemma F_6e2c0 : fetch_word Ubsan.M.loaded_segments (0x6e2c0 : word) = Some W_6e2c0.
Proof. vm_refl. Qed.
Lemma D_6e2c0 : decode_any W_6e2c0 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c4 : bv 32 := 0x0036f813.
Lemma F_6e2c4 : fetch_word Ubsan.M.loaded_segments (0x6e2c4 : word) = Some W_6e2c4.
Proof. vm_refl. Qed.
Lemma D_6e2c4 : decode_any W_6e2c4 = Some (OpImm ALU_AND 16 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c8 : bv 32 := 0x00068663.
Lemma F_6e2c8 : fetch_word Ubsan.M.loaded_segments (0x6e2c8 : word) = Some W_6e2c8.
Proof. vm_refl. Qed.
Lemma D_6e2c8 : decode_any W_6e2c8 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2cc : bv 32 := 0x08081863.
Lemma F_6e2cc : fetch_word Ubsan.M.loaded_segments (0x6e2cc : word) = Some W_6e2cc.
Proof. vm_refl. Qed.
Lemma D_6e2cc : decode_any W_6e2cc = Some (Branch BC_NE 16 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d0 : bv 32 := 0x0006a023.
Lemma F_6e2d0 : fetch_word Ubsan.M.loaded_segments (0x6e2d0 : word) = Some W_6e2d0.
Proof. vm_refl. Qed.
Lemma D_6e2d0 : decode_any W_6e2d0 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d4 : bv 32 := 0x04050663.
Lemma F_6e2d4 : fetch_word Ubsan.M.loaded_segments (0x6e2d4 : word) = Some W_6e2d4.
Proof. vm_refl. Qed.
Lemma D_6e2d4 : decode_any W_6e2d4 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d8 : bv 32 := 0x00757893.
Lemma F_6e2d8 : fetch_word Ubsan.M.loaded_segments (0x6e2d8 : word) = Some W_6e2d8.
Proof. vm_refl. Qed.
Lemma D_6e2d8 : decode_any W_6e2d8 = Some (OpImm ALU_AND 17 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2dc : bv 32 := 0x00058a63.
Lemma F_6e2dc : fetch_word Ubsan.M.loaded_segments (0x6e2dc : word) = Some W_6e2dc.
Proof. vm_refl. Qed.
Lemma D_6e2dc : decode_any W_6e2dc = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e0 : bv 32 := 0x00e8e733.
Lemma F_6e2e0 : fetch_word Ubsan.M.loaded_segments (0x6e2e0 : word) = Some W_6e2e0.
Proof. vm_refl. Qed.
Lemma D_6e2e0 : decode_any W_6e2e0 = Some (Op ALU_OR 14 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e4 : bv 32 := 0x06071c63.
Lemma F_6e2e4 : fetch_word Ubsan.M.loaded_segments (0x6e2e4 : word) = Some W_6e2e4.
Proof. vm_refl. Qed.
Lemma D_6e2e4 : decode_any W_6e2e4 = Some (Branch BC_NE 14 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e8 : bv 32 := 0x00052703.
Lemma F_6e2e8 : fetch_word Ubsan.M.loaded_segments (0x6e2e8 : word) = Some W_6e2e8.
Proof. vm_refl. Qed.
Lemma D_6e2e8 : decode_any W_6e2e8 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2ec : bv 32 := 0x00e5a023.
Lemma F_6e2ec : fetch_word Ubsan.M.loaded_segments (0x6e2ec : word) = Some W_6e2ec.
Proof. vm_refl. Qed.
Lemma D_6e2ec : decode_any W_6e2ec = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f0 : bv 32 := 0x00060a63.
Lemma F_6e2f0 : fetch_word Ubsan.M.loaded_segments (0x6e2f0 : word) = Some W_6e2f0.
Proof. vm_refl. Qed.
Lemma D_6e2f0 : decode_any W_6e2f0 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f4 : bv 32 := 0x00f8e5b3.
Lemma F_6e2f4 : fetch_word Ubsan.M.loaded_segments (0x6e2f4 : word) = Some W_6e2f4.
Proof. vm_refl. Qed.
Lemma D_6e2f4 : decode_any W_6e2f4 = Some (Op ALU_OR 11 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f8 : bv 32 := 0x06059263.
Lemma F_6e2f8 : fetch_word Ubsan.M.loaded_segments (0x6e2f8 : word) = Some W_6e2f8.
Proof. vm_refl. Qed.
Lemma D_6e2f8 : decode_any W_6e2f8 = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2fc : bv 32 := 0x00452583.
Lemma F_6e2fc : fetch_word Ubsan.M.loaded_segments (0x6e2fc : word) = Some W_6e2fc.
Proof. vm_refl. Qed.
Lemma D_6e2fc : decode_any W_6e2fc = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e300 : bv 32 := 0x00b62023.
Lemma F_6e300 : fetch_word Ubsan.M.loaded_segments (0x6e300 : word) = Some W_6e300.
Proof. vm_refl. Qed.
Lemma D_6e300 : decode_any W_6e300 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e304 : bv 32 := 0x04068463.
Lemma F_6e304 : fetch_word Ubsan.M.loaded_segments (0x6e304 : word) = Some W_6e304.
Proof. vm_refl. Qed.
Lemma D_6e304 : decode_any W_6e304 = Some (Branch BC_EQ 13 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e308 : bv 32 := 0x0108e5b3.
Lemma F_6e308 : fetch_word Ubsan.M.loaded_segments (0x6e308 : word) = Some W_6e308.
Proof. vm_refl. Qed.
Lemma D_6e308 : decode_any W_6e308 = Some (Op ALU_OR 11 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e30c : bv 32 := 0x04059863.
Lemma F_6e30c : fetch_word Ubsan.M.loaded_segments (0x6e30c : word) = Some W_6e30c.
Proof. vm_refl. Qed.
Lemma D_6e30c : decode_any W_6e30c = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e310 : bv 32 := 0x00852503.
Lemma F_6e310 : fetch_word Ubsan.M.loaded_segments (0x6e310 : word) = Some W_6e310.
Proof. vm_refl. Qed.
Lemma D_6e310 : decode_any W_6e310 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e314 : bv 32 := 0x00a6a023.
Lemma F_6e314 : fetch_word Ubsan.M.loaded_segments (0x6e314 : word) = Some W_6e314.
Proof. vm_refl. Qed.
Lemma D_6e314 : decode_any W_6e314 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e318 : bv 32 := 0x00058513.
Lemma F_6e318 : fetch_word Ubsan.M.loaded_segments (0x6e318 : word) = Some W_6e318.
Proof. vm_refl. Qed.
Lemma D_6e318 : decode_any W_6e318 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e31c : bv 32 := 0x00008067.
Lemma F_6e31c : fetch_word Ubsan.M.loaded_segments (0x6e31c : word) = Some W_6e31c.
Proof. vm_refl. Qed.
Lemma D_6e31c : decode_any W_6e31c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e360 : bv 32 := 0x02050663.
Lemma F_6e360 : fetch_word Ubsan.M.loaded_segments (0x6e360 : word) = Some W_6e360.
Proof. vm_refl. Qed.
Lemma D_6e360 : decode_any W_6e360 = Some (Branch BC_EQ 10 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e364 : bv 32 := 0x04058a63.
Lemma F_6e364 : fetch_word Ubsan.M.loaded_segments (0x6e364 : word) = Some W_6e364.
Proof. vm_refl. Qed.
Lemma D_6e364 : decode_any W_6e364 = Some (Branch BC_EQ 11 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e368 : bv 32 := 0x0ca58463.
Lemma F_6e368 : fetch_word Ubsan.M.loaded_segments (0x6e368 : word) = Some W_6e368.
Proof. vm_refl. Qed.
Lemma D_6e368 : decode_any W_6e368 = Some (Branch BC_EQ 11 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e36c : bv 32 := 0x0075f613.
Lemma F_6e36c : fetch_word Ubsan.M.loaded_segments (0x6e36c : word) = Some W_6e36c.
Proof. vm_refl. Qed.
Lemma D_6e36c : decode_any W_6e36c = Some (OpImm ALU_AND 12 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e370 : bv 32 := 0x0c061463.
Lemma F_6e370 : fetch_word Ubsan.M.loaded_segments (0x6e370 : word) = Some W_6e370.
Proof. vm_refl. Qed.
Lemma D_6e370 : decode_any W_6e370 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e374 : bv 32 := 0x00c5a583.
Lemma F_6e374 : fetch_word Ubsan.M.loaded_segments (0x6e374 : word) = Some W_6e374.
Proof. vm_refl. Qed.
Lemma D_6e374 : decode_any W_6e374 = Some (Load SZ4 true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e378 : bv 32 := 0x06b05a63.
Lemma F_6e378 : fetch_word Ubsan.M.loaded_segments (0x6e378 : word) = Some W_6e378.
Proof. vm_refl. Qed.
Lemma D_6e378 : decode_any W_6e378 = Some (Branch BC_GE 0 11 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e37c : bv 32 := 0x00757613.
Lemma F_6e37c : fetch_word Ubsan.M.loaded_segments (0x6e37c : word) = Some W_6e37c.
Proof. vm_refl. Qed.
Lemma D_6e37c : decode_any W_6e37c = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e380 : bv 32 := 0x0a061c63.
Lemma F_6e380 : fetch_word Ubsan.M.loaded_segments (0x6e380 : word) = Some W_6e380.
Proof. vm_refl. Qed.
Lemma D_6e380 : decode_any W_6e380 = Some (Branch BC_NE 12 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e384 : bv 32 := 0x00b52623.
Lemma F_6e384 : fetch_word Ubsan.M.loaded_segments (0x6e384 : word) = Some W_6e384.
Proof. vm_refl. Qed.
Lemma D_6e384 : decode_any W_6e384 = Some (Store SZ4 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e388 : bv 32 := 0x0a80006f.
Lemma F_6e388 : fetch_word Ubsan.M.loaded_segments (0x6e388 : word) = Some W_6e388.
Proof. vm_refl. Qed.
Lemma D_6e388 : decode_any W_6e388 = Some (Jal 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e430 : bv 32 := 0x00000513.
Lemma F_6e430 : fetch_word Ubsan.M.loaded_segments (0x6e430 : word) = Some W_6e430.
Proof. vm_refl. Qed.
Lemma D_6e430 : decode_any W_6e430 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e434 : bv 32 := 0x00008067.
Lemma F_6e434 : fetch_word Ubsan.M.loaded_segments (0x6e434 : word) = Some W_6e434.
Proof. vm_refl. Qed.
Lemma D_6e434 : decode_any W_6e434 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f114 : bv 32 := 0x00050a63.
Lemma F_6f114 : fetch_word Ubsan.M.loaded_segments (0x6f114 : word) = Some W_6f114.
Proof. vm_refl. Qed.
Lemma D_6f114 : decode_any W_6f114 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f118 : bv 32 := 0x00757593.
Lemma F_6f118 : fetch_word Ubsan.M.loaded_segments (0x6f118 : word) = Some W_6f118.
Proof. vm_refl. Qed.
Lemma D_6f118 : decode_any W_6f118 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f11c : bv 32 := 0x04059063.
Lemma F_6f11c : fetch_word Ubsan.M.loaded_segments (0x6f11c : word) = Some W_6f11c.
Proof. vm_refl. Qed.
Lemma D_6f11c : decode_any W_6f11c = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f120 : bv 32 := 0x00852503.
Lemma F_6f120 : fetch_word Ubsan.M.loaded_segments (0x6f120 : word) = Some W_6f120.
Proof. vm_refl. Qed.
Lemma D_6f120 : decode_any W_6f120 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f124 : bv 32 := 0x00008067.
Lemma F_6f124 : fetch_word Ubsan.M.loaded_segments (0x6f124 : word) = Some W_6f124.
Proof. vm_refl. Qed.
Lemma D_6f124 : decode_any W_6f124 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_711d4 : bv 32 := 0x00050c63.
Lemma F_711d4 : fetch_word Ubsan.M.loaded_segments (0x711d4 : word) = Some W_711d4.
Proof. vm_refl. Qed.
Lemma D_711d4 : decode_any W_711d4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_711d8 : bv 32 := 0x04058063.
Lemma F_711d8 : fetch_word Ubsan.M.loaded_segments (0x711d8 : word) = Some W_711d8.
Proof. vm_refl. Qed.
Lemma D_711d8 : decode_any W_711d8 = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_711dc : bv 32 := 0x00058613.
Lemma F_711dc : fetch_word Ubsan.M.loaded_segments (0x711dc : word) = Some W_711dc.
Proof. vm_refl. Qed.
Lemma D_711dc : decode_any W_711dc = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_711e0 : bv 32 := 0x00058693.
Lemma F_711e0 : fetch_word Ubsan.M.loaded_segments (0x711e0 : word) = Some W_711e0.
Proof. vm_refl. Qed.
Lemma D_711e0 : decode_any W_711e0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_711e4 : bv 32 := 0x00058713.
Lemma F_711e4 : fetch_word Ubsan.M.loaded_segments (0x711e4 : word) = Some W_711e4.
Proof. vm_refl. Qed.
Lemma D_711e4 : decode_any W_711e4 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_711e8 : bv 32 := 0x03c0006f.
Lemma F_711e8 : fetch_word Ubsan.M.loaded_segments (0x711e8 : word) = Some W_711e8.
Proof. vm_refl. Qed.
Lemma D_711e8 : decode_any W_711e8 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_71224 : bv 32 := 0xfa010113.
Lemma F_71224 : fetch_word Ubsan.M.loaded_segments (0x71224 : word) = Some W_71224.
Proof. vm_refl. Qed.
Lemma D_71224 : decode_any W_71224 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_71228 : bv 32 := 0x04113c23.
Lemma F_71228 : fetch_word Ubsan.M.loaded_segments (0x71228 : word) = Some W_71228.
Proof. vm_refl. Qed.
Lemma D_71228 : decode_any W_71228 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7122c : bv 32 := 0x04813823.
Lemma F_7122c : fetch_word Ubsan.M.loaded_segments (0x7122c : word) = Some W_7122c.
Proof. vm_refl. Qed.
Lemma D_7122c : decode_any W_7122c = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_71230 : bv 32 := 0x04913423.
Lemma F_71230 : fetch_word Ubsan.M.loaded_segments (0x71230 : word) = Some W_71230.
Proof. vm_refl. Qed.
Lemma D_71230 : decode_any W_71230 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_71234 : bv 32 := 0x05213023.
Lemma F_71234 : fetch_word Ubsan.M.loaded_segments (0x71234 : word) = Some W_71234.
Proof. vm_refl. Qed.
Lemma D_71234 : decode_any W_71234 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_71238 : bv 32 := 0x03313c23.
Lemma F_71238 : fetch_word Ubsan.M.loaded_segments (0x71238 : word) = Some W_71238.
Proof. vm_refl. Qed.
Lemma D_71238 : decode_any W_71238 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7123c : bv 32 := 0x03413823.
Lemma F_7123c : fetch_word Ubsan.M.loaded_segments (0x7123c : word) = Some W_7123c.
Proof. vm_refl. Qed.
Lemma D_7123c : decode_any W_7123c = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_71240 : bv 32 := 0x03513423.
Lemma F_71240 : fetch_word Ubsan.M.loaded_segments (0x71240 : word) = Some W_71240.
Proof. vm_refl. Qed.
Lemma D_71240 : decode_any W_71240 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_71244 : bv 32 := 0x03713023.
Lemma F_71244 : fetch_word Ubsan.M.loaded_segments (0x71244 : word) = Some W_71244.
Proof. vm_refl. Qed.
Lemma D_71244 : decode_any W_71244 = Some (Store SZ8 2 23 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71248 : bv 32 := 0x12050463.
Lemma F_71248 : fetch_word Ubsan.M.loaded_segments (0x71248 : word) = Some W_71248.
Proof. vm_refl. Qed.
Lemma D_71248 : decode_any W_71248 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_7124c : bv 32 := 0x00070a93.
Lemma F_7124c : fetch_word Ubsan.M.loaded_segments (0x7124c : word) = Some W_7124c.
Proof. vm_refl. Qed.
Lemma D_7124c : decode_any W_7124c = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71250 : bv 32 := 0x00068413.
Lemma F_71250 : fetch_word Ubsan.M.loaded_segments (0x71250 : word) = Some W_71250.
Proof. vm_refl. Qed.
Lemma D_71250 : decode_any W_71250 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71254 : bv 32 := 0x00060a13.
Lemma F_71254 : fetch_word Ubsan.M.loaded_segments (0x71254 : word) = Some W_71254.
Proof. vm_refl. Qed.
Lemma D_71254 : decode_any W_71254 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71258 : bv 32 := 0x00058493.
Lemma F_71258 : fetch_word Ubsan.M.loaded_segments (0x71258 : word) = Some W_71258.
Proof. vm_refl. Qed.
Lemma D_71258 : decode_any W_71258 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7125c : bv 32 := 0x00b665b3.
Lemma F_7125c : fetch_word Ubsan.M.loaded_segments (0x7125c : word) = Some W_7125c.
Proof. vm_refl. Qed.
Lemma D_7125c : decode_any W_7125c = Some (Op ALU_OR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_71260 : bv 32 := 0x00e6e633.
Lemma F_71260 : fetch_word Ubsan.M.loaded_segments (0x71260 : word) = Some W_71260.
Proof. vm_refl. Qed.
Lemma D_71260 : decode_any W_71260 = Some (Op ALU_OR 12 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_71264 : bv 32 := 0x00c5e5b3.
Lemma F_71264 : fetch_word Ubsan.M.loaded_segments (0x71264 : word) = Some W_71264.
Proof. vm_refl. Qed.
Lemma D_71264 : decode_any W_71264 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71268 : bv 32 := 0x1205c863.
Lemma F_71268 : fetch_word Ubsan.M.loaded_segments (0x71268 : word) = Some W_71268.
Proof. vm_refl. Qed.
Lemma D_71268 : decode_any W_71268 = Some (Branch BC_LT 11 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_7126c : bv 32 := 0x01c10593.
Lemma F_7126c : fetch_word Ubsan.M.loaded_segments (0x7126c : word) = Some W_7126c.
Proof. vm_refl. Qed.
Lemma D_7126c : decode_any W_7126c = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_71270 : bv 32 := 0x01810613.
Lemma F_71270 : fetch_word Ubsan.M.loaded_segments (0x71270 : word) = Some W_71270.
Proof. vm_refl. Qed.
Lemma D_71270 : decode_any W_71270 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_71274 : bv 32 := 0x01410693.
Lemma F_71274 : fetch_word Ubsan.M.loaded_segments (0x71274 : word) = Some W_71274.
Proof. vm_refl. Qed.
Lemma D_71274 : decode_any W_71274 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_71278 : bv 32 := 0x00050913.
Lemma F_71278 : fetch_word Ubsan.M.loaded_segments (0x71278 : word) = Some W_71278.
Proof. vm_refl. Qed.
Lemma D_71278 : decode_any W_71278 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7127c : bv 32 := 0x828fd0ef.
Lemma F_7127c : fetch_word Ubsan.M.loaded_segments (0x7127c : word) = Some W_7127c.
Proof. vm_refl. Qed.
Lemma D_7127c : decode_any W_7127c = Some (Jal 1 2084904, 4%Z).
Proof. vm_refl. Qed.

Definition W_71280 : bv 32 := 0x01c12583.
Lemma F_71280 : fetch_word Ubsan.M.loaded_segments (0x71280 : word) = Some W_71280.
Proof. vm_refl. Qed.
Lemma D_71280 : decode_any W_71280 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_71284 : bv 32 := 0x40958533.
Lemma F_71284 : fetch_word Ubsan.M.loaded_segments (0x71284 : word) = Some W_71284.
Proof. vm_refl. Qed.
Lemma D_71284 : decode_any W_71284 = Some (Op ALU_SUB 10 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_71288 : bv 32 := 0x409585bb.
Lemma F_71288 : fetch_word Ubsan.M.loaded_segments (0x71288 : word) = Some W_71288.
Proof. vm_refl. Qed.
Lemma D_71288 : decode_any W_71288 = Some (Op32 ALU_SUB 11 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7128c : bv 32 := 0x20a59463.
Lemma F_7128c : fetch_word Ubsan.M.loaded_segments (0x7128c : word) = Some W_7128c.
Proof. vm_refl. Qed.
Lemma D_7128c : decode_any W_7128c = Some (Branch BC_NE 11 10 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_71290 : bv 32 := 0x0005051b.
Lemma F_71290 : fetch_word Ubsan.M.loaded_segments (0x71290 : word) = Some W_71290.
Proof. vm_refl. Qed.
Lemma D_71290 : decode_any W_71290 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71294 : bv 32 := 0x414509bb.
Lemma F_71294 : fetch_word Ubsan.M.loaded_segments (0x71294 : word) = Some W_71294.
Proof. vm_refl. Qed.
Lemma D_71294 : decode_any W_71294 = Some (Op32 ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_71298 : bv 32 := 0x41450533.
Lemma F_71298 : fetch_word Ubsan.M.loaded_segments (0x71298 : word) = Some W_71298.
Proof. vm_refl. Qed.
Lemma D_71298 : decode_any W_71298 = Some (Op ALU_SUB 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7129c : bv 32 := 0x1ea99c63.
Lemma F_7129c : fetch_word Ubsan.M.loaded_segments (0x7129c : word) = Some W_7129c.
Proof. vm_refl. Qed.
Lemma D_7129c : decode_any W_7129c = Some (Branch BC_NE 19 10 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_712a0 : bv 32 := 0x01812583.
Lemma F_712a0 : fetch_word Ubsan.M.loaded_segments (0x712a0 : word) = Some W_712a0.
Proof. vm_refl. Qed.
Lemma D_712a0 : decode_any W_712a0 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_712a4 : bv 32 := 0x40858533.
Lemma F_712a4 : fetch_word Ubsan.M.loaded_segments (0x712a4 : word) = Some W_712a4.
Proof. vm_refl. Qed.
Lemma D_712a4 : decode_any W_712a4 = Some (Op ALU_SUB 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_712a8 : bv 32 := 0x408585bb.
Lemma F_712a8 : fetch_word Ubsan.M.loaded_segments (0x712a8 : word) = Some W_712a8.
Proof. vm_refl. Qed.
Lemma D_712a8 : decode_any W_712a8 = Some (Op32 ALU_SUB 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_712ac : bv 32 := 0x1ea59463.
Lemma F_712ac : fetch_word Ubsan.M.loaded_segments (0x712ac : word) = Some W_712ac.
Proof. vm_refl. Qed.
Lemma D_712ac : decode_any W_712ac = Some (Branch BC_NE 11 10 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_712b0 : bv 32 := 0x0005051b.
Lemma F_712b0 : fetch_word Ubsan.M.loaded_segments (0x712b0 : word) = Some W_712b0.
Proof. vm_refl. Qed.
Lemma D_712b0 : decode_any W_712b0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712b4 : bv 32 := 0x41550a3b.
Lemma F_712b4 : fetch_word Ubsan.M.loaded_segments (0x712b4 : word) = Some W_712b4.
Proof. vm_refl. Qed.
Lemma D_712b4 : decode_any W_712b4 = Some (Op32 ALU_SUB 20 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_712b8 : bv 32 := 0x41550533.
Lemma F_712b8 : fetch_word Ubsan.M.loaded_segments (0x712b8 : word) = Some W_712b8.
Proof. vm_refl. Qed.
Lemma D_712b8 : decode_any W_712b8 = Some (Op ALU_SUB 10 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_712bc : bv 32 := 0x1caa1c63.
Lemma F_712bc : fetch_word Ubsan.M.loaded_segments (0x712bc : word) = Some W_712bc.
Proof. vm_refl. Qed.
Lemma D_712bc : decode_any W_712bc = Some (Branch BC_NE 20 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_712c0 : bv 32 := 0x13305463.
Lemma F_712c0 : fetch_word Ubsan.M.loaded_segments (0x712c0 : word) = Some W_712c0.
Proof. vm_refl. Qed.
Lemma D_712c0 : decode_any W_712c0 = Some (Branch BC_GE 0 19 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_712c4 : bv 32 := 0x15405663.
Lemma F_712c4 : fetch_word Ubsan.M.loaded_segments (0x712c4 : word) = Some W_712c4.
Proof. vm_refl. Qed.
Lemma D_712c4 : decode_any W_712c4 = Some (Branch BC_GE 0 20 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_712c8 : bv 32 := 0x01412603.
Lemma F_712c8 : fetch_word Ubsan.M.loaded_segments (0x712c8 : word) = Some W_712c8.
Proof. vm_refl. Qed.
Lemma D_712c8 : decode_any W_712c8 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_712cc : bv 32 := 0x00098513.
Lemma F_712cc : fetch_word Ubsan.M.loaded_segments (0x712cc : word) = Some W_712cc.
Proof. vm_refl. Qed.
Lemma D_712cc : decode_any W_712cc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712d0 : bv 32 := 0x000a0593.
Lemma F_712d0 : fetch_word Ubsan.M.loaded_segments (0x712d0 : word) = Some W_712d0.
Proof. vm_refl. Qed.
Lemma D_712d0 : decode_any W_712d0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712d4 : bv 32 := 0xf68fc0ef.
Lemma F_712d4 : fetch_word Ubsan.M.loaded_segments (0x712d4 : word) = Some W_712d4.
Proof. vm_refl. Qed.
Lemma D_712d4 : decode_any W_712d4 = Some (Jal 1 2082664, 4%Z).
Proof. vm_refl. Qed.

Definition W_712d8 : bv 32 := 0x16050063.
Lemma F_712d8 : fetch_word Ubsan.M.loaded_segments (0x712d8 : word) = Some W_712d8.
Proof. vm_refl. Qed.
Lemma D_712d8 : decode_any W_712d8 = Some (Branch BC_EQ 10 0 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_712dc : bv 32 := 0x00050a93.
Lemma F_712dc : fetch_word Ubsan.M.loaded_segments (0x712dc : word) = Some W_712dc.
Proof. vm_refl. Qed.
Lemma D_712dc : decode_any W_712dc = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712e0 : bv 32 := 0x00090593.
Lemma F_712e0 : fetch_word Ubsan.M.loaded_segments (0x712e0 : word) = Some W_712e0.
Proof. vm_refl. Qed.
Lemma D_712e0 : decode_any W_712e0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712e4 : bv 32 := 0x958fd0ef.
Lemma F_712e4 : fetch_word Ubsan.M.loaded_segments (0x712e4 : word) = Some W_712e4.
Proof. vm_refl. Qed.
Lemma D_712e4 : decode_any W_712e4 = Some (Jal 1 2085208, 4%Z).
Proof. vm_refl. Qed.

Definition W_712e8 : bv 32 := 0x000a8513.
Lemma F_712e8 : fetch_word Ubsan.M.loaded_segments (0x712e8 : word) = Some W_712e8.
Proof. vm_refl. Qed.
Lemma D_712e8 : decode_any W_712e8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712ec : bv 32 := 0x00090593.
Lemma F_712ec : fetch_word Ubsan.M.loaded_segments (0x712ec : word) = Some W_712ec.
Proof. vm_refl. Qed.
Lemma D_712ec : decode_any W_712ec = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f0 : bv 32 := 0x870fd0ef.
Lemma F_712f0 : fetch_word Ubsan.M.loaded_segments (0x712f0 : word) = Some W_712f0.
Proof. vm_refl. Qed.
Lemma D_712f0 : decode_any W_712f0 = Some (Jal 1 2084976, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f4 : bv 32 := 0x000a8513.
Lemma F_712f4 : fetch_word Ubsan.M.loaded_segments (0x712f4 : word) = Some W_712f4.
Proof. vm_refl. Qed.
Lemma D_712f4 : decode_any W_712f4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712f8 : bv 32 := 0x00090593.
Lemma F_712f8 : fetch_word Ubsan.M.loaded_segments (0x712f8 : word) = Some W_712f8.
Proof. vm_refl. Qed.
Lemma D_712f8 : decode_any W_712f8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_712fc : bv 32 := 0x9d0fd0ef.
Lemma F_712fc : fetch_word Ubsan.M.loaded_segments (0x712fc : word) = Some W_712fc.
Proof. vm_refl. Qed.
Lemma D_712fc : decode_any W_712fc = Some (Jal 1 2085328, 4%Z).
Proof. vm_refl. Qed.

Definition W_71300 : bv 32 := 0x00c00793.
Lemma F_71300 : fetch_word Ubsan.M.loaded_segments (0x71300 : word) = Some W_71300.
Proof. vm_refl. Qed.
Lemma D_71300 : decode_any W_71300 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71304 : bv 32 := 0x00813023.
Lemma F_71304 : fetch_word Ubsan.M.loaded_segments (0x71304 : word) = Some W_71304.
Proof. vm_refl. Qed.
Lemma D_71304 : decode_any W_71304 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71308 : bv 32 := 0x000a8b93.
Lemma F_71308 : fetch_word Ubsan.M.loaded_segments (0x71308 : word) = Some W_71308.
Proof. vm_refl. Qed.
Lemma D_71308 : decode_any W_71308 = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7130c : bv 32 := 0x000a8513.
Lemma F_7130c : fetch_word Ubsan.M.loaded_segments (0x7130c : word) = Some W_7130c.
Proof. vm_refl. Qed.
Lemma D_7130c : decode_any W_7130c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71310 : bv 32 := 0x00000593.
Lemma F_71310 : fetch_word Ubsan.M.loaded_segments (0x71310 : word) = Some W_71310.
Proof. vm_refl. Qed.
Lemma D_71310 : decode_any W_71310 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71314 : bv 32 := 0x00000613.
Lemma F_71314 : fetch_word Ubsan.M.loaded_segments (0x71314 : word) = Some W_71314.
Proof. vm_refl. Qed.
Lemma D_71314 : decode_any W_71314 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71318 : bv 32 := 0x00098693.
Lemma F_71318 : fetch_word Ubsan.M.loaded_segments (0x71318 : word) = Some W_71318.
Proof. vm_refl. Qed.
Lemma D_71318 : decode_any W_71318 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7131c : bv 32 := 0x000a0713.
Lemma F_7131c : fetch_word Ubsan.M.loaded_segments (0x7131c : word) = Some W_7131c.
Proof. vm_refl. Qed.
Lemma D_7131c : decode_any W_7131c = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71320 : bv 32 := 0x00090813.
Lemma F_71320 : fetch_word Ubsan.M.loaded_segments (0x71320 : word) = Some W_71320.
Proof. vm_refl. Qed.
Lemma D_71320 : decode_any W_71320 = Some (OpImm ALU_ADD 16 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71324 : bv 32 := 0x00048893.
Lemma F_71324 : fetch_word Ubsan.M.loaded_segments (0x71324 : word) = Some W_71324.
Proof. vm_refl. Qed.
Lemma D_71324 : decode_any W_71324 = Some (OpImm ALU_ADD 17 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71328 : bv 32 := 0x6150d0ef.
Lemma F_71328 : fetch_word Ubsan.M.loaded_segments (0x71328 : word) = Some W_71328.
Proof. vm_refl. Qed.
Lemma D_71328 : decode_any W_71328 = Some (Jal 1 56852, 4%Z).
Proof. vm_refl. Qed.

Definition W_7132c : bv 32 := 0x00090513.
Lemma F_7132c : fetch_word Ubsan.M.loaded_segments (0x7132c : word) = Some W_7132c.
Proof. vm_refl. Qed.
Lemma D_7132c : decode_any W_7132c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71330 : bv 32 := 0xde5fd0ef.
Lemma F_71330 : fetch_word Ubsan.M.loaded_segments (0x71330 : word) = Some W_71330.
Proof. vm_refl. Qed.
Lemma D_71330 : decode_any W_71330 = Some (Jal 1 2088420, 4%Z).
Proof. vm_refl. Qed.

Definition W_71334 : bv 32 := 0x02000593.
Lemma F_71334 : fetch_word Ubsan.M.loaded_segments (0x71334 : word) = Some W_71334.
Proof. vm_refl. Qed.
Lemma D_71334 : decode_any W_71334 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71338 : bv 32 := 0x02b51863.
Lemma F_71338 : fetch_word Ubsan.M.loaded_segments (0x71338 : word) = Some W_71338.
Proof. vm_refl. Qed.
Lemma D_71338 : decode_any W_71338 = Some (Branch BC_NE 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_71368 : bv 32 := 0x000b8513.
Lemma F_71368 : fetch_word Ubsan.M.loaded_segments (0x71368 : word) = Some W_71368.
Proof. vm_refl. Qed.
Lemma D_71368 : decode_any W_71368 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7136c : bv 32 := 0x1000006f.
Lemma F_7136c : fetch_word Ubsan.M.loaded_segments (0x7136c : word) = Some W_7136c.
Proof. vm_refl. Qed.
Lemma D_7136c : decode_any W_7136c = Some (Jal 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_71370 : bv 32 := 0x000b5517.
Lemma F_71370 : fetch_word Ubsan.M.loaded_segments (0x71370 : word) = Some W_71370.
Proof. vm_refl. Qed.
Lemma D_71370 : decode_any W_71370 = Some (Auipc 10 181, 4%Z).
Proof. vm_refl. Qed.

Definition W_71374 : bv 32 := 0x70053503.
Lemma F_71374 : fetch_word Ubsan.M.loaded_segments (0x71374 : word) = Some W_71374.
Proof. vm_refl. Qed.
Lemma D_71374 : decode_any W_71374 = Some (Load SZ8 true 10 10 1792, 4%Z).
Proof. vm_refl. Qed.

Definition W_71378 : bv 32 := 0x00052503.
Lemma F_71378 : fetch_word Ubsan.M.loaded_segments (0x71378 : word) = Some W_71378.
Proof. vm_refl. Qed.
Lemma D_71378 : decode_any W_71378 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7137c : bv 32 := 0x00500593.
Lemma F_7137c : fetch_word Ubsan.M.loaded_segments (0x7137c : word) = Some W_7137c.
Proof. vm_refl. Qed.
Lemma D_7137c : decode_any W_7137c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_71380 : bv 32 := 0x0ea5c463.
Lemma F_71380 : fetch_word Ubsan.M.loaded_segments (0x71380 : word) = Some W_71380.
Proof. vm_refl. Qed.
Lemma D_71380 : decode_any W_71380 = Some (Branch BC_LT 11 10 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_71384 : bv 32 := 0xfff9f517.
Lemma F_71384 : fetch_word Ubsan.M.loaded_segments (0x71384 : word) = Some W_71384.
Proof. vm_refl. Qed.
Lemma D_71384 : decode_any W_71384 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_71388 : bv 32 := 0xfffa7597.
Lemma F_71388 : fetch_word Ubsan.M.loaded_segments (0x71388 : word) = Some W_71388.
Proof. vm_refl. Qed.
Lemma D_71388 : decode_any W_71388 = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_7138c : bv 32 := 0xfd150513.
Lemma F_7138c : fetch_word Ubsan.M.loaded_segments (0x7138c : word) = Some W_7138c.
Proof. vm_refl. Qed.
Lemma D_7138c : decode_any W_7138c = Some (OpImm ALU_ADD 10 10 4049, 4%Z).
Proof. vm_refl. Qed.

Definition W_71390 : bv 32 := 0x07458593.
Lemma F_71390 : fetch_word Ubsan.M.loaded_segments (0x71390 : word) = Some W_71390.
Proof. vm_refl. Qed.
Lemma D_71390 : decode_any W_71390 = Some (OpImm ALU_ADD 11 11 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_71394 : bv 32 := 0x0280006f.
Lemma F_71394 : fetch_word Ubsan.M.loaded_segments (0x71394 : word) = Some W_71394.
Proof. vm_refl. Qed.
Lemma D_71394 : decode_any W_71394 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_713bc : bv 32 := 0x00000613.
Lemma F_713bc : fetch_word Ubsan.M.loaded_segments (0x713bc : word) = Some W_713bc.
Proof. vm_refl. Qed.
Lemma D_713bc : decode_any W_713bc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_713c0 : bv 32 := 0x05813083.
Lemma F_713c0 : fetch_word Ubsan.M.loaded_segments (0x713c0 : word) = Some W_713c0.
Proof. vm_refl. Qed.
Lemma D_713c0 : decode_any W_713c0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_713c4 : bv 32 := 0x05013403.
Lemma F_713c4 : fetch_word Ubsan.M.loaded_segments (0x713c4 : word) = Some W_713c4.
Proof. vm_refl. Qed.
Lemma D_713c4 : decode_any W_713c4 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_713c8 : bv 32 := 0x04813483.
Lemma F_713c8 : fetch_word Ubsan.M.loaded_segments (0x713c8 : word) = Some W_713c8.
Proof. vm_refl. Qed.
Lemma D_713c8 : decode_any W_713c8 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_713cc : bv 32 := 0x04013903.
Lemma F_713cc : fetch_word Ubsan.M.loaded_segments (0x713cc : word) = Some W_713cc.
Proof. vm_refl. Qed.
Lemma D_713cc : decode_any W_713cc = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_713d0 : bv 32 := 0x03813983.
Lemma F_713d0 : fetch_word Ubsan.M.loaded_segments (0x713d0 : word) = Some W_713d0.
Proof. vm_refl. Qed.
Lemma D_713d0 : decode_any W_713d0 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_713d4 : bv 32 := 0x03013a03.
Lemma F_713d4 : fetch_word Ubsan.M.loaded_segments (0x713d4 : word) = Some W_713d4.
Proof. vm_refl. Qed.
Lemma D_713d4 : decode_any W_713d4 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_713d8 : bv 32 := 0x02813a83.
Lemma F_713d8 : fetch_word Ubsan.M.loaded_segments (0x713d8 : word) = Some W_713d8.
Proof. vm_refl. Qed.
Lemma D_713d8 : decode_any W_713d8 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_713dc : bv 32 := 0x02013b83.
Lemma F_713dc : fetch_word Ubsan.M.loaded_segments (0x713dc : word) = Some W_713dc.
Proof. vm_refl. Qed.
Lemma D_713dc : decode_any W_713dc = Some (Load SZ8 true 23 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_713e0 : bv 32 := 0x06010113.
Lemma F_713e0 : fetch_word Ubsan.M.loaded_segments (0x713e0 : word) = Some W_713e0.
Proof. vm_refl. Qed.
Lemma D_713e0 : decode_any W_713e0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_713e4 : bv 32 := 0xb5cf206f.
Lemma F_713e4 : fetch_word Ubsan.M.loaded_segments (0x713e4 : word) = Some W_713e4.
Proof. vm_refl. Qed.
Lemma D_713e4 : decode_any W_713e4 = Some (Jal 0 2040668, 4%Z).
Proof. vm_refl. Qed.

Definition W_71438 : bv 32 := 0x000b5517.
Lemma F_71438 : fetch_word Ubsan.M.loaded_segments (0x71438 : word) = Some W_71438.
Proof. vm_refl. Qed.
Lemma D_71438 : decode_any W_71438 = Some (Auipc 10 181, 4%Z).
Proof. vm_refl. Qed.

Definition W_7143c : bv 32 := 0x63853503.
Lemma F_7143c : fetch_word Ubsan.M.loaded_segments (0x7143c : word) = Some W_7143c.
Proof. vm_refl. Qed.
Lemma D_7143c : decode_any W_7143c = Some (Load SZ8 true 10 10 1592, 4%Z).
Proof. vm_refl. Qed.

Definition W_71440 : bv 32 := 0x00052503.
Lemma F_71440 : fetch_word Ubsan.M.loaded_segments (0x71440 : word) = Some W_71440.
Proof. vm_refl. Qed.
Lemma D_71440 : decode_any W_71440 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71444 : bv 32 := 0x00500593.
Lemma F_71444 : fetch_word Ubsan.M.loaded_segments (0x71444 : word) = Some W_71444.
Proof. vm_refl. Qed.
Lemma D_71444 : decode_any W_71444 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_71448 : bv 32 := 0x02a5c063.
Lemma F_71448 : fetch_word Ubsan.M.loaded_segments (0x71448 : word) = Some W_71448.
Proof. vm_refl. Qed.
Lemma D_71448 : decode_any W_71448 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7144c : bv 32 := 0xfffa1517.
Lemma F_7144c : fetch_word Ubsan.M.loaded_segments (0x7144c : word) = Some W_7144c.
Proof. vm_refl. Qed.
Lemma D_7144c : decode_any W_7144c = Some (Auipc 10 1048481, 4%Z).
Proof. vm_refl. Qed.

Definition W_71450 : bv 32 := 0xfffa7597.
Lemma F_71450 : fetch_word Ubsan.M.loaded_segments (0x71450 : word) = Some W_71450.
Proof. vm_refl. Qed.
Lemma D_71450 : decode_any W_71450 = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_71454 : bv 32 := 0x28e50513.
Lemma F_71454 : fetch_word Ubsan.M.loaded_segments (0x71454 : word) = Some W_71454.
Proof. vm_refl. Qed.
Lemma D_71454 : decode_any W_71454 = Some (OpImm ALU_ADD 10 10 654, 4%Z).
Proof. vm_refl. Qed.

Definition W_71458 : bv 32 := 0xfac58593.
Lemma F_71458 : fetch_word Ubsan.M.loaded_segments (0x71458 : word) = Some W_71458.
Proof. vm_refl. Qed.
Lemma D_71458 : decode_any W_71458 = Some (OpImm ALU_ADD 11 11 4012, 4%Z).
Proof. vm_refl. Qed.

Definition W_7145c : bv 32 := 0x00000613.
Lemma F_7145c : fetch_word Ubsan.M.loaded_segments (0x7145c : word) = Some W_7145c.
Proof. vm_refl. Qed.
Lemma D_7145c : decode_any W_7145c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71460 : bv 32 := 0xae0f20ef.
Lemma F_71460 : fetch_word Ubsan.M.loaded_segments (0x71460 : word) = Some W_71460.
Proof. vm_refl. Qed.
Lemma D_71460 : decode_any W_71460 = Some (Jal 1 2040544, 4%Z).
Proof. vm_refl. Qed.

Definition W_71464 : bv 32 := 0x0080006f.
Lemma F_71464 : fetch_word Ubsan.M.loaded_segments (0x71464 : word) = Some W_71464.
Proof. vm_refl. Qed.
Lemma D_71464 : decode_any W_71464 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7146c : bv 32 := 0x05813083.
Lemma F_7146c : fetch_word Ubsan.M.loaded_segments (0x7146c : word) = Some W_7146c.
Proof. vm_refl. Qed.
Lemma D_7146c : decode_any W_7146c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_71470 : bv 32 := 0x05013403.
Lemma F_71470 : fetch_word Ubsan.M.loaded_segments (0x71470 : word) = Some W_71470.
Proof. vm_refl. Qed.
Lemma D_71470 : decode_any W_71470 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_71474 : bv 32 := 0x04813483.
Lemma F_71474 : fetch_word Ubsan.M.loaded_segments (0x71474 : word) = Some W_71474.
Proof. vm_refl. Qed.
Lemma D_71474 : decode_any W_71474 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_71478 : bv 32 := 0x04013903.
Lemma F_71478 : fetch_word Ubsan.M.loaded_segments (0x71478 : word) = Some W_71478.
Proof. vm_refl. Qed.
Lemma D_71478 : decode_any W_71478 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7147c : bv 32 := 0x03813983.
Lemma F_7147c : fetch_word Ubsan.M.loaded_segments (0x7147c : word) = Some W_7147c.
Proof. vm_refl. Qed.
Lemma D_7147c : decode_any W_7147c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_71480 : bv 32 := 0x03013a03.
Lemma F_71480 : fetch_word Ubsan.M.loaded_segments (0x71480 : word) = Some W_71480.
Proof. vm_refl. Qed.
Lemma D_71480 : decode_any W_71480 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_71484 : bv 32 := 0x02813a83.
Lemma F_71484 : fetch_word Ubsan.M.loaded_segments (0x71484 : word) = Some W_71484.
Proof. vm_refl. Qed.
Lemma D_71484 : decode_any W_71484 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_71488 : bv 32 := 0x02013b83.
Lemma F_71488 : fetch_word Ubsan.M.loaded_segments (0x71488 : word) = Some W_71488.
Proof. vm_refl. Qed.
Lemma D_71488 : decode_any W_71488 = Some (Load SZ8 true 23 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7148c : bv 32 := 0x06010113.
Lemma F_7148c : fetch_word Ubsan.M.loaded_segments (0x7148c : word) = Some W_7148c.
Proof. vm_refl. Qed.
Lemma D_7148c : decode_any W_7148c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_71490 : bv 32 := 0x00008067.
Lemma F_71490 : fetch_word Ubsan.M.loaded_segments (0x71490 : word) = Some W_71490.
Proof. vm_refl. Qed.
Lemma D_71490 : decode_any W_71490 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
