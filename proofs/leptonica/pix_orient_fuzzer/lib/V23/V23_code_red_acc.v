(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6df4c : bv 32 := 0x00050a63.
Lemma F_6df4c : fetch_word Ubsan.M.loaded_segments (0x6df4c : word) = Some W_6df4c.
Proof. vm_refl. Qed.
Lemma D_6df4c : decode_any W_6df4c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df50 : bv 32 := 0x00757593.
Lemma F_6df50 : fetch_word Ubsan.M.loaded_segments (0x6df50 : word) = Some W_6df50.
Proof. vm_refl. Qed.
Lemma D_6df50 : decode_any W_6df50 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df54 : bv 32 := 0x04059063.
Lemma F_6df54 : fetch_word Ubsan.M.loaded_segments (0x6df54 : word) = Some W_6df54.
Proof. vm_refl. Qed.
Lemma D_6df54 : decode_any W_6df54 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df58 : bv 32 := 0x01052503.
Lemma F_6df58 : fetch_word Ubsan.M.loaded_segments (0x6df58 : word) = Some W_6df58.
Proof. vm_refl. Qed.
Lemma D_6df58 : decode_any W_6df58 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df5c : bv 32 := 0x00008067.
Lemma F_6df5c : fetch_word Ubsan.M.loaded_segments (0x6df5c : word) = Some W_6df5c.
Proof. vm_refl. Qed.
Lemma D_6df5c : decode_any W_6df5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df60 : bv 32 := 0x000b9517.
Lemma F_6df60 : fetch_word Ubsan.M.loaded_segments (0x6df60 : word) = Some W_6df60.
Proof. vm_refl. Qed.
Lemma D_6df60 : decode_any W_6df60 = Some (Auipc 10 185, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df64 : bv 32 := 0xb1053503.
Lemma F_6df64 : fetch_word Ubsan.M.loaded_segments (0x6df64 : word) = Some W_6df64.
Proof. vm_refl. Qed.
Lemma D_6df64 : decode_any W_6df64 = Some (Load SZ8 true 10 10 2832, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df68 : bv 32 := 0x00052503.
Lemma F_6df68 : fetch_word Ubsan.M.loaded_segments (0x6df68 : word) = Some W_6df68.
Proof. vm_refl. Qed.
Lemma D_6df68 : decode_any W_6df68 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df6c : bv 32 := 0x00500593.
Lemma F_6df6c : fetch_word Ubsan.M.loaded_segments (0x6df6c : word) = Some W_6df6c.
Proof. vm_refl. Qed.
Lemma D_6df6c : decode_any W_6df6c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df70 : bv 32 := 0x00a5ce63.
Lemma F_6df70 : fetch_word Ubsan.M.loaded_segments (0x6df70 : word) = Some W_6df70.
Proof. vm_refl. Qed.
Lemma D_6df70 : decode_any W_6df70 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df74 : bv 32 := 0xfffa3517.
Lemma F_6df74 : fetch_word Ubsan.M.loaded_segments (0x6df74 : word) = Some W_6df74.
Proof. vm_refl. Qed.
Lemma D_6df74 : decode_any W_6df74 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df78 : bv 32 := 0xfffad597.
Lemma F_6df78 : fetch_word Ubsan.M.loaded_segments (0x6df78 : word) = Some W_6df78.
Proof. vm_refl. Qed.
Lemma D_6df78 : decode_any W_6df78 = Some (Auipc 11 1048493, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df7c : bv 32 := 0x0d750513.
Lemma F_6df7c : fetch_word Ubsan.M.loaded_segments (0x6df7c : word) = Some W_6df7c.
Proof. vm_refl. Qed.
Lemma D_6df7c : decode_any W_6df7c = Some (OpImm ALU_ADD 10 10 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df80 : bv 32 := 0xccf58593.
Lemma F_6df80 : fetch_word Ubsan.M.loaded_segments (0x6df80 : word) = Some W_6df80.
Proof. vm_refl. Qed.
Lemma D_6df80 : decode_any W_6df80 = Some (OpImm ALU_ADD 11 11 3279, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df84 : bv 32 := 0x00000613.
Lemma F_6df84 : fetch_word Ubsan.M.loaded_segments (0x6df84 : word) = Some W_6df84.
Proof. vm_refl. Qed.
Lemma D_6df84 : decode_any W_6df84 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df88 : bv 32 := 0xee8f506f.
Lemma F_6df88 : fetch_word Ubsan.M.loaded_segments (0x6df88 : word) = Some W_6df88.
Proof. vm_refl. Qed.
Lemma D_6df88 : decode_any W_6df88 = Some (Jal 0 2053864, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df8c : bv 32 := 0x00000513.
Lemma F_6df8c : fetch_word Ubsan.M.loaded_segments (0x6df8c : word) = Some W_6df8c.
Proof. vm_refl. Qed.
Lemma D_6df8c : decode_any W_6df8c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df90 : bv 32 := 0x00008067.
Lemma F_6df90 : fetch_word Ubsan.M.loaded_segments (0x6df90 : word) = Some W_6df90.
Proof. vm_refl. Qed.
Lemma D_6df90 : decode_any W_6df90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_6e320 : bv 32 := 0x000b8517.
Lemma F_6e320 : fetch_word Ubsan.M.loaded_segments (0x6e320 : word) = Some W_6e320.
Proof. vm_refl. Qed.
Lemma D_6e320 : decode_any W_6e320 = Some (Auipc 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e324 : bv 32 := 0x75053503.
Lemma F_6e324 : fetch_word Ubsan.M.loaded_segments (0x6e324 : word) = Some W_6e324.
Proof. vm_refl. Qed.
Lemma D_6e324 : decode_any W_6e324 = Some (Load SZ8 true 10 10 1872, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e328 : bv 32 := 0x00052503.
Lemma F_6e328 : fetch_word Ubsan.M.loaded_segments (0x6e328 : word) = Some W_6e328.
Proof. vm_refl. Qed.
Lemma D_6e328 : decode_any W_6e328 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e32c : bv 32 := 0x00500593.
Lemma F_6e32c : fetch_word Ubsan.M.loaded_segments (0x6e32c : word) = Some W_6e32c.
Proof. vm_refl. Qed.
Lemma D_6e32c : decode_any W_6e32c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e330 : bv 32 := 0x02a5c263.
Lemma F_6e330 : fetch_word Ubsan.M.loaded_segments (0x6e330 : word) = Some W_6e330.
Proof. vm_refl. Qed.
Lemma D_6e330 : decode_any W_6e330 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e334 : bv 32 := 0xfffa3517.
Lemma F_6e334 : fetch_word Ubsan.M.loaded_segments (0x6e334 : word) = Some W_6e334.
Proof. vm_refl. Qed.
Lemma D_6e334 : decode_any W_6e334 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e338 : bv 32 := 0xfffb0597.
Lemma F_6e338 : fetch_word Ubsan.M.loaded_segments (0x6e338 : word) = Some W_6e338.
Proof. vm_refl. Qed.
Lemma D_6e338 : decode_any W_6e338 = Some (Auipc 11 1048496, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e33c : bv 32 := 0xd1750513.
Lemma F_6e33c : fetch_word Ubsan.M.loaded_segments (0x6e33c : word) = Some W_6e33c.
Proof. vm_refl. Qed.
Lemma D_6e33c : decode_any W_6e33c = Some (OpImm ALU_ADD 10 10 3351, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e340 : bv 32 := 0x13f58593.
Lemma F_6e340 : fetch_word Ubsan.M.loaded_segments (0x6e340 : word) = Some W_6e340.
Proof. vm_refl. Qed.
Lemma D_6e340 : decode_any W_6e340 = Some (OpImm ALU_ADD 11 11 319, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e344 : bv 32 := 0x00100613.
Lemma F_6e344 : fetch_word Ubsan.M.loaded_segments (0x6e344 : word) = Some W_6e344.
Proof. vm_refl. Qed.
Lemma D_6e344 : decode_any W_6e344 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e348 : bv 32 := 0xb28f506f.
Lemma F_6e348 : fetch_word Ubsan.M.loaded_segments (0x6e348 : word) = Some W_6e348.
Proof. vm_refl. Qed.
Lemma D_6e348 : decode_any W_6e348 = Some (Jal 0 2052904, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e34c : bv 32 := 0x00000513.
Lemma F_6e34c : fetch_word Ubsan.M.loaded_segments (0x6e34c : word) = Some W_6e34c.
Proof. vm_refl. Qed.
Lemma D_6e34c : decode_any W_6e34c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e350 : bv 32 := 0x00008067.
Lemma F_6e350 : fetch_word Ubsan.M.loaded_segments (0x6e350 : word) = Some W_6e350.
Proof. vm_refl. Qed.
Lemma D_6e350 : decode_any W_6e350 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e354 : bv 32 := 0x00100513.
Lemma F_6e354 : fetch_word Ubsan.M.loaded_segments (0x6e354 : word) = Some W_6e354.
Proof. vm_refl. Qed.
Lemma D_6e354 : decode_any W_6e354 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e358 : bv 32 := 0x00008067.
Lemma F_6e358 : fetch_word Ubsan.M.loaded_segments (0x6e358 : word) = Some W_6e358.
Proof. vm_refl. Qed.
Lemma D_6e358 : decode_any W_6e358 = Some (Jalr 0 1 0, 4%Z).
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

Definition W_6f128 : bv 32 := 0x000b8517.
Lemma F_6f128 : fetch_word Ubsan.M.loaded_segments (0x6f128 : word) = Some W_6f128.
Proof. vm_refl. Qed.
Lemma D_6f128 : decode_any W_6f128 = Some (Auipc 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f12c : bv 32 := 0x94853503.
Lemma F_6f12c : fetch_word Ubsan.M.loaded_segments (0x6f12c : word) = Some W_6f12c.
Proof. vm_refl. Qed.
Lemma D_6f12c : decode_any W_6f12c = Some (Load SZ8 true 10 10 2376, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f130 : bv 32 := 0x00052503.
Lemma F_6f130 : fetch_word Ubsan.M.loaded_segments (0x6f130 : word) = Some W_6f130.
Proof. vm_refl. Qed.
Lemma D_6f130 : decode_any W_6f130 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f134 : bv 32 := 0x00500593.
Lemma F_6f134 : fetch_word Ubsan.M.loaded_segments (0x6f134 : word) = Some W_6f134.
Proof. vm_refl. Qed.
Lemma D_6f134 : decode_any W_6f134 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f138 : bv 32 := 0x00a5ce63.
Lemma F_6f138 : fetch_word Ubsan.M.loaded_segments (0x6f138 : word) = Some W_6f138.
Proof. vm_refl. Qed.
Lemma D_6f138 : decode_any W_6f138 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f13c : bv 32 := 0xfffa2517.
Lemma F_6f13c : fetch_word Ubsan.M.loaded_segments (0x6f13c : word) = Some W_6f13c.
Proof. vm_refl. Qed.
Lemma D_6f13c : decode_any W_6f13c = Some (Auipc 10 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f140 : bv 32 := 0xfffa1597.
Lemma F_6f140 : fetch_word Ubsan.M.loaded_segments (0x6f140 : word) = Some W_6f140.
Proof. vm_refl. Qed.
Lemma D_6f140 : decode_any W_6f140 = Some (Auipc 11 1048481, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f144 : bv 32 := 0xf0f50513.
Lemma F_6f144 : fetch_word Ubsan.M.loaded_segments (0x6f144 : word) = Some W_6f144.
Proof. vm_refl. Qed.
Lemma D_6f144 : decode_any W_6f144 = Some (OpImm ALU_ADD 10 10 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f148 : bv 32 := 0x29158593.
Lemma F_6f148 : fetch_word Ubsan.M.loaded_segments (0x6f148 : word) = Some W_6f148.
Proof. vm_refl. Qed.
Lemma D_6f148 : decode_any W_6f148 = Some (OpImm ALU_ADD 11 11 657, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f14c : bv 32 := 0x00000613.
Lemma F_6f14c : fetch_word Ubsan.M.loaded_segments (0x6f14c : word) = Some W_6f14c.
Proof. vm_refl. Qed.
Lemma D_6f14c : decode_any W_6f14c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f150 : bv 32 := 0xd20f406f.
Lemma F_6f150 : fetch_word Ubsan.M.loaded_segments (0x6f150 : word) = Some W_6f150.
Proof. vm_refl. Qed.
Lemma D_6f150 : decode_any W_6f150 = Some (Jal 0 2049312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f154 : bv 32 := 0x00000513.
Lemma F_6f154 : fetch_word Ubsan.M.loaded_segments (0x6f154 : word) = Some W_6f154.
Proof. vm_refl. Qed.
Lemma D_6f154 : decode_any W_6f154 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f158 : bv 32 := 0x00008067.
Lemma F_6f158 : fetch_word Ubsan.M.loaded_segments (0x6f158 : word) = Some W_6f158.
Proof. vm_refl. Qed.
Lemma D_6f158 : decode_any W_6f158 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f1ec : bv 32 := 0x00050a63.
Lemma F_6f1ec : fetch_word Ubsan.M.loaded_segments (0x6f1ec : word) = Some W_6f1ec.
Proof. vm_refl. Qed.
Lemma D_6f1ec : decode_any W_6f1ec = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f1f0 : bv 32 := 0x00757593.
Lemma F_6f1f0 : fetch_word Ubsan.M.loaded_segments (0x6f1f0 : word) = Some W_6f1f0.
Proof. vm_refl. Qed.
Lemma D_6f1f0 : decode_any W_6f1f0 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f1f4 : bv 32 := 0x04059063.
Lemma F_6f1f4 : fetch_word Ubsan.M.loaded_segments (0x6f1f4 : word) = Some W_6f1f4.
Proof. vm_refl. Qed.
Lemma D_6f1f4 : decode_any W_6f1f4 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f1f8 : bv 32 := 0x03853503.
Lemma F_6f1f8 : fetch_word Ubsan.M.loaded_segments (0x6f1f8 : word) = Some W_6f1f8.
Proof. vm_refl. Qed.
Lemma D_6f1f8 : decode_any W_6f1f8 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f1fc : bv 32 := 0x00008067.
Lemma F_6f1fc : fetch_word Ubsan.M.loaded_segments (0x6f1fc : word) = Some W_6f1fc.
Proof. vm_refl. Qed.
Lemma D_6f1fc : decode_any W_6f1fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f200 : bv 32 := 0x000b8517.
Lemma F_6f200 : fetch_word Ubsan.M.loaded_segments (0x6f200 : word) = Some W_6f200.
Proof. vm_refl. Qed.
Lemma D_6f200 : decode_any W_6f200 = Some (Auipc 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f204 : bv 32 := 0x87053503.
Lemma F_6f204 : fetch_word Ubsan.M.loaded_segments (0x6f204 : word) = Some W_6f204.
Proof. vm_refl. Qed.
Lemma D_6f204 : decode_any W_6f204 = Some (Load SZ8 true 10 10 2160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f208 : bv 32 := 0x00052503.
Lemma F_6f208 : fetch_word Ubsan.M.loaded_segments (0x6f208 : word) = Some W_6f208.
Proof. vm_refl. Qed.
Lemma D_6f208 : decode_any W_6f208 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f20c : bv 32 := 0x00500593.
Lemma F_6f20c : fetch_word Ubsan.M.loaded_segments (0x6f20c : word) = Some W_6f20c.
Proof. vm_refl. Qed.
Lemma D_6f20c : decode_any W_6f20c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f210 : bv 32 := 0x00a5ce63.
Lemma F_6f210 : fetch_word Ubsan.M.loaded_segments (0x6f210 : word) = Some W_6f210.
Proof. vm_refl. Qed.
Lemma D_6f210 : decode_any W_6f210 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f214 : bv 32 := 0xfffa2517.
Lemma F_6f214 : fetch_word Ubsan.M.loaded_segments (0x6f214 : word) = Some W_6f214.
Proof. vm_refl. Qed.
Lemma D_6f214 : decode_any W_6f214 = Some (Auipc 10 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f218 : bv 32 := 0xfffa2597.
Lemma F_6f218 : fetch_word Ubsan.M.loaded_segments (0x6f218 : word) = Some W_6f218.
Proof. vm_refl. Qed.
Lemma D_6f218 : decode_any W_6f218 = Some (Auipc 11 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f21c : bv 32 := 0xe3750513.
Lemma F_6f21c : fetch_word Ubsan.M.loaded_segments (0x6f21c : word) = Some W_6f21c.
Proof. vm_refl. Qed.
Lemma D_6f21c : decode_any W_6f21c = Some (OpImm ALU_ADD 10 10 3639, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f220 : bv 32 := 0xe7f58593.
Lemma F_6f220 : fetch_word Ubsan.M.loaded_segments (0x6f220 : word) = Some W_6f220.
Proof. vm_refl. Qed.
Lemma D_6f220 : decode_any W_6f220 = Some (OpImm ALU_ADD 11 11 3711, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f224 : bv 32 := 0x00000613.
Lemma F_6f224 : fetch_word Ubsan.M.loaded_segments (0x6f224 : word) = Some W_6f224.
Proof. vm_refl. Qed.
Lemma D_6f224 : decode_any W_6f224 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f228 : bv 32 := 0xd18f406f.
Lemma F_6f228 : fetch_word Ubsan.M.loaded_segments (0x6f228 : word) = Some W_6f228.
Proof. vm_refl. Qed.
Lemma D_6f228 : decode_any W_6f228 = Some (Jal 0 2049304, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f22c : bv 32 := 0x00000513.
Lemma F_6f22c : fetch_word Ubsan.M.loaded_segments (0x6f22c : word) = Some W_6f22c.
Proof. vm_refl. Qed.
Lemma D_6f22c : decode_any W_6f22c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f230 : bv 32 := 0x00008067.
Lemma F_6f230 : fetch_word Ubsan.M.loaded_segments (0x6f230 : word) = Some W_6f230.
Proof. vm_refl. Qed.
Lemma D_6f230 : decode_any W_6f230 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
