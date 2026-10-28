(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
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

Definition W_6df94 : bv 32 := 0xc0001073.
Lemma F_6df94 : fetch_word Ubsan.M.loaded_segments (0x6df94 : word) = Some W_6df94.
Proof. vm_refl. Qed.
Lemma D_6df94 : decode_any W_6df94 = Some (Csr CSR_RW 0 0 3072, 4%Z).
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

Definition W_6e35c : bv 32 := 0xc0001073.
Lemma F_6e35c : fetch_word Ubsan.M.loaded_segments (0x6e35c : word) = Some W_6e35c.
Proof. vm_refl. Qed.
Lemma D_6e35c : decode_any W_6e35c = Some (Csr CSR_RW 0 0 3072, 4%Z).
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

Definition W_6f234 : bv 32 := 0xc0001073.
Lemma F_6f234 : fetch_word Ubsan.M.loaded_segments (0x6f234 : word) = Some W_6f234.
Proof. vm_refl. Qed.
Lemma D_6f234 : decode_any W_6f234 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f13c : bv 32 := 0xf2010113.
Lemma F_7f13c : fetch_word Ubsan.M.loaded_segments (0x7f13c : word) = Some W_7f13c.
Proof. vm_refl. Qed.
Lemma D_7f13c : decode_any W_7f13c = Some (OpImm ALU_ADD 2 2 3872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f140 : bv 32 := 0x0c113c23.
Lemma F_7f140 : fetch_word Ubsan.M.loaded_segments (0x7f140 : word) = Some W_7f140.
Proof. vm_refl. Qed.
Lemma D_7f140 : decode_any W_7f140 = Some (Store SZ8 2 1 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f144 : bv 32 := 0x0c813823.
Lemma F_7f144 : fetch_word Ubsan.M.loaded_segments (0x7f144 : word) = Some W_7f144.
Proof. vm_refl. Qed.
Lemma D_7f144 : decode_any W_7f144 = Some (Store SZ8 2 8 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f148 : bv 32 := 0x0c913423.
Lemma F_7f148 : fetch_word Ubsan.M.loaded_segments (0x7f148 : word) = Some W_7f148.
Proof. vm_refl. Qed.
Lemma D_7f148 : decode_any W_7f148 = Some (Store SZ8 2 9 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f14c : bv 32 := 0x0d213023.
Lemma F_7f14c : fetch_word Ubsan.M.loaded_segments (0x7f14c : word) = Some W_7f14c.
Proof. vm_refl. Qed.
Lemma D_7f14c : decode_any W_7f14c = Some (Store SZ8 2 18 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f150 : bv 32 := 0x0b313c23.
Lemma F_7f150 : fetch_word Ubsan.M.loaded_segments (0x7f150 : word) = Some W_7f150.
Proof. vm_refl. Qed.
Lemma D_7f150 : decode_any W_7f150 = Some (Store SZ8 2 19 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f154 : bv 32 := 0x0b413823.
Lemma F_7f154 : fetch_word Ubsan.M.loaded_segments (0x7f154 : word) = Some W_7f154.
Proof. vm_refl. Qed.
Lemma D_7f154 : decode_any W_7f154 = Some (Store SZ8 2 20 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f158 : bv 32 := 0x0b513423.
Lemma F_7f158 : fetch_word Ubsan.M.loaded_segments (0x7f158 : word) = Some W_7f158.
Proof. vm_refl. Qed.
Lemma D_7f158 : decode_any W_7f158 = Some (Store SZ8 2 21 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f15c : bv 32 := 0x0b613023.
Lemma F_7f15c : fetch_word Ubsan.M.loaded_segments (0x7f15c : word) = Some W_7f15c.
Proof. vm_refl. Qed.
Lemma D_7f15c : decode_any W_7f15c = Some (Store SZ8 2 22 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f160 : bv 32 := 0x09713c23.
Lemma F_7f160 : fetch_word Ubsan.M.loaded_segments (0x7f160 : word) = Some W_7f160.
Proof. vm_refl. Qed.
Lemma D_7f160 : decode_any W_7f160 = Some (Store SZ8 2 23 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f164 : bv 32 := 0x09813823.
Lemma F_7f164 : fetch_word Ubsan.M.loaded_segments (0x7f164 : word) = Some W_7f164.
Proof. vm_refl. Qed.
Lemma D_7f164 : decode_any W_7f164 = Some (Store SZ8 2 24 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f168 : bv 32 := 0x09913423.
Lemma F_7f168 : fetch_word Ubsan.M.loaded_segments (0x7f168 : word) = Some W_7f168.
Proof. vm_refl. Qed.
Lemma D_7f168 : decode_any W_7f168 = Some (Store SZ8 2 25 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f16c : bv 32 := 0x09a13023.
Lemma F_7f16c : fetch_word Ubsan.M.loaded_segments (0x7f16c : word) = Some W_7f16c.
Proof. vm_refl. Qed.
Lemma D_7f16c : decode_any W_7f16c = Some (Store SZ8 2 26 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f170 : bv 32 := 0x07b13c23.
Lemma F_7f170 : fetch_word Ubsan.M.loaded_segments (0x7f170 : word) = Some W_7f170.
Proof. vm_refl. Qed.
Lemma D_7f170 : decode_any W_7f170 = Some (Store SZ8 2 27 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f174 : bv 32 := 0x0a050863.
Lemma F_7f174 : fetch_word Ubsan.M.loaded_segments (0x7f174 : word) = Some W_7f174.
Proof. vm_refl. Qed.
Lemma D_7f174 : decode_any W_7f174 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f178 : bv 32 := 0x00078993.
Lemma F_7f178 : fetch_word Ubsan.M.loaded_segments (0x7f178 : word) = Some W_7f178.
Proof. vm_refl. Qed.
Lemma D_7f178 : decode_any W_7f178 = Some (OpImm ALU_ADD 19 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f17c : bv 32 := 0x00a00793.
Lemma F_7f17c : fetch_word Ubsan.M.loaded_segments (0x7f17c : word) = Some W_7f17c.
Proof. vm_refl. Qed.
Lemma D_7f17c : decode_any W_7f17c = Some (OpImm ALU_ADD 15 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f180 : bv 32 := 0x08f98e63.
Lemma F_7f180 : fetch_word Ubsan.M.loaded_segments (0x7f180 : word) = Some W_7f180.
Proof. vm_refl. Qed.
Lemma D_7f180 : decode_any W_7f180 = Some (Branch BC_EQ 19 15 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f184 : bv 32 := 0x00080c93.
Lemma F_7f184 : fetch_word Ubsan.M.loaded_segments (0x7f184 : word) = Some W_7f184.
Proof. vm_refl. Qed.
Lemma D_7f184 : decode_any W_7f184 = Some (OpImm ALU_ADD 25 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f188 : bv 32 := 0x00088b13.
Lemma F_7f188 : fetch_word Ubsan.M.loaded_segments (0x7f188 : word) = Some W_7f188.
Proof. vm_refl. Qed.
Lemma D_7f188 : decode_any W_7f188 = Some (OpImm ALU_ADD 22 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f18c : bv 32 := 0x00070d93.
Lemma F_7f18c : fetch_word Ubsan.M.loaded_segments (0x7f18c : word) = Some W_7f18c.
Proof. vm_refl. Qed.
Lemma D_7f18c : decode_any W_7f18c = Some (OpImm ALU_ADD 27 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f190 : bv 32 := 0x00058913.
Lemma F_7f190 : fetch_word Ubsan.M.loaded_segments (0x7f190 : word) = Some W_7f190.
Proof. vm_refl. Qed.
Lemma D_7f190 : decode_any W_7f190 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f194 : bv 32 := 0x00060493.
Lemma F_7f194 : fetch_word Ubsan.M.loaded_segments (0x7f194 : word) = Some W_7f194.
Proof. vm_refl. Qed.
Lemma D_7f194 : decode_any W_7f194 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f198 : bv 32 := 0x00068413.
Lemma F_7f198 : fetch_word Ubsan.M.loaded_segments (0x7f198 : word) = Some W_7f198.
Proof. vm_refl. Qed.
Lemma D_7f198 : decode_any W_7f198 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f19c : bv 32 := 0x0e013a83.
Lemma F_7f19c : fetch_word Ubsan.M.loaded_segments (0x7f19c : word) = Some W_7f19c.
Proof. vm_refl. Qed.
Lemma D_7f19c : decode_any W_7f19c = Some (Load SZ8 true 21 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a0 : bv 32 := 0x07410593.
Lemma F_7f1a0 : fetch_word Ubsan.M.loaded_segments (0x7f1a0 : word) = Some W_7f1a0.
Proof. vm_refl. Qed.
Lemma D_7f1a0 : decode_any W_7f1a0 = Some (OpImm ALU_ADD 11 2 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a4 : bv 32 := 0x07010613.
Lemma F_7f1a4 : fetch_word Ubsan.M.loaded_segments (0x7f1a4 : word) = Some W_7f1a4.
Proof. vm_refl. Qed.
Lemma D_7f1a4 : decode_any W_7f1a4 = Some (OpImm ALU_ADD 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a8 : bv 32 := 0x06c10693.
Lemma F_7f1a8 : fetch_word Ubsan.M.loaded_segments (0x7f1a8 : word) = Some W_7f1a8.
Proof. vm_refl. Qed.
Lemma D_7f1a8 : decode_any W_7f1a8 = Some (OpImm ALU_ADD 13 2 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1ac : bv 32 := 0x00050a13.
Lemma F_7f1ac : fetch_word Ubsan.M.loaded_segments (0x7f1ac : word) = Some W_7f1ac.
Proof. vm_refl. Qed.
Lemma D_7f1ac : decode_any W_7f1ac = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b0 : bv 32 := 0x8f4ef0ef.
Lemma F_7f1b0 : fetch_word Ubsan.M.loaded_segments (0x7f1b0 : word) = Some W_7f1b0.
Proof. vm_refl. Qed.
Lemma D_7f1b0 : decode_any W_7f1b0 = Some (Jal 1 2027764, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b4 : bv 32 := 0x00f00513.
Lemma F_7f1b4 : fetch_word Ubsan.M.loaded_segments (0x7f1b4 : word) = Some W_7f1b4.
Proof. vm_refl. Qed.
Lemma D_7f1b4 : decode_any W_7f1b4 = Some (OpImm ALU_ADD 10 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b8 : bv 32 := 0x0d356863.
Lemma F_7f1b8 : fetch_word Ubsan.M.loaded_segments (0x7f1b8 : word) = Some W_7f1b8.
Proof. vm_refl. Qed.
Lemma D_7f1b8 : decode_any W_7f1b8 = Some (Branch BC_LTU 10 19 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1bc : bv 32 := 0x00008537.
Lemma F_7f1bc : fetch_word Ubsan.M.loaded_segments (0x7f1bc : word) = Some W_7f1bc.
Proof. vm_refl. Qed.
Lemma D_7f1bc : decode_any W_7f1bc = Some (Lui 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c0 : bv 32 := 0x0215051b.
Lemma F_7f1c0 : fetch_word Ubsan.M.loaded_segments (0x7f1c0 : word) = Some W_7f1c0.
Proof. vm_refl. Qed.
Lemma D_7f1c0 : decode_any W_7f1c0 = Some (OpImm32 10 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c4 : bv 32 := 0x01355533.
Lemma F_7f1c4 : fetch_word Ubsan.M.loaded_segments (0x7f1c4 : word) = Some W_7f1c4.
Proof. vm_refl. Qed.
Lemma D_7f1c4 : decode_any W_7f1c4 = Some (Op ALU_SRL 10 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c8 : bv 32 := 0x00157513.
Lemma F_7f1c8 : fetch_word Ubsan.M.loaded_segments (0x7f1c8 : word) = Some W_7f1c8.
Proof. vm_refl. Qed.
Lemma D_7f1c8 : decode_any W_7f1c8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1cc : bv 32 := 0x0a050e63.
Lemma F_7f1cc : fetch_word Ubsan.M.loaded_segments (0x7f1cc : word) = Some W_7f1cc.
Proof. vm_refl. Qed.
Lemma D_7f1cc : decode_any W_7f1cc = Some (Branch BC_EQ 10 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d0 : bv 32 := 0x000a0513.
Lemma F_7f1d0 : fetch_word Ubsan.M.loaded_segments (0x7f1d0 : word) = Some W_7f1d0.
Proof. vm_refl. Qed.
Lemma D_7f1d0 : decode_any W_7f1d0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d4 : bv 32 := 0x818f00ef.
Lemma F_7f1d4 : fetch_word Ubsan.M.loaded_segments (0x7f1d4 : word) = Some W_7f1d4.
Proof. vm_refl. Qed.
Lemma D_7f1d4 : decode_any W_7f1d4 = Some (Jal 1 2031640, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d8 : bv 32 := 0x07412a83.
Lemma F_7f1d8 : fetch_word Ubsan.M.loaded_segments (0x7f1d8 : word) = Some W_7f1d8.
Proof. vm_refl. Qed.
Lemma D_7f1d8 : decode_any W_7f1d8 = Some (Load SZ4 true 21 2 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1dc : bv 32 := 0x07012b03.
Lemma F_7f1dc : fetch_word Ubsan.M.loaded_segments (0x7f1dc : word) = Some W_7f1dc.
Proof. vm_refl. Qed.
Lemma D_7f1dc : decode_any W_7f1dc = Some (Load SZ4 true 22 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1e0 : bv 32 := 0x06c12b83.
Lemma F_7f1e0 : fetch_word Ubsan.M.loaded_segments (0x7f1e0 : word) = Some W_7f1e0.
Proof. vm_refl. Qed.
Lemma D_7f1e0 : decode_any W_7f1e0 = Some (Load SZ4 true 23 2 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1e4 : bv 32 := 0x00050c13.
Lemma F_7f1e4 : fetch_word Ubsan.M.loaded_segments (0x7f1e4 : word) = Some W_7f1e4.
Proof. vm_refl. Qed.
Lemma D_7f1e4 : decode_any W_7f1e4 = Some (OpImm ALU_ADD 24 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1e8 : bv 32 := 0x000a0513.
Lemma F_7f1e8 : fetch_word Ubsan.M.loaded_segments (0x7f1e8 : word) = Some W_7f1e8.
Proof. vm_refl. Qed.
Lemma D_7f1e8 : decode_any W_7f1e8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1ec : bv 32 := 0xd61ee0ef.
Lemma F_7f1ec : fetch_word Ubsan.M.loaded_segments (0x7f1ec : word) = Some W_7f1ec.
Proof. vm_refl. Qed.
Lemma D_7f1ec : decode_any W_7f1ec = Some (Jal 1 2026848, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f0 : bv 32 := 0x00050713.
Lemma F_7f1f0 : fetch_word Ubsan.M.loaded_segments (0x7f1f0 : word) = Some W_7f1f0.
Proof. vm_refl. Qed.
Lemma D_7f1f0 : decode_any W_7f1f0 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f4 : bv 32 := 0x01b13023.
Lemma F_7f1f4 : fetch_word Ubsan.M.loaded_segments (0x7f1f4 : word) = Some W_7f1f4.
Proof. vm_refl. Qed.
Lemma D_7f1f4 : decode_any W_7f1f4 = Some (Store SZ8 2 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f8 : bv 32 := 0x01313423.
Lemma F_7f1f8 : fetch_word Ubsan.M.loaded_segments (0x7f1f8 : word) = Some W_7f1f8.
Proof. vm_refl. Qed.
Lemma D_7f1f8 : decode_any W_7f1f8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1fc : bv 32 := 0x000c0513.
Lemma F_7f1fc : fetch_word Ubsan.M.loaded_segments (0x7f1fc : word) = Some W_7f1fc.
Proof. vm_refl. Qed.
Lemma D_7f1fc : decode_any W_7f1fc = Some (OpImm ALU_ADD 10 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f200 : bv 32 := 0x000a8593.
Lemma F_7f200 : fetch_word Ubsan.M.loaded_segments (0x7f200 : word) = Some W_7f200.
Proof. vm_refl. Qed.
Lemma D_7f200 : decode_any W_7f200 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f204 : bv 32 := 0x000b0613.
Lemma F_7f204 : fetch_word Ubsan.M.loaded_segments (0x7f204 : word) = Some W_7f204.
Proof. vm_refl. Qed.
Lemma D_7f204 : decode_any W_7f204 = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f208 : bv 32 := 0x000b8693.
Lemma F_7f208 : fetch_word Ubsan.M.loaded_segments (0x7f208 : word) = Some W_7f208.
Proof. vm_refl. Qed.
Lemma D_7f208 : decode_any W_7f208 = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f20c : bv 32 := 0x00090793.
Lemma F_7f20c : fetch_word Ubsan.M.loaded_segments (0x7f20c : word) = Some W_7f20c.
Proof. vm_refl. Qed.
Lemma D_7f20c : decode_any W_7f20c = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f210 : bv 32 := 0x00048813.
Lemma F_7f210 : fetch_word Ubsan.M.loaded_segments (0x7f210 : word) = Some W_7f210.
Proof. vm_refl. Qed.
Lemma D_7f210 : decode_any W_7f210 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f214 : bv 32 := 0x00040893.
Lemma F_7f214 : fetch_word Ubsan.M.loaded_segments (0x7f214 : word) = Some W_7f214.
Proof. vm_refl. Qed.
Lemma D_7f214 : decode_any W_7f214 = Some (OpImm ALU_ADD 17 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f218 : bv 32 := 0x1c0000ef.
Lemma F_7f218 : fetch_word Ubsan.M.loaded_segments (0x7f218 : word) = Some W_7f218.
Proof. vm_refl. Qed.
Lemma D_7f218 : decode_any W_7f218 = Some (Jal 1 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f21c : bv 32 := 0x00000513.
Lemma F_7f21c : fetch_word Ubsan.M.loaded_segments (0x7f21c : word) = Some W_7f21c.
Proof. vm_refl. Qed.
Lemma D_7f21c : decode_any W_7f21c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f220 : bv 32 := 0x17c0006f.
Lemma F_7f220 : fetch_word Ubsan.M.loaded_segments (0x7f220 : word) = Some W_7f220.
Proof. vm_refl. Qed.
Lemma D_7f220 : decode_any W_7f220 = Some (Jal 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f224 : bv 32 := 0x000a8517.
Lemma F_7f224 : fetch_word Ubsan.M.loaded_segments (0x7f224 : word) = Some W_7f224.
Proof. vm_refl. Qed.
Lemma D_7f224 : decode_any W_7f224 = Some (Auipc 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f228 : bv 32 := 0x84c53503.
Lemma F_7f228 : fetch_word Ubsan.M.loaded_segments (0x7f228 : word) = Some W_7f228.
Proof. vm_refl. Qed.
Lemma D_7f228 : decode_any W_7f228 = Some (Load SZ8 true 10 10 2124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f22c : bv 32 := 0x00052503.
Lemma F_7f22c : fetch_word Ubsan.M.loaded_segments (0x7f22c : word) = Some W_7f22c.
Proof. vm_refl. Qed.
Lemma D_7f22c : decode_any W_7f22c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f230 : bv 32 := 0x00500593.
Lemma F_7f230 : fetch_word Ubsan.M.loaded_segments (0x7f230 : word) = Some W_7f230.
Proof. vm_refl. Qed.
Lemma D_7f230 : decode_any W_7f230 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f234 : bv 32 := 0x16a5c263.
Lemma F_7f234 : fetch_word Ubsan.M.loaded_segments (0x7f234 : word) = Some W_7f234.
Proof. vm_refl. Qed.
Lemma D_7f234 : decode_any W_7f234 = Some (Branch BC_LT 11 10 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f238 : bv 32 := 0xfff9b517.
Lemma F_7f238 : fetch_word Ubsan.M.loaded_segments (0x7f238 : word) = Some W_7f238.
Proof. vm_refl. Qed.
Lemma D_7f238 : decode_any W_7f238 = Some (Auipc 10 1048475, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f23c : bv 32 := 0xfff9a597.
Lemma F_7f23c : fetch_word Ubsan.M.loaded_segments (0x7f23c : word) = Some W_7f23c.
Proof. vm_refl. Qed.
Lemma D_7f23c : decode_any W_7f23c = Some (Auipc 11 1048474, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f240 : bv 32 := 0x89c50513.
Lemma F_7f240 : fetch_word Ubsan.M.loaded_segments (0x7f240 : word) = Some W_7f240.
Proof. vm_refl. Qed.
Lemma D_7f240 : decode_any W_7f240 = Some (OpImm ALU_ADD 10 10 2204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f244 : bv 32 := 0xa0358593.
Lemma F_7f244 : fetch_word Ubsan.M.loaded_segments (0x7f244 : word) = Some W_7f244.
Proof. vm_refl. Qed.
Lemma D_7f244 : decode_any W_7f244 = Some (OpImm ALU_ADD 11 11 2563, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f248 : bv 32 := 0x00100613.
Lemma F_7f248 : fetch_word Ubsan.M.loaded_segments (0x7f248 : word) = Some W_7f248.
Proof. vm_refl. Qed.
Lemma D_7f248 : decode_any W_7f248 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f24c : bv 32 := 0x0d813083.
Lemma F_7f24c : fetch_word Ubsan.M.loaded_segments (0x7f24c : word) = Some W_7f24c.
Proof. vm_refl. Qed.
Lemma D_7f24c : decode_any W_7f24c = Some (Load SZ8 true 1 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f250 : bv 32 := 0x0d013403.
Lemma F_7f250 : fetch_word Ubsan.M.loaded_segments (0x7f250 : word) = Some W_7f250.
Proof. vm_refl. Qed.
Lemma D_7f250 : decode_any W_7f250 = Some (Load SZ8 true 8 2 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f254 : bv 32 := 0x0c813483.
Lemma F_7f254 : fetch_word Ubsan.M.loaded_segments (0x7f254 : word) = Some W_7f254.
Proof. vm_refl. Qed.
Lemma D_7f254 : decode_any W_7f254 = Some (Load SZ8 true 9 2 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f258 : bv 32 := 0x0c013903.
Lemma F_7f258 : fetch_word Ubsan.M.loaded_segments (0x7f258 : word) = Some W_7f258.
Proof. vm_refl. Qed.
Lemma D_7f258 : decode_any W_7f258 = Some (Load SZ8 true 18 2 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f25c : bv 32 := 0x0b813983.
Lemma F_7f25c : fetch_word Ubsan.M.loaded_segments (0x7f25c : word) = Some W_7f25c.
Proof. vm_refl. Qed.
Lemma D_7f25c : decode_any W_7f25c = Some (Load SZ8 true 19 2 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f260 : bv 32 := 0x0b013a03.
Lemma F_7f260 : fetch_word Ubsan.M.loaded_segments (0x7f260 : word) = Some W_7f260.
Proof. vm_refl. Qed.
Lemma D_7f260 : decode_any W_7f260 = Some (Load SZ8 true 20 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f264 : bv 32 := 0x0a813a83.
Lemma F_7f264 : fetch_word Ubsan.M.loaded_segments (0x7f264 : word) = Some W_7f264.
Proof. vm_refl. Qed.
Lemma D_7f264 : decode_any W_7f264 = Some (Load SZ8 true 21 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f268 : bv 32 := 0x0a013b03.
Lemma F_7f268 : fetch_word Ubsan.M.loaded_segments (0x7f268 : word) = Some W_7f268.
Proof. vm_refl. Qed.
Lemma D_7f268 : decode_any W_7f268 = Some (Load SZ8 true 22 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f26c : bv 32 := 0x09813b83.
Lemma F_7f26c : fetch_word Ubsan.M.loaded_segments (0x7f26c : word) = Some W_7f26c.
Proof. vm_refl. Qed.
Lemma D_7f26c : decode_any W_7f26c = Some (Load SZ8 true 23 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f270 : bv 32 := 0x09013c03.
Lemma F_7f270 : fetch_word Ubsan.M.loaded_segments (0x7f270 : word) = Some W_7f270.
Proof. vm_refl. Qed.
Lemma D_7f270 : decode_any W_7f270 = Some (Load SZ8 true 24 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f274 : bv 32 := 0x08813c83.
Lemma F_7f274 : fetch_word Ubsan.M.loaded_segments (0x7f274 : word) = Some W_7f274.
Proof. vm_refl. Qed.
Lemma D_7f274 : decode_any W_7f274 = Some (Load SZ8 true 25 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f278 : bv 32 := 0x08013d03.
Lemma F_7f278 : fetch_word Ubsan.M.loaded_segments (0x7f278 : word) = Some W_7f278.
Proof. vm_refl. Qed.
Lemma D_7f278 : decode_any W_7f278 = Some (Load SZ8 true 26 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f27c : bv 32 := 0x07813d83.
Lemma F_7f27c : fetch_word Ubsan.M.loaded_segments (0x7f27c : word) = Some W_7f27c.
Proof. vm_refl. Qed.
Lemma D_7f27c : decode_any W_7f27c = Some (Load SZ8 true 27 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f280 : bv 32 := 0x0e010113.
Lemma F_7f280 : fetch_word Ubsan.M.loaded_segments (0x7f280 : word) = Some W_7f280.
Proof. vm_refl. Qed.
Lemma D_7f280 : decode_any W_7f280 = Some (OpImm ALU_ADD 2 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f284 : bv 32 := 0xbece406f.
Lemma F_7f284 : fetch_word Ubsan.M.loaded_segments (0x7f284 : word) = Some W_7f284.
Proof. vm_refl. Qed.
Lemma D_7f284 : decode_any W_7f284 = Some (Jal 0 1983468, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f288 : bv 32 := 0x0a0c8c63.
Lemma F_7f288 : fetch_word Ubsan.M.loaded_segments (0x7f288 : word) = Some W_7f288.
Proof. vm_refl. Qed.
Lemma D_7f288 : decode_any W_7f288 = Some (Branch BC_EQ 25 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f28c : bv 32 := 0x000c8513.
Lemma F_7f28c : fetch_word Ubsan.M.loaded_segments (0x7f28c : word) = Some W_7f28c.
Proof. vm_refl. Qed.
Lemma D_7f28c : decode_any W_7f28c = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f290 : bv 32 := 0x06810593.
Lemma F_7f290 : fetch_word Ubsan.M.loaded_segments (0x7f290 : word) = Some W_7f290.
Proof. vm_refl. Qed.
Lemma D_7f290 : decode_any W_7f290 = Some (OpImm ALU_ADD 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f294 : bv 32 := 0x06410613.
Lemma F_7f294 : fetch_word Ubsan.M.loaded_segments (0x7f294 : word) = Some W_7f294.
Proof. vm_refl. Qed.
Lemma D_7f294 : decode_any W_7f294 = Some (OpImm ALU_ADD 12 2 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f298 : bv 32 := 0x06010693.
Lemma F_7f298 : fetch_word Ubsan.M.loaded_segments (0x7f298 : word) = Some W_7f298.
Proof. vm_refl. Qed.
Lemma D_7f298 : decode_any W_7f298 = Some (OpImm ALU_ADD 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f29c : bv 32 := 0x808ef0ef.
Lemma F_7f29c : fetch_word Ubsan.M.loaded_segments (0x7f29c : word) = Some W_7f29c.
Proof. vm_refl. Qed.
Lemma D_7f29c : decode_any W_7f29c = Some (Jal 1 2027528, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a0 : bv 32 := 0x06c12503.
Lemma F_7f2a0 : fetch_word Ubsan.M.loaded_segments (0x7f2a0 : word) = Some W_7f2a0.
Proof. vm_refl. Qed.
Lemma D_7f2a0 : decode_any W_7f2a0 = Some (Load SZ4 true 10 2 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a4 : bv 32 := 0x06012583.
Lemma F_7f2a4 : fetch_word Ubsan.M.loaded_segments (0x7f2a4 : word) = Some W_7f2a4.
Proof. vm_refl. Qed.
Lemma D_7f2a4 : decode_any W_7f2a4 = Some (Load SZ4 true 11 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a8 : bv 32 := 0x0cb51063.
Lemma F_7f2a8 : fetch_word Ubsan.M.loaded_segments (0x7f2a8 : word) = Some W_7f2a8.
Proof. vm_refl. Qed.
Lemma D_7f2a8 : decode_any W_7f2a8 = Some (Branch BC_NE 10 11 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2ac : bv 32 := 0x000a0513.
Lemma F_7f2ac : fetch_word Ubsan.M.loaded_segments (0x7f2ac : word) = Some W_7f2ac.
Proof. vm_refl. Qed.
Lemma D_7f2ac : decode_any W_7f2ac = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b0 : bv 32 := 0xf3def0ef.
Lemma F_7f2b0 : fetch_word Ubsan.M.loaded_segments (0x7f2b0 : word) = Some W_7f2b0.
Proof. vm_refl. Qed.
Lemma D_7f2b0 : decode_any W_7f2b0 = Some (Jal 1 2031420, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b4 : bv 32 := 0x07412583.
Lemma F_7f2b4 : fetch_word Ubsan.M.loaded_segments (0x7f2b4 : word) = Some W_7f2b4.
Proof. vm_refl. Qed.
Lemma D_7f2b4 : decode_any W_7f2b4 = Some (Load SZ4 true 11 2 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b8 : bv 32 := 0x04b13c23.
Lemma F_7f2b8 : fetch_word Ubsan.M.loaded_segments (0x7f2b8 : word) = Some W_7f2b8.
Proof. vm_refl. Qed.
Lemma D_7f2b8 : decode_any W_7f2b8 = Some (Store SZ8 2 11 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2bc : bv 32 := 0x07012583.
Lemma F_7f2bc : fetch_word Ubsan.M.loaded_segments (0x7f2bc : word) = Some W_7f2bc.
Proof. vm_refl. Qed.
Lemma D_7f2bc : decode_any W_7f2bc = Some (Load SZ4 true 11 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c0 : bv 32 := 0x04b13823.
Lemma F_7f2c0 : fetch_word Ubsan.M.loaded_segments (0x7f2c0 : word) = Some W_7f2c0.
Proof. vm_refl. Qed.
Lemma D_7f2c0 : decode_any W_7f2c0 = Some (Store SZ8 2 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c4 : bv 32 := 0x06c12583.
Lemma F_7f2c4 : fetch_word Ubsan.M.loaded_segments (0x7f2c4 : word) = Some W_7f2c4.
Proof. vm_refl. Qed.
Lemma D_7f2c4 : decode_any W_7f2c4 = Some (Load SZ4 true 11 2 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c8 : bv 32 := 0x04b13423.
Lemma F_7f2c8 : fetch_word Ubsan.M.loaded_segments (0x7f2c8 : word) = Some W_7f2c8.
Proof. vm_refl. Qed.
Lemma D_7f2c8 : decode_any W_7f2c8 = Some (Store SZ8 2 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2cc : bv 32 := 0x04a13023.
Lemma F_7f2cc : fetch_word Ubsan.M.loaded_segments (0x7f2cc : word) = Some W_7f2cc.
Proof. vm_refl. Qed.
Lemma D_7f2cc : decode_any W_7f2cc = Some (Store SZ8 2 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d0 : bv 32 := 0x000a0513.
Lemma F_7f2d0 : fetch_word Ubsan.M.loaded_segments (0x7f2d0 : word) = Some W_7f2d0.
Proof. vm_refl. Qed.
Lemma D_7f2d0 : decode_any W_7f2d0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d4 : bv 32 := 0xc79ee0ef.
Lemma F_7f2d4 : fetch_word Ubsan.M.loaded_segments (0x7f2d4 : word) = Some W_7f2d4.
Proof. vm_refl. Qed.
Lemma D_7f2d4 : decode_any W_7f2d4 = Some (Jal 1 2026616, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d8 : bv 32 := 0x00050a13.
Lemma F_7f2d8 : fetch_word Ubsan.M.loaded_segments (0x7f2d8 : word) = Some W_7f2d8.
Proof. vm_refl. Qed.
Lemma D_7f2d8 : decode_any W_7f2d8 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2dc : bv 32 := 0x000c8513.
Lemma F_7f2dc : fetch_word Ubsan.M.loaded_segments (0x7f2dc : word) = Some W_7f2dc.
Proof. vm_refl. Qed.
Lemma D_7f2dc : decode_any W_7f2dc = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e0 : bv 32 := 0xf0def0ef.
Lemma F_7f2e0 : fetch_word Ubsan.M.loaded_segments (0x7f2e0 : word) = Some W_7f2e0.
Proof. vm_refl. Qed.
Lemma D_7f2e0 : decode_any W_7f2e0 = Some (Jal 1 2031372, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e4 : bv 32 := 0x06812b83.
Lemma F_7f2e4 : fetch_word Ubsan.M.loaded_segments (0x7f2e4 : word) = Some W_7f2e4.
Proof. vm_refl. Qed.
Lemma D_7f2e4 : decode_any W_7f2e4 = Some (Load SZ4 true 23 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e8 : bv 32 := 0x06412c03.
Lemma F_7f2e8 : fetch_word Ubsan.M.loaded_segments (0x7f2e8 : word) = Some W_7f2e8.
Proof. vm_refl. Qed.
Lemma D_7f2e8 : decode_any W_7f2e8 = Some (Load SZ4 true 24 2 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2ec : bv 32 := 0x00050d13.
Lemma F_7f2ec : fetch_word Ubsan.M.loaded_segments (0x7f2ec : word) = Some W_7f2ec.
Proof. vm_refl. Qed.
Lemma D_7f2ec : decode_any W_7f2ec = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f0 : bv 32 := 0x000c8513.
Lemma F_7f2f0 : fetch_word Ubsan.M.loaded_segments (0x7f2f0 : word) = Some W_7f2f0.
Proof. vm_refl. Qed.
Lemma D_7f2f0 : decode_any W_7f2f0 = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f4 : bv 32 := 0xc59ee0ef.
Lemma F_7f2f4 : fetch_word Ubsan.M.loaded_segments (0x7f2f4 : word) = Some W_7f2f4.
Proof. vm_refl. Qed.
Lemma D_7f2f4 : decode_any W_7f2f4 = Some (Jal 1 2026584, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f8 : bv 32 := 0x03813023.
Lemma F_7f2f8 : fetch_word Ubsan.M.loaded_segments (0x7f2f8 : word) = Some W_7f2f8.
Proof. vm_refl. Qed.
Lemma D_7f2f8 : decode_any W_7f2f8 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2fc : bv 32 := 0x02a13423.
Lemma F_7f2fc : fetch_word Ubsan.M.loaded_segments (0x7f2fc : word) = Some W_7f2fc.
Proof. vm_refl. Qed.
Lemma D_7f2fc : decode_any W_7f2fc = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f300 : bv 32 := 0x03613823.
Lemma F_7f300 : fetch_word Ubsan.M.loaded_segments (0x7f300 : word) = Some W_7f300.
Proof. vm_refl. Qed.
Lemma D_7f300 : decode_any W_7f300 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f304 : bv 32 := 0x03513c23.
Lemma F_7f304 : fetch_word Ubsan.M.loaded_segments (0x7f304 : word) = Some W_7f304.
Proof. vm_refl. Qed.
Lemma D_7f304 : decode_any W_7f304 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f308 : bv 32 := 0x01b13023.
Lemma F_7f308 : fetch_word Ubsan.M.loaded_segments (0x7f308 : word) = Some W_7f308.
Proof. vm_refl. Qed.
Lemma D_7f308 : decode_any W_7f308 = Some (Store SZ8 2 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f30c : bv 32 := 0x01313423.
Lemma F_7f30c : fetch_word Ubsan.M.loaded_segments (0x7f30c : word) = Some W_7f30c.
Proof. vm_refl. Qed.
Lemma D_7f30c : decode_any W_7f30c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f310 : bv 32 := 0x01a13823.
Lemma F_7f310 : fetch_word Ubsan.M.loaded_segments (0x7f310 : word) = Some W_7f310.
Proof. vm_refl. Qed.
Lemma D_7f310 : decode_any W_7f310 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f314 : bv 32 := 0x01713c23.
Lemma F_7f314 : fetch_word Ubsan.M.loaded_segments (0x7f314 : word) = Some W_7f314.
Proof. vm_refl. Qed.
Lemma D_7f314 : decode_any W_7f314 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f318 : bv 32 := 0x04013503.
Lemma F_7f318 : fetch_word Ubsan.M.loaded_segments (0x7f318 : word) = Some W_7f318.
Proof. vm_refl. Qed.
Lemma D_7f318 : decode_any W_7f318 = Some (Load SZ8 true 10 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f31c : bv 32 := 0x05813583.
Lemma F_7f31c : fetch_word Ubsan.M.loaded_segments (0x7f31c : word) = Some W_7f31c.
Proof. vm_refl. Qed.
Lemma D_7f31c : decode_any W_7f31c = Some (Load SZ8 true 11 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f320 : bv 32 := 0x05013603.
Lemma F_7f320 : fetch_word Ubsan.M.loaded_segments (0x7f320 : word) = Some W_7f320.
Proof. vm_refl. Qed.
Lemma D_7f320 : decode_any W_7f320 = Some (Load SZ8 true 12 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f324 : bv 32 := 0x04813683.
Lemma F_7f324 : fetch_word Ubsan.M.loaded_segments (0x7f324 : word) = Some W_7f324.
Proof. vm_refl. Qed.
Lemma D_7f324 : decode_any W_7f324 = Some (Load SZ8 true 13 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f328 : bv 32 := 0x000a0713.
Lemma F_7f328 : fetch_word Ubsan.M.loaded_segments (0x7f328 : word) = Some W_7f328.
Proof. vm_refl. Qed.
Lemma D_7f328 : decode_any W_7f328 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f32c : bv 32 := 0x00090793.
Lemma F_7f32c : fetch_word Ubsan.M.loaded_segments (0x7f32c : word) = Some W_7f32c.
Proof. vm_refl. Qed.
Lemma D_7f32c : decode_any W_7f32c = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f330 : bv 32 := 0x00048813.
Lemma F_7f330 : fetch_word Ubsan.M.loaded_segments (0x7f330 : word) = Some W_7f330.
Proof. vm_refl. Qed.
Lemma D_7f330 : decode_any W_7f330 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f334 : bv 32 := 0x00040893.
Lemma F_7f334 : fetch_word Ubsan.M.loaded_segments (0x7f334 : word) = Some W_7f334.
Proof. vm_refl. Qed.
Lemma D_7f334 : decode_any W_7f334 = Some (OpImm ALU_ADD 17 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f338 : bv 32 := 0x165000ef.
Lemma F_7f338 : fetch_word Ubsan.M.loaded_segments (0x7f338 : word) = Some W_7f338.
Proof. vm_refl. Qed.
Lemma D_7f338 : decode_any W_7f338 = Some (Jal 1 2404, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f33c : bv 32 := 0xee1ff06f.
Lemma F_7f33c : fetch_word Ubsan.M.loaded_segments (0x7f33c : word) = Some W_7f33c.
Proof. vm_refl. Qed.
Lemma D_7f33c : decode_any W_7f33c = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f340 : bv 32 := 0x000a7517.
Lemma F_7f340 : fetch_word Ubsan.M.loaded_segments (0x7f340 : word) = Some W_7f340.
Proof. vm_refl. Qed.
Lemma D_7f340 : decode_any W_7f340 = Some (Auipc 10 167, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f344 : bv 32 := 0x73053503.
Lemma F_7f344 : fetch_word Ubsan.M.loaded_segments (0x7f344 : word) = Some W_7f344.
Proof. vm_refl. Qed.
Lemma D_7f344 : decode_any W_7f344 = Some (Load SZ8 true 10 10 1840, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f348 : bv 32 := 0x00052503.
Lemma F_7f348 : fetch_word Ubsan.M.loaded_segments (0x7f348 : word) = Some W_7f348.
Proof. vm_refl. Qed.
Lemma D_7f348 : decode_any W_7f348 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f34c : bv 32 := 0x00500593.
Lemma F_7f34c : fetch_word Ubsan.M.loaded_segments (0x7f34c : word) = Some W_7f34c.
Proof. vm_refl. Qed.
Lemma D_7f34c : decode_any W_7f34c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f350 : bv 32 := 0x04a5c463.
Lemma F_7f350 : fetch_word Ubsan.M.loaded_segments (0x7f350 : word) = Some W_7f350.
Proof. vm_refl. Qed.
Lemma D_7f350 : decode_any W_7f350 = Some (Branch BC_LT 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f354 : bv 32 := 0xfff91517.
Lemma F_7f354 : fetch_word Ubsan.M.loaded_segments (0x7f354 : word) = Some W_7f354.
Proof. vm_refl. Qed.
Lemma D_7f354 : decode_any W_7f354 = Some (Auipc 10 1048465, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f358 : bv 32 := 0xfff9a597.
Lemma F_7f358 : fetch_word Ubsan.M.loaded_segments (0x7f358 : word) = Some W_7f358.
Proof. vm_refl. Qed.
Lemma D_7f358 : decode_any W_7f358 = Some (Auipc 11 1048474, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f35c : bv 32 := 0x00150513.
Lemma F_7f35c : fetch_word Ubsan.M.loaded_segments (0x7f35c : word) = Some W_7f35c.
Proof. vm_refl. Qed.
Lemma D_7f35c : decode_any W_7f35c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f360 : bv 32 := 0x8e758593.
Lemma F_7f360 : fetch_word Ubsan.M.loaded_segments (0x7f360 : word) = Some W_7f360.
Proof. vm_refl. Qed.
Lemma D_7f360 : decode_any W_7f360 = Some (OpImm ALU_ADD 11 11 2279, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f364 : bv 32 := 0x0280006f.
Lemma F_7f364 : fetch_word Ubsan.M.loaded_segments (0x7f364 : word) = Some W_7f364.
Proof. vm_refl. Qed.
Lemma D_7f364 : decode_any W_7f364 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f368 : bv 32 := 0x000a7517.
Lemma F_7f368 : fetch_word Ubsan.M.loaded_segments (0x7f368 : word) = Some W_7f368.
Proof. vm_refl. Qed.
Lemma D_7f368 : decode_any W_7f368 = Some (Auipc 10 167, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f36c : bv 32 := 0x70853503.
Lemma F_7f36c : fetch_word Ubsan.M.loaded_segments (0x7f36c : word) = Some W_7f36c.
Proof. vm_refl. Qed.
Lemma D_7f36c : decode_any W_7f36c = Some (Load SZ8 true 10 10 1800, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f370 : bv 32 := 0x00052503.
Lemma F_7f370 : fetch_word Ubsan.M.loaded_segments (0x7f370 : word) = Some W_7f370.
Proof. vm_refl. Qed.
Lemma D_7f370 : decode_any W_7f370 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f374 : bv 32 := 0x00500593.
Lemma F_7f374 : fetch_word Ubsan.M.loaded_segments (0x7f374 : word) = Some W_7f374.
Proof. vm_refl. Qed.
Lemma D_7f374 : decode_any W_7f374 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f378 : bv 32 := 0x02a5c063.
Lemma F_7f378 : fetch_word Ubsan.M.loaded_segments (0x7f378 : word) = Some W_7f378.
Proof. vm_refl. Qed.
Lemma D_7f378 : decode_any W_7f378 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f37c : bv 32 := 0xfff9c517.
Lemma F_7f37c : fetch_word Ubsan.M.loaded_segments (0x7f37c : word) = Some W_7f37c.
Proof. vm_refl. Qed.
Lemma D_7f37c : decode_any W_7f37c = Some (Auipc 10 1048476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f380 : bv 32 := 0xfff9a597.
Lemma F_7f380 : fetch_word Ubsan.M.loaded_segments (0x7f380 : word) = Some W_7f380.
Proof. vm_refl. Qed.
Lemma D_7f380 : decode_any W_7f380 = Some (Auipc 11 1048474, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f384 : bv 32 := 0x64c50513.
Lemma F_7f384 : fetch_word Ubsan.M.loaded_segments (0x7f384 : word) = Some W_7f384.
Proof. vm_refl. Qed.
Lemma D_7f384 : decode_any W_7f384 = Some (OpImm ALU_ADD 10 10 1612, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f388 : bv 32 := 0x8bf58593.
Lemma F_7f388 : fetch_word Ubsan.M.loaded_segments (0x7f388 : word) = Some W_7f388.
Proof. vm_refl. Qed.
Lemma D_7f388 : decode_any W_7f388 = Some (OpImm ALU_ADD 11 11 2239, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f38c : bv 32 := 0x00100613.
Lemma F_7f38c : fetch_word Ubsan.M.loaded_segments (0x7f38c : word) = Some W_7f38c.
Proof. vm_refl. Qed.
Lemma D_7f38c : decode_any W_7f38c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f390 : bv 32 := 0xae0e40ef.
Lemma F_7f390 : fetch_word Ubsan.M.loaded_segments (0x7f390 : word) = Some W_7f390.
Proof. vm_refl. Qed.
Lemma D_7f390 : decode_any W_7f390 = Some (Jal 1 1983200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f394 : bv 32 := 0x0080006f.
Lemma F_7f394 : fetch_word Ubsan.M.loaded_segments (0x7f394 : word) = Some W_7f394.
Proof. vm_refl. Qed.
Lemma D_7f394 : decode_any W_7f394 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f398 : bv 32 := 0x00100513.
Lemma F_7f398 : fetch_word Ubsan.M.loaded_segments (0x7f398 : word) = Some W_7f398.
Proof. vm_refl. Qed.
Lemma D_7f398 : decode_any W_7f398 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f39c : bv 32 := 0x0d813083.
Lemma F_7f39c : fetch_word Ubsan.M.loaded_segments (0x7f39c : word) = Some W_7f39c.
Proof. vm_refl. Qed.
Lemma D_7f39c : decode_any W_7f39c = Some (Load SZ8 true 1 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3a0 : bv 32 := 0x0d013403.
Lemma F_7f3a0 : fetch_word Ubsan.M.loaded_segments (0x7f3a0 : word) = Some W_7f3a0.
Proof. vm_refl. Qed.
Lemma D_7f3a0 : decode_any W_7f3a0 = Some (Load SZ8 true 8 2 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3a4 : bv 32 := 0x0c813483.
Lemma F_7f3a4 : fetch_word Ubsan.M.loaded_segments (0x7f3a4 : word) = Some W_7f3a4.
Proof. vm_refl. Qed.
Lemma D_7f3a4 : decode_any W_7f3a4 = Some (Load SZ8 true 9 2 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3a8 : bv 32 := 0x0c013903.
Lemma F_7f3a8 : fetch_word Ubsan.M.loaded_segments (0x7f3a8 : word) = Some W_7f3a8.
Proof. vm_refl. Qed.
Lemma D_7f3a8 : decode_any W_7f3a8 = Some (Load SZ8 true 18 2 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3ac : bv 32 := 0x0b813983.
Lemma F_7f3ac : fetch_word Ubsan.M.loaded_segments (0x7f3ac : word) = Some W_7f3ac.
Proof. vm_refl. Qed.
Lemma D_7f3ac : decode_any W_7f3ac = Some (Load SZ8 true 19 2 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3b0 : bv 32 := 0x0b013a03.
Lemma F_7f3b0 : fetch_word Ubsan.M.loaded_segments (0x7f3b0 : word) = Some W_7f3b0.
Proof. vm_refl. Qed.
Lemma D_7f3b0 : decode_any W_7f3b0 = Some (Load SZ8 true 20 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3b4 : bv 32 := 0x0a813a83.
Lemma F_7f3b4 : fetch_word Ubsan.M.loaded_segments (0x7f3b4 : word) = Some W_7f3b4.
Proof. vm_refl. Qed.
Lemma D_7f3b4 : decode_any W_7f3b4 = Some (Load SZ8 true 21 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3b8 : bv 32 := 0x0a013b03.
Lemma F_7f3b8 : fetch_word Ubsan.M.loaded_segments (0x7f3b8 : word) = Some W_7f3b8.
Proof. vm_refl. Qed.
Lemma D_7f3b8 : decode_any W_7f3b8 = Some (Load SZ8 true 22 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3bc : bv 32 := 0x09813b83.
Lemma F_7f3bc : fetch_word Ubsan.M.loaded_segments (0x7f3bc : word) = Some W_7f3bc.
Proof. vm_refl. Qed.
Lemma D_7f3bc : decode_any W_7f3bc = Some (Load SZ8 true 23 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3c0 : bv 32 := 0x09013c03.
Lemma F_7f3c0 : fetch_word Ubsan.M.loaded_segments (0x7f3c0 : word) = Some W_7f3c0.
Proof. vm_refl. Qed.
Lemma D_7f3c0 : decode_any W_7f3c0 = Some (Load SZ8 true 24 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3c4 : bv 32 := 0x08813c83.
Lemma F_7f3c4 : fetch_word Ubsan.M.loaded_segments (0x7f3c4 : word) = Some W_7f3c4.
Proof. vm_refl. Qed.
Lemma D_7f3c4 : decode_any W_7f3c4 = Some (Load SZ8 true 25 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3c8 : bv 32 := 0x08013d03.
Lemma F_7f3c8 : fetch_word Ubsan.M.loaded_segments (0x7f3c8 : word) = Some W_7f3c8.
Proof. vm_refl. Qed.
Lemma D_7f3c8 : decode_any W_7f3c8 = Some (Load SZ8 true 26 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3cc : bv 32 := 0x07813d83.
Lemma F_7f3cc : fetch_word Ubsan.M.loaded_segments (0x7f3cc : word) = Some W_7f3cc.
Proof. vm_refl. Qed.
Lemma D_7f3cc : decode_any W_7f3cc = Some (Load SZ8 true 27 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3d0 : bv 32 := 0x0e010113.
Lemma F_7f3d0 : fetch_word Ubsan.M.loaded_segments (0x7f3d0 : word) = Some W_7f3d0.
Proof. vm_refl. Qed.
Lemma D_7f3d0 : decode_any W_7f3d0 = Some (OpImm ALU_ADD 2 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3d4 : bv 32 := 0x00008067.
Lemma F_7f3d4 : fetch_word Ubsan.M.loaded_segments (0x7f3d4 : word) = Some W_7f3d4.
Proof. vm_refl. Qed.
Lemma D_7f3d4 : decode_any W_7f3d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
