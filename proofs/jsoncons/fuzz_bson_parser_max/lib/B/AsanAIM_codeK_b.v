(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7a768 : bv 32 := 0xfff48693.
Lemma F_7a768 : fetch_word AsanUbsan.M.loaded_segments (0x7ab80 : word) = Some W_7a768.
Proof. vm_refl. Qed.
Lemma D_7a768 : decode_any W_7a768 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a76c : bv 32 := 0x00d4b733.
Lemma F_7a76c : fetch_word AsanUbsan.M.loaded_segments (0x7ab84 : word) = Some W_7a76c.
Proof. vm_refl. Qed.
Lemma D_7a76c : decode_any W_7a76c = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a770 : bv 32 := 0xfff70713.
Lemma F_7a770 : fetch_word AsanUbsan.M.loaded_segments (0x7ab88 : word) = Some W_7a770.
Proof. vm_refl. Qed.
Lemma D_7a770 : decode_any W_7a770 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a774 : bv 32 := 0x00d77733.
Lemma F_7a774 : fetch_word AsanUbsan.M.loaded_segments (0x7ab8c : word) = Some W_7a774.
Proof. vm_refl. Qed.
Lemma D_7a774 : decode_any W_7a774 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a778 : bv 32 := 0x1ca77c63.
Lemma F_7a778 : fetch_word AsanUbsan.M.loaded_segments (0x7ab90 : word) = Some W_7a778.
Proof. vm_refl. Qed.
Lemma D_7a778 : decode_any W_7a778 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a77c : bv 32 := 0x000bd797.
Lemma F_7a77c : fetch_word AsanUbsan.M.loaded_segments (0x7ab94 : word) = Some W_7a77c.
Proof. vm_refl. Qed.
Lemma D_7a77c : decode_any W_7a77c = Some (Auipc 15 189, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a780 : bv 32 := 0x9347b783.
Lemma F_7a780 : fetch_word AsanUbsan.M.loaded_segments (0x7ab98 : word) = Some W_7a780.
Proof. vm_refl. Qed.
Lemma D_7a780 : decode_any W_7a780 = Some (Load SZ8 true 15 15 2356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a784 : bv 32 := 0x000bd817.
Lemma F_7a784 : fetch_word AsanUbsan.M.loaded_segments (0x7ab9c : word) = Some W_7a784.
Proof. vm_refl. Qed.
Lemma D_7a784 : decode_any W_7a784 = Some (Auipc 16 189, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a788 : bv 32 := 0x93483803.
Lemma F_7a788 : fetch_word AsanUbsan.M.loaded_segments (0x7aba0 : word) = Some W_7a788.
Proof. vm_refl. Qed.
Lemma D_7a788 : decode_any W_7a788 = Some (Load SZ8 true 16 16 2356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a78c : bv 32 := 0x0007b883.
Lemma F_7a78c : fetch_word AsanUbsan.M.loaded_segments (0x7aba4 : word) = Some W_7a78c.
Proof. vm_refl. Qed.
Lemma D_7a78c : decode_any W_7a78c = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a790 : bv 32 := 0x00083783.
Lemma F_7a790 : fetch_word AsanUbsan.M.loaded_segments (0x7aba8 : word) = Some W_7a790.
Proof. vm_refl. Qed.
Lemma D_7a790 : decode_any W_7a790 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a794 : bv 32 := 0xfff88813.
Lemma F_7a794 : fetch_word AsanUbsan.M.loaded_segments (0x7abac : word) = Some W_7a794.
Proof. vm_refl. Qed.
Lemma D_7a794 : decode_any W_7a794 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a798 : bv 32 := 0x00a87463.
Lemma F_7a798 : fetch_word AsanUbsan.M.loaded_segments (0x7abb0 : word) = Some W_7a798.
Proof. vm_refl. Qed.
Lemma D_7a798 : decode_any W_7a798 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a79c : bv 32 := 0x1aa7fa63.
Lemma F_7a79c : fetch_word AsanUbsan.M.loaded_segments (0x7abb4 : word) = Some W_7a79c.
Proof. vm_refl. Qed.
Lemma D_7a79c : decode_any W_7a79c = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7a0 : bv 32 := 0x000bd297.
Lemma F_7a7a0 : fetch_word AsanUbsan.M.loaded_segments (0x7abb8 : word) = Some W_7a7a0.
Proof. vm_refl. Qed.
Lemma D_7a7a0 : decode_any W_7a7a0 = Some (Auipc 5 189, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7a4 : bv 32 := 0x9202b283.
Lemma F_7a7a4 : fetch_word AsanUbsan.M.loaded_segments (0x7abbc : word) = Some W_7a7a4.
Proof. vm_refl. Qed.
Lemma D_7a7a4 : decode_any W_7a7a4 = Some (Load SZ8 true 5 5 2336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7a8 : bv 32 := 0x0002be03.
Lemma F_7a7a8 : fetch_word AsanUbsan.M.loaded_segments (0x7abc0 : word) = Some W_7a7a8.
Proof. vm_refl. Qed.
Lemma D_7a7a8 : decode_any W_7a7a8 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7ac : bv 32 := 0x003e5313.
Lemma F_7a7ac : fetch_word AsanUbsan.M.loaded_segments (0x7abc4 : word) = Some W_7a7ac.
Proof. vm_refl. Qed.
Lemma D_7a7ac : decode_any W_7a7ac = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7b0 : bv 32 := 0x009303b3.
Lemma F_7a7b0 : fetch_word AsanUbsan.M.loaded_segments (0x7abc8 : word) = Some W_7a7b0.
Proof. vm_refl. Qed.
Lemma D_7a7b0 : decode_any W_7a7b0 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7b4 : bv 32 := 0x00ae6463.
Lemma F_7a7b4 : fetch_word AsanUbsan.M.loaded_segments (0x7abcc : word) = Some W_7a7b4.
Proof. vm_refl. Qed.
Lemma D_7a7b4 : decode_any W_7a7b4 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7b8 : bv 32 := 0x0ca3e463.
Lemma F_7a7b8 : fetch_word AsanUbsan.M.loaded_segments (0x7abd0 : word) = Some W_7a7b8.
Proof. vm_refl. Qed.
Lemma D_7a7b8 : decode_any W_7a7b8 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7bc : bv 32 := 0x000bde17.
Lemma F_7a7bc : fetch_word AsanUbsan.M.loaded_segments (0x7abd4 : word) = Some W_7a7bc.
Proof. vm_refl. Qed.
Lemma D_7a7bc : decode_any W_7a7bc = Some (Auipc 28 189, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7c0 : bv 32 := 0x8e4e3e03.
Lemma F_7a7c0 : fetch_word AsanUbsan.M.loaded_segments (0x7abd8 : word) = Some W_7a7c0.
Proof. vm_refl. Qed.
Lemma D_7a7c0 : decode_any W_7a7c0 = Some (Load SZ8 true 28 28 2276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7c4 : bv 32 := 0x04ee4e03.
Lemma F_7a7c4 : fetch_word AsanUbsan.M.loaded_segments (0x7abdc : word) = Some W_7a7c4.
Proof. vm_refl. Qed.
Lemma D_7a7c4 : decode_any W_7a7c4 = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7c8 : bv 32 := 0x3e0e1063.
Lemma F_7a7c8 : fetch_word AsanUbsan.M.loaded_segments (0x7abe0 : word) = Some W_7a7c8.
Proof. vm_refl. Qed.
Lemma D_7a7c8 : decode_any W_7a7c8 = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7cc : bv 32 := 0x04088e63.
Lemma F_7a7cc : fetch_word AsanUbsan.M.loaded_segments (0x7abe4 : word) = Some W_7a7cc.
Proof. vm_refl. Qed.
Lemma D_7a7cc : decode_any W_7a7cc = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7d0 : bv 32 := 0x0038d393.
Lemma F_7a7d0 : fetch_word AsanUbsan.M.loaded_segments (0x7abe8 : word) = Some W_7a7d0.
Proof. vm_refl. Qed.
Lemma D_7a7d0 : decode_any W_7a7d0 = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7d4 : bv 32 := 0x00d383b3.
Lemma F_7a7d4 : fetch_word AsanUbsan.M.loaded_segments (0x7abec : word) = Some W_7a7d4.
Proof. vm_refl. Qed.
Lemma D_7a7d4 : decode_any W_7a7d4 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7d8 : bv 32 := 0x06a3fe63.
Lemma F_7a7d8 : fetch_word AsanUbsan.M.loaded_segments (0x7abf0 : word) = Some W_7a7d8.
Proof. vm_refl. Qed.
Lemma D_7a7d8 : decode_any W_7a7d8 = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7dc : bv 32 := 0x00148393.
Lemma F_7a7dc : fetch_word AsanUbsan.M.loaded_segments (0x7abf4 : word) = Some W_7a7dc.
Proof. vm_refl. Qed.
Lemma D_7a7dc : decode_any W_7a7dc = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7e0 : bv 32 := 0x00a86863.
Lemma F_7a7e0 : fetch_word AsanUbsan.M.loaded_segments (0x7abf8 : word) = Some W_7a7e0.
Proof. vm_refl. Qed.
Lemma D_7a7e0 : decode_any W_7a7e0 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7e4 : bv 32 := 0x0037de13.
Lemma F_7a7e4 : fetch_word AsanUbsan.M.loaded_segments (0x7abfc : word) = Some W_7a7e4.
Proof. vm_refl. Qed.
Lemma D_7a7e4 : decode_any W_7a7e4 = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7e8 : bv 32 := 0x007e0e33.
Lemma F_7a7e8 : fetch_word AsanUbsan.M.loaded_segments (0x7ac00 : word) = Some W_7a7e8.
Proof. vm_refl. Qed.
Lemma D_7a7e8 : decode_any W_7a7e8 = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7ec : bv 32 := 0x09c57a63.
Lemma F_7a7ec : fetch_word AsanUbsan.M.loaded_segments (0x7ac04 : word) = Some W_7a7ec.
Proof. vm_refl. Qed.
Lemma D_7a7ec : decode_any W_7a7ec = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7f0 : bv 32 := 0x00178e13.
Lemma F_7a7f0 : fetch_word AsanUbsan.M.loaded_segments (0x7ac08 : word) = Some W_7a7f0.
Proof. vm_refl. Qed.
Lemma D_7a7f0 : decode_any W_7a7f0 = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7f4 : bv 32 := 0x3bc56a63.
Lemma F_7a7f4 : fetch_word AsanUbsan.M.loaded_segments (0x7ac0c : word) = Some W_7a7f4.
Proof. vm_refl. Qed.
Lemma D_7a7f4 : decode_any W_7a7f4 = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7f8 : bv 32 := 0x00730333.
Lemma F_7a7f8 : fetch_word AsanUbsan.M.loaded_segments (0x7ac10 : word) = Some W_7a7f8.
Proof. vm_refl. Qed.
Lemma D_7a7f8 : decode_any W_7a7f8 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7fc : bv 32 := 0x00335313.
Lemma F_7a7fc : fetch_word AsanUbsan.M.loaded_segments (0x7ac14 : word) = Some W_7a7fc.
Proof. vm_refl. Qed.
Lemma D_7a7fc : decode_any W_7a7fc = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a800 : bv 32 := 0x0480006f.
Lemma F_7a800 : fetch_word AsanUbsan.M.loaded_segments (0x7ac18 : word) = Some W_7a800.
Proof. vm_refl. Qed.
Lemma D_7a800 : decode_any W_7a800 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a804 : bv 32 := 0x03813083.
Lemma F_7a804 : fetch_word AsanUbsan.M.loaded_segments (0x7ac1c : word) = Some W_7a804.
Proof. vm_refl. Qed.
Lemma D_7a804 : decode_any W_7a804 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a808 : bv 32 := 0x03013403.
Lemma F_7a808 : fetch_word AsanUbsan.M.loaded_segments (0x7ac20 : word) = Some W_7a808.
Proof. vm_refl. Qed.
Lemma D_7a808 : decode_any W_7a808 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a80c : bv 32 := 0x02813483.
Lemma F_7a80c : fetch_word AsanUbsan.M.loaded_segments (0x7ac24 : word) = Some W_7a80c.
Proof. vm_refl. Qed.
Lemma D_7a80c : decode_any W_7a80c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a810 : bv 32 := 0x02013903.
Lemma F_7a810 : fetch_word AsanUbsan.M.loaded_segments (0x7ac28 : word) = Some W_7a810.
Proof. vm_refl. Qed.
Lemma D_7a810 : decode_any W_7a810 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a814 : bv 32 := 0x01813983.
Lemma F_7a814 : fetch_word AsanUbsan.M.loaded_segments (0x7ac2c : word) = Some W_7a814.
Proof. vm_refl. Qed.
Lemma D_7a814 : decode_any W_7a814 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a818 : bv 32 := 0x01013a03.
Lemma F_7a818 : fetch_word AsanUbsan.M.loaded_segments (0x7ac30 : word) = Some W_7a818.
Proof. vm_refl. Qed.
Lemma D_7a818 : decode_any W_7a818 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a81c : bv 32 := 0x00813a83.
Lemma F_7a81c : fetch_word AsanUbsan.M.loaded_segments (0x7ac34 : word) = Some W_7a81c.
Proof. vm_refl. Qed.
Lemma D_7a81c : decode_any W_7a81c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a820 : bv 32 := 0x04010113.
Lemma F_7a820 : fetch_word AsanUbsan.M.loaded_segments (0x7ac38 : word) = Some W_7a820.
Proof. vm_refl. Qed.
Lemma D_7a820 : decode_any W_7a820 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a824 : bv 32 := 0x00008067.
Lemma F_7a824 : fetch_word AsanUbsan.M.loaded_segments (0x7ac3c : word) = Some W_7a824.
Proof. vm_refl. Qed.
Lemma D_7a824 : decode_any W_7a824 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a828 : bv 32 := 0x04048463.
Lemma F_7a828 : fetch_word AsanUbsan.M.loaded_segments (0x7ac40 : word) = Some W_7a828.
Proof. vm_refl. Qed.
Lemma D_7a828 : decode_any W_7a828 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a82c : bv 32 := 0x0036d313.
Lemma F_7a82c : fetch_word AsanUbsan.M.loaded_segments (0x7ac44 : word) = Some W_7a82c.
Proof. vm_refl. Qed.
Lemma D_7a82c : decode_any W_7a82c = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a830 : bv 32 := 0x00930333.
Lemma F_7a830 : fetch_word AsanUbsan.M.loaded_segments (0x7ac48 : word) = Some W_7a830.
Proof. vm_refl. Qed.
Lemma D_7a830 : decode_any W_7a830 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a834 : bv 32 := 0x00030663.
Lemma F_7a834 : fetch_word AsanUbsan.M.loaded_segments (0x7ac4c : word) = Some W_7a834.
Proof. vm_refl. Qed.
Lemma D_7a834 : decode_any W_7a834 = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a838 : bv 32 := 0x00130313.
Lemma F_7a838 : fetch_word AsanUbsan.M.loaded_segments (0x7ac50 : word) = Some W_7a838.
Proof. vm_refl. Qed.
Lemma D_7a838 : decode_any W_7a838 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a83c : bv 32 := 0x36656663.
Lemma F_7a83c : fetch_word AsanUbsan.M.loaded_segments (0x7ac54 : word) = Some W_7a83c.
Proof. vm_refl. Qed.
Lemma D_7a83c : decode_any W_7a83c = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a840 : bv 32 := 0x00138393.
Lemma F_7a840 : fetch_word AsanUbsan.M.loaded_segments (0x7ac58 : word) = Some W_7a840.
Proof. vm_refl. Qed.
Lemma D_7a840 : decode_any W_7a840 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a844 : bv 32 := 0x0033d313.
Lemma F_7a844 : fetch_word AsanUbsan.M.loaded_segments (0x7ac5c : word) = Some W_7a844.
Proof. vm_refl. Qed.
Lemma D_7a844 : decode_any W_7a844 = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a848 : bv 32 := 0x00d30333.
Lemma F_7a848 : fetch_word AsanUbsan.M.loaded_segments (0x7ac60 : word) = Some W_7a848.
Proof. vm_refl. Qed.
Lemma D_7a848 : decode_any W_7a848 = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a84c : bv 32 := 0x02a37a63.
Lemma F_7a84c : fetch_word AsanUbsan.M.loaded_segments (0x7ac64 : word) = Some W_7a84c.
Proof. vm_refl. Qed.
Lemma D_7a84c : decode_any W_7a84c = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a850 : bv 32 := 0x3580006f.
Lemma F_7a850 : fetch_word AsanUbsan.M.loaded_segments (0x7ac68 : word) = Some W_7a850.
Proof. vm_refl. Qed.
Lemma D_7a850 : decode_any W_7a850 = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a854 : bv 32 := 0x02048663.
Lemma F_7a854 : fetch_word AsanUbsan.M.loaded_segments (0x7ac6c : word) = Some W_7a854.
Proof. vm_refl. Qed.
Lemma D_7a854 : decode_any W_7a854 = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a858 : bv 32 := 0x0036d313.
Lemma F_7a858 : fetch_word AsanUbsan.M.loaded_segments (0x7ac70 : word) = Some W_7a858.
Proof. vm_refl. Qed.
Lemma D_7a858 : decode_any W_7a858 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a85c : bv 32 := 0x00930333.
Lemma F_7a85c : fetch_word AsanUbsan.M.loaded_segments (0x7ac74 : word) = Some W_7a85c.
Proof. vm_refl. Qed.
Lemma D_7a85c : decode_any W_7a85c = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a860 : bv 32 := 0x02030063.
Lemma F_7a860 : fetch_word AsanUbsan.M.loaded_segments (0x7ac78 : word) = Some W_7a860.
Proof. vm_refl. Qed.
Lemma D_7a860 : decode_any W_7a860 = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a864 : bv 32 := 0x00130313.
Lemma F_7a864 : fetch_word AsanUbsan.M.loaded_segments (0x7ac7c : word) = Some W_7a864.
Proof. vm_refl. Qed.
Lemma D_7a864 : decode_any W_7a864 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a868 : bv 32 := 0x00657c63.
Lemma F_7a868 : fetch_word AsanUbsan.M.loaded_segments (0x7ac80 : word) = Some W_7a868.
Proof. vm_refl. Qed.
Lemma D_7a868 : decode_any W_7a868 = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a86c : bv 32 := 0x33c0006f.
Lemma F_7a86c : fetch_word AsanUbsan.M.loaded_segments (0x7ac84 : word) = Some W_7a86c.
Proof. vm_refl. Qed.
Lemma D_7a86c : decode_any W_7a86c = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a870 : bv 32 := 0x00130313.
Lemma F_7a870 : fetch_word AsanUbsan.M.loaded_segments (0x7ac88 : word) = Some W_7a870.
Proof. vm_refl. Qed.
Lemma D_7a870 : decode_any W_7a870 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a874 : bv 32 := 0x00335313.
Lemma F_7a874 : fetch_word AsanUbsan.M.loaded_segments (0x7ac8c : word) = Some W_7a874.
Proof. vm_refl. Qed.
Lemma D_7a874 : decode_any W_7a874 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a878 : bv 32 := 0xfff30313.
Lemma F_7a878 : fetch_word AsanUbsan.M.loaded_segments (0x7ac90 : word) = Some W_7a878.
Proof. vm_refl. Qed.
Lemma D_7a878 : decode_any W_7a878 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a87c : bv 32 := 0x32a36663.
Lemma F_7a87c : fetch_word AsanUbsan.M.loaded_segments (0x7ac94 : word) = Some W_7a87c.
Proof. vm_refl. Qed.
Lemma D_7a87c : decode_any W_7a87c = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a880 : bv 32 := 0x0002b383.
Lemma F_7a880 : fetch_word AsanUbsan.M.loaded_segments (0x7ac98 : word) = Some W_7a880.
Proof. vm_refl. Qed.
Lemma D_7a880 : decode_any W_7a880 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a884 : bv 32 := 0x0033d293.
Lemma F_7a884 : fetch_word AsanUbsan.M.loaded_segments (0x7ac9c : word) = Some W_7a884.
Proof. vm_refl. Qed.
Lemma D_7a884 : decode_any W_7a884 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a888 : bv 32 := 0x00928333.
Lemma F_7a888 : fetch_word AsanUbsan.M.loaded_segments (0x7aca0 : word) = Some W_7a888.
Proof. vm_refl. Qed.
Lemma D_7a888 : decode_any W_7a888 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a88c : bv 32 := 0x00a3e463.
Lemma F_7a88c : fetch_word AsanUbsan.M.loaded_segments (0x7aca4 : word) = Some W_7a88c.
Proof. vm_refl. Qed.
Lemma D_7a88c : decode_any W_7a88c = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a890 : bv 32 := 0x0ca36063.
Lemma F_7a890 : fetch_word AsanUbsan.M.loaded_segments (0x7aca8 : word) = Some W_7a890.
Proof. vm_refl. Qed.
Lemma D_7a890 : decode_any W_7a890 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a894 : bv 32 := 0x000bd397.
Lemma F_7a894 : fetch_word AsanUbsan.M.loaded_segments (0x7acac : word) = Some W_7a894.
Proof. vm_refl. Qed.
Lemma D_7a894 : decode_any W_7a894 = Some (Auipc 7 189, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a898 : bv 32 := 0x80c3b383.
Lemma F_7a898 : fetch_word AsanUbsan.M.loaded_segments (0x7acb0 : word) = Some W_7a898.
Proof. vm_refl. Qed.
Lemma D_7a898 : decode_any W_7a898 = Some (Load SZ8 true 7 7 2060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a89c : bv 32 := 0x04e3c383.
Lemma F_7a89c : fetch_word AsanUbsan.M.loaded_segments (0x7acb4 : word) = Some W_7a89c.
Proof. vm_refl. Qed.
Lemma D_7a89c : decode_any W_7a89c = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8a0 : bv 32 := 0x08039063.
Lemma F_7a8a0 : fetch_word AsanUbsan.M.loaded_segments (0x7acb8 : word) = Some W_7a8a0.
Proof. vm_refl. Qed.
Lemma D_7a8a0 : decode_any W_7a8a0 = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8a4 : bv 32 := 0x02088c63.
Lemma F_7a8a4 : fetch_word AsanUbsan.M.loaded_segments (0x7acbc : word) = Some W_7a8a4.
Proof. vm_refl. Qed.
Lemma D_7a8a4 : decode_any W_7a8a4 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8a8 : bv 32 := 0x0038d893.
Lemma F_7a8a8 : fetch_word AsanUbsan.M.loaded_segments (0x7acc0 : word) = Some W_7a8a8.
Proof. vm_refl. Qed.
Lemma D_7a8a8 : decode_any W_7a8a8 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8ac : bv 32 := 0x00d888b3.
Lemma F_7a8ac : fetch_word AsanUbsan.M.loaded_segments (0x7acc4 : word) = Some W_7a8ac.
Proof. vm_refl. Qed.
Lemma D_7a8ac : decode_any W_7a8ac = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8b0 : bv 32 := 0x04a8fc63.
Lemma F_7a8b0 : fetch_word AsanUbsan.M.loaded_segments (0x7acc8 : word) = Some W_7a8b0.
Proof. vm_refl. Qed.
Lemma D_7a8b0 : decode_any W_7a8b0 = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8b4 : bv 32 := 0x00148893.
Lemma F_7a8b4 : fetch_word AsanUbsan.M.loaded_segments (0x7accc : word) = Some W_7a8b4.
Proof. vm_refl. Qed.
Lemma D_7a8b4 : decode_any W_7a8b4 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8b8 : bv 32 := 0x00a86863.
Lemma F_7a8b8 : fetch_word AsanUbsan.M.loaded_segments (0x7acd0 : word) = Some W_7a8b8.
Proof. vm_refl. Qed.
Lemma D_7a8b8 : decode_any W_7a8b8 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8bc : bv 32 := 0x0037d813.
Lemma F_7a8bc : fetch_word AsanUbsan.M.loaded_segments (0x7acd4 : word) = Some W_7a8bc.
Proof. vm_refl. Qed.
Lemma D_7a8bc : decode_any W_7a8bc = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8c0 : bv 32 := 0x01180833.
Lemma F_7a8c0 : fetch_word AsanUbsan.M.loaded_segments (0x7acd8 : word) = Some W_7a8c0.
Proof. vm_refl. Qed.
Lemma D_7a8c0 : decode_any W_7a8c0 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8c4 : bv 32 := 0x09057663.
Lemma F_7a8c4 : fetch_word AsanUbsan.M.loaded_segments (0x7acdc : word) = Some W_7a8c4.
Proof. vm_refl. Qed.
Lemma D_7a8c4 : decode_any W_7a8c4 = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8c8 : bv 32 := 0x00178793.
Lemma F_7a8c8 : fetch_word AsanUbsan.M.loaded_segments (0x7ace0 : word) = Some W_7a8c8.
Proof. vm_refl. Qed.
Lemma D_7a8c8 : decode_any W_7a8c8 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8cc : bv 32 := 0x04f56a63.
Lemma F_7a8cc : fetch_word AsanUbsan.M.loaded_segments (0x7ace4 : word) = Some W_7a8cc.
Proof. vm_refl. Qed.
Lemma D_7a8cc : decode_any W_7a8cc = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8d0 : bv 32 := 0x011288b3.
Lemma F_7a8d0 : fetch_word AsanUbsan.M.loaded_segments (0x7ace8 : word) = Some W_7a8d0.
Proof. vm_refl. Qed.
Lemma D_7a8d0 : decode_any W_7a8d0 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8d4 : bv 32 := 0x0038d793.
Lemma F_7a8d4 : fetch_word AsanUbsan.M.loaded_segments (0x7acec : word) = Some W_7a8d4.
Proof. vm_refl. Qed.
Lemma D_7a8d4 : decode_any W_7a8d4 = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8d8 : bv 32 := 0x0240006f.
Lemma F_7a8d8 : fetch_word AsanUbsan.M.loaded_segments (0x7acf0 : word) = Some W_7a8d8.
Proof. vm_refl. Qed.
Lemma D_7a8d8 : decode_any W_7a8d8 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8dc : bv 32 := 0x06048263.
Lemma F_7a8dc : fetch_word AsanUbsan.M.loaded_segments (0x7acf4 : word) = Some W_7a8dc.
Proof. vm_refl. Qed.
Lemma D_7a8dc : decode_any W_7a8dc = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8e0 : bv 32 := 0x0036d793.
Lemma F_7a8e0 : fetch_word AsanUbsan.M.loaded_segments (0x7acf8 : word) = Some W_7a8e0.
Proof. vm_refl. Qed.
Lemma D_7a8e0 : decode_any W_7a8e0 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8e4 : bv 32 := 0x009787b3.
Lemma F_7a8e4 : fetch_word AsanUbsan.M.loaded_segments (0x7acfc : word) = Some W_7a8e4.
Proof. vm_refl. Qed.
Lemma D_7a8e4 : decode_any W_7a8e4 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8e8 : bv 32 := 0x00078663.
Lemma F_7a8e8 : fetch_word AsanUbsan.M.loaded_segments (0x7ad00 : word) = Some W_7a8e8.
Proof. vm_refl. Qed.
Lemma D_7a8e8 : decode_any W_7a8e8 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8ec : bv 32 := 0x00178793.
Lemma F_7a8ec : fetch_word AsanUbsan.M.loaded_segments (0x7ad04 : word) = Some W_7a8ec.
Proof. vm_refl. Qed.
Lemma D_7a8ec : decode_any W_7a8ec = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8f0 : bv 32 := 0x02f56863.
Lemma F_7a8f0 : fetch_word AsanUbsan.M.loaded_segments (0x7ad08 : word) = Some W_7a8f0.
Proof. vm_refl. Qed.
Lemma D_7a8f0 : decode_any W_7a8f0 = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8f4 : bv 32 := 0x00130313.
Lemma F_7a8f4 : fetch_word AsanUbsan.M.loaded_segments (0x7ad0c : word) = Some W_7a8f4.
Proof. vm_refl. Qed.
Lemma D_7a8f4 : decode_any W_7a8f4 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8f8 : bv 32 := 0x00335793.
Lemma F_7a8f8 : fetch_word AsanUbsan.M.loaded_segments (0x7ad10 : word) = Some W_7a8f8.
Proof. vm_refl. Qed.
Lemma D_7a8f8 : decode_any W_7a8f8 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a8fc : bv 32 := 0x00d787b3.
Lemma F_7a8fc : fetch_word AsanUbsan.M.loaded_segments (0x7ad14 : word) = Some W_7a8fc.
Proof. vm_refl. Qed.
Lemma D_7a8fc : decode_any W_7a8fc = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a900 : bv 32 := 0x04a7f863.
Lemma F_7a900 : fetch_word AsanUbsan.M.loaded_segments (0x7ad18 : word) = Some W_7a900.
Proof. vm_refl. Qed.
Lemma D_7a900 : decode_any W_7a900 = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a904 : bv 32 := 0x01c0006f.
Lemma F_7a904 : fetch_word AsanUbsan.M.loaded_segments (0x7ad1c : word) = Some W_7a904.
Proof. vm_refl. Qed.
Lemma D_7a904 : decode_any W_7a904 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a908 : bv 32 := 0x04048463.
Lemma F_7a908 : fetch_word AsanUbsan.M.loaded_segments (0x7ad20 : word) = Some W_7a908.
Proof. vm_refl. Qed.
Lemma D_7a908 : decode_any W_7a908 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a90c : bv 32 := 0x0036d793.
Lemma F_7a90c : fetch_word AsanUbsan.M.loaded_segments (0x7ad24 : word) = Some W_7a90c.
Proof. vm_refl. Qed.
Lemma D_7a90c : decode_any W_7a90c = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a910 : bv 32 := 0x009787b3.
Lemma F_7a910 : fetch_word AsanUbsan.M.loaded_segments (0x7ad28 : word) = Some W_7a910.
Proof. vm_refl. Qed.
Lemma D_7a910 : decode_any W_7a910 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a914 : bv 32 := 0x02078e63.
Lemma F_7a914 : fetch_word AsanUbsan.M.loaded_segments (0x7ad2c : word) = Some W_7a914.
Proof. vm_refl. Qed.
Lemma D_7a914 : decode_any W_7a914 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a918 : bv 32 := 0x00178793.
Lemma F_7a918 : fetch_word AsanUbsan.M.loaded_segments (0x7ad30 : word) = Some W_7a918.
Proof. vm_refl. Qed.
Lemma D_7a918 : decode_any W_7a918 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a91c : bv 32 := 0x02f57a63.
Lemma F_7a91c : fetch_word AsanUbsan.M.loaded_segments (0x7ad34 : word) = Some W_7a91c.
Proof. vm_refl. Qed.
Lemma D_7a91c : decode_any W_7a91c = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a920 : bv 32 := 0xfffa6517.
Lemma F_7a920 : fetch_word AsanUbsan.M.loaded_segments (0x7ad38 : word) = Some W_7a920.
Proof. vm_refl. Qed.
Lemma D_7a920 : decode_any W_7a920 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a924 : bv 32 := 0xfff9e597.
Lemma F_7a924 : fetch_word AsanUbsan.M.loaded_segments (0x7ad3c : word) = Some W_7a924.
Proof. vm_refl. Qed.
Lemma D_7a924 : decode_any W_7a924 = Some (Auipc 11 1048478, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a928 : bv 32 := 0x58650513.
Lemma F_7a928 : fetch_word AsanUbsan.M.loaded_segments (0x7ad40 : word) = Some W_7a928.
Proof. vm_refl. Qed.
Lemma D_7a928 : decode_any W_7a928 = Some (OpImm ALU_ADD 10 10 1414, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a92c : bv 32 := 0xa2858613.
Lemma F_7a92c : fetch_word AsanUbsan.M.loaded_segments (0x7ad44 : word) = Some W_7a92c.
Proof. vm_refl. Qed.
Lemma D_7a92c : decode_any W_7a92c = Some (OpImm ALU_ADD 12 11 2600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a930 : bv 32 := 0x02f00593.
Lemma F_7a930 : fetch_word AsanUbsan.M.loaded_segments (0x7ad48 : word) = Some W_7a930.
Proof. vm_refl. Qed.
Lemma D_7a930 : decode_any W_7a930 = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a934 : bv 32 := 0x00000693.
Lemma F_7a934 : fetch_word AsanUbsan.M.loaded_segments (0x7ad4c : word) = Some W_7a934.
Proof. vm_refl. Qed.
Lemma D_7a934 : decode_any W_7a934 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a938 : bv 32 := 0x00000713.
Lemma F_7a938 : fetch_word AsanUbsan.M.loaded_segments (0x7ad50 : word) = Some W_7a938.
Proof. vm_refl. Qed.
Lemma D_7a938 : decode_any W_7a938 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a93c : bv 32 := 0x430180ef.
Lemma F_7a93c : fetch_word AsanUbsan.M.loaded_segments (0x7ad54 : word) = Some W_7a93c.
Proof. vm_refl. Qed.
Lemma D_7a93c : decode_any W_7a93c = Some (Jal 1 99376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a940 : bv 32 := 0x00128293.
Lemma F_7a940 : fetch_word AsanUbsan.M.loaded_segments (0x7ad58 : word) = Some W_7a940.
Proof. vm_refl. Qed.
Lemma D_7a940 : decode_any W_7a940 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a944 : bv 32 := 0x0032d793.
Lemma F_7a944 : fetch_word AsanUbsan.M.loaded_segments (0x7ad5c : word) = Some W_7a944.
Proof. vm_refl. Qed.
Lemma D_7a944 : decode_any W_7a944 = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a948 : bv 32 := 0xfff78793.
Lemma F_7a948 : fetch_word AsanUbsan.M.loaded_segments (0x7ad60 : word) = Some W_7a948.
Proof. vm_refl. Qed.
Lemma D_7a948 : decode_any W_7a948 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a94c : bv 32 := 0xfca7eae3.
Lemma F_7a94c : fetch_word AsanUbsan.M.loaded_segments (0x7ad64 : word) = Some W_7a94c.
Proof. vm_refl. Qed.
Lemma D_7a94c : decode_any W_7a94c = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a950 : bv 32 := 0x0075f793.
Lemma F_7a950 : fetch_word AsanUbsan.M.loaded_segments (0x7ad68 : word) = Some W_7a950.
Proof. vm_refl. Qed.
Lemma D_7a950 : decode_any W_7a950 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a954 : bv 32 := 0x26079a63.
Lemma F_7a954 : fetch_word AsanUbsan.M.loaded_segments (0x7ad6c : word) = Some W_7a954.
Proof. vm_refl. Qed.
Lemma D_7a954 : decode_any W_7a954 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a958 : bv 32 := 0x00b505b3.
Lemma F_7a958 : fetch_word AsanUbsan.M.loaded_segments (0x7ad70 : word) = Some W_7a958.
Proof. vm_refl. Qed.
Lemma D_7a958 : decode_any W_7a958 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a95c : bv 32 := 0xff858593.
Lemma F_7a95c : fetch_word AsanUbsan.M.loaded_segments (0x7ad74 : word) = Some W_7a95c.
Proof. vm_refl. Qed.
Lemma D_7a95c : decode_any W_7a95c = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a960 : bv 32 := 0x04b77263.
Lemma F_7a960 : fetch_word AsanUbsan.M.loaded_segments (0x7ad78 : word) = Some W_7a960.
Proof. vm_refl. Qed.
Lemma D_7a960 : decode_any W_7a960 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a964 : bv 32 := 0x000bc717.
Lemma F_7a964 : fetch_word AsanUbsan.M.loaded_segments (0x7ad7c : word) = Some W_7a964.
Proof. vm_refl. Qed.
Lemma D_7a964 : decode_any W_7a964 = Some (Auipc 14 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a968 : bv 32 := 0x74c73703.
Lemma F_7a968 : fetch_word AsanUbsan.M.loaded_segments (0x7ad80 : word) = Some W_7a968.
Proof. vm_refl. Qed.
Lemma D_7a968 : decode_any W_7a968 = Some (Load SZ8 true 14 14 1868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a96c : bv 32 := 0x000bc797.
Lemma F_7a96c : fetch_word AsanUbsan.M.loaded_segments (0x7ad84 : word) = Some W_7a96c.
Proof. vm_refl. Qed.
Lemma D_7a96c : decode_any W_7a96c = Some (Auipc 15 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a970 : bv 32 := 0x74c7b783.
Lemma F_7a970 : fetch_word AsanUbsan.M.loaded_segments (0x7ad88 : word) = Some W_7a970.
Proof. vm_refl. Qed.
Lemma D_7a970 : decode_any W_7a970 = Some (Load SZ8 true 15 15 1868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a974 : bv 32 := 0x00073883.
Lemma F_7a974 : fetch_word AsanUbsan.M.loaded_segments (0x7ad8c : word) = Some W_7a974.
Proof. vm_refl. Qed.
Lemma D_7a974 : decode_any W_7a974 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a978 : bv 32 := 0x0007b703.
Lemma F_7a978 : fetch_word AsanUbsan.M.loaded_segments (0x7ad90 : word) = Some W_7a978.
Proof. vm_refl. Qed.
Lemma D_7a978 : decode_any W_7a978 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a97c : bv 32 := 0xfff88813.
Lemma F_7a97c : fetch_word AsanUbsan.M.loaded_segments (0x7ad94 : word) = Some W_7a97c.
Proof. vm_refl. Qed.
Lemma D_7a97c : decode_any W_7a97c = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a980 : bv 32 := 0x00b87463.
Lemma F_7a980 : fetch_word AsanUbsan.M.loaded_segments (0x7ad98 : word) = Some W_7a980.
Proof. vm_refl. Qed.
Lemma D_7a980 : decode_any W_7a980 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a984 : bv 32 := 0x02b77063.
Lemma F_7a984 : fetch_word AsanUbsan.M.loaded_segments (0x7ad9c : word) = Some W_7a984.
Proof. vm_refl. Qed.
Lemma D_7a984 : decode_any W_7a984 = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a988 : bv 32 := 0x000bc797.
Lemma F_7a988 : fetch_word AsanUbsan.M.loaded_segments (0x7ada0 : word) = Some W_7a988.
Proof. vm_refl. Qed.
Lemma D_7a988 : decode_any W_7a988 = Some (Auipc 15 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a98c : bv 32 := 0x7387b783.
Lemma F_7a98c : fetch_word AsanUbsan.M.loaded_segments (0x7ada4 : word) = Some W_7a98c.
Proof. vm_refl. Qed.
Lemma D_7a98c : decode_any W_7a98c = Some (Load SZ8 true 15 15 1848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a990 : bv 32 := 0x0007b303.
Lemma F_7a990 : fetch_word AsanUbsan.M.loaded_segments (0x7ada8 : word) = Some W_7a990.
Proof. vm_refl. Qed.
Lemma D_7a990 : decode_any W_7a990 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a994 : bv 32 := 0x00335793.
Lemma F_7a994 : fetch_word AsanUbsan.M.loaded_segments (0x7adac : word) = Some W_7a994.
Proof. vm_refl. Qed.
Lemma D_7a994 : decode_any W_7a994 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a998 : bv 32 := 0x009782b3.
Lemma F_7a998 : fetch_word AsanUbsan.M.loaded_segments (0x7adb0 : word) = Some W_7a998.
Proof. vm_refl. Qed.
Lemma D_7a998 : decode_any W_7a998 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a99c : bv 32 := 0x12b36263.
Lemma F_7a99c : fetch_word AsanUbsan.M.loaded_segments (0x7adb4 : word) = Some W_7a99c.
Proof. vm_refl. Qed.
Lemma D_7a99c : decode_any W_7a99c = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9a0 : bv 32 := 0x12b2f063.
Lemma F_7a9a0 : fetch_word AsanUbsan.M.loaded_segments (0x7adb8 : word) = Some W_7a9a0.
Proof. vm_refl. Qed.
Lemma D_7a9a0 : decode_any W_7a9a0 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9a4 : bv 32 := 0x000bc697.
Lemma F_7a9a4 : fetch_word AsanUbsan.M.loaded_segments (0x7adbc : word) = Some W_7a9a4.
Proof. vm_refl. Qed.
Lemma D_7a9a4 : decode_any W_7a9a4 = Some (Auipc 13 188, 4%Z).
Proof. vm_refl. Qed.
