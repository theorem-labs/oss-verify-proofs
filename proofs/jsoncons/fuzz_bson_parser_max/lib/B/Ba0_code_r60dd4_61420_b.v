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
Definition W_7a70c : bv 32 := 0x000c5517.
Lemma F_7a70c : fetch_word AsanUbsan.M.loaded_segments (0x7ab24 : word) = Some W_7a70c.
Proof. vm_refl. Qed.
Lemma D_7a70c : decode_any W_7a70c = Some (Auipc 10 197, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a710 : bv 32 := 0x97850503.
Lemma F_7a710 : fetch_word AsanUbsan.M.loaded_segments (0x7ab28 : word) = Some W_7a710.
Proof. vm_refl. Qed.
Lemma D_7a710 : decode_any W_7a710 = Some (Load SZ1 true 10 10 2424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a714 : bv 32 := 0x0230000f.
Lemma F_7a714 : fetch_word AsanUbsan.M.loaded_segments (0x7ab2c : word) = Some W_7a714.
Proof. vm_refl. Qed.
Lemma D_7a714 : decode_any W_7a714 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a718 : bv 32 := 0x00a03533.
Lemma F_7a718 : fetch_word AsanUbsan.M.loaded_segments (0x7ab30 : word) = Some W_7a718.
Proof. vm_refl. Qed.
Lemma D_7a718 : decode_any W_7a718 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a71c : bv 32 := 0x00008067.
Lemma F_7a71c : fetch_word AsanUbsan.M.loaded_segments (0x7ab34 : word) = Some W_7a71c.
Proof. vm_refl. Qed.
Lemma D_7a71c : decode_any W_7a71c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a720 : bv 32 := 0xfc010113.
Lemma F_7a720 : fetch_word AsanUbsan.M.loaded_segments (0x7ab38 : word) = Some W_7a720.
Proof. vm_refl. Qed.
Lemma D_7a720 : decode_any W_7a720 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a724 : bv 32 := 0x02113c23.
Lemma F_7a724 : fetch_word AsanUbsan.M.loaded_segments (0x7ab3c : word) = Some W_7a724.
Proof. vm_refl. Qed.
Lemma D_7a724 : decode_any W_7a724 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a728 : bv 32 := 0x02813823.
Lemma F_7a728 : fetch_word AsanUbsan.M.loaded_segments (0x7ab40 : word) = Some W_7a728.
Proof. vm_refl. Qed.
Lemma D_7a728 : decode_any W_7a728 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a72c : bv 32 := 0x02913423.
Lemma F_7a72c : fetch_word AsanUbsan.M.loaded_segments (0x7ab44 : word) = Some W_7a72c.
Proof. vm_refl. Qed.
Lemma D_7a72c : decode_any W_7a72c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a730 : bv 32 := 0x03213023.
Lemma F_7a730 : fetch_word AsanUbsan.M.loaded_segments (0x7ab48 : word) = Some W_7a730.
Proof. vm_refl. Qed.
Lemma D_7a730 : decode_any W_7a730 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a734 : bv 32 := 0x01313c23.
Lemma F_7a734 : fetch_word AsanUbsan.M.loaded_segments (0x7ab4c : word) = Some W_7a734.
Proof. vm_refl. Qed.
Lemma D_7a734 : decode_any W_7a734 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a738 : bv 32 := 0x01413823.
Lemma F_7a738 : fetch_word AsanUbsan.M.loaded_segments (0x7ab50 : word) = Some W_7a738.
Proof. vm_refl. Qed.
Lemma D_7a738 : decode_any W_7a738 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a73c : bv 32 := 0x01513423.
Lemma F_7a73c : fetch_word AsanUbsan.M.loaded_segments (0x7ab54 : word) = Some W_7a73c.
Proof. vm_refl. Qed.
Lemma D_7a73c : decode_any W_7a73c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a740 : bv 32 := 0x00060a63.
Lemma F_7a740 : fetch_word AsanUbsan.M.loaded_segments (0x7ab58 : word) = Some W_7a740.
Proof. vm_refl. Qed.
Lemma D_7a740 : decode_any W_7a740 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a744 : bv 32 := 0x000c5697.
Lemma F_7a744 : fetch_word AsanUbsan.M.loaded_segments (0x7ab5c : word) = Some W_7a744.
Proof. vm_refl. Qed.
Lemma D_7a744 : decode_any W_7a744 = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a748 : bv 32 := 0x94068683.
Lemma F_7a748 : fetch_word AsanUbsan.M.loaded_segments (0x7ab60 : word) = Some W_7a748.
Proof. vm_refl. Qed.
Lemma D_7a748 : decode_any W_7a748 = Some (Load SZ1 true 13 13 2368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a74c : bv 32 := 0x0230000f.
Lemma F_7a74c : fetch_word AsanUbsan.M.loaded_segments (0x7ab64 : word) = Some W_7a74c.
Proof. vm_refl. Qed.
Lemma D_7a74c : decode_any W_7a74c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a750 : bv 32 := 0x0a068a63.
Lemma F_7a750 : fetch_word AsanUbsan.M.loaded_segments (0x7ab68 : word) = Some W_7a750.
Proof. vm_refl. Qed.
Lemma D_7a750 : decode_any W_7a750 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a754 : bv 32 := 0x00757693.
Lemma F_7a754 : fetch_word AsanUbsan.M.loaded_segments (0x7ab6c : word) = Some W_7a754.
Proof. vm_refl. Qed.
Lemma D_7a754 : decode_any W_7a754 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a758 : bv 32 := 0x42069863.
Lemma F_7a758 : fetch_word AsanUbsan.M.loaded_segments (0x7ab70 : word) = Some W_7a758.
Proof. vm_refl. Qed.
Lemma D_7a758 : decode_any W_7a758 = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a75c : bv 32 := 0x000bd697.
Lemma F_7a75c : fetch_word AsanUbsan.M.loaded_segments (0x7ab74 : word) = Some W_7a75c.
Proof. vm_refl. Qed.
Lemma D_7a75c : decode_any W_7a75c = Some (Auipc 13 189, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a760 : bv 32 := 0x94c6b683.
Lemma F_7a760 : fetch_word AsanUbsan.M.loaded_segments (0x7ab78 : word) = Some W_7a760.
Proof. vm_refl. Qed.
Lemma D_7a760 : decode_any W_7a760 = Some (Load SZ8 true 13 13 2380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a764 : bv 32 := 0x0006b483.
Lemma F_7a764 : fetch_word AsanUbsan.M.loaded_segments (0x7ab7c : word) = Some W_7a764.
Proof. vm_refl. Qed.
Lemma D_7a764 : decode_any W_7a764 = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

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

(* [comment removed for export] *)
Definition W_7a9a8 : bv 32 := 0x7246b983.
Lemma F_7a9a8 : fetch_word AsanUbsan.M.loaded_segments (0x7adc0 : word) = Some W_7a9a8.
Proof. vm_refl. Qed.
Lemma D_7a9a8 : decode_any W_7a9a8 = Some (Load SZ8 true 19 13 1828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9ac : bv 32 := 0x0009b303.
Lemma F_7a9ac : fetch_word AsanUbsan.M.loaded_segments (0x7adc4 : word) = Some W_7a9ac.
Proof. vm_refl. Qed.
Lemma D_7a9ac : decode_any W_7a9ac = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9b0 : bv 32 := 0x22030c63.
Lemma F_7a9b0 : fetch_word AsanUbsan.M.loaded_segments (0x7adc8 : word) = Some W_7a9b0.
Proof. vm_refl. Qed.
Lemma D_7a9b0 : decode_any W_7a9b0 = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9b4 : bv 32 := 0x00355693.
Lemma F_7a9b4 : fetch_word AsanUbsan.M.loaded_segments (0x7adcc : word) = Some W_7a9b4.
Proof. vm_refl. Qed.
Lemma D_7a9b4 : decode_any W_7a9b4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9b8 : bv 32 := 0x0035d593.
Lemma F_7a9b8 : fetch_word AsanUbsan.M.loaded_segments (0x7add0 : word) = Some W_7a9b8.
Proof. vm_refl. Qed.
Lemma D_7a9b8 : decode_any W_7a9b8 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9bc : bv 32 := 0x00d48533.
Lemma F_7a9bc : fetch_word AsanUbsan.M.loaded_segments (0x7add4 : word) = Some W_7a9bc.
Proof. vm_refl. Qed.
Lemma D_7a9bc : decode_any W_7a9bc = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9c0 : bv 32 := 0x00158913.
Lemma F_7a9c0 : fetch_word AsanUbsan.M.loaded_segments (0x7add8 : word) = Some W_7a9c0.
Proof. vm_refl. Qed.
Lemma D_7a9c0 : decode_any W_7a9c0 = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9c4 : bv 32 := 0x40d90433.
Lemma F_7a9c4 : fetch_word AsanUbsan.M.loaded_segments (0x7addc : word) = Some W_7a9c4.
Proof. vm_refl. Qed.
Lemma D_7a9c4 : decode_any W_7a9c4 = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9c8 : bv 32 := 0x0c061063.
Lemma F_7a9c8 : fetch_word AsanUbsan.M.loaded_segments (0x7ade0 : word) = Some W_7a9c8.
Proof. vm_refl. Qed.
Lemma D_7a9c8 : decode_any W_7a9c8 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9cc : bv 32 := 0x000bc597.
Lemma F_7a9cc : fetch_word AsanUbsan.M.loaded_segments (0x7ade4 : word) = Some W_7a9cc.
Proof. vm_refl. Qed.
Lemma D_7a9cc : decode_any W_7a9cc = Some (Auipc 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9d0 : bv 32 := 0x6cc5b583.
Lemma F_7a9d0 : fetch_word AsanUbsan.M.loaded_segments (0x7ade8 : word) = Some W_7a9d0.
Proof. vm_refl. Qed.
Lemma D_7a9d0 : decode_any W_7a9d0 = Some (Load SZ8 true 11 11 1740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9d4 : bv 32 := 0x0785b583.
Lemma F_7a9d4 : fetch_word AsanUbsan.M.loaded_segments (0x7adec : word) = Some W_7a9d4.
Proof. vm_refl. Qed.
Lemma D_7a9d4 : decode_any W_7a9d4 = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9d8 : bv 32 := 0x0ab46863.
Lemma F_7a9d8 : fetch_word AsanUbsan.M.loaded_segments (0x7adf0 : word) = Some W_7a9d8.
Proof. vm_refl. Qed.
Lemma D_7a9d8 : decode_any W_7a9d8 = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9e8 : bv 32 := 0x00059c63.
Lemma F_7a9e8 : fetch_word AsanUbsan.M.loaded_segments (0x7ae00 : word) = Some W_7a9e8.
Proof. vm_refl. Qed.
Lemma D_7a9e8 : decode_any W_7a9e8 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9ec : bv 32 := 0x00050a93.
Lemma F_7a9ec : fetch_word AsanUbsan.M.loaded_segments (0x7ae04 : word) = Some W_7a9ec.
Proof. vm_refl. Qed.
Lemma D_7a9ec : decode_any W_7a9ec = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9f0 : bv 32 := 0x5a1110ef.
Lemma F_7a9f0 : fetch_word AsanUbsan.M.loaded_segments (0x7ae08 : word) = Some W_7a9f0.
Proof. vm_refl. Qed.
Lemma D_7a9f0 : decode_any W_7a9f0 = Some (Jal 1 73120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9f4 : bv 32 := 0x00050593.
Lemma F_7a9f4 : fetch_word AsanUbsan.M.loaded_segments (0x7ae0c : word) = Some W_7a9f4.
Proof. vm_refl. Qed.
Lemma D_7a9f4 : decode_any W_7a9f4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9f8 : bv 32 := 0x000a8513.
Lemma F_7a9f8 : fetch_word AsanUbsan.M.loaded_segments (0x7ae10 : word) = Some W_7a9f8.
Proof. vm_refl. Qed.
Lemma D_7a9f8 : decode_any W_7a9f8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9fc : bv 32 := 0x00ba3023.
Lemma F_7a9fc : fetch_word AsanUbsan.M.loaded_segments (0x7ae14 : word) = Some W_7a9fc.
Proof. vm_refl. Qed.
Lemma D_7a9fc : decode_any W_7a9fc = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa00 : bv 32 := 0xfff58613.
Lemma F_7aa00 : fetch_word AsanUbsan.M.loaded_segments (0x7ae18 : word) = Some W_7aa00.
Proof. vm_refl. Qed.
Lemma D_7aa00 : decode_any W_7aa00 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa04 : bv 32 := 0x00c5f633.
Lemma F_7aa04 : fetch_word AsanUbsan.M.loaded_segments (0x7ae1c : word) = Some W_7aa04.
Proof. vm_refl. Qed.
Lemma D_7aa04 : decode_any W_7aa04 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa08 : bv 32 := 0x20061063.
Lemma F_7aa08 : fetch_word AsanUbsan.M.loaded_segments (0x7ae20 : word) = Some W_7aa08.
Proof. vm_refl. Qed.
Lemma D_7aa08 : decode_any W_7aa08 = Some (Branch BC_NE 12 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa0c : bv 32 := 0x00990a33.
Lemma F_7aa0c : fetch_word AsanUbsan.M.loaded_segments (0x7ae24 : word) = Some W_7aa0c.
Proof. vm_refl. Qed.
Lemma D_7aa0c : decode_any W_7aa0c = Some (Op ALU_ADD 20 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa10 : bv 32 := 0x00b50633.
Lemma F_7aa10 : fetch_word AsanUbsan.M.loaded_segments (0x7ae28 : word) = Some W_7aa10.
Proof. vm_refl. Qed.
Lemma D_7aa10 : decode_any W_7aa10 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa14 : bv 32 := 0x40b005b3.
Lemma F_7aa14 : fetch_word AsanUbsan.M.loaded_segments (0x7ae2c : word) = Some W_7aa14.
Proof. vm_refl. Qed.
Lemma D_7aa14 : decode_any W_7aa14 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa18 : bv 32 := 0xfff60613.
Lemma F_7aa18 : fetch_word AsanUbsan.M.loaded_segments (0x7ae30 : word) = Some W_7aa18.
Proof. vm_refl. Qed.
Lemma D_7aa18 : decode_any W_7aa18 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa1c : bv 32 := 0x00b674b3.
Lemma F_7aa1c : fetch_word AsanUbsan.M.loaded_segments (0x7ae34 : word) = Some W_7aa1c.
Proof. vm_refl. Qed.
Lemma D_7aa1c : decode_any W_7aa1c = Some (Op ALU_AND 9 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa20 : bv 32 := 0x00ba7933.
Lemma F_7aa20 : fetch_word AsanUbsan.M.loaded_segments (0x7ae38 : word) = Some W_7aa20.
Proof. vm_refl. Qed.
Lemma D_7aa20 : decode_any W_7aa20 = Some (Op ALU_AND 18 20 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa24 : bv 32 := 0x0724f663.
Lemma F_7aa24 : fetch_word AsanUbsan.M.loaded_segments (0x7ae3c : word) = Some W_7aa24.
Proof. vm_refl. Qed.
Lemma D_7aa24 : decode_any W_7aa24 = Some (Branch BC_GEU 9 18 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa28 : bv 32 := 0x00a48a63.
Lemma F_7aa28 : fetch_word AsanUbsan.M.loaded_segments (0x7ae40 : word) = Some W_7aa28.
Proof. vm_refl. Qed.
Lemma D_7aa28 : decode_any W_7aa28 = Some (Branch BC_EQ 9 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa2c : bv 32 := 0x0009b683.
Lemma F_7aa2c : fetch_word AsanUbsan.M.loaded_segments (0x7ae44 : word) = Some W_7aa2c.
Proof. vm_refl. Qed.
Lemma D_7aa2c : decode_any W_7aa2c = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa30 : bv 32 := 0x40a48633.
Lemma F_7aa30 : fetch_word AsanUbsan.M.loaded_segments (0x7ae48 : word) = Some W_7aa30.
Proof. vm_refl. Qed.
Lemma D_7aa30 : decode_any W_7aa30 = Some (Op ALU_SUB 12 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa34 : bv 32 := 0x00000593.
Lemma F_7aa34 : fetch_word AsanUbsan.M.loaded_segments (0x7ae4c : word) = Some W_7aa34.
Proof. vm_refl. Qed.
Lemma D_7aa34 : decode_any W_7aa34 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa38 : bv 32 := 0x000680e7.
Lemma F_7aa38 : fetch_word AsanUbsan.M.loaded_segments (0x7ae50 : word) = Some W_7aa38.
Proof. vm_refl. Qed.
Lemma D_7aa38 : decode_any W_7aa38 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa3c : bv 32 := 0x012a0c63.
Lemma F_7aa3c : fetch_word AsanUbsan.M.loaded_segments (0x7ae54 : word) = Some W_7aa3c.
Proof. vm_refl. Qed.
Lemma D_7aa3c : decode_any W_7aa3c = Some (Branch BC_EQ 20 18 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa40 : bv 32 := 0x0009b683.
Lemma F_7aa40 : fetch_word AsanUbsan.M.loaded_segments (0x7ae58 : word) = Some W_7aa40.
Proof. vm_refl. Qed.
Lemma D_7aa40 : decode_any W_7aa40 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa44 : bv 32 := 0x412a0633.
Lemma F_7aa44 : fetch_word AsanUbsan.M.loaded_segments (0x7ae5c : word) = Some W_7aa44.
Proof. vm_refl. Qed.
Lemma D_7aa44 : decode_any W_7aa44 = Some (Op ALU_SUB 12 20 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa48 : bv 32 := 0x00090513.
Lemma F_7aa48 : fetch_word AsanUbsan.M.loaded_segments (0x7ae60 : word) = Some W_7aa48.
Proof. vm_refl. Qed.
Lemma D_7aa48 : decode_any W_7aa48 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa4c : bv 32 := 0x00000593.
Lemma F_7aa4c : fetch_word AsanUbsan.M.loaded_segments (0x7ae64 : word) = Some W_7aa4c.
Proof. vm_refl. Qed.
Lemma D_7aa4c : decode_any W_7aa4c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa50 : bv 32 := 0x000680e7.
Lemma F_7aa50 : fetch_word AsanUbsan.M.loaded_segments (0x7ae68 : word) = Some W_7aa50.
Proof. vm_refl. Qed.
Lemma D_7aa50 : decode_any W_7aa50 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa54 : bv 32 := 0xfff90593.
Lemma F_7aa54 : fetch_word AsanUbsan.M.loaded_segments (0x7ae6c : word) = Some W_7aa54.
Proof. vm_refl. Qed.
Lemma D_7aa54 : decode_any W_7aa54 = Some (OpImm ALU_ADD 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa58 : bv 32 := 0x00100693.
Lemma F_7aa58 : fetch_word AsanUbsan.M.loaded_segments (0x7ae70 : word) = Some W_7aa58.
Proof. vm_refl. Qed.
Lemma D_7aa58 : decode_any W_7aa58 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa5c : bv 32 := 0x00048513.
Lemma F_7aa5c : fetch_word AsanUbsan.M.loaded_segments (0x7ae74 : word) = Some W_7aa5c.
Proof. vm_refl. Qed.
Lemma D_7aa5c : decode_any W_7aa5c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa60 : bv 32 := 0x00000613.
Lemma F_7aa60 : fetch_word AsanUbsan.M.loaded_segments (0x7ae78 : word) = Some W_7aa60.
Proof. vm_refl. Qed.
Lemma D_7aa60 : decode_any W_7aa60 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa64 : bv 32 := 0x03813083.
Lemma F_7aa64 : fetch_word AsanUbsan.M.loaded_segments (0x7ae7c : word) = Some W_7aa64.
Proof. vm_refl. Qed.
Lemma D_7aa64 : decode_any W_7aa64 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa68 : bv 32 := 0x03013403.
Lemma F_7aa68 : fetch_word AsanUbsan.M.loaded_segments (0x7ae80 : word) = Some W_7aa68.
Proof. vm_refl. Qed.
Lemma D_7aa68 : decode_any W_7aa68 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa6c : bv 32 := 0x02813483.
Lemma F_7aa6c : fetch_word AsanUbsan.M.loaded_segments (0x7ae84 : word) = Some W_7aa6c.
Proof. vm_refl. Qed.
Lemma D_7aa6c : decode_any W_7aa6c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa70 : bv 32 := 0x02013903.
Lemma F_7aa70 : fetch_word AsanUbsan.M.loaded_segments (0x7ae88 : word) = Some W_7aa70.
Proof. vm_refl. Qed.
Lemma D_7aa70 : decode_any W_7aa70 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa74 : bv 32 := 0x01813983.
Lemma F_7aa74 : fetch_word AsanUbsan.M.loaded_segments (0x7ae8c : word) = Some W_7aa74.
Proof. vm_refl. Qed.
Lemma D_7aa74 : decode_any W_7aa74 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa78 : bv 32 := 0x01013a03.
Lemma F_7aa78 : fetch_word AsanUbsan.M.loaded_segments (0x7ae90 : word) = Some W_7aa78.
Proof. vm_refl. Qed.
Lemma D_7aa78 : decode_any W_7aa78 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa7c : bv 32 := 0x00813a83.
Lemma F_7aa7c : fetch_word AsanUbsan.M.loaded_segments (0x7ae94 : word) = Some W_7aa7c.
Proof. vm_refl. Qed.
Lemma D_7aa7c : decode_any W_7aa7c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa80 : bv 32 := 0x04010113.
Lemma F_7aa80 : fetch_word AsanUbsan.M.loaded_segments (0x7ae98 : word) = Some W_7aa80.
Proof. vm_refl. Qed.
Lemma D_7aa80 : decode_any W_7aa80 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa84 : bv 32 := 0x2f11806f.
Lemma F_7aa84 : fetch_word AsanUbsan.M.loaded_segments (0x7ae9c : word) = Some W_7aa84.
Proof. vm_refl. Qed.
Lemma D_7aa84 : decode_any W_7aa84 = Some (Jal 0 101104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa88 : bv 32 := 0x00060593.
Lemma F_7aa88 : fetch_word AsanUbsan.M.loaded_segments (0x7aea0 : word) = Some W_7aa88.
Proof. vm_refl. Qed.
Lemma D_7aa88 : decode_any W_7aa88 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa8c : bv 32 := 0x00c0006f.
Lemma F_7aa8c : fetch_word AsanUbsan.M.loaded_segments (0x7aea4 : word) = Some W_7aa8c.
Proof. vm_refl. Qed.
Lemma D_7aa8c : decode_any W_7aa8c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa90 : bv 32 := 0x0009b303.
Lemma F_7aa90 : fetch_word AsanUbsan.M.loaded_segments (0x7aea8 : word) = Some W_7aa90.
Proof. vm_refl. Qed.
Lemma D_7aa90 : decode_any W_7aa90 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa94 : bv 32 := 0x00000593.
Lemma F_7aa94 : fetch_word AsanUbsan.M.loaded_segments (0x7aeac : word) = Some W_7aa94.
Proof. vm_refl. Qed.
Lemma D_7aa94 : decode_any W_7aa94 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa98 : bv 32 := 0x00040613.
Lemma F_7aa98 : fetch_word AsanUbsan.M.loaded_segments (0x7aeb0 : word) = Some W_7aa98.
Proof. vm_refl. Qed.
Lemma D_7aa98 : decode_any W_7aa98 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa9c : bv 32 := 0x03813083.
Lemma F_7aa9c : fetch_word AsanUbsan.M.loaded_segments (0x7aeb4 : word) = Some W_7aa9c.
Proof. vm_refl. Qed.
Lemma D_7aa9c : decode_any W_7aa9c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa0 : bv 32 := 0x03013403.
Lemma F_7aaa0 : fetch_word AsanUbsan.M.loaded_segments (0x7aeb8 : word) = Some W_7aaa0.
Proof. vm_refl. Qed.
Lemma D_7aaa0 : decode_any W_7aaa0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa4 : bv 32 := 0x02813483.
Lemma F_7aaa4 : fetch_word AsanUbsan.M.loaded_segments (0x7aebc : word) = Some W_7aaa4.
Proof. vm_refl. Qed.
Lemma D_7aaa4 : decode_any W_7aaa4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa8 : bv 32 := 0x02013903.
Lemma F_7aaa8 : fetch_word AsanUbsan.M.loaded_segments (0x7aec0 : word) = Some W_7aaa8.
Proof. vm_refl. Qed.
Lemma D_7aaa8 : decode_any W_7aaa8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaac : bv 32 := 0x01813983.
Lemma F_7aaac : fetch_word AsanUbsan.M.loaded_segments (0x7aec4 : word) = Some W_7aaac.
Proof. vm_refl. Qed.
Lemma D_7aaac : decode_any W_7aaac = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aab0 : bv 32 := 0x01013a03.
Lemma F_7aab0 : fetch_word AsanUbsan.M.loaded_segments (0x7aec8 : word) = Some W_7aab0.
Proof. vm_refl. Qed.
Lemma D_7aab0 : decode_any W_7aab0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aab4 : bv 32 := 0x00813a83.
Lemma F_7aab4 : fetch_word AsanUbsan.M.loaded_segments (0x7aecc : word) = Some W_7aab4.
Proof. vm_refl. Qed.
Lemma D_7aab4 : decode_any W_7aab4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aab8 : bv 32 := 0x04010113.
Lemma F_7aab8 : fetch_word AsanUbsan.M.loaded_segments (0x7aed0 : word) = Some W_7aab8.
Proof. vm_refl. Qed.
Lemma D_7aab8 : decode_any W_7aab8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aabc : bv 32 := 0x00030067.
Lemma F_7aabc : fetch_word AsanUbsan.M.loaded_segments (0x7aed4 : word) = Some W_7aabc.
Proof. vm_refl. Qed.
Lemma D_7aabc : decode_any W_7aabc = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aac0 : bv 32 := 0x000bc317.
Lemma F_7aac0 : fetch_word AsanUbsan.M.loaded_segments (0x7aed8 : word) = Some W_7aac0.
Proof. vm_refl. Qed.
Lemma D_7aac0 : decode_any W_7aac0 = Some (Auipc 6 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aac4 : bv 32 := 0x5e033303.
Lemma F_7aac4 : fetch_word AsanUbsan.M.loaded_segments (0x7aedc : word) = Some W_7aac4.
Proof. vm_refl. Qed.
Lemma D_7aac4 : decode_any W_7aac4 = Some (Load SZ8 true 6 6 1504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aac8 : bv 32 := 0x04e34303.
Lemma F_7aac8 : fetch_word AsanUbsan.M.loaded_segments (0x7aee0 : word) = Some W_7aac8.
Proof. vm_refl. Qed.
Lemma D_7aac8 : decode_any W_7aac8 = Some (Load SZ1 false 6 6 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aacc : bv 32 := 0x08031e63.
Lemma F_7aacc : fetch_word AsanUbsan.M.loaded_segments (0x7aee4 : word) = Some W_7aacc.
Proof. vm_refl. Qed.
Lemma D_7aacc : decode_any W_7aacc = Some (Branch BC_NE 6 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aad0 : bv 32 := 0x04088063.
Lemma F_7aad0 : fetch_word AsanUbsan.M.loaded_segments (0x7aee8 : word) = Some W_7aad0.
Proof. vm_refl. Qed.
Lemma D_7aad0 : decode_any W_7aad0 = Some (Branch BC_EQ 17 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aad4 : bv 32 := 0x0038d893.
Lemma F_7aad4 : fetch_word AsanUbsan.M.loaded_segments (0x7aeec : word) = Some W_7aad4.
Proof. vm_refl. Qed.
Lemma D_7aad4 : decode_any W_7aad4 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aad8 : bv 32 := 0x00d888b3.
Lemma F_7aad8 : fetch_word AsanUbsan.M.loaded_segments (0x7aef0 : word) = Some W_7aad8.
Proof. vm_refl. Qed.
Lemma D_7aad8 : decode_any W_7aad8 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aadc : bv 32 := 0x06b8f063.
Lemma F_7aadc : fetch_word AsanUbsan.M.loaded_segments (0x7aef4 : word) = Some W_7aadc.
Proof. vm_refl. Qed.
Lemma D_7aadc : decode_any W_7aadc = Some (Branch BC_GEU 17 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aae0 : bv 32 := 0x00148893.
Lemma F_7aae0 : fetch_word AsanUbsan.M.loaded_segments (0x7aef8 : word) = Some W_7aae0.
Proof. vm_refl. Qed.
Lemma D_7aae0 : decode_any W_7aae0 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aae4 : bv 32 := 0x00b86863.
Lemma F_7aae4 : fetch_word AsanUbsan.M.loaded_segments (0x7aefc : word) = Some W_7aae4.
Proof. vm_refl. Qed.
Lemma D_7aae4 : decode_any W_7aae4 = Some (Branch BC_LTU 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aae8 : bv 32 := 0x00375813.
Lemma F_7aae8 : fetch_word AsanUbsan.M.loaded_segments (0x7af00 : word) = Some W_7aae8.
Proof. vm_refl. Qed.
Lemma D_7aae8 : decode_any W_7aae8 = Some (ShiftImm ALU_SRL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaec : bv 32 := 0x01180833.
Lemma F_7aaec : fetch_word AsanUbsan.M.loaded_segments (0x7af04 : word) = Some W_7aaec.
Proof. vm_refl. Qed.
Lemma D_7aaec : decode_any W_7aaec = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaf0 : bv 32 := 0xeb05fae3.
Lemma F_7aaf0 : fetch_word AsanUbsan.M.loaded_segments (0x7af08 : word) = Some W_7aaf0.
Proof. vm_refl. Qed.
Lemma D_7aaf0 : decode_any W_7aaf0 = Some (Branch BC_GEU 11 16 7860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaf4 : bv 32 := 0x00170713.
Lemma F_7aaf4 : fetch_word AsanUbsan.M.loaded_segments (0x7af0c : word) = Some W_7aaf4.
Proof. vm_refl. Qed.
Lemma D_7aaf4 : decode_any W_7aaf4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaf8 : bv 32 := 0x06e5e863.
Lemma F_7aaf8 : fetch_word AsanUbsan.M.loaded_segments (0x7af10 : word) = Some W_7aaf8.
Proof. vm_refl. Qed.
Lemma D_7aaf8 : decode_any W_7aaf8 = Some (Branch BC_LTU 11 14 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aafc : bv 32 := 0x011787b3.
Lemma F_7aafc : fetch_word AsanUbsan.M.loaded_segments (0x7af14 : word) = Some W_7aafc.
Proof. vm_refl. Qed.
Lemma D_7aafc : decode_any W_7aafc = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab00 : bv 32 := 0x0037d793.
Lemma F_7ab00 : fetch_word AsanUbsan.M.loaded_segments (0x7af18 : word) = Some W_7ab00.
Proof. vm_refl. Qed.
Lemma D_7ab00 : decode_any W_7ab00 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab04 : bv 32 := 0x00d786b3.
Lemma F_7ab04 : fetch_word AsanUbsan.M.loaded_segments (0x7af1c : word) = Some W_7ab04.
Proof. vm_refl. Qed.
Lemma D_7ab04 : decode_any W_7ab04 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab08 : bv 32 := 0xe8b6fee3.
Lemma F_7ab08 : fetch_word AsanUbsan.M.loaded_segments (0x7af20 : word) = Some W_7ab08.
Proof. vm_refl. Qed.
Lemma D_7ab08 : decode_any W_7ab08 = Some (Branch BC_GEU 13 11 7836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab0c : bv 32 := 0x05c0006f.
Lemma F_7ab0c : fetch_word AsanUbsan.M.loaded_segments (0x7af24 : word) = Some W_7ab0c.
Proof. vm_refl. Qed.
Lemma D_7ab0c : decode_any W_7ab0c = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab10 : bv 32 := 0x04048463.
Lemma F_7ab10 : fetch_word AsanUbsan.M.loaded_segments (0x7af28 : word) = Some W_7ab10.
Proof. vm_refl. Qed.
Lemma D_7ab10 : decode_any W_7ab10 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab14 : bv 32 := 0x0036d713.
Lemma F_7ab14 : fetch_word AsanUbsan.M.loaded_segments (0x7af2c : word) = Some W_7ab14.
Proof. vm_refl. Qed.
Lemma D_7ab14 : decode_any W_7ab14 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab18 : bv 32 := 0x00970733.
Lemma F_7ab18 : fetch_word AsanUbsan.M.loaded_segments (0x7af30 : word) = Some W_7ab18.
Proof. vm_refl. Qed.
Lemma D_7ab18 : decode_any W_7ab18 = Some (Op ALU_ADD 14 14 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab1c : bv 32 := 0x00070663.
Lemma F_7ab1c : fetch_word AsanUbsan.M.loaded_segments (0x7af34 : word) = Some W_7ab1c.
Proof. vm_refl. Qed.
Lemma D_7ab1c : decode_any W_7ab1c = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab20 : bv 32 := 0x00170713.
Lemma F_7ab20 : fetch_word AsanUbsan.M.loaded_segments (0x7af38 : word) = Some W_7ab20.
Proof. vm_refl. Qed.
Lemma D_7ab20 : decode_any W_7ab20 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab24 : bv 32 := 0x04e5e263.
Lemma F_7ab24 : fetch_word AsanUbsan.M.loaded_segments (0x7af3c : word) = Some W_7ab24.
Proof. vm_refl. Qed.
Lemma D_7ab24 : decode_any W_7ab24 = Some (Branch BC_LTU 11 14 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab28 : bv 32 := 0x00128293.
Lemma F_7ab28 : fetch_word AsanUbsan.M.loaded_segments (0x7af40 : word) = Some W_7ab28.
Proof. vm_refl. Qed.
Lemma D_7ab28 : decode_any W_7ab28 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab2c : bv 32 := 0x0032d713.
Lemma F_7ab2c : fetch_word AsanUbsan.M.loaded_segments (0x7af44 : word) = Some W_7ab2c.
Proof. vm_refl. Qed.
Lemma D_7ab2c : decode_any W_7ab2c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab30 : bv 32 := 0x00d706b3.
Lemma F_7ab30 : fetch_word AsanUbsan.M.loaded_segments (0x7af48 : word) = Some W_7ab30.
Proof. vm_refl. Qed.
Lemma D_7ab30 : decode_any W_7ab30 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab34 : bv 32 := 0xe6b6f8e3.
Lemma F_7ab34 : fetch_word AsanUbsan.M.loaded_segments (0x7af4c : word) = Some W_7ab34.
Proof. vm_refl. Qed.
Lemma D_7ab34 : decode_any W_7ab34 = Some (Branch BC_GEU 13 11 7792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab38 : bv 32 := 0x0300006f.
Lemma F_7ab38 : fetch_word AsanUbsan.M.loaded_segments (0x7af50 : word) = Some W_7ab38.
Proof. vm_refl. Qed.
Lemma D_7ab38 : decode_any W_7ab38 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab3c : bv 32 := 0xe60484e3.
Lemma F_7ab3c : fetch_word AsanUbsan.M.loaded_segments (0x7af54 : word) = Some W_7ab3c.
Proof. vm_refl. Qed.
Lemma D_7ab3c : decode_any W_7ab3c = Some (Branch BC_EQ 9 0 7784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab40 : bv 32 := 0x0036d693.
Lemma F_7ab40 : fetch_word AsanUbsan.M.loaded_segments (0x7af58 : word) = Some W_7ab40.
Proof. vm_refl. Qed.
Lemma D_7ab40 : decode_any W_7ab40 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab44 : bv 32 := 0x009686b3.
Lemma F_7ab44 : fetch_word AsanUbsan.M.loaded_segments (0x7af5c : word) = Some W_7ab44.
Proof. vm_refl. Qed.
Lemma D_7ab44 : decode_any W_7ab44 = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab48 : bv 32 := 0xe4068ee3.
Lemma F_7ab48 : fetch_word AsanUbsan.M.loaded_segments (0x7af60 : word) = Some W_7ab48.
Proof. vm_refl. Qed.
Lemma D_7ab48 : decode_any W_7ab48 = Some (Branch BC_EQ 13 0 7772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab4c : bv 32 := 0x00168693.
Lemma F_7ab4c : fetch_word AsanUbsan.M.loaded_segments (0x7af64 : word) = Some W_7ab4c.
Proof. vm_refl. Qed.
Lemma D_7ab4c : decode_any W_7ab4c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab50 : bv 32 := 0xe4d5fae3.
Lemma F_7ab50 : fetch_word AsanUbsan.M.loaded_segments (0x7af68 : word) = Some W_7ab50.
Proof. vm_refl. Qed.
Lemma D_7ab50 : decode_any W_7ab50 = Some (Branch BC_GEU 11 13 7764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab54 : bv 32 := 0x0140006f.
Lemma F_7ab54 : fetch_word AsanUbsan.M.loaded_segments (0x7af6c : word) = Some W_7ab54.
Proof. vm_refl. Qed.
Lemma D_7ab54 : decode_any W_7ab54 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab58 : bv 32 := 0x00178793.
Lemma F_7ab58 : fetch_word AsanUbsan.M.loaded_segments (0x7af70 : word) = Some W_7ab58.
Proof. vm_refl. Qed.
Lemma D_7ab58 : decode_any W_7ab58 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab5c : bv 32 := 0x0037d793.
Lemma F_7ab5c : fetch_word AsanUbsan.M.loaded_segments (0x7af74 : word) = Some W_7ab5c.
Proof. vm_refl. Qed.
Lemma D_7ab5c : decode_any W_7ab5c = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab60 : bv 32 := 0xfff78793.
Lemma F_7ab60 : fetch_word AsanUbsan.M.loaded_segments (0x7af78 : word) = Some W_7ab60.
Proof. vm_refl. Qed.
Lemma D_7ab60 : decode_any W_7ab60 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab64 : bv 32 := 0xe4b7f0e3.
Lemma F_7ab64 : fetch_word AsanUbsan.M.loaded_segments (0x7af7c : word) = Some W_7ab64.
Proof. vm_refl. Qed.
Lemma D_7ab64 : decode_any W_7ab64 = Some (Branch BC_GEU 15 11 7744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab68 : bv 32 := 0xfffa6517.
Lemma F_7ab68 : fetch_word AsanUbsan.M.loaded_segments (0x7af80 : word) = Some W_7ab68.
Proof. vm_refl. Qed.
Lemma D_7ab68 : decode_any W_7ab68 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab6c : bv 32 := 0xfff99597.
Lemma F_7ab6c : fetch_word AsanUbsan.M.loaded_segments (0x7af84 : word) = Some W_7ab6c.
Proof. vm_refl. Qed.
Lemma D_7ab6c : decode_any W_7ab6c = Some (Auipc 11 1048473, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab70 : bv 32 := 0x33e50513.
Lemma F_7ab70 : fetch_word AsanUbsan.M.loaded_segments (0x7af88 : word) = Some W_7ab70.
Proof. vm_refl. Qed.
Lemma D_7ab70 : decode_any W_7ab70 = Some (OpImm ALU_ADD 10 10 830, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab74 : bv 32 := 0x06858613.
Lemma F_7ab74 : fetch_word AsanUbsan.M.loaded_segments (0x7af8c : word) = Some W_7ab74.
Proof. vm_refl. Qed.
Lemma D_7ab74 : decode_any W_7ab74 = Some (OpImm ALU_ADD 12 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab78 : bv 32 := 0x03100593.
Lemma F_7ab78 : fetch_word AsanUbsan.M.loaded_segments (0x7af90 : word) = Some W_7ab78.
Proof. vm_refl. Qed.
Lemma D_7ab78 : decode_any W_7ab78 = Some (OpImm ALU_ADD 11 0 49, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab7c : bv 32 := 0x00000693.
Lemma F_7ab7c : fetch_word AsanUbsan.M.loaded_segments (0x7af94 : word) = Some W_7ab7c.
Proof. vm_refl. Qed.
Lemma D_7ab7c : decode_any W_7ab7c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab80 : bv 32 := 0x00000713.
Lemma F_7ab80 : fetch_word AsanUbsan.M.loaded_segments (0x7af98 : word) = Some W_7ab80.
Proof. vm_refl. Qed.
Lemma D_7ab80 : decode_any W_7ab80 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab84 : bv 32 := 0x1e8180ef.
Lemma F_7ab84 : fetch_word AsanUbsan.M.loaded_segments (0x7af9c : word) = Some W_7ab84.
Proof. vm_refl. Qed.
Lemma D_7ab84 : decode_any W_7ab84 = Some (Jal 1 98792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab88 : bv 32 := 0xfffa6517.
Lemma F_7ab88 : fetch_word AsanUbsan.M.loaded_segments (0x7afa0 : word) = Some W_7ab88.
Proof. vm_refl. Qed.
Lemma D_7ab88 : decode_any W_7ab88 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab8c : bv 32 := 0xfffa4597.
Lemma F_7ab8c : fetch_word AsanUbsan.M.loaded_segments (0x7afa4 : word) = Some W_7ab8c.
Proof. vm_refl. Qed.
Lemma D_7ab8c : decode_any W_7ab8c = Some (Auipc 11 1048484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab90 : bv 32 := 0x31e50513.
Lemma F_7ab90 : fetch_word AsanUbsan.M.loaded_segments (0x7afa8 : word) = Some W_7ab90.
Proof. vm_refl. Qed.
Lemma D_7ab90 : decode_any W_7ab90 = Some (OpImm ALU_ADD 10 10 798, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab94 : bv 32 := 0xde658613.
Lemma F_7ab94 : fetch_word AsanUbsan.M.loaded_segments (0x7afac : word) = Some W_7ab94.
Proof. vm_refl. Qed.
Lemma D_7ab94 : decode_any W_7ab94 = Some (OpImm ALU_ADD 12 11 3558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab98 : bv 32 := 0x02700593.
Lemma F_7ab98 : fetch_word AsanUbsan.M.loaded_segments (0x7afb0 : word) = Some W_7ab98.
Proof. vm_refl. Qed.
Lemma D_7ab98 : decode_any W_7ab98 = Some (OpImm ALU_ADD 11 0 39, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ab9c : bv 32 := 0x00000693.
Lemma F_7ab9c : fetch_word AsanUbsan.M.loaded_segments (0x7afb4 : word) = Some W_7ab9c.
Proof. vm_refl. Qed.
Lemma D_7ab9c : decode_any W_7ab9c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aba0 : bv 32 := 0x00000713.
Lemma F_7aba0 : fetch_word AsanUbsan.M.loaded_segments (0x7afb8 : word) = Some W_7aba0.
Proof. vm_refl. Qed.
Lemma D_7aba0 : decode_any W_7aba0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aba4 : bv 32 := 0x1c8180ef.
Lemma F_7aba4 : fetch_word AsanUbsan.M.loaded_segments (0x7afbc : word) = Some W_7aba4.
Proof. vm_refl. Qed.
Lemma D_7aba4 : decode_any W_7aba4 = Some (Jal 1 98760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aba8 : bv 32 := 0x000bc317.
Lemma F_7aba8 : fetch_word AsanUbsan.M.loaded_segments (0x7afc0 : word) = Some W_7aba8.
Proof. vm_refl. Qed.
Lemma D_7aba8 : decode_any W_7aba8 = Some (Auipc 6 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abac : bv 32 := 0x54033303.
Lemma F_7abac : fetch_word AsanUbsan.M.loaded_segments (0x7afc4 : word) = Some W_7abac.
Proof. vm_refl. Qed.
Lemma D_7abac : decode_any W_7abac = Some (Load SZ8 true 6 6 1344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abb0 : bv 32 := 0xcc0308e3.
Lemma F_7abb0 : fetch_word AsanUbsan.M.loaded_segments (0x7afc8 : word) = Some W_7abb0.
Proof. vm_refl. Qed.
Lemma D_7abb0 : decode_any W_7abb0 = Some (Branch BC_EQ 6 0 7376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abb4 : bv 32 := 0x000bc517.
Lemma F_7abb4 : fetch_word AsanUbsan.M.loaded_segments (0x7afcc : word) = Some W_7abb4.
Proof. vm_refl. Qed.
Lemma D_7abb4 : decode_any W_7abb4 = Some (Auipc 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abb8 : bv 32 := 0x53c53503.
Lemma F_7abb8 : fetch_word AsanUbsan.M.loaded_segments (0x7afd0 : word) = Some W_7abb8.
Proof. vm_refl. Qed.
Lemma D_7abb8 : decode_any W_7abb8 = Some (Load SZ8 true 10 10 1340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abbc : bv 32 := 0x00052503.
Lemma F_7abbc : fetch_word AsanUbsan.M.loaded_segments (0x7afd4 : word) = Some W_7abbc.
Proof. vm_refl. Qed.
Lemma D_7abbc : decode_any W_7abbc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abc0 : bv 32 := 0x04051c63.
Lemma F_7abc0 : fetch_word AsanUbsan.M.loaded_segments (0x7afd8 : word) = Some W_7abc0.
Proof. vm_refl. Qed.
Lemma D_7abc0 : decode_any W_7abc0 = Some (Branch BC_NE 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abc4 : bv 32 := 0x0000006f.
Lemma F_7abc4 : fetch_word AsanUbsan.M.loaded_segments (0x7afdc : word) = Some W_7abc4.
Proof. vm_refl. Qed.
Lemma D_7abc4 : decode_any W_7abc4 = Some (Jal 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abc8 : bv 32 := 0xfffa6517.
Lemma F_7abc8 : fetch_word AsanUbsan.M.loaded_segments (0x7afe0 : word) = Some W_7abc8.
Proof. vm_refl. Qed.
Lemma D_7abc8 : decode_any W_7abc8 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abcc : bv 32 := 0xfff98597.
Lemma F_7abcc : fetch_word AsanUbsan.M.loaded_segments (0x7afe4 : word) = Some W_7abcc.
Proof. vm_refl. Qed.
Lemma D_7abcc : decode_any W_7abcc = Some (Auipc 11 1048472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abd0 : bv 32 := 0x2de50513.
Lemma F_7abd0 : fetch_word AsanUbsan.M.loaded_segments (0x7afe8 : word) = Some W_7abd0.
Proof. vm_refl. Qed.
Lemma D_7abd0 : decode_any W_7abd0 = Some (OpImm ALU_ADD 10 10 734, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abd4 : bv 32 := 0x66058613.
Lemma F_7abd4 : fetch_word AsanUbsan.M.loaded_segments (0x7afec : word) = Some W_7abd4.
Proof. vm_refl. Qed.
Lemma D_7abd4 : decode_any W_7abd4 = Some (OpImm ALU_ADD 12 11 1632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abd8 : bv 32 := 0x03000593.
Lemma F_7abd8 : fetch_word AsanUbsan.M.loaded_segments (0x7aff0 : word) = Some W_7abd8.
Proof. vm_refl. Qed.
Lemma D_7abd8 : decode_any W_7abd8 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abdc : bv 32 := 0x00000693.
Lemma F_7abdc : fetch_word AsanUbsan.M.loaded_segments (0x7aff4 : word) = Some W_7abdc.
Proof. vm_refl. Qed.
Lemma D_7abdc : decode_any W_7abdc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abe0 : bv 32 := 0x00000713.
Lemma F_7abe0 : fetch_word AsanUbsan.M.loaded_segments (0x7aff8 : word) = Some W_7abe0.
Proof. vm_refl. Qed.
Lemma D_7abe0 : decode_any W_7abe0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abe4 : bv 32 := 0x188180ef.
Lemma F_7abe4 : fetch_word AsanUbsan.M.loaded_segments (0x7affc : word) = Some W_7abe4.
Proof. vm_refl. Qed.
Lemma D_7abe4 : decode_any W_7abe4 = Some (Jal 1 98696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abe8 : bv 32 := 0xfffa6517.
Lemma F_7abe8 : fetch_word AsanUbsan.M.loaded_segments (0x7b000 : word) = Some W_7abe8.
Proof. vm_refl. Qed.
Lemma D_7abe8 : decode_any W_7abe8 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abec : bv 32 := 0xfff9e597.
Lemma F_7abec : fetch_word AsanUbsan.M.loaded_segments (0x7b004 : word) = Some W_7abec.
Proof. vm_refl. Qed.
Lemma D_7abec : decode_any W_7abec = Some (Auipc 11 1048478, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abf0 : bv 32 := 0x2be50513.
Lemma F_7abf0 : fetch_word AsanUbsan.M.loaded_segments (0x7b008 : word) = Some W_7abf0.
Proof. vm_refl. Qed.
Lemma D_7abf0 : decode_any W_7abf0 = Some (OpImm ALU_ADD 10 10 702, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abf4 : bv 32 := 0x18e58613.
Lemma F_7abf4 : fetch_word AsanUbsan.M.loaded_segments (0x7b00c : word) = Some W_7abf4.
Proof. vm_refl. Qed.
Lemma D_7abf4 : decode_any W_7abf4 = Some (OpImm ALU_ADD 12 11 398, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abf8 : bv 32 := 0x03200593.
Lemma F_7abf8 : fetch_word AsanUbsan.M.loaded_segments (0x7b010 : word) = Some W_7abf8.
Proof. vm_refl. Qed.
Lemma D_7abf8 : decode_any W_7abf8 = Some (OpImm ALU_ADD 11 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7abfc : bv 32 := 0x00000693.
Lemma F_7abfc : fetch_word AsanUbsan.M.loaded_segments (0x7b014 : word) = Some W_7abfc.
Proof. vm_refl. Qed.
Lemma D_7abfc : decode_any W_7abfc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac00 : bv 32 := 0x00000713.
Lemma F_7ac00 : fetch_word AsanUbsan.M.loaded_segments (0x7b018 : word) = Some W_7ac00.
Proof. vm_refl. Qed.
Lemma D_7ac00 : decode_any W_7ac00 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac04 : bv 32 := 0x168180ef.
Lemma F_7ac04 : fetch_word AsanUbsan.M.loaded_segments (0x7b01c : word) = Some W_7ac04.
Proof. vm_refl. Qed.
Lemma D_7ac04 : decode_any W_7ac04 = Some (Jal 1 98664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac08 : bv 32 := 0xfff98517.
Lemma F_7ac08 : fetch_word AsanUbsan.M.loaded_segments (0x7b020 : word) = Some W_7ac08.
Proof. vm_refl. Qed.
Lemma D_7ac08 : decode_any W_7ac08 = Some (Auipc 10 1048472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac0c : bv 32 := 0x84d50513.
Lemma F_7ac0c : fetch_word AsanUbsan.M.loaded_segments (0x7b024 : word) = Some W_7ac0c.
Proof. vm_refl. Qed.
Lemma D_7ac0c : decode_any W_7ac0c = Some (OpImm ALU_ADD 10 10 2125, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac10 : bv 32 := 0x2ec0d0ef.
Lemma F_7ac10 : fetch_word AsanUbsan.M.loaded_segments (0x7b028 : word) = Some W_7ac10.
Proof. vm_refl. Qed.
Lemma D_7ac10 : decode_any W_7ac10 = Some (Jal 1 53996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac14 : bv 32 := 0x08c180ef.
Lemma F_7ac14 : fetch_word AsanUbsan.M.loaded_segments (0x7b02c : word) = Some W_7ac14.
Proof. vm_refl. Qed.
Lemma D_7ac14 : decode_any W_7ac14 = Some (Jal 1 98444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac18 : bv 32 := 0x1b01a0ef.
Lemma F_7ac18 : fetch_word AsanUbsan.M.loaded_segments (0x7b030 : word) = Some W_7ac18.
Proof. vm_refl. Qed.
Lemma D_7ac18 : decode_any W_7ac18 = Some (Jal 1 106928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac1c : bv 32 := 0x000bc597.
Lemma F_7ac1c : fetch_word AsanUbsan.M.loaded_segments (0x7b034 : word) = Some W_7ac1c.
Proof. vm_refl. Qed.
Lemma D_7ac1c : decode_any W_7ac1c = Some (Auipc 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac20 : bv 32 := 0x48c5b583.
Lemma F_7ac20 : fetch_word AsanUbsan.M.loaded_segments (0x7b038 : word) = Some W_7ac20.
Proof. vm_refl. Qed.
Lemma D_7ac20 : decode_any W_7ac20 = Some (Load SZ8 true 11 11 1164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac24 : bv 32 := 0x0005b583.
Lemma F_7ac24 : fetch_word AsanUbsan.M.loaded_segments (0x7b03c : word) = Some W_7ac24.
Proof. vm_refl. Qed.
Lemma D_7ac24 : decode_any W_7ac24 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac28 : bv 32 := 0xfff58613.
Lemma F_7ac28 : fetch_word AsanUbsan.M.loaded_segments (0x7b040 : word) = Some W_7ac28.
Proof. vm_refl. Qed.
Lemma D_7ac28 : decode_any W_7ac28 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac2c : bv 32 := 0x00c5b6b3.
Lemma F_7ac2c : fetch_word AsanUbsan.M.loaded_segments (0x7b044 : word) = Some W_7ac2c.
Proof. vm_refl. Qed.
Lemma D_7ac2c : decode_any W_7ac2c = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac30 : bv 32 := 0xfff68693.
Lemma F_7ac30 : fetch_word AsanUbsan.M.loaded_segments (0x7b048 : word) = Some W_7ac30.
Proof. vm_refl. Qed.
Lemma D_7ac30 : decode_any W_7ac30 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac34 : bv 32 := 0x00c6f6b3.
Lemma F_7ac34 : fetch_word AsanUbsan.M.loaded_segments (0x7b04c : word) = Some W_7ac34.
Proof. vm_refl. Qed.
Lemma D_7ac34 : decode_any W_7ac34 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac38 : bv 32 := 0x04a6f263.
Lemma F_7ac38 : fetch_word AsanUbsan.M.loaded_segments (0x7b050 : word) = Some W_7ac38.
Proof. vm_refl. Qed.
Lemma D_7ac38 : decode_any W_7ac38 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac3c : bv 32 := 0x000bc697.
Lemma F_7ac3c : fetch_word AsanUbsan.M.loaded_segments (0x7b054 : word) = Some W_7ac3c.
Proof. vm_refl. Qed.
Lemma D_7ac3c : decode_any W_7ac3c = Some (Auipc 13 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac40 : bv 32 := 0x4746b683.
Lemma F_7ac40 : fetch_word AsanUbsan.M.loaded_segments (0x7b058 : word) = Some W_7ac40.
Proof. vm_refl. Qed.
Lemma D_7ac40 : decode_any W_7ac40 = Some (Load SZ8 true 13 13 1140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac44 : bv 32 := 0x000bc717.
Lemma F_7ac44 : fetch_word AsanUbsan.M.loaded_segments (0x7b05c : word) = Some W_7ac44.
Proof. vm_refl. Qed.
Lemma D_7ac44 : decode_any W_7ac44 = Some (Auipc 14 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac48 : bv 32 := 0x47473703.
Lemma F_7ac48 : fetch_word AsanUbsan.M.loaded_segments (0x7b060 : word) = Some W_7ac48.
Proof. vm_refl. Qed.
Lemma D_7ac48 : decode_any W_7ac48 = Some (Load SZ8 true 14 14 1140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac4c : bv 32 := 0x0006b803.
Lemma F_7ac4c : fetch_word AsanUbsan.M.loaded_segments (0x7b064 : word) = Some W_7ac4c.
Proof. vm_refl. Qed.
Lemma D_7ac4c : decode_any W_7ac4c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac50 : bv 32 := 0x00073683.
Lemma F_7ac50 : fetch_word AsanUbsan.M.loaded_segments (0x7b068 : word) = Some W_7ac50.
Proof. vm_refl. Qed.
Lemma D_7ac50 : decode_any W_7ac50 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac54 : bv 32 := 0xfff80793.
Lemma F_7ac54 : fetch_word AsanUbsan.M.loaded_segments (0x7b06c : word) = Some W_7ac54.
Proof. vm_refl. Qed.
Lemma D_7ac54 : decode_any W_7ac54 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac58 : bv 32 := 0x00a7f463.
Lemma F_7ac58 : fetch_word AsanUbsan.M.loaded_segments (0x7b070 : word) = Some W_7ac58.
Proof. vm_refl. Qed.
Lemma D_7ac58 : decode_any W_7ac58 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac60 : bv 32 := 0x000bc717.
Lemma F_7ac60 : fetch_word AsanUbsan.M.loaded_segments (0x7b078 : word) = Some W_7ac60.
Proof. vm_refl. Qed.
Lemma D_7ac60 : decode_any W_7ac60 = Some (Auipc 14 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac64 : bv 32 := 0x46073703.
Lemma F_7ac64 : fetch_word AsanUbsan.M.loaded_segments (0x7b07c : word) = Some W_7ac64.
Proof. vm_refl. Qed.
Lemma D_7ac64 : decode_any W_7ac64 = Some (Load SZ8 true 14 14 1120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac68 : bv 32 := 0x00073283.
Lemma F_7ac68 : fetch_word AsanUbsan.M.loaded_segments (0x7b080 : word) = Some W_7ac68.
Proof. vm_refl. Qed.
Lemma D_7ac68 : decode_any W_7ac68 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac6c : bv 32 := 0x0032d713.
Lemma F_7ac6c : fetch_word AsanUbsan.M.loaded_segments (0x7b084 : word) = Some W_7ac6c.
Proof. vm_refl. Qed.
Lemma D_7ac6c : decode_any W_7ac6c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac70 : bv 32 := 0x00b708b3.
Lemma F_7ac70 : fetch_word AsanUbsan.M.loaded_segments (0x7b088 : word) = Some W_7ac70.
Proof. vm_refl. Qed.
Lemma D_7ac70 : decode_any W_7ac70 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac74 : bv 32 := 0x00a2ea63.
Lemma F_7ac74 : fetch_word AsanUbsan.M.loaded_segments (0x7b08c : word) = Some W_7ac74.
Proof. vm_refl. Qed.
Lemma D_7ac74 : decode_any W_7ac74 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac78 : bv 32 := 0x00a8f863.
Lemma F_7ac78 : fetch_word AsanUbsan.M.loaded_segments (0x7b090 : word) = Some W_7ac78.
Proof. vm_refl. Qed.
Lemma D_7ac78 : decode_any W_7ac78 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac7c : bv 32 := 0x00355513.
Lemma F_7ac7c : fetch_word AsanUbsan.M.loaded_segments (0x7b094 : word) = Some W_7ac7c.
Proof. vm_refl. Qed.
Lemma D_7ac7c : decode_any W_7ac7c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac80 : bv 32 := 0x00a58533.
Lemma F_7ac80 : fetch_word AsanUbsan.M.loaded_segments (0x7b098 : word) = Some W_7ac80.
Proof. vm_refl. Qed.
Lemma D_7ac80 : decode_any W_7ac80 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ac84 : bv 32 := 0x00008067.
Lemma F_7ac84 : fetch_word AsanUbsan.M.loaded_segments (0x7b09c : word) = Some W_7ac84.
Proof. vm_refl. Qed.
Lemma D_7ac84 : decode_any W_7ac84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
