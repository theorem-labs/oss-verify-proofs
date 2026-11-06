(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_44228 : bv 32 := 0x5b80006f.
Lemma F_44228 : fetch_word AsanUbsan.M.loaded_segments (0x44228 : word) = Some W_44228.
Proof. vm_refl. Qed.
Lemma D_44228 : decode_any W_44228 = Some (Jal 0 1464, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_447dc : bv 32 := 0x00008067.
Lemma F_447dc : fetch_word AsanUbsan.M.loaded_segments (0x447dc : word) = Some W_447dc.
Proof. vm_refl. Qed.
Lemma D_447dc : decode_any W_447dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_447e0 : bv 32 := 0x81010113.
Lemma F_447e0 : fetch_word AsanUbsan.M.loaded_segments (0x447e0 : word) = Some W_447e0.
Proof. vm_refl. Qed.
Lemma D_447e0 : decode_any W_447e0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_447e4 : bv 32 := 0x7e113423.
Lemma F_447e4 : fetch_word AsanUbsan.M.loaded_segments (0x447e4 : word) = Some W_447e4.
Proof. vm_refl. Qed.
Lemma D_447e4 : decode_any W_447e4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_447e8 : bv 32 := 0x7e813023.
Lemma F_447e8 : fetch_word AsanUbsan.M.loaded_segments (0x447e8 : word) = Some W_447e8.
Proof. vm_refl. Qed.
Lemma D_447e8 : decode_any W_447e8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_447ec : bv 32 := 0x7c913c23.
Lemma F_447ec : fetch_word AsanUbsan.M.loaded_segments (0x447ec : word) = Some W_447ec.
Proof. vm_refl. Qed.
Lemma D_447ec : decode_any W_447ec = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_447f0 : bv 32 := 0x7d213823.
Lemma F_447f0 : fetch_word AsanUbsan.M.loaded_segments (0x447f0 : word) = Some W_447f0.
Proof. vm_refl. Qed.
Lemma D_447f0 : decode_any W_447f0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_447f4 : bv 32 := 0x7d313423.
Lemma F_447f4 : fetch_word AsanUbsan.M.loaded_segments (0x447f4 : word) = Some W_447f4.
Proof. vm_refl. Qed.
Lemma D_447f4 : decode_any W_447f4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_447f8 : bv 32 := 0x7d413023.
Lemma F_447f8 : fetch_word AsanUbsan.M.loaded_segments (0x447f8 : word) = Some W_447f8.
Proof. vm_refl. Qed.
Lemma D_447f8 : decode_any W_447f8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_447fc : bv 32 := 0x7b513c23.
Lemma F_447fc : fetch_word AsanUbsan.M.loaded_segments (0x447fc : word) = Some W_447fc.
Proof. vm_refl. Qed.
Lemma D_447fc : decode_any W_447fc = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44800 : bv 32 := 0x7b613823.
Lemma F_44800 : fetch_word AsanUbsan.M.loaded_segments (0x44800 : word) = Some W_44800.
Proof. vm_refl. Qed.
Lemma D_44800 : decode_any W_44800 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44804 : bv 32 := 0x7b713423.
Lemma F_44804 : fetch_word AsanUbsan.M.loaded_segments (0x44804 : word) = Some W_44804.
Proof. vm_refl. Qed.
Lemma D_44804 : decode_any W_44804 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44808 : bv 32 := 0x7b813023.
Lemma F_44808 : fetch_word AsanUbsan.M.loaded_segments (0x44808 : word) = Some W_44808.
Proof. vm_refl. Qed.
Lemma D_44808 : decode_any W_44808 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4480c : bv 32 := 0x79913c23.
Lemma F_4480c : fetch_word AsanUbsan.M.loaded_segments (0x4480c : word) = Some W_4480c.
Proof. vm_refl. Qed.
Lemma D_4480c : decode_any W_4480c = Some (Store SZ8 2 25 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44810 : bv 32 := 0x79a13823.
Lemma F_44810 : fetch_word AsanUbsan.M.loaded_segments (0x44810 : word) = Some W_44810.
Proof. vm_refl. Qed.
Lemma D_44810 : decode_any W_44810 = Some (Store SZ8 2 26 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44814 : bv 32 := 0x79b13423.
Lemma F_44814 : fetch_word AsanUbsan.M.loaded_segments (0x44814 : word) = Some W_44814.
Proof. vm_refl. Qed.
Lemma D_44814 : decode_any W_44814 = Some (Store SZ8 2 27 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44818 : bv 32 := 0x7f010413.
Lemma F_44818 : fetch_word AsanUbsan.M.loaded_segments (0x44818 : word) = Some W_44818.
Proof. vm_refl. Qed.
Lemma D_44818 : decode_any W_44818 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4481c : bv 32 := 0xf6010113.
Lemma F_4481c : fetch_word AsanUbsan.M.loaded_segments (0x4481c : word) = Some W_4481c.
Proof. vm_refl. Qed.
Lemma D_4481c : decode_any W_4481c = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44820 : bv 32 := 0x00008993.
Lemma F_44820 : fetch_word AsanUbsan.M.loaded_segments (0x44820 : word) = Some W_44820.
Proof. vm_refl. Qed.
Lemma D_44820 : decode_any W_44820 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44824 : bv 32 := 0x00058493.
Lemma F_44824 : fetch_word AsanUbsan.M.loaded_segments (0x44824 : word) = Some W_44824.
Proof. vm_refl. Qed.
Lemma D_44824 : decode_any W_44824 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44828 : bv 32 := 0x00050913.
Lemma F_44828 : fetch_word AsanUbsan.M.loaded_segments (0x44828 : word) = Some W_44828.
Proof. vm_refl. Qed.
Lemma D_44828 : decode_any W_44828 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4482c : bv 32 := 0x604170ef.
Lemma F_4482c : fetch_word AsanUbsan.M.loaded_segments (0x4482c : word) = Some W_4482c.
Proof. vm_refl. Qed.
Lemma D_4482c : decode_any W_4482c = Some (Jal 1 95748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44830 : bv 32 := 0x14050663.
Lemma F_44830 : fetch_word AsanUbsan.M.loaded_segments (0x44830 : word) = Some W_44830.
Proof. vm_refl. Qed.
Lemma D_44830 : decode_any W_44830 = Some (Branch BC_EQ 10 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44834 : bv 32 := 0x00000a13.
Lemma F_44834 : fetch_word AsanUbsan.M.loaded_segments (0x44834 : word) = Some W_44834.
Proof. vm_refl. Qed.
Lemma D_44834 : decode_any W_44834 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44838 : bv 32 := 0x80040d93.
Lemma F_44838 : fetch_word AsanUbsan.M.loaded_segments (0x44838 : word) = Some W_44838.
Proof. vm_refl. Qed.
Lemma D_44838 : decode_any W_44838 = Some (OpImm ALU_ADD 27 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4483c : bv 32 := 0xf80d8d93.
Lemma F_4483c : fetch_word AsanUbsan.M.loaded_segments (0x4483c : word) = Some W_4483c.
Proof. vm_refl. Qed.
Lemma D_4483c : decode_any W_4483c = Some (OpImm ALU_ADD 27 27 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44840 : bv 32 := 0x01490533.
Lemma F_44840 : fetch_word AsanUbsan.M.loaded_segments (0x44840 : word) = Some W_44840.
Proof. vm_refl. Qed.
Lemma D_44840 : decode_any W_44840 = Some (Op ALU_ADD 10 18 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44844 : bv 32 := 0x00054c83.
Lemma F_44844 : fetch_word AsanUbsan.M.loaded_segments (0x44844 : word) = Some W_44844.
Proof. vm_refl. Qed.
Lemma D_44844 : decode_any W_44844 = Some (Load SZ1 false 25 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44848 : bv 32 := 0x01448533.
Lemma F_44848 : fetch_word AsanUbsan.M.loaded_segments (0x44848 : word) = Some W_44848.
Proof. vm_refl. Qed.
Lemma D_44848 : decode_any W_44848 = Some (Op ALU_ADD 10 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4484c : bv 32 := 0x00054d03.
Lemma F_4484c : fetch_word AsanUbsan.M.loaded_segments (0x4484c : word) = Some W_4484c.
Proof. vm_refl. Qed.
Lemma D_4484c : decode_any W_4484c = Some (Load SZ1 false 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44850 : bv 32 := 0x001a0a13.
Lemma F_44850 : fetch_word AsanUbsan.M.loaded_segments (0x44850 : word) = Some W_44850.
Proof. vm_refl. Qed.
Lemma D_44850 : decode_any W_44850 = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44854 : bv 32 := 0x000c8463.
Lemma F_44854 : fetch_word AsanUbsan.M.loaded_segments (0x44854 : word) = Some W_44854.
Proof. vm_refl. Qed.
Lemma D_44854 : decode_any W_44854 = Some (Branch BC_EQ 25 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44858 : bv 32 := 0xffac84e3.
Lemma F_44858 : fetch_word AsanUbsan.M.loaded_segments (0x44858 : word) = Some W_44858.
Proof. vm_refl. Qed.
Lemma D_44858 : decode_any W_44858 = Some (Branch BC_EQ 25 26 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4485c : bv 32 := 0x00065517.
Lemma F_4485c : fetch_word AsanUbsan.M.loaded_segments (0x4485c : word) = Some W_4485c.
Proof. vm_refl. Qed.
Lemma D_4485c : decode_any W_4485c = Some (Auipc 10 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44860 : bv 32 := 0xc4c53c03.
Lemma F_44860 : fetch_word AsanUbsan.M.loaded_segments (0x44860 : word) = Some W_44860.
Proof. vm_refl. Qed.
Lemma D_44860 : decode_any W_44860 = Some (Load SZ8 true 24 10 3148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44864 : bv 32 := 0x0fac4503.
Lemma F_44864 : fetch_word AsanUbsan.M.loaded_segments (0x44864 : word) = Some W_44864.
Proof. vm_refl. Qed.
Lemma D_44864 : decode_any W_44864 = Some (Load SZ1 false 10 24 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44868 : bv 32 := 0x0a050863.
Lemma F_44868 : fetch_word AsanUbsan.M.loaded_segments (0x44868 : word) = Some W_44868.
Proof. vm_refl. Qed.
Lemma D_44868 : decode_any W_44868 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4486c : bv 32 := 0x0f5c4583.
Lemma F_4486c : fetch_word AsanUbsan.M.loaded_segments (0x4486c : word) = Some W_4486c.
Proof. vm_refl. Qed.
Lemma D_4486c : decode_any W_4486c = Some (Load SZ1 false 11 24 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44870 : bv 32 := 0xfffa0a93.
Lemma F_44870 : fetch_word AsanUbsan.M.loaded_segments (0x44870 : word) = Some W_44870.
Proof. vm_refl. Qed.
Lemma D_44870 : decode_any W_44870 = Some (OpImm ALU_ADD 21 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44874 : bv 32 := 0x000a0b13.
Lemma F_44874 : fetch_word AsanUbsan.M.loaded_segments (0x44874 : word) = Some W_44874.
Proof. vm_refl. Qed.
Lemma D_44874 : decode_any W_44874 = Some (OpImm ALU_ADD 22 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44878 : bv 32 := 0x000a8513.
Lemma F_44878 : fetch_word AsanUbsan.M.loaded_segments (0x44878 : word) = Some W_44878.
Proof. vm_refl. Qed.
Lemma D_44878 : decode_any W_44878 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4487c : bv 32 := 0x14059863.
Lemma F_4487c : fetch_word AsanUbsan.M.loaded_segments (0x4487c : word) = Some W_4487c.
Proof. vm_refl. Qed.
Lemma D_4487c : decode_any W_4487c = Some (Branch BC_NE 11 0 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44880 : bv 32 := 0xfff94593.
Lemma F_44880 : fetch_word AsanUbsan.M.loaded_segments (0x44880 : word) = Some W_44880.
Proof. vm_refl. Qed.
Lemma D_44880 : decode_any W_44880 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44884 : bv 32 := 0x1565ee63.
Lemma F_44884 : fetch_word AsanUbsan.M.loaded_segments (0x44884 : word) = Some W_44884.
Proof. vm_refl. Qed.
Lemma D_44884 : decode_any W_44884 = Some (Branch BC_LTU 11 22 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44888 : bv 32 := 0x04000593.
Lemma F_44888 : fetch_word AsanUbsan.M.loaded_segments (0x44888 : word) = Some W_44888.
Proof. vm_refl. Qed.
Lemma D_44888 : decode_any W_44888 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4488c : bv 32 := 0x1cb57863.
Lemma F_4488c : fetch_word AsanUbsan.M.loaded_segments (0x4488c : word) = Some W_4488c.
Proof. vm_refl. Qed.
Lemma D_4488c : decode_any W_4488c = Some (Branch BC_GEU 10 11 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44890 : bv 32 := 0x00065597.
Lemma F_44890 : fetch_word AsanUbsan.M.loaded_segments (0x44890 : word) = Some W_44890.
Proof. vm_refl. Qed.
Lemma D_44890 : decode_any W_44890 = Some (Auipc 11 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44894 : bv 32 := 0xc285b583.
Lemma F_44894 : fetch_word AsanUbsan.M.loaded_segments (0x44894 : word) = Some W_44894.
Proof. vm_refl. Qed.
Lemma D_44894 : decode_any W_44894 = Some (Load SZ8 true 11 11 3112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44898 : bv 32 := 0x0005b583.
Lemma F_44898 : fetch_word AsanUbsan.M.loaded_segments (0x44898 : word) = Some W_44898.
Proof. vm_refl. Qed.
Lemma D_44898 : decode_any W_44898 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4489c : bv 32 := 0x01250633.
Lemma F_4489c : fetch_word AsanUbsan.M.loaded_segments (0x4489c : word) = Some W_4489c.
Proof. vm_refl. Qed.
Lemma D_4489c : decode_any W_4489c = Some (Op ALU_ADD 12 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448a0 : bv 32 := 0x00395513.
Lemma F_448a0 : fetch_word AsanUbsan.M.loaded_segments (0x448a0 : word) = Some W_448a0.
Proof. vm_refl. Qed.
Lemma D_448a0 : decode_any W_448a0 = Some (ShiftImm ALU_SRL 10 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448a4 : bv 32 := 0x00365693.
Lemma F_448a4 : fetch_word AsanUbsan.M.loaded_segments (0x448a4 : word) = Some W_448a4.
Proof. vm_refl. Qed.
Lemma D_448a4 : decode_any W_448a4 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448a8 : bv 32 := 0x00a58533.
Lemma F_448a8 : fetch_word AsanUbsan.M.loaded_segments (0x448a8 : word) = Some W_448a8.
Proof. vm_refl. Qed.
Lemma D_448a8 : decode_any W_448a8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448ac : bv 32 := 0x00d585b3.
Lemma F_448ac : fetch_word AsanUbsan.M.loaded_segments (0x448ac : word) = Some W_448ac.
Proof. vm_refl. Qed.
Lemma D_448ac : decode_any W_448ac = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448b0 : bv 32 := 0xff857693.
Lemma F_448b0 : fetch_word AsanUbsan.M.loaded_segments (0x448b0 : word) = Some W_448b0.
Proof. vm_refl. Qed.
Lemma D_448b0 : decode_any W_448b0 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448b4 : bv 32 := 0xff85f713.
Lemma F_448b4 : fetch_word AsanUbsan.M.loaded_segments (0x448b4 : word) = Some W_448b4.
Proof. vm_refl. Qed.
Lemma D_448b4 : decode_any W_448b4 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448b8 : bv 32 := 0x0006b683.
Lemma F_448b8 : fetch_word AsanUbsan.M.loaded_segments (0x448b8 : word) = Some W_448b8.
Proof. vm_refl. Qed.
Lemma D_448b8 : decode_any W_448b8 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448bc : bv 32 := 0x00073703.
Lemma F_448bc : fetch_word AsanUbsan.M.loaded_segments (0x448bc : word) = Some W_448bc.
Proof. vm_refl. Qed.
Lemma D_448bc : decode_any W_448bc = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448c0 : bv 32 := 0x00d766b3.
Lemma F_448c0 : fetch_word AsanUbsan.M.loaded_segments (0x448c0 : word) = Some W_448c0.
Proof. vm_refl. Qed.
Lemma D_448c0 : decode_any W_448c0 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448c4 : bv 32 := 0x22069263.
Lemma F_448c4 : fetch_word AsanUbsan.M.loaded_segments (0x448c4 : word) = Some W_448c4.
Proof. vm_refl. Qed.
Lemma D_448c4 : decode_any W_448c4 = Some (Branch BC_NE 13 0 548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448c8 : bv 32 := 0x0f5c4503.
Lemma F_448c8 : fetch_word AsanUbsan.M.loaded_segments (0x448c8 : word) = Some W_448c8.
Proof. vm_refl. Qed.
Lemma D_448c8 : decode_any W_448c8 = Some (Load SZ1 false 10 24 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448cc : bv 32 := 0x18051c63.
Lemma F_448cc : fetch_word AsanUbsan.M.loaded_segments (0x448cc : word) = Some W_448cc.
Proof. vm_refl. Qed.
Lemma D_448cc : decode_any W_448cc = Some (Branch BC_NE 10 0 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448d0 : bv 32 := 0xfff4c513.
Lemma F_448d0 : fetch_word AsanUbsan.M.loaded_segments (0x448d0 : word) = Some W_448d0.
Proof. vm_refl. Qed.
Lemma D_448d0 : decode_any W_448d0 = Some (OpImm ALU_XOR 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448d4 : bv 32 := 0x1b456463.
Lemma F_448d4 : fetch_word AsanUbsan.M.loaded_segments (0x448d4 : word) = Some W_448d4.
Proof. vm_refl. Qed.
Lemma D_448d4 : decode_any W_448d4 = Some (Branch BC_LTU 10 20 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448d8 : bv 32 := 0x04000513.
Lemma F_448d8 : fetch_word AsanUbsan.M.loaded_segments (0x448d8 : word) = Some W_448d8.
Proof. vm_refl. Qed.
Lemma D_448d8 : decode_any W_448d8 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448dc : bv 32 := 0x20aaf263.
Lemma F_448dc : fetch_word AsanUbsan.M.loaded_segments (0x448dc : word) = Some W_448dc.
Proof. vm_refl. Qed.
Lemma D_448dc : decode_any W_448dc = Some (Branch BC_GEU 21 10 516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448e0 : bv 32 := 0x00065517.
Lemma F_448e0 : fetch_word AsanUbsan.M.loaded_segments (0x448e0 : word) = Some W_448e0.
Proof. vm_refl. Qed.
Lemma D_448e0 : decode_any W_448e0 = Some (Auipc 10 101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448e4 : bv 32 := 0xbd853503.
Lemma F_448e4 : fetch_word AsanUbsan.M.loaded_segments (0x448e4 : word) = Some W_448e4.
Proof. vm_refl. Qed.
Lemma D_448e4 : decode_any W_448e4 = Some (Load SZ8 true 10 10 3032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448e8 : bv 32 := 0x00053583.
Lemma F_448e8 : fetch_word AsanUbsan.M.loaded_segments (0x448e8 : word) = Some W_448e8.
Proof. vm_refl. Qed.
Lemma D_448e8 : decode_any W_448e8 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448ec : bv 32 := 0x009a8ab3.
Lemma F_448ec : fetch_word AsanUbsan.M.loaded_segments (0x448ec : word) = Some W_448ec.
Proof. vm_refl. Qed.
Lemma D_448ec : decode_any W_448ec = Some (Op ALU_ADD 21 21 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448f0 : bv 32 := 0x0034d513.
Lemma F_448f0 : fetch_word AsanUbsan.M.loaded_segments (0x448f0 : word) = Some W_448f0.
Proof. vm_refl. Qed.
Lemma D_448f0 : decode_any W_448f0 = Some (ShiftImm ALU_SRL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448f4 : bv 32 := 0x003ad613.
Lemma F_448f4 : fetch_word AsanUbsan.M.loaded_segments (0x448f4 : word) = Some W_448f4.
Proof. vm_refl. Qed.
Lemma D_448f4 : decode_any W_448f4 = Some (ShiftImm ALU_SRL 12 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448f8 : bv 32 := 0x00a58533.
Lemma F_448f8 : fetch_word AsanUbsan.M.loaded_segments (0x448f8 : word) = Some W_448f8.
Proof. vm_refl. Qed.
Lemma D_448f8 : decode_any W_448f8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_448fc : bv 32 := 0x00c585b3.
Lemma F_448fc : fetch_word AsanUbsan.M.loaded_segments (0x448fc : word) = Some W_448fc.
Proof. vm_refl. Qed.
Lemma D_448fc : decode_any W_448fc = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44900 : bv 32 := 0xff857613.
Lemma F_44900 : fetch_word AsanUbsan.M.loaded_segments (0x44900 : word) = Some W_44900.
Proof. vm_refl. Qed.
Lemma D_44900 : decode_any W_44900 = Some (OpImm ALU_AND 12 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44904 : bv 32 := 0xff85f693.
Lemma F_44904 : fetch_word AsanUbsan.M.loaded_segments (0x44904 : word) = Some W_44904.
Proof. vm_refl. Qed.
Lemma D_44904 : decode_any W_44904 = Some (OpImm ALU_AND 13 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44908 : bv 32 := 0x00063603.
Lemma F_44908 : fetch_word AsanUbsan.M.loaded_segments (0x44908 : word) = Some W_44908.
Proof. vm_refl. Qed.
Lemma D_44908 : decode_any W_44908 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4490c : bv 32 := 0x0006b683.
Lemma F_4490c : fetch_word AsanUbsan.M.loaded_segments (0x4490c : word) = Some W_4490c.
Proof. vm_refl. Qed.
Lemma D_4490c : decode_any W_4490c = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44910 : bv 32 := 0x00c6e633.
Lemma F_44910 : fetch_word AsanUbsan.M.loaded_segments (0x44910 : word) = Some W_44910.
Proof. vm_refl. Qed.
Lemma D_44910 : decode_any W_44910 = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44914 : bv 32 := 0x2a061a63.
Lemma F_44914 : fetch_word AsanUbsan.M.loaded_segments (0x44914 : word) = Some W_44914.
Proof. vm_refl. Qed.
Lemma D_44914 : decode_any W_44914 = Some (Branch BC_NE 12 0 692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44918 : bv 32 := 0x01acb533.
Lemma F_44918 : fetch_word AsanUbsan.M.loaded_segments (0x44918 : word) = Some W_44918.
Proof. vm_refl. Qed.
Lemma D_44918 : decode_any W_44918 = Some (Op ALU_SLTU 10 25 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4491c : bv 32 := 0x019d35b3.
Lemma F_4491c : fetch_word AsanUbsan.M.loaded_segments (0x4491c : word) = Some W_4491c.
Proof. vm_refl. Qed.
Lemma D_4491c : decode_any W_4491c = Some (Op ALU_SLTU 11 26 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44920 : bv 32 := 0x40a58a33.
Lemma F_44920 : fetch_word AsanUbsan.M.loaded_segments (0x44920 : word) = Some W_44920.
Proof. vm_refl. Qed.
Lemma D_44920 : decode_any W_44920 = Some (Op ALU_SUB 20 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44924 : bv 32 := 0x00098513.
Lemma F_44924 : fetch_word AsanUbsan.M.loaded_segments (0x44924 : word) = Some W_44924.
Proof. vm_refl. Qed.
Lemma D_44924 : decode_any W_44924 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44928 : bv 32 := 0x00090593.
Lemma F_44928 : fetch_word AsanUbsan.M.loaded_segments (0x44928 : word) = Some W_44928.
Proof. vm_refl. Qed.
Lemma D_44928 : decode_any W_44928 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4492c : bv 32 := 0x00048613.
Lemma F_4492c : fetch_word AsanUbsan.M.loaded_segments (0x4492c : word) = Some W_4492c.
Proof. vm_refl. Qed.
Lemma D_4492c : decode_any W_4492c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44930 : bv 32 := 0x000a0693.
Lemma F_44930 : fetch_word AsanUbsan.M.loaded_segments (0x44930 : word) = Some W_44930.
Proof. vm_refl. Qed.
Lemma D_44930 : decode_any W_44930 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44934 : bv 32 := 0xea9ff0ef.
Lemma F_44934 : fetch_word AsanUbsan.M.loaded_segments (0x44934 : word) = Some W_44934.
Proof. vm_refl. Qed.
Lemma D_44934 : decode_any W_44934 = Some (Jal 1 2096808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44938 : bv 32 := 0x000a0513.
Lemma F_44938 : fetch_word AsanUbsan.M.loaded_segments (0x44938 : word) = Some W_44938.
Proof. vm_refl. Qed.
Lemma D_44938 : decode_any W_44938 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4493c : bv 32 := 0x0a010113.
Lemma F_4493c : fetch_word AsanUbsan.M.loaded_segments (0x4493c : word) = Some W_4493c.
Proof. vm_refl. Qed.
Lemma D_4493c : decode_any W_4493c = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44940 : bv 32 := 0x7e813083.
Lemma F_44940 : fetch_word AsanUbsan.M.loaded_segments (0x44940 : word) = Some W_44940.
Proof. vm_refl. Qed.
Lemma D_44940 : decode_any W_44940 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44944 : bv 32 := 0x7e013403.
Lemma F_44944 : fetch_word AsanUbsan.M.loaded_segments (0x44944 : word) = Some W_44944.
Proof. vm_refl. Qed.
Lemma D_44944 : decode_any W_44944 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44948 : bv 32 := 0x7d813483.
Lemma F_44948 : fetch_word AsanUbsan.M.loaded_segments (0x44948 : word) = Some W_44948.
Proof. vm_refl. Qed.
Lemma D_44948 : decode_any W_44948 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4494c : bv 32 := 0x7d013903.
Lemma F_4494c : fetch_word AsanUbsan.M.loaded_segments (0x4494c : word) = Some W_4494c.
Proof. vm_refl. Qed.
Lemma D_4494c : decode_any W_4494c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44950 : bv 32 := 0x7c813983.
Lemma F_44950 : fetch_word AsanUbsan.M.loaded_segments (0x44950 : word) = Some W_44950.
Proof. vm_refl. Qed.
Lemma D_44950 : decode_any W_44950 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44954 : bv 32 := 0x7c013a03.
Lemma F_44954 : fetch_word AsanUbsan.M.loaded_segments (0x44954 : word) = Some W_44954.
Proof. vm_refl. Qed.
Lemma D_44954 : decode_any W_44954 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44958 : bv 32 := 0x7b813a83.
Lemma F_44958 : fetch_word AsanUbsan.M.loaded_segments (0x44958 : word) = Some W_44958.
Proof. vm_refl. Qed.
Lemma D_44958 : decode_any W_44958 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4495c : bv 32 := 0x7b013b03.
Lemma F_4495c : fetch_word AsanUbsan.M.loaded_segments (0x4495c : word) = Some W_4495c.
Proof. vm_refl. Qed.
Lemma D_4495c : decode_any W_4495c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44960 : bv 32 := 0x7a813b83.
Lemma F_44960 : fetch_word AsanUbsan.M.loaded_segments (0x44960 : word) = Some W_44960.
Proof. vm_refl. Qed.
Lemma D_44960 : decode_any W_44960 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44964 : bv 32 := 0x7a013c03.
Lemma F_44964 : fetch_word AsanUbsan.M.loaded_segments (0x44964 : word) = Some W_44964.
Proof. vm_refl. Qed.
Lemma D_44964 : decode_any W_44964 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44968 : bv 32 := 0x79813c83.
Lemma F_44968 : fetch_word AsanUbsan.M.loaded_segments (0x44968 : word) = Some W_44968.
Proof. vm_refl. Qed.
Lemma D_44968 : decode_any W_44968 = Some (Load SZ8 true 25 2 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4496c : bv 32 := 0x79013d03.
Lemma F_4496c : fetch_word AsanUbsan.M.loaded_segments (0x4496c : word) = Some W_4496c.
Proof. vm_refl. Qed.
Lemma D_4496c : decode_any W_4496c = Some (Load SZ8 true 26 2 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44970 : bv 32 := 0x78813d83.
Lemma F_44970 : fetch_word AsanUbsan.M.loaded_segments (0x44970 : word) = Some W_44970.
Proof. vm_refl. Qed.
Lemma D_44970 : decode_any W_44970 = Some (Load SZ8 true 27 2 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44974 : bv 32 := 0x7f010113.
Lemma F_44974 : fetch_word AsanUbsan.M.loaded_segments (0x44974 : word) = Some W_44974.
Proof. vm_refl. Qed.
Lemma D_44974 : decode_any W_44974 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44978 : bv 32 := 0x00008067.
Lemma F_44978 : fetch_word AsanUbsan.M.loaded_segments (0x44978 : word) = Some W_44978.
Proof. vm_refl. Qed.
Lemma D_44978 : decode_any W_44978 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4497c : bv 32 := 0x00067517.
Lemma F_4497c : fetch_word AsanUbsan.M.loaded_segments (0x4497c : word) = Some W_4497c.
Proof. vm_refl. Qed.
Lemma D_4497c : decode_any W_4497c = Some (Auipc 10 103, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44980 : bv 32 := 0x85453303.
Lemma F_44980 : fetch_word AsanUbsan.M.loaded_segments (0x44980 : word) = Some W_44980.
Proof. vm_refl. Qed.
Lemma D_44980 : decode_any W_44980 = Some (Load SZ8 true 6 10 2132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44984 : bv 32 := 0x00090513.
Lemma F_44984 : fetch_word AsanUbsan.M.loaded_segments (0x44984 : word) = Some W_44984.
Proof. vm_refl. Qed.
Lemma D_44984 : decode_any W_44984 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44988 : bv 32 := 0x00048593.
Lemma F_44988 : fetch_word AsanUbsan.M.loaded_segments (0x44988 : word) = Some W_44988.
Proof. vm_refl. Qed.
Lemma D_44988 : decode_any W_44988 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4498c : bv 32 := 0x0a010113.
Lemma F_4498c : fetch_word AsanUbsan.M.loaded_segments (0x4498c : word) = Some W_4498c.
Proof. vm_refl. Qed.
Lemma D_4498c : decode_any W_4498c = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44990 : bv 32 := 0x7e813083.
Lemma F_44990 : fetch_word AsanUbsan.M.loaded_segments (0x44990 : word) = Some W_44990.
Proof. vm_refl. Qed.
Lemma D_44990 : decode_any W_44990 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44994 : bv 32 := 0x7e013403.
Lemma F_44994 : fetch_word AsanUbsan.M.loaded_segments (0x44994 : word) = Some W_44994.
Proof. vm_refl. Qed.
Lemma D_44994 : decode_any W_44994 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44998 : bv 32 := 0x7d813483.
Lemma F_44998 : fetch_word AsanUbsan.M.loaded_segments (0x44998 : word) = Some W_44998.
Proof. vm_refl. Qed.
Lemma D_44998 : decode_any W_44998 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_4499c : bv 32 := 0x7d013903.
Lemma F_4499c : fetch_word AsanUbsan.M.loaded_segments (0x4499c : word) = Some W_4499c.
Proof. vm_refl. Qed.
Lemma D_4499c : decode_any W_4499c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449a0 : bv 32 := 0x7c813983.
Lemma F_449a0 : fetch_word AsanUbsan.M.loaded_segments (0x449a0 : word) = Some W_449a0.
Proof. vm_refl. Qed.
Lemma D_449a0 : decode_any W_449a0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449a4 : bv 32 := 0x7c013a03.
Lemma F_449a4 : fetch_word AsanUbsan.M.loaded_segments (0x449a4 : word) = Some W_449a4.
Proof. vm_refl. Qed.
Lemma D_449a4 : decode_any W_449a4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449a8 : bv 32 := 0x7b813a83.
Lemma F_449a8 : fetch_word AsanUbsan.M.loaded_segments (0x449a8 : word) = Some W_449a8.
Proof. vm_refl. Qed.
Lemma D_449a8 : decode_any W_449a8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449ac : bv 32 := 0x7b013b03.
Lemma F_449ac : fetch_word AsanUbsan.M.loaded_segments (0x449ac : word) = Some W_449ac.
Proof. vm_refl. Qed.
Lemma D_449ac : decode_any W_449ac = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449b0 : bv 32 := 0x7a813b83.
Lemma F_449b0 : fetch_word AsanUbsan.M.loaded_segments (0x449b0 : word) = Some W_449b0.
Proof. vm_refl. Qed.
Lemma D_449b0 : decode_any W_449b0 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449b4 : bv 32 := 0x7a013c03.
Lemma F_449b4 : fetch_word AsanUbsan.M.loaded_segments (0x449b4 : word) = Some W_449b4.
Proof. vm_refl. Qed.
Lemma D_449b4 : decode_any W_449b4 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449b8 : bv 32 := 0x79813c83.
Lemma F_449b8 : fetch_word AsanUbsan.M.loaded_segments (0x449b8 : word) = Some W_449b8.
Proof. vm_refl. Qed.
Lemma D_449b8 : decode_any W_449b8 = Some (Load SZ8 true 25 2 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449bc : bv 32 := 0x79013d03.
Lemma F_449bc : fetch_word AsanUbsan.M.loaded_segments (0x449bc : word) = Some W_449bc.
Proof. vm_refl. Qed.
Lemma D_449bc : decode_any W_449bc = Some (Load SZ8 true 26 2 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449c0 : bv 32 := 0x78813d83.
Lemma F_449c0 : fetch_word AsanUbsan.M.loaded_segments (0x449c0 : word) = Some W_449c0.
Proof. vm_refl. Qed.
Lemma D_449c0 : decode_any W_449c0 = Some (Load SZ8 true 27 2 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449c4 : bv 32 := 0x7f010113.
Lemma F_449c4 : fetch_word AsanUbsan.M.loaded_segments (0x449c4 : word) = Some W_449c4.
Proof. vm_refl. Qed.
Lemma D_449c4 : decode_any W_449c4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449c8 : bv 32 := 0x00030067.
Lemma F_449c8 : fetch_word AsanUbsan.M.loaded_segments (0x449c8 : word) = Some W_449c8.
Proof. vm_refl. Qed.
Lemma D_449c8 : decode_any W_449c8 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449cc : bv 32 := 0x00090513.
Lemma F_449cc : fetch_word AsanUbsan.M.loaded_segments (0x449cc : word) = Some W_449cc.
Proof. vm_refl. Qed.
Lemma D_449cc : decode_any W_449cc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449d0 : bv 32 := 0x131210ef.
Lemma F_449d0 : fetch_word AsanUbsan.M.loaded_segments (0x449d0 : word) = Some W_449d0.
Proof. vm_refl. Qed.
Lemma D_449d0 : decode_any W_449d0 = Some (Jal 1 137520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449d4 : bv 32 := 0x00150b13.
Lemma F_449d4 : fetch_word AsanUbsan.M.loaded_segments (0x449d4 : word) = Some W_449d4.
Proof. vm_refl. Qed.
Lemma D_449d4 : decode_any W_449d4 = Some (OpImm ALU_ADD 22 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449d8 : bv 32 := 0xfff94593.
Lemma F_449d8 : fetch_word AsanUbsan.M.loaded_segments (0x449d8 : word) = Some W_449d8.
Proof. vm_refl. Qed.
Lemma D_449d8 : decode_any W_449d8 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449dc : bv 32 := 0xeb65f6e3.
Lemma F_449dc : fetch_word AsanUbsan.M.loaded_segments (0x449dc : word) = Some W_449dc.
Proof. vm_refl. Qed.
Lemma D_449dc : decode_any W_449dc = Some (Branch BC_GEU 11 22 7852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449e0 : bv 32 := 0x80040593.
Lemma F_449e0 : fetch_word AsanUbsan.M.loaded_segments (0x449e0 : word) = Some W_449e0.
Proof. vm_refl. Qed.
Lemma D_449e0 : decode_any W_449e0 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449e4 : bv 32 := 0xf9058593.
Lemma F_449e4 : fetch_word AsanUbsan.M.loaded_segments (0x449e4 : word) = Some W_449e4.
Proof. vm_refl. Qed.
Lemma D_449e4 : decode_any W_449e4 = Some (OpImm ALU_ADD 11 11 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449e8 : bv 32 := 0x80040613.
Lemma F_449e8 : fetch_word AsanUbsan.M.loaded_segments (0x449e8 : word) = Some W_449e8.
Proof. vm_refl. Qed.
Lemma D_449e8 : decode_any W_449e8 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449ec : bv 32 := 0xf8060613.
Lemma F_449ec : fetch_word AsanUbsan.M.loaded_segments (0x449ec : word) = Some W_449ec.
Proof. vm_refl. Qed.
Lemma D_449ec : decode_any W_449ec = Some (OpImm ALU_ADD 12 12 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449f0 : bv 32 := 0x7ff60b93.
Lemma F_449f0 : fetch_word AsanUbsan.M.loaded_segments (0x449f0 : word) = Some W_449f0.
Proof. vm_refl. Qed.
Lemma D_449f0 : decode_any W_449f0 = Some (OpImm ALU_ADD 23 12 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449f4 : bv 32 := 0x000bb4a3.
Lemma F_449f4 : fetch_word AsanUbsan.M.loaded_segments (0x449f4 : word) = Some W_449f4.
Proof. vm_refl. Qed.
Lemma D_449f4 : decode_any W_449f4 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449f8 : bv 32 := 0x00bdb023.
Lemma F_449f8 : fetch_word AsanUbsan.M.loaded_segments (0x449f8 : word) = Some W_449f8.
Proof. vm_refl. Qed.
Lemma D_449f8 : decode_any W_449f8 = Some (Store SZ8 27 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_449fc : bv 32 := 0x000db423.
Lemma F_449fc : fetch_word AsanUbsan.M.loaded_segments (0x449fc : word) = Some W_449fc.
Proof. vm_refl. Qed.
Lemma D_449fc : decode_any W_449fc = Some (Store SZ8 27 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a00 : bv 32 := 0x000015b7.
Lemma F_44a00 : fetch_word AsanUbsan.M.loaded_segments (0x44a00 : word) = Some W_44a00.
Proof. vm_refl. Qed.
Lemma D_44a00 : decode_any W_44a00 = Some (Lui 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a04 : bv 32 := 0x40b405b3.
Lemma F_44a04 : fetch_word AsanUbsan.M.loaded_segments (0x44a04 : word) = Some W_44a04.
Proof. vm_refl. Qed.
Lemma D_44a04 : decode_any W_44a04 = Some (Op ALU_SUB 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a08 : bv 32 := 0x76a5bc23.
Lemma F_44a08 : fetch_word AsanUbsan.M.loaded_segments (0x44a08 : word) = Some W_44a08.
Proof. vm_refl. Qed.
Lemma D_44a08 : decode_any W_44a08 = Some (Store SZ8 11 10 1912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a0c : bv 32 := 0x46d300ef.
Lemma F_44a0c : fetch_word AsanUbsan.M.loaded_segments (0x44a0c : word) = Some W_44a0c.
Proof. vm_refl. Qed.
Lemma D_44a0c : decode_any W_44a0c = Some (Jal 1 199788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a10 : bv 32 := 0x00050593.
Lemma F_44a10 : fetch_word AsanUbsan.M.loaded_segments (0x44a10 : word) = Some W_44a10.
Proof. vm_refl. Qed.
Lemma D_44a10 : decode_any W_44a10 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a14 : bv 32 := 0x021c4703.
Lemma F_44a14 : fetch_word AsanUbsan.M.loaded_segments (0x44a14 : word) = Some W_44a14.
Proof. vm_refl. Qed.
Lemma D_44a14 : decode_any W_44a14 = Some (Load SZ1 false 14 24 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a18 : bv 32 := 0x008bb4a3.
Lemma F_44a18 : fetch_word AsanUbsan.M.loaded_segments (0x44a18 : word) = Some W_44a18.
Proof. vm_refl. Qed.
Lemma D_44a18 : decode_any W_44a18 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a1c : bv 32 := 0x80040513.
Lemma F_44a1c : fetch_word AsanUbsan.M.loaded_segments (0x44a1c : word) = Some W_44a1c.
Proof. vm_refl. Qed.
Lemma D_44a1c : decode_any W_44a1c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a20 : bv 32 := 0xf8050513.
Lemma F_44a20 : fetch_word AsanUbsan.M.loaded_segments (0x44a20 : word) = Some W_44a20.
Proof. vm_refl. Qed.
Lemma D_44a20 : decode_any W_44a20 = Some (OpImm ALU_ADD 10 10 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a24 : bv 32 := 0x0ff00793.
Lemma F_44a24 : fetch_word AsanUbsan.M.loaded_segments (0x44a24 : word) = Some W_44a24.
Proof. vm_refl. Qed.
Lemma D_44a24 : decode_any W_44a24 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a28 : bv 32 := 0x00040613.
Lemma F_44a28 : fetch_word AsanUbsan.M.loaded_segments (0x44a28 : word) = Some W_44a28.
Proof. vm_refl. Qed.
Lemma D_44a28 : decode_any W_44a28 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a2c : bv 32 := 0x00000693.
Lemma F_44a2c : fetch_word AsanUbsan.M.loaded_segments (0x44a2c : word) = Some W_44a2c.
Proof. vm_refl. Qed.
Lemma D_44a2c : decode_any W_44a2c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a30 : bv 32 := 0x198180ef.
Lemma F_44a30 : fetch_word AsanUbsan.M.loaded_segments (0x44a30 : word) = Some W_44a30.
Proof. vm_refl. Qed.
Lemma D_44a30 : decode_any W_44a30 = Some (Jal 1 98712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a34 : bv 32 := 0x80040613.
Lemma F_44a34 : fetch_word AsanUbsan.M.loaded_segments (0x44a34 : word) = Some W_44a34.
Proof. vm_refl. Qed.
Lemma D_44a34 : decode_any W_44a34 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a38 : bv 32 := 0xf8060613.
Lemma F_44a38 : fetch_word AsanUbsan.M.loaded_segments (0x44a38 : word) = Some W_44a38.
Proof. vm_refl. Qed.
Lemma D_44a38 : decode_any W_44a38 = Some (OpImm ALU_ADD 12 12 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a3c : bv 32 := 0x00090513.
Lemma F_44a3c : fetch_word AsanUbsan.M.loaded_segments (0x44a3c : word) = Some W_44a3c.
Proof. vm_refl. Qed.
Lemma D_44a3c : decode_any W_44a3c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a40 : bv 32 := 0x000b0593.
Lemma F_44a40 : fetch_word AsanUbsan.M.loaded_segments (0x44a40 : word) = Some W_44a40.
Proof. vm_refl. Qed.
Lemma D_44a40 : decode_any W_44a40 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a44 : bv 32 := 0x73d140ef.
Lemma F_44a44 : fetch_word AsanUbsan.M.loaded_segments (0x44a44 : word) = Some W_44a44.
Proof. vm_refl. Qed.
Lemma D_44a44 : decode_any W_44a44 = Some (Jal 1 85820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a48 : bv 32 := 0x00001537.
Lemma F_44a48 : fetch_word AsanUbsan.M.loaded_segments (0x44a48 : word) = Some W_44a48.
Proof. vm_refl. Qed.
Lemma D_44a48 : decode_any W_44a48 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a4c : bv 32 := 0x40a40533.
Lemma F_44a4c : fetch_word AsanUbsan.M.loaded_segments (0x44a4c : word) = Some W_44a4c.
Proof. vm_refl. Qed.
Lemma D_44a4c : decode_any W_44a4c = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a50 : bv 32 := 0x77853503.
Lemma F_44a50 : fetch_word AsanUbsan.M.loaded_segments (0x44a50 : word) = Some W_44a50.
Proof. vm_refl. Qed.
Lemma D_44a50 : decode_any W_44a50 = Some (Load SZ8 true 10 10 1912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a54 : bv 32 := 0x04000593.
Lemma F_44a54 : fetch_word AsanUbsan.M.loaded_segments (0x44a54 : word) = Some W_44a54.
Proof. vm_refl. Qed.
Lemma D_44a54 : decode_any W_44a54 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a58 : bv 32 := 0xe2b56ce3.
Lemma F_44a58 : fetch_word AsanUbsan.M.loaded_segments (0x44a58 : word) = Some W_44a58.
Proof. vm_refl. Qed.
Lemma D_44a58 : decode_any W_44a58 = Some (Branch BC_LTU 10 11 7736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a5c : bv 32 := 0x0c0b1063.
Lemma F_44a5c : fetch_word AsanUbsan.M.loaded_segments (0x44a5c : word) = Some W_44a5c.
Proof. vm_refl. Qed.
Lemma D_44a5c : decode_any W_44a5c = Some (Branch BC_NE 22 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a60 : bv 32 := 0xe69ff06f.
Lemma F_44a60 : fetch_word AsanUbsan.M.loaded_segments (0x44a60 : word) = Some W_44a60.
Proof. vm_refl. Qed.
Lemma D_44a60 : decode_any W_44a60 = Some (Jal 0 2096744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a64 : bv 32 := 0x00048513.
Lemma F_44a64 : fetch_word AsanUbsan.M.loaded_segments (0x44a64 : word) = Some W_44a64.
Proof. vm_refl. Qed.
Lemma D_44a64 : decode_any W_44a64 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a68 : bv 32 := 0x099210ef.
Lemma F_44a68 : fetch_word AsanUbsan.M.loaded_segments (0x44a68 : word) = Some W_44a68.
Proof. vm_refl. Qed.
Lemma D_44a68 : decode_any W_44a68 = Some (Jal 1 137368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a6c : bv 32 := 0x00050a93.
Lemma F_44a6c : fetch_word AsanUbsan.M.loaded_segments (0x44a6c : word) = Some W_44a6c.
Proof. vm_refl. Qed.
Lemma D_44a6c : decode_any W_44a6c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a70 : bv 32 := 0x00150a13.
Lemma F_44a70 : fetch_word AsanUbsan.M.loaded_segments (0x44a70 : word) = Some W_44a70.
Proof. vm_refl. Qed.
Lemma D_44a70 : decode_any W_44a70 = Some (OpImm ALU_ADD 20 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a74 : bv 32 := 0xfff4c513.
Lemma F_44a74 : fetch_word AsanUbsan.M.loaded_segments (0x44a74 : word) = Some W_44a74.
Proof. vm_refl. Qed.
Lemma D_44a74 : decode_any W_44a74 = Some (OpImm ALU_XOR 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a78 : bv 32 := 0xe74570e3.
Lemma F_44a78 : fetch_word AsanUbsan.M.loaded_segments (0x44a78 : word) = Some W_44a78.
Proof. vm_refl. Qed.
Lemma D_44a78 : decode_any W_44a78 = Some (Branch BC_GEU 10 20 7776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a7c : bv 32 := 0x80040513.
Lemma F_44a7c : fetch_word AsanUbsan.M.loaded_segments (0x44a7c : word) = Some W_44a7c.
Proof. vm_refl. Qed.
Lemma D_44a7c : decode_any W_44a7c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a80 : bv 32 := 0xf9050513.
Lemma F_44a80 : fetch_word AsanUbsan.M.loaded_segments (0x44a80 : word) = Some W_44a80.
Proof. vm_refl. Qed.
Lemma D_44a80 : decode_any W_44a80 = Some (OpImm ALU_ADD 10 10 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a84 : bv 32 := 0x80040593.
Lemma F_44a84 : fetch_word AsanUbsan.M.loaded_segments (0x44a84 : word) = Some W_44a84.
Proof. vm_refl. Qed.
Lemma D_44a84 : decode_any W_44a84 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a88 : bv 32 := 0xf8058593.
Lemma F_44a88 : fetch_word AsanUbsan.M.loaded_segments (0x44a88 : word) = Some W_44a88.
Proof. vm_refl. Qed.
Lemma D_44a88 : decode_any W_44a88 = Some (OpImm ALU_ADD 11 11 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a8c : bv 32 := 0x7ff58b13.
Lemma F_44a8c : fetch_word AsanUbsan.M.loaded_segments (0x44a8c : word) = Some W_44a8c.
Proof. vm_refl. Qed.
Lemma D_44a8c : decode_any W_44a8c = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a90 : bv 32 := 0x000b34a3.
Lemma F_44a90 : fetch_word AsanUbsan.M.loaded_segments (0x44a90 : word) = Some W_44a90.
Proof. vm_refl. Qed.
Lemma D_44a90 : decode_any W_44a90 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a94 : bv 32 := 0x00adb023.
Lemma F_44a94 : fetch_word AsanUbsan.M.loaded_segments (0x44a94 : word) = Some W_44a94.
Proof. vm_refl. Qed.
Lemma D_44a94 : decode_any W_44a94 = Some (Store SZ8 27 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a98 : bv 32 := 0x000db423.
Lemma F_44a98 : fetch_word AsanUbsan.M.loaded_segments (0x44a98 : word) = Some W_44a98.
Proof. vm_refl. Qed.
Lemma D_44a98 : decode_any W_44a98 = Some (Store SZ8 27 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44a9c : bv 32 := 0x3dd300ef.
Lemma F_44a9c : fetch_word AsanUbsan.M.loaded_segments (0x44a9c : word) = Some W_44a9c.
Proof. vm_refl. Qed.
Lemma D_44a9c : decode_any W_44a9c = Some (Jal 1 199644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44aa0 : bv 32 := 0x00050593.
Lemma F_44aa0 : fetch_word AsanUbsan.M.loaded_segments (0x44aa0 : word) = Some W_44aa0.
Proof. vm_refl. Qed.
Lemma D_44aa0 : decode_any W_44aa0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44aa4 : bv 32 := 0x021c4703.
Lemma F_44aa4 : fetch_word AsanUbsan.M.loaded_segments (0x44aa4 : word) = Some W_44aa4.
Proof. vm_refl. Qed.
Lemma D_44aa4 : decode_any W_44aa4 = Some (Load SZ1 false 14 24 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44aa8 : bv 32 := 0x008b34a3.
Lemma F_44aa8 : fetch_word AsanUbsan.M.loaded_segments (0x44aa8 : word) = Some W_44aa8.
Proof. vm_refl. Qed.
Lemma D_44aa8 : decode_any W_44aa8 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44aac : bv 32 := 0x80040513.
Lemma F_44aac : fetch_word AsanUbsan.M.loaded_segments (0x44aac : word) = Some W_44aac.
Proof. vm_refl. Qed.
Lemma D_44aac : decode_any W_44aac = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ab0 : bv 32 := 0xf8050513.
Lemma F_44ab0 : fetch_word AsanUbsan.M.loaded_segments (0x44ab0 : word) = Some W_44ab0.
Proof. vm_refl. Qed.
Lemma D_44ab0 : decode_any W_44ab0 = Some (OpImm ALU_ADD 10 10 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ab4 : bv 32 := 0x0ff00793.
Lemma F_44ab4 : fetch_word AsanUbsan.M.loaded_segments (0x44ab4 : word) = Some W_44ab4.
Proof. vm_refl. Qed.
Lemma D_44ab4 : decode_any W_44ab4 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ab8 : bv 32 := 0x00040613.
Lemma F_44ab8 : fetch_word AsanUbsan.M.loaded_segments (0x44ab8 : word) = Some W_44ab8.
Proof. vm_refl. Qed.
Lemma D_44ab8 : decode_any W_44ab8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44abc : bv 32 := 0x00000693.
Lemma F_44abc : fetch_word AsanUbsan.M.loaded_segments (0x44abc : word) = Some W_44abc.
Proof. vm_refl. Qed.
Lemma D_44abc : decode_any W_44abc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ac0 : bv 32 := 0x108180ef.
Lemma F_44ac0 : fetch_word AsanUbsan.M.loaded_segments (0x44ac0 : word) = Some W_44ac0.
Proof. vm_refl. Qed.
Lemma D_44ac0 : decode_any W_44ac0 = Some (Jal 1 98568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ac4 : bv 32 := 0x80040613.
Lemma F_44ac4 : fetch_word AsanUbsan.M.loaded_segments (0x44ac4 : word) = Some W_44ac4.
Proof. vm_refl. Qed.
Lemma D_44ac4 : decode_any W_44ac4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ac8 : bv 32 := 0xf8060613.
Lemma F_44ac8 : fetch_word AsanUbsan.M.loaded_segments (0x44ac8 : word) = Some W_44ac8.
Proof. vm_refl. Qed.
Lemma D_44ac8 : decode_any W_44ac8 = Some (OpImm ALU_ADD 12 12 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44acc : bv 32 := 0x00048513.
Lemma F_44acc : fetch_word AsanUbsan.M.loaded_segments (0x44acc : word) = Some W_44acc.
Proof. vm_refl. Qed.
Lemma D_44acc : decode_any W_44acc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ad0 : bv 32 := 0x000a0593.
Lemma F_44ad0 : fetch_word AsanUbsan.M.loaded_segments (0x44ad0 : word) = Some W_44ad0.
Proof. vm_refl. Qed.
Lemma D_44ad0 : decode_any W_44ad0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ad4 : bv 32 := 0x6ad140ef.
Lemma F_44ad4 : fetch_word AsanUbsan.M.loaded_segments (0x44ad4 : word) = Some W_44ad4.
Proof. vm_refl. Qed.
Lemma D_44ad4 : decode_any W_44ad4 = Some (Jal 1 85676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ad8 : bv 32 := 0x04000513.
Lemma F_44ad8 : fetch_word AsanUbsan.M.loaded_segments (0x44ad8 : word) = Some W_44ad8.
Proof. vm_refl. Qed.
Lemma D_44ad8 : decode_any W_44ad8 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44adc : bv 32 := 0xe0aae2e3.
Lemma F_44adc : fetch_word AsanUbsan.M.loaded_segments (0x44adc : word) = Some W_44adc.
Proof. vm_refl. Qed.
Lemma D_44adc : decode_any W_44adc = Some (Branch BC_LTU 21 10 7684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ae0 : bv 32 := 0x100a1e63.
Lemma F_44ae0 : fetch_word AsanUbsan.M.loaded_segments (0x44ae0 : word) = Some W_44ae0.
Proof. vm_refl. Qed.
Lemma D_44ae0 : decode_any W_44ae0 = Some (Branch BC_NE 20 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ae4 : bv 32 := 0xe35ff06f.
Lemma F_44ae4 : fetch_word AsanUbsan.M.loaded_segments (0x44ae4 : word) = Some W_44ae4.
Proof. vm_refl. Qed.
Lemma D_44ae4 : decode_any W_44ae4 = Some (Jal 0 2096692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ae8 : bv 32 := 0x00058683.
Lemma F_44ae8 : fetch_word AsanUbsan.M.loaded_segments (0x44ae8 : word) = Some W_44ae8.
Proof. vm_refl. Qed.
Lemma D_44ae8 : decode_any W_44ae8 = Some (Load SZ1 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44aec : bv 32 := 0x00767613.
Lemma F_44aec : fetch_word AsanUbsan.M.loaded_segments (0x44aec : word) = Some W_44aec.
Proof. vm_refl. Qed.
Lemma D_44aec : decode_any W_44aec = Some (OpImm ALU_AND 12 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44af0 : bv 32 := 0x00d03733.
Lemma F_44af0 : fetch_word AsanUbsan.M.loaded_segments (0x44af0 : word) = Some W_44af0.
Proof. vm_refl. Qed.
Lemma D_44af0 : decode_any W_44af0 = Some (Op ALU_SLTU 14 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44af4 : bv 32 := 0x00d62633.
Lemma F_44af4 : fetch_word AsanUbsan.M.loaded_segments (0x44af4 : word) = Some W_44af4.
Proof. vm_refl. Qed.
Lemma D_44af4 : decode_any W_44af4 = Some (Op ALU_SLT 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44af8 : bv 32 := 0x00164613.
Lemma F_44af8 : fetch_word AsanUbsan.M.loaded_segments (0x44af8 : word) = Some W_44af8.
Proof. vm_refl. Qed.
Lemma D_44af8 : decode_any W_44af8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44afc : bv 32 := 0x00c77633.
Lemma F_44afc : fetch_word AsanUbsan.M.loaded_segments (0x44afc : word) = Some W_44afc.
Proof. vm_refl. Qed.
Lemma D_44afc : decode_any W_44afc = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b00 : bv 32 := 0x00b57a63.
Lemma F_44b00 : fetch_word AsanUbsan.M.loaded_segments (0x44b00 : word) = Some W_44b00.
Proof. vm_refl. Qed.
Lemma D_44b00 : decode_any W_44b00 = Some (Branch BC_GEU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b04 : bv 32 := 0x00054683.
Lemma F_44b04 : fetch_word AsanUbsan.M.loaded_segments (0x44b04 : word) = Some W_44b04.
Proof. vm_refl. Qed.
Lemma D_44b04 : decode_any W_44b04 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b08 : bv 32 := 0x00150513.
Lemma F_44b08 : fetch_word AsanUbsan.M.loaded_segments (0x44b08 : word) = Some W_44b08.
Proof. vm_refl. Qed.
Lemma D_44b08 : decode_any W_44b08 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b0c : bv 32 := 0x00c6e633.
Lemma F_44b0c : fetch_word AsanUbsan.M.loaded_segments (0x44b0c : word) = Some W_44b0c.
Proof. vm_refl. Qed.
Lemma D_44b0c : decode_any W_44b0c = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b10 : bv 32 := 0xfeb51ae3.
Lemma F_44b10 : fetch_word AsanUbsan.M.loaded_segments (0x44b10 : word) = Some W_44b10.
Proof. vm_refl. Qed.
Lemma D_44b10 : decode_any W_44b10 = Some (Branch BC_NE 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b14 : bv 32 := 0x0ff67513.
Lemma F_44b14 : fetch_word AsanUbsan.M.loaded_segments (0x44b14 : word) = Some W_44b14.
Proof. vm_refl. Qed.
Lemma D_44b14 : decode_any W_44b14 = Some (OpImm ALU_AND 10 12 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b18 : bv 32 := 0xda0508e3.
Lemma F_44b18 : fetch_word AsanUbsan.M.loaded_segments (0x44b18 : word) = Some W_44b18.
Proof. vm_refl. Qed.
Lemma D_44b18 : decode_any W_44b18 = Some (Branch BC_EQ 10 0 7600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b1c : bv 32 := 0x00090513.
Lemma F_44b1c : fetch_word AsanUbsan.M.loaded_segments (0x44b1c : word) = Some W_44b1c.
Proof. vm_refl. Qed.
Lemma D_44b1c : decode_any W_44b1c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b20 : bv 32 := 0x000b0593.
Lemma F_44b20 : fetch_word AsanUbsan.M.loaded_segments (0x44b20 : word) = Some W_44b20.
Proof. vm_refl. Qed.
Lemma D_44b20 : decode_any W_44b20 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b24 : bv 32 := 0x679110ef.
Lemma F_44b24 : fetch_word AsanUbsan.M.loaded_segments (0x44b24 : word) = Some W_44b24.
Proof. vm_refl. Qed.
Lemma D_44b24 : decode_any W_44b24 = Some (Jal 1 73336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b28 : bv 32 := 0xda0500e3.
Lemma F_44b28 : fetch_word AsanUbsan.M.loaded_segments (0x44b28 : word) = Some W_44b28.
Proof. vm_refl. Qed.
Lemma D_44b28 : decode_any W_44b28 = Some (Branch BC_EQ 10 0 7584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b2c : bv 32 := 0x00050b93.
Lemma F_44b2c : fetch_word AsanUbsan.M.loaded_segments (0x44b2c : word) = Some W_44b2c.
Proof. vm_refl. Qed.
Lemma D_44b2c : decode_any W_44b2c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b30 : bv 32 := 0xfffd8517.
Lemma F_44b30 : fetch_word AsanUbsan.M.loaded_segments (0x44b30 : word) = Some W_44b30.
Proof. vm_refl. Qed.
Lemma D_44b30 : decode_any W_44b30 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b34 : bv 32 := 0x55250513.
Lemma F_44b34 : fetch_word AsanUbsan.M.loaded_segments (0x44b34 : word) = Some W_44b34.
Proof. vm_refl. Qed.
Lemma D_44b34 : decode_any W_44b34 = Some (OpImm ALU_ADD 10 10 1362, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b38 : bv 32 := 0x03c190ef.
Lemma F_44b38 : fetch_word AsanUbsan.M.loaded_segments (0x44b38 : word) = Some W_44b38.
Proof. vm_refl. Qed.
Lemma D_44b38 : decode_any W_44b38 = Some (Jal 1 102460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b3c : bv 32 := 0xd80516e3.
Lemma F_44b3c : fetch_word AsanUbsan.M.loaded_segments (0x44b3c : word) = Some W_44b3c.
Proof. vm_refl. Qed.
Lemma D_44b3c : decode_any W_44b3c = Some (Branch BC_NE 10 0 7564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b40 : bv 32 := 0x09c190ef.
Lemma F_44b40 : fetch_word AsanUbsan.M.loaded_segments (0x44b40 : word) = Some W_44b40.
Proof. vm_refl. Qed.
Lemma D_44b40 : decode_any W_44b40 = Some (Jal 1 102556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b44 : bv 32 := 0x14050263.
Lemma F_44b44 : fetch_word AsanUbsan.M.loaded_segments (0x44b44 : word) = Some W_44b44.
Proof. vm_refl. Qed.
Lemma D_44b44 : decode_any W_44b44 = Some (Branch BC_EQ 10 0 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b48 : bv 32 := 0x80040513.
Lemma F_44b48 : fetch_word AsanUbsan.M.loaded_segments (0x44b48 : word) = Some W_44b48.
Proof. vm_refl. Qed.
Lemma D_44b48 : decode_any W_44b48 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b4c : bv 32 := 0xf9050513.
Lemma F_44b4c : fetch_word AsanUbsan.M.loaded_segments (0x44b4c : word) = Some W_44b4c.
Proof. vm_refl. Qed.
Lemma D_44b4c : decode_any W_44b4c = Some (OpImm ALU_ADD 10 10 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b50 : bv 32 := 0x80040593.
Lemma F_44b50 : fetch_word AsanUbsan.M.loaded_segments (0x44b50 : word) = Some W_44b50.
Proof. vm_refl. Qed.
Lemma D_44b50 : decode_any W_44b50 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b54 : bv 32 := 0xf8058593.
Lemma F_44b54 : fetch_word AsanUbsan.M.loaded_segments (0x44b54 : word) = Some W_44b54.
Proof. vm_refl. Qed.
Lemma D_44b54 : decode_any W_44b54 = Some (OpImm ALU_ADD 11 11 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b58 : bv 32 := 0x7ff58593.
Lemma F_44b58 : fetch_word AsanUbsan.M.loaded_segments (0x44b58 : word) = Some W_44b58.
Proof. vm_refl. Qed.
Lemma D_44b58 : decode_any W_44b58 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b5c : bv 32 := 0x00001637.
Lemma F_44b5c : fetch_word AsanUbsan.M.loaded_segments (0x44b5c : word) = Some W_44b5c.
Proof. vm_refl. Qed.
Lemma D_44b5c : decode_any W_44b5c = Some (Lui 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b60 : bv 32 := 0x40c40633.
Lemma F_44b60 : fetch_word AsanUbsan.M.loaded_segments (0x44b60 : word) = Some W_44b60.
Proof. vm_refl. Qed.
Lemma D_44b60 : decode_any W_44b60 = Some (Op ALU_SUB 12 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b64 : bv 32 := 0x76b63c23.
Lemma F_44b64 : fetch_word AsanUbsan.M.loaded_segments (0x44b64 : word) = Some W_44b64.
Proof. vm_refl. Qed.
Lemma D_44b64 : decode_any W_44b64 = Some (Store SZ8 12 11 1912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b68 : bv 32 := 0x0005b4a3.
Lemma F_44b68 : fetch_word AsanUbsan.M.loaded_segments (0x44b68 : word) = Some W_44b68.
Proof. vm_refl. Qed.
Lemma D_44b68 : decode_any W_44b68 = Some (Store SZ8 11 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b6c : bv 32 := 0x00adb023.
Lemma F_44b6c : fetch_word AsanUbsan.M.loaded_segments (0x44b6c : word) = Some W_44b6c.
Proof. vm_refl. Qed.
Lemma D_44b6c : decode_any W_44b6c = Some (Store SZ8 27 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b70 : bv 32 := 0x000db423.
Lemma F_44b70 : fetch_word AsanUbsan.M.loaded_segments (0x44b70 : word) = Some W_44b70.
Proof. vm_refl. Qed.
Lemma D_44b70 : decode_any W_44b70 = Some (Store SZ8 27 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b74 : bv 32 := 0x305300ef.
Lemma F_44b74 : fetch_word AsanUbsan.M.loaded_segments (0x44b74 : word) = Some W_44b74.
Proof. vm_refl. Qed.
Lemma D_44b74 : decode_any W_44b74 = Some (Jal 1 199428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b78 : bv 32 := 0x00050593.
Lemma F_44b78 : fetch_word AsanUbsan.M.loaded_segments (0x44b78 : word) = Some W_44b78.
Proof. vm_refl. Qed.
Lemma D_44b78 : decode_any W_44b78 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b7c : bv 32 := 0x021c4703.
Lemma F_44b7c : fetch_word AsanUbsan.M.loaded_segments (0x44b7c : word) = Some W_44b7c.
Proof. vm_refl. Qed.
Lemma D_44b7c : decode_any W_44b7c = Some (Load SZ1 false 14 24 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b80 : bv 32 := 0x00001537.
Lemma F_44b80 : fetch_word AsanUbsan.M.loaded_segments (0x44b80 : word) = Some W_44b80.
Proof. vm_refl. Qed.
Lemma D_44b80 : decode_any W_44b80 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b84 : bv 32 := 0x40a40533.
Lemma F_44b84 : fetch_word AsanUbsan.M.loaded_segments (0x44b84 : word) = Some W_44b84.
Proof. vm_refl. Qed.
Lemma D_44b84 : decode_any W_44b84 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b88 : bv 32 := 0x77853503.
Lemma F_44b88 : fetch_word AsanUbsan.M.loaded_segments (0x44b88 : word) = Some W_44b88.
Proof. vm_refl. Qed.
Lemma D_44b88 : decode_any W_44b88 = Some (Load SZ8 true 10 10 1912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b8c : bv 32 := 0x008534a3.
Lemma F_44b8c : fetch_word AsanUbsan.M.loaded_segments (0x44b8c : word) = Some W_44b8c.
Proof. vm_refl. Qed.
Lemma D_44b8c : decode_any W_44b8c = Some (Store SZ8 10 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b90 : bv 32 := 0x80040513.
Lemma F_44b90 : fetch_word AsanUbsan.M.loaded_segments (0x44b90 : word) = Some W_44b90.
Proof. vm_refl. Qed.
Lemma D_44b90 : decode_any W_44b90 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b94 : bv 32 := 0xf8050513.
Lemma F_44b94 : fetch_word AsanUbsan.M.loaded_segments (0x44b94 : word) = Some W_44b94.
Proof. vm_refl. Qed.
Lemma D_44b94 : decode_any W_44b94 = Some (OpImm ALU_ADD 10 10 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b98 : bv 32 := 0x0ff00793.
Lemma F_44b98 : fetch_word AsanUbsan.M.loaded_segments (0x44b98 : word) = Some W_44b98.
Proof. vm_refl. Qed.
Lemma D_44b98 : decode_any W_44b98 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44b9c : bv 32 := 0x00040613.
Lemma F_44b9c : fetch_word AsanUbsan.M.loaded_segments (0x44b9c : word) = Some W_44b9c.
Proof. vm_refl. Qed.
Lemma D_44b9c : decode_any W_44b9c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ba0 : bv 32 := 0x00000693.
Lemma F_44ba0 : fetch_word AsanUbsan.M.loaded_segments (0x44ba0 : word) = Some W_44ba0.
Proof. vm_refl. Qed.
Lemma D_44ba0 : decode_any W_44ba0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ba4 : bv 32 := 0x024180ef.
Lemma F_44ba4 : fetch_word AsanUbsan.M.loaded_segments (0x44ba4 : word) = Some W_44ba4.
Proof. vm_refl. Qed.
Lemma D_44ba4 : decode_any W_44ba4 = Some (Jal 1 98340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44ba8 : bv 32 := 0x80040513.
Lemma F_44ba8 : fetch_word AsanUbsan.M.loaded_segments (0x44ba8 : word) = Some W_44ba8.
Proof. vm_refl. Qed.
Lemma D_44ba8 : decode_any W_44ba8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bac : bv 32 := 0xf8050513.
Lemma F_44bac : fetch_word AsanUbsan.M.loaded_segments (0x44bac : word) = Some W_44bac.
Proof. vm_refl. Qed.
Lemma D_44bac : decode_any W_44bac = Some (OpImm ALU_ADD 10 10 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bb0 : bv 32 := 0x334190ef.
Lemma F_44bb0 : fetch_word AsanUbsan.M.loaded_segments (0x44bb0 : word) = Some W_44bb0.
Proof. vm_refl. Qed.
Lemma D_44bb0 : decode_any W_44bb0 = Some (Jal 1 103220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bb4 : bv 32 := 0x000015b7.
Lemma F_44bb4 : fetch_word AsanUbsan.M.loaded_segments (0x44bb4 : word) = Some W_44bb4.
Proof. vm_refl. Qed.
Lemma D_44bb4 : decode_any W_44bb4 = Some (Lui 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bb8 : bv 32 := 0x40b405b3.
Lemma F_44bb8 : fetch_word AsanUbsan.M.loaded_segments (0x44bb8 : word) = Some W_44bb8.
Proof. vm_refl. Qed.
Lemma D_44bb8 : decode_any W_44bb8 = Some (Op ALU_SUB 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bbc : bv 32 := 0x7685bc23.
Lemma F_44bbc : fetch_word AsanUbsan.M.loaded_segments (0x44bbc : word) = Some W_44bbc.
Proof. vm_refl. Qed.
Lemma D_44bbc : decode_any W_44bbc = Some (Store SZ8 11 8 1912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bc0 : bv 32 := 0xd00514e3.
Lemma F_44bc0 : fetch_word AsanUbsan.M.loaded_segments (0x44bc0 : word) = Some W_44bc0.
Proof. vm_refl. Qed.
Lemma D_44bc0 : decode_any W_44bc0 = Some (Branch BC_NE 10 0 7432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bc4 : bv 32 := 0x0d00006f.
Lemma F_44bc4 : fetch_word AsanUbsan.M.loaded_segments (0x44bc4 : word) = Some W_44bc4.
Proof. vm_refl. Qed.
Lemma D_44bc4 : decode_any W_44bc4 = Some (Jal 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bc8 : bv 32 := 0x00058603.
Lemma F_44bc8 : fetch_word AsanUbsan.M.loaded_segments (0x44bc8 : word) = Some W_44bc8.
Proof. vm_refl. Qed.
Lemma D_44bc8 : decode_any W_44bc8 = Some (Load SZ1 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bcc : bv 32 := 0x007af693.
Lemma F_44bcc : fetch_word AsanUbsan.M.loaded_segments (0x44bcc : word) = Some W_44bcc.
Proof. vm_refl. Qed.
Lemma D_44bcc : decode_any W_44bcc = Some (OpImm ALU_AND 13 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bd0 : bv 32 := 0x00c03733.
Lemma F_44bd0 : fetch_word AsanUbsan.M.loaded_segments (0x44bd0 : word) = Some W_44bd0.
Proof. vm_refl. Qed.
Lemma D_44bd0 : decode_any W_44bd0 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bd4 : bv 32 := 0x00c6a633.
Lemma F_44bd4 : fetch_word AsanUbsan.M.loaded_segments (0x44bd4 : word) = Some W_44bd4.
Proof. vm_refl. Qed.
Lemma D_44bd4 : decode_any W_44bd4 = Some (Op ALU_SLT 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bd8 : bv 32 := 0x00164613.
Lemma F_44bd8 : fetch_word AsanUbsan.M.loaded_segments (0x44bd8 : word) = Some W_44bd8.
Proof. vm_refl. Qed.
Lemma D_44bd8 : decode_any W_44bd8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bdc : bv 32 := 0x00c77633.
Lemma F_44bdc : fetch_word AsanUbsan.M.loaded_segments (0x44bdc : word) = Some W_44bdc.
Proof. vm_refl. Qed.
Lemma D_44bdc : decode_any W_44bdc = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44be0 : bv 32 := 0x00b57a63.
Lemma F_44be0 : fetch_word AsanUbsan.M.loaded_segments (0x44be0 : word) = Some W_44be0.
Proof. vm_refl. Qed.
Lemma D_44be0 : decode_any W_44be0 = Some (Branch BC_GEU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44be4 : bv 32 := 0x00054683.
Lemma F_44be4 : fetch_word AsanUbsan.M.loaded_segments (0x44be4 : word) = Some W_44be4.
Proof. vm_refl. Qed.
Lemma D_44be4 : decode_any W_44be4 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44be8 : bv 32 := 0x00150513.
Lemma F_44be8 : fetch_word AsanUbsan.M.loaded_segments (0x44be8 : word) = Some W_44be8.
Proof. vm_refl. Qed.
Lemma D_44be8 : decode_any W_44be8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bec : bv 32 := 0x00c6e633.
Lemma F_44bec : fetch_word AsanUbsan.M.loaded_segments (0x44bec : word) = Some W_44bec.
Proof. vm_refl. Qed.
Lemma D_44bec : decode_any W_44bec = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bf0 : bv 32 := 0xfeb51ae3.
Lemma F_44bf0 : fetch_word AsanUbsan.M.loaded_segments (0x44bf0 : word) = Some W_44bf0.
Proof. vm_refl. Qed.
Lemma D_44bf0 : decode_any W_44bf0 = Some (Branch BC_NE 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bf4 : bv 32 := 0x0ff67513.
Lemma F_44bf4 : fetch_word AsanUbsan.M.loaded_segments (0x44bf4 : word) = Some W_44bf4.
Proof. vm_refl. Qed.
Lemma D_44bf4 : decode_any W_44bf4 = Some (OpImm ALU_AND 10 12 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bf8 : bv 32 := 0xd20500e3.
Lemma F_44bf8 : fetch_word AsanUbsan.M.loaded_segments (0x44bf8 : word) = Some W_44bf8.
Proof. vm_refl. Qed.
Lemma D_44bf8 : decode_any W_44bf8 = Some (Branch BC_EQ 10 0 7456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44bfc : bv 32 := 0x00048513.
Lemma F_44bfc : fetch_word AsanUbsan.M.loaded_segments (0x44bfc : word) = Some W_44bfc.
Proof. vm_refl. Qed.
Lemma D_44bfc : decode_any W_44bfc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44c00 : bv 32 := 0x000a0593.
Lemma F_44c00 : fetch_word AsanUbsan.M.loaded_segments (0x44c00 : word) = Some W_44c00.
Proof. vm_refl. Qed.
Lemma D_44c00 : decode_any W_44c00 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44c04 : bv 32 := 0x599110ef.
Lemma F_44c04 : fetch_word AsanUbsan.M.loaded_segments (0x44c04 : word) = Some W_44c04.
Proof. vm_refl. Qed.
Lemma D_44c04 : decode_any W_44c04 = Some (Jal 1 73112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_44c08 : bv 32 := 0xd00508e3.
Lemma F_44c08 : fetch_word AsanUbsan.M.loaded_segments (0x44c08 : word) = Some W_44c08.
Proof. vm_refl. Qed.
Lemma D_44c08 : decode_any W_44c08 = Some (Branch BC_EQ 10 0 7440, 4%Z).
Proof. vm_refl. Qed.
