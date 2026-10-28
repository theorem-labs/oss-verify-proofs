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
Definition W_5d814 : bv 32 := 0xfe010113.
Lemma F_5d814 : fetch_word AsanUbsan.M.loaded_segments (0x5dc2c : word) = Some W_5d814.
Proof. vm_refl. Qed.
Lemma D_5d814 : decode_any W_5d814 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d818 : bv 32 := 0x00113c23.
Lemma F_5d818 : fetch_word AsanUbsan.M.loaded_segments (0x5dc30 : word) = Some W_5d818.
Proof. vm_refl. Qed.
Lemma D_5d818 : decode_any W_5d818 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d81c : bv 32 := 0x00813823.
Lemma F_5d81c : fetch_word AsanUbsan.M.loaded_segments (0x5dc34 : word) = Some W_5d81c.
Proof. vm_refl. Qed.
Lemma D_5d81c : decode_any W_5d81c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d820 : bv 32 := 0x00913423.
Lemma F_5d820 : fetch_word AsanUbsan.M.loaded_segments (0x5dc38 : word) = Some W_5d820.
Proof. vm_refl. Qed.
Lemma D_5d820 : decode_any W_5d820 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d824 : bv 32 := 0x01213023.
Lemma F_5d824 : fetch_word AsanUbsan.M.loaded_segments (0x5dc3c : word) = Some W_5d824.
Proof. vm_refl. Qed.
Lemma D_5d824 : decode_any W_5d824 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d828 : bv 32 := 0x02010413.
Lemma F_5d828 : fetch_word AsanUbsan.M.loaded_segments (0x5dc40 : word) = Some W_5d828.
Proof. vm_refl. Qed.
Lemma D_5d828 : decode_any W_5d828 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d82c : bv 32 := 0x000da517.
Lemma F_5d82c : fetch_word AsanUbsan.M.loaded_segments (0x5dc44 : word) = Some W_5d82c.
Proof. vm_refl. Qed.
Lemma D_5d82c : decode_any W_5d82c = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d830 : bv 32 := 0x67450513.
Lemma F_5d830 : fetch_word AsanUbsan.M.loaded_segments (0x5dc48 : word) = Some W_5d830.
Proof. vm_refl. Qed.
Lemma D_5d830 : decode_any W_5d830 = Some (OpImm ALU_ADD 10 10 1652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d834 : bv 32 := 0x7a4050ef.
Lemma F_5d834 : fetch_word AsanUbsan.M.loaded_segments (0x5dc4c : word) = Some W_5d834.
Proof. vm_refl. Qed.
Lemma D_5d834 : decode_any W_5d834 = Some (Jal 1 22436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d838 : bv 32 := 0x00053483.
Lemma F_5d838 : fetch_word AsanUbsan.M.loaded_segments (0x5dc50 : word) = Some W_5d838.
Proof. vm_refl. Qed.
Lemma D_5d838 : decode_any W_5d838 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d83c : bv 32 := 0x08048063.
Lemma F_5d83c : fetch_word AsanUbsan.M.loaded_segments (0x5dc54 : word) = Some W_5d83c.
Proof. vm_refl. Qed.
Lemma D_5d83c : decode_any W_5d83c = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d840 : bv 32 := 0x0604c503.
Lemma F_5d840 : fetch_word AsanUbsan.M.loaded_segments (0x5dc58 : word) = Some W_5d840.
Proof. vm_refl. Qed.
Lemma D_5d840 : decode_any W_5d840 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d844 : bv 32 := 0x0584b903.
Lemma F_5d844 : fetch_word AsanUbsan.M.loaded_segments (0x5dc5c : word) = Some W_5d844.
Proof. vm_refl. Qed.
Lemma D_5d844 : decode_any W_5d844 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d848 : bv 32 := 0x00050863.
Lemma F_5d848 : fetch_word AsanUbsan.M.loaded_segments (0x5dc60 : word) = Some W_5d848.
Proof. vm_refl. Qed.
Lemma D_5d848 : decode_any W_5d848 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d84c : bv 32 := 0x00048513.
Lemma F_5d84c : fetch_word AsanUbsan.M.loaded_segments (0x5dc64 : word) = Some W_5d84c.
Proof. vm_refl. Qed.
Lemma D_5d84c : decode_any W_5d84c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d850 : bv 32 := 0x00040593.
Lemma F_5d850 : fetch_word AsanUbsan.M.loaded_segments (0x5dc68 : word) = Some W_5d850.
Proof. vm_refl. Qed.
Lemma D_5d850 : decode_any W_5d850 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d854 : bv 32 := 0xb75ff0ef.
Lemma F_5d854 : fetch_word AsanUbsan.M.loaded_segments (0x5dc6c : word) = Some W_5d854.
Proof. vm_refl. Qed.
Lemma D_5d854 : decode_any W_5d854 = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d858 : bv 32 := 0xffa90593.
Lemma F_5d858 : fetch_word AsanUbsan.M.loaded_segments (0x5dc70 : word) = Some W_5d858.
Proof. vm_refl. Qed.
Lemma D_5d858 : decode_any W_5d858 = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d85c : bv 32 := 0x00100513.
Lemma F_5d85c : fetch_word AsanUbsan.M.loaded_segments (0x5dc74 : word) = Some W_5d85c.
Proof. vm_refl. Qed.
Lemma D_5d85c : decode_any W_5d85c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d860 : bv 32 := 0x00b51533.
Lemma F_5d860 : fetch_word AsanUbsan.M.loaded_segments (0x5dc78 : word) = Some W_5d860.
Proof. vm_refl. Qed.
Lemma D_5d860 : decode_any W_5d860 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d864 : bv 32 := 0x0005061b.
Lemma F_5d864 : fetch_word AsanUbsan.M.loaded_segments (0x5dc7c : word) = Some W_5d864.
Proof. vm_refl. Qed.
Lemma D_5d864 : decode_any W_5d864 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d868 : bv 32 := 0x06c05a63.
Lemma F_5d868 : fetch_word AsanUbsan.M.loaded_segments (0x5dc80 : word) = Some W_5d868.
Proof. vm_refl. Qed.
Lemma D_5d868 : decode_any W_5d868 = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d86c : bv 32 := 0x000016b7.
Lemma F_5d86c : fetch_word AsanUbsan.M.loaded_segments (0x5dc84 : word) = Some W_5d86c.
Proof. vm_refl. Qed.
Lemma D_5d86c : decode_any W_5d86c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d870 : bv 32 := 0xfff00713.
Lemma F_5d870 : fetch_word AsanUbsan.M.loaded_segments (0x5dc88 : word) = Some W_5d870.
Proof. vm_refl. Qed.
Lemma D_5d870 : decode_any W_5d870 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d874 : bv 32 := 0x0004b603.
Lemma F_5d874 : fetch_word AsanUbsan.M.loaded_segments (0x5dc8c : word) = Some W_5d874.
Proof. vm_refl. Qed.
Lemma D_5d874 : decode_any W_5d874 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d878 : bv 32 := 0x00b71733.
Lemma F_5d878 : fetch_word AsanUbsan.M.loaded_segments (0x5dc90 : word) = Some W_5d878.
Proof. vm_refl. Qed.
Lemma D_5d878 : decode_any W_5d878 = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d87c : bv 32 := 0xfff50793.
Lemma F_5d87c : fetch_word AsanUbsan.M.loaded_segments (0x5dc94 : word) = Some W_5d87c.
Proof. vm_refl. Qed.
Lemma D_5d87c : decode_any W_5d87c = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d880 : bv 32 := 0x00d485b3.
Lemma F_5d880 : fetch_word AsanUbsan.M.loaded_segments (0x5dc98 : word) = Some W_5d880.
Proof. vm_refl. Qed.
Lemma D_5d880 : decode_any W_5d880 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d884 : bv 32 := 0xfff74693.
Lemma F_5d884 : fetch_word AsanUbsan.M.loaded_segments (0x5dc9c : word) = Some W_5d884.
Proof. vm_refl. Qed.
Lemma D_5d884 : decode_any W_5d884 = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d888 : bv 32 := 0x02079793.
Lemma F_5d888 : fetch_word AsanUbsan.M.loaded_segments (0x5dca0 : word) = Some W_5d888.
Proof. vm_refl. Qed.
Lemma D_5d888 : decode_any W_5d888 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d88c : bv 32 := 0x0207d793.
Lemma F_5d88c : fetch_word AsanUbsan.M.loaded_segments (0x5dca4 : word) = Some W_5d88c.
Proof. vm_refl. Qed.
Lemma D_5d88c : decode_any W_5d88c = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d890 : bv 32 := 0x00f60733.
Lemma F_5d890 : fetch_word AsanUbsan.M.loaded_segments (0x5dca8 : word) = Some W_5d890.
Proof. vm_refl. Qed.
Lemma D_5d890 : decode_any W_5d890 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d894 : bv 32 := 0x00170713.
Lemma F_5d894 : fetch_word AsanUbsan.M.loaded_segments (0x5dcac : word) = Some W_5d894.
Proof. vm_refl. Qed.
Lemma D_5d894 : decode_any W_5d894 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d898 : bv 32 := 0x00d67833.
Lemma F_5d898 : fetch_word AsanUbsan.M.loaded_segments (0x5dcb0 : word) = Some W_5d898.
Proof. vm_refl. Qed.
Lemma D_5d898 : decode_any W_5d898 = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d89c : bv 32 := 0x010587b3.
Lemma F_5d89c : fetch_word AsanUbsan.M.loaded_segments (0x5dcb4 : word) = Some W_5d89c.
Proof. vm_refl. Qed.
Lemma D_5d89c : decode_any W_5d89c = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8a0 : bv 32 := 0x0007c883.
Lemma F_5d8a0 : fetch_word AsanUbsan.M.loaded_segments (0x5dcb8 : word) = Some W_5d8a0.
Proof. vm_refl. Qed.
Lemma D_5d8a0 : decode_any W_5d8a0 = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8a4 : bv 32 := 0x06088663.
Lemma F_5d8a4 : fetch_word AsanUbsan.M.loaded_segments (0x5dcbc : word) = Some W_5d8a4.
Proof. vm_refl. Qed.
Lemma D_5d8a4 : decode_any W_5d8a4 = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8a8 : bv 32 := 0xfff5051b.
Lemma F_5d8a8 : fetch_word AsanUbsan.M.loaded_segments (0x5dcc0 : word) = Some W_5d8a8.
Proof. vm_refl. Qed.
Lemma D_5d8a8 : decode_any W_5d8a8 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8ac : bv 32 := 0x00160613.
Lemma F_5d8ac : fetch_word AsanUbsan.M.loaded_segments (0x5dcc4 : word) = Some W_5d8ac.
Proof. vm_refl. Qed.
Lemma D_5d8ac : decode_any W_5d8ac = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8b0 : bv 32 := 0xfe0514e3.
Lemma F_5d8b0 : fetch_word AsanUbsan.M.loaded_segments (0x5dcc8 : word) = Some W_5d8b0.
Proof. vm_refl. Qed.
Lemma D_5d8b0 : decode_any W_5d8b0 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8b4 : bv 32 := 0x00e4b023.
Lemma F_5d8b4 : fetch_word AsanUbsan.M.loaded_segments (0x5dccc : word) = Some W_5d8b4.
Proof. vm_refl. Qed.
Lemma D_5d8b4 : decode_any W_5d8b4 = Some (Store SZ8 9 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8b8 : bv 32 := 0x0400006f.
Lemma F_5d8b8 : fetch_word AsanUbsan.M.loaded_segments (0x5dcd0 : word) = Some W_5d8b8.
Proof. vm_refl. Qed.
Lemma D_5d8b8 : decode_any W_5d8b8 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8bc : bv 32 := 0x000da517.
Lemma F_5d8bc : fetch_word AsanUbsan.M.loaded_segments (0x5dcd4 : word) = Some W_5d8bc.
Proof. vm_refl. Qed.
Lemma D_5d8bc : decode_any W_5d8bc = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8c0 : bv 32 := 0x84453503.
Lemma F_5d8c0 : fetch_word AsanUbsan.M.loaded_segments (0x5dcd8 : word) = Some W_5d8c0.
Proof. vm_refl. Qed.
Lemma D_5d8c0 : decode_any W_5d8c0 = Some (Load SZ8 true 10 10 2116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8c4 : bv 32 := 0x00052503.
Lemma F_5d8c4 : fetch_word AsanUbsan.M.loaded_segments (0x5dcdc : word) = Some W_5d8c4.
Proof. vm_refl. Qed.
Lemma D_5d8c4 : decode_any W_5d8c4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8c8 : bv 32 := 0x02050863.
Lemma F_5d8c8 : fetch_word AsanUbsan.M.loaded_segments (0x5dce0 : word) = Some W_5d8c8.
Proof. vm_refl. Qed.
Lemma D_5d8c8 : decode_any W_5d8c8 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8cc : bv 32 := 0x401250ef.
Lemma F_5d8cc : fetch_word AsanUbsan.M.loaded_segments (0x5dce4 : word) = Some W_5d8cc.
Proof. vm_refl. Qed.
Lemma D_5d8cc : decode_any W_5d8cc = Some (Jal 1 154624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d0 : bv 32 := 0x02050463.
Lemma F_5d8d0 : fetch_word AsanUbsan.M.loaded_segments (0x5dce8 : word) = Some W_5d8d0.
Proof. vm_refl. Qed.
Lemma D_5d8d0 : decode_any W_5d8d0 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d4 : bv 32 := 0x02850583.
Lemma F_5d8d4 : fetch_word AsanUbsan.M.loaded_segments (0x5dcec : word) = Some W_5d8d4.
Proof. vm_refl. Qed.
Lemma D_5d8d4 : decode_any W_5d8d4 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d8 : bv 32 := 0x08058a63.
Lemma F_5d8d8 : fetch_word AsanUbsan.M.loaded_segments (0x5dcf0 : word) = Some W_5d8d8.
Proof. vm_refl. Qed.
Lemma D_5d8d8 : decode_any W_5d8d8 = Some (Branch BC_EQ 11 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8dc : bv 32 := 0x00000513.
Lemma F_5d8dc : fetch_word AsanUbsan.M.loaded_segments (0x5dcf4 : word) = Some W_5d8dc.
Proof. vm_refl. Qed.
Lemma D_5d8dc : decode_any W_5d8dc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8e0 : bv 32 := 0x01813083.
Lemma F_5d8e0 : fetch_word AsanUbsan.M.loaded_segments (0x5dcf8 : word) = Some W_5d8e0.
Proof. vm_refl. Qed.
Lemma D_5d8e0 : decode_any W_5d8e0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8e4 : bv 32 := 0x01013403.
Lemma F_5d8e4 : fetch_word AsanUbsan.M.loaded_segments (0x5dcfc : word) = Some W_5d8e4.
Proof. vm_refl. Qed.
Lemma D_5d8e4 : decode_any W_5d8e4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8e8 : bv 32 := 0x00813483.
Lemma F_5d8e8 : fetch_word AsanUbsan.M.loaded_segments (0x5dd00 : word) = Some W_5d8e8.
Proof. vm_refl. Qed.
Lemma D_5d8e8 : decode_any W_5d8e8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8ec : bv 32 := 0x00013903.
Lemma F_5d8ec : fetch_word AsanUbsan.M.loaded_segments (0x5dd04 : word) = Some W_5d8ec.
Proof. vm_refl. Qed.
Lemma D_5d8ec : decode_any W_5d8ec = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8f0 : bv 32 := 0x02010113.
Lemma F_5d8f0 : fetch_word AsanUbsan.M.loaded_segments (0x5dd08 : word) = Some W_5d8f0.
Proof. vm_refl. Qed.
Lemma D_5d8f0 : decode_any W_5d8f0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8f4 : bv 32 := 0x00008067.
Lemma F_5d8f4 : fetch_word AsanUbsan.M.loaded_segments (0x5dd0c : word) = Some W_5d8f4.
Proof. vm_refl. Qed.
Lemma D_5d8f4 : decode_any W_5d8f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8f8 : bv 32 := 0x01813083.
Lemma F_5d8f8 : fetch_word AsanUbsan.M.loaded_segments (0x5dd10 : word) = Some W_5d8f8.
Proof. vm_refl. Qed.
Lemma D_5d8f8 : decode_any W_5d8f8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8fc : bv 32 := 0x01013403.
Lemma F_5d8fc : fetch_word AsanUbsan.M.loaded_segments (0x5dd14 : word) = Some W_5d8fc.
Proof. vm_refl. Qed.
Lemma D_5d8fc : decode_any W_5d8fc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d900 : bv 32 := 0x00813483.
Lemma F_5d900 : fetch_word AsanUbsan.M.loaded_segments (0x5dd18 : word) = Some W_5d900.
Proof. vm_refl. Qed.
Lemma D_5d900 : decode_any W_5d900 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d904 : bv 32 := 0x00013903.
Lemma F_5d904 : fetch_word AsanUbsan.M.loaded_segments (0x5dd1c : word) = Some W_5d904.
Proof. vm_refl. Qed.
Lemma D_5d904 : decode_any W_5d904 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d908 : bv 32 := 0x02010113.
Lemma F_5d908 : fetch_word AsanUbsan.M.loaded_segments (0x5dd20 : word) = Some W_5d908.
Proof. vm_refl. Qed.
Lemma D_5d908 : decode_any W_5d908 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d90c : bv 32 := 0x00008067.
Lemma F_5d90c : fetch_word AsanUbsan.M.loaded_segments (0x5dd24 : word) = Some W_5d90c.
Proof. vm_refl. Qed.
Lemma D_5d90c : decode_any W_5d90c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d910 : bv 32 := 0x00160613.
Lemma F_5d910 : fetch_word AsanUbsan.M.loaded_segments (0x5dd28 : word) = Some W_5d910.
Proof. vm_refl. Qed.
Lemma D_5d910 : decode_any W_5d910 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d914 : bv 32 := 0x00100513.
Lemma F_5d914 : fetch_word AsanUbsan.M.loaded_segments (0x5dd2c : word) = Some W_5d914.
Proof. vm_refl. Qed.
Lemma D_5d914 : decode_any W_5d914 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d918 : bv 32 := 0xffb90913.
Lemma F_5d918 : fetch_word AsanUbsan.M.loaded_segments (0x5dd30 : word) = Some W_5d918.
Proof. vm_refl. Qed.
Lemma D_5d918 : decode_any W_5d918 = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d91c : bv 32 := 0x00681813.
Lemma F_5d91c : fetch_word AsanUbsan.M.loaded_segments (0x5dd34 : word) = Some W_5d91c.
Proof. vm_refl. Qed.
Lemma D_5d91c : decode_any W_5d91c = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d920 : bv 32 := 0x00c4b023.
Lemma F_5d920 : fetch_word AsanUbsan.M.loaded_segments (0x5dd38 : word) = Some W_5d920.
Proof. vm_refl. Qed.
Lemma D_5d920 : decode_any W_5d920 = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d924 : bv 32 := 0x00a78023.
Lemma F_5d924 : fetch_word AsanUbsan.M.loaded_segments (0x5dd3c : word) = Some W_5d924.
Proof. vm_refl. Qed.
Lemma D_5d924 : decode_any W_5d924 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d928 : bv 32 := 0x01251533.
Lemma F_5d928 : fetch_word AsanUbsan.M.loaded_segments (0x5dd40 : word) = Some W_5d928.
Proof. vm_refl. Qed.
Lemma D_5d928 : decode_any W_5d928 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d92c : bv 32 := 0x00a58533.
Lemma F_5d92c : fetch_word AsanUbsan.M.loaded_segments (0x5dd44 : word) = Some W_5d92c.
Proof. vm_refl. Qed.
Lemma D_5d92c : decode_any W_5d92c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d930 : bv 32 := 0x010504b3.
Lemma F_5d930 : fetch_word AsanUbsan.M.loaded_segments (0x5dd48 : word) = Some W_5d930.
Proof. vm_refl. Qed.
Lemma D_5d930 : decode_any W_5d930 = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d934 : bv 32 := 0x0084bc23.
Lemma F_5d934 : fetch_word AsanUbsan.M.loaded_segments (0x5dd4c : word) = Some W_5d934.
Proof. vm_refl. Qed.
Lemma D_5d934 : decode_any W_5d934 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d938 : bv 32 := 0x02f4bc23.
Lemma F_5d938 : fetch_word AsanUbsan.M.loaded_segments (0x5dd50 : word) = Some W_5d938.
Proof. vm_refl. Qed.
Lemma D_5d938 : decode_any W_5d938 = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d93c : bv 32 := 0x00048513.
Lemma F_5d93c : fetch_word AsanUbsan.M.loaded_segments (0x5dd54 : word) = Some W_5d93c.
Proof. vm_refl. Qed.
Lemma D_5d93c : decode_any W_5d93c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d940 : bv 32 := 0x644000ef.
Lemma F_5d940 : fetch_word AsanUbsan.M.loaded_segments (0x5dd58 : word) = Some W_5d940.
Proof. vm_refl. Qed.
Lemma D_5d940 : decode_any W_5d940 = Some (Jal 1 1604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d944 : bv 32 := 0x00050593.
Lemma F_5d944 : fetch_word AsanUbsan.M.loaded_segments (0x5dd5c : word) = Some W_5d944.
Proof. vm_refl. Qed.
Lemma D_5d944 : decode_any W_5d944 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d948 : bv 32 := 0x00048513.
Lemma F_5d948 : fetch_word AsanUbsan.M.loaded_segments (0x5dd60 : word) = Some W_5d948.
Proof. vm_refl. Qed.
Lemma D_5d948 : decode_any W_5d948 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d94c : bv 32 := 0x00000613.
Lemma F_5d94c : fetch_word AsanUbsan.M.loaded_segments (0x5dd64 : word) = Some W_5d94c.
Proof. vm_refl. Qed.
Lemma D_5d94c : decode_any W_5d94c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d950 : bv 32 := 0x0005b023.
Lemma F_5d950 : fetch_word AsanUbsan.M.loaded_segments (0x5dd68 : word) = Some W_5d950.
Proof. vm_refl. Qed.
Lemma D_5d950 : decode_any W_5d950 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d954 : bv 32 := 0x01813083.
Lemma F_5d954 : fetch_word AsanUbsan.M.loaded_segments (0x5dd6c : word) = Some W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : decode_any W_5d954 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d958 : bv 32 := 0x01013403.
Lemma F_5d958 : fetch_word AsanUbsan.M.loaded_segments (0x5dd70 : word) = Some W_5d958.
Proof. vm_refl. Qed.
Lemma D_5d958 : decode_any W_5d958 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d95c : bv 32 := 0x00813483.
Lemma F_5d95c : fetch_word AsanUbsan.M.loaded_segments (0x5dd74 : word) = Some W_5d95c.
Proof. vm_refl. Qed.
Lemma D_5d95c : decode_any W_5d95c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d960 : bv 32 := 0x00013903.
Lemma F_5d960 : fetch_word AsanUbsan.M.loaded_segments (0x5dd78 : word) = Some W_5d960.
Proof. vm_refl. Qed.
Lemma D_5d960 : decode_any W_5d960 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d964 : bv 32 := 0x02010113.
Lemma F_5d964 : fetch_word AsanUbsan.M.loaded_segments (0x5dd7c : word) = Some W_5d964.
Proof. vm_refl. Qed.
Lemma D_5d964 : decode_any W_5d964 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d968 : bv 32 := 0x00008067.
Lemma F_5d968 : fetch_word AsanUbsan.M.loaded_segments (0x5dd80 : word) = Some W_5d968.
Proof. vm_refl. Qed.
Lemma D_5d968 : decode_any W_5d968 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d96c : bv 32 := 0x04853483.
Lemma F_5d96c : fetch_word AsanUbsan.M.loaded_segments (0x5dd84 : word) = Some W_5d96c.
Proof. vm_refl. Qed.
Lemma D_5d96c : decode_any W_5d96c = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d970 : bv 32 := 0x00100593.
Lemma F_5d970 : fetch_word AsanUbsan.M.loaded_segments (0x5dd88 : word) = Some W_5d970.
Proof. vm_refl. Qed.
Lemma D_5d970 : decode_any W_5d970 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d974 : bv 32 := 0x0095e663.
Lemma F_5d974 : fetch_word AsanUbsan.M.loaded_segments (0x5dd8c : word) = Some W_5d974.
Proof. vm_refl. Qed.
Lemma D_5d974 : decode_any W_5d974 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d978 : bv 32 := 0x5c9250ef.
Lemma F_5d978 : fetch_word AsanUbsan.M.loaded_segments (0x5dd90 : word) = Some W_5d978.
Proof. vm_refl. Qed.
Lemma D_5d978 : decode_any W_5d978 = Some (Jal 1 155080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d97c : bv 32 := 0x00050493.
Lemma F_5d97c : fetch_word AsanUbsan.M.loaded_segments (0x5dd94 : word) = Some W_5d97c.
Proof. vm_refl. Qed.
Lemma D_5d97c : decode_any W_5d97c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d980 : bv 32 := 0xec0490e3.
Lemma F_5d980 : fetch_word AsanUbsan.M.loaded_segments (0x5dd98 : word) = Some W_5d980.
Proof. vm_refl. Qed.
Lemma D_5d980 : decode_any W_5d980 = Some (Branch BC_NE 9 0 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d984 : bv 32 := 0xf59ff06f.
Lemma F_5d984 : fetch_word AsanUbsan.M.loaded_segments (0x5dd9c : word) = Some W_5d984.
Proof. vm_refl. Qed.
Lemma D_5d984 : decode_any W_5d984 = Some (Jal 0 2096984, 4%Z).
Proof. vm_refl. Qed.
