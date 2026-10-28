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

Definition W_3aa5c : bv 32 := 0xfd010113.
Lemma F_3aa5c : fetch_word Ubsan.M.loaded_segments (0x3aa5c : word) = Some W_3aa5c.
Proof. vm_refl. Qed.
Lemma D_3aa5c : decode_any W_3aa5c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa60 : bv 32 := 0x02113423.
Lemma F_3aa60 : fetch_word Ubsan.M.loaded_segments (0x3aa60 : word) = Some W_3aa60.
Proof. vm_refl. Qed.
Lemma D_3aa60 : decode_any W_3aa60 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa64 : bv 32 := 0x02813023.
Lemma F_3aa64 : fetch_word Ubsan.M.loaded_segments (0x3aa64 : word) = Some W_3aa64.
Proof. vm_refl. Qed.
Lemma D_3aa64 : decode_any W_3aa64 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa68 : bv 32 := 0x00913c23.
Lemma F_3aa68 : fetch_word Ubsan.M.loaded_segments (0x3aa68 : word) = Some W_3aa68.
Proof. vm_refl. Qed.
Lemma D_3aa68 : decode_any W_3aa68 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa6c : bv 32 := 0x01213823.
Lemma F_3aa6c : fetch_word Ubsan.M.loaded_segments (0x3aa6c : word) = Some W_3aa6c.
Proof. vm_refl. Qed.
Lemma D_3aa6c : decode_any W_3aa6c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa70 : bv 32 := 0x01313423.
Lemma F_3aa70 : fetch_word Ubsan.M.loaded_segments (0x3aa70 : word) = Some W_3aa70.
Proof. vm_refl. Qed.
Lemma D_3aa70 : decode_any W_3aa70 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa74 : bv 32 := 0x00050413.
Lemma F_3aa74 : fetch_word Ubsan.M.loaded_segments (0x3aa74 : word) = Some W_3aa74.
Proof. vm_refl. Qed.
Lemma D_3aa74 : decode_any W_3aa74 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa78 : bv 32 := 0x00757513.
Lemma F_3aa78 : fetch_word Ubsan.M.loaded_segments (0x3aa78 : word) = Some W_3aa78.
Proof. vm_refl. Qed.
Lemma D_3aa78 : decode_any W_3aa78 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa7c : bv 32 := 0x0c051c63.
Lemma F_3aa7c : fetch_word Ubsan.M.loaded_segments (0x3aa7c : word) = Some W_3aa7c.
Proof. vm_refl. Qed.
Lemma D_3aa7c : decode_any W_3aa7c = Some (Branch BC_NE 10 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa80 : bv 32 := 0x00043483.
Lemma F_3aa80 : fetch_word Ubsan.M.loaded_segments (0x3aa80 : word) = Some W_3aa80.
Proof. vm_refl. Qed.
Lemma D_3aa80 : decode_any W_3aa80 = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa84 : bv 32 := 0x0a048a63.
Lemma F_3aa84 : fetch_word Ubsan.M.loaded_segments (0x3aa84 : word) = Some W_3aa84.
Proof. vm_refl. Qed.
Lemma D_3aa84 : decode_any W_3aa84 = Some (Branch BC_EQ 9 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa88 : bv 32 := 0x0074f513.
Lemma F_3aa88 : fetch_word Ubsan.M.loaded_segments (0x3aa88 : word) = Some W_3aa88.
Proof. vm_refl. Qed.
Lemma D_3aa88 : decode_any W_3aa88 = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa8c : bv 32 := 0x0c051463.
Lemma F_3aa8c : fetch_word Ubsan.M.loaded_segments (0x3aa8c : word) = Some W_3aa8c.
Proof. vm_refl. Qed.
Lemma D_3aa8c : decode_any W_3aa8c = Some (Branch BC_NE 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa90 : bv 32 := 0x00048513.
Lemma F_3aa90 : fetch_word Ubsan.M.loaded_segments (0x3aa90 : word) = Some W_3aa90.
Proof. vm_refl. Qed.
Lemma D_3aa90 : decode_any W_3aa90 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa94 : bv 32 := 0xd99de0ef.
Lemma F_3aa94 : fetch_word Ubsan.M.loaded_segments (0x3aa94 : word) = Some W_3aa94.
Proof. vm_refl. Qed.
Lemma D_3aa94 : decode_any W_3aa94 = Some (Jal 1 1961368, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa98 : bv 32 := 0x00848513.
Lemma F_3aa98 : fetch_word Ubsan.M.loaded_segments (0x3aa98 : word) = Some W_3aa98.
Proof. vm_refl. Qed.
Lemma D_3aa98 : decode_any W_3aa98 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aa9c : bv 32 := 0xd91de0ef.
Lemma F_3aa9c : fetch_word Ubsan.M.loaded_segments (0x3aa9c : word) = Some W_3aa9c.
Proof. vm_refl. Qed.
Lemma D_3aa9c : decode_any W_3aa9c = Some (Jal 1 1961360, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aaa0 : bv 32 := 0x05848513.
Lemma F_3aaa0 : fetch_word Ubsan.M.loaded_segments (0x3aaa0 : word) = Some W_3aaa0.
Proof. vm_refl. Qed.
Lemma D_3aaa0 : decode_any W_3aaa0 = Some (OpImm ALU_ADD 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aaa4 : bv 32 := 0x89ddd0ef.
Lemma F_3aaa4 : fetch_word Ubsan.M.loaded_segments (0x3aaa4 : word) = Some W_3aaa4.
Proof. vm_refl. Qed.
Lemma D_3aaa4 : decode_any W_3aaa4 = Some (Jal 1 1955996, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aaa8 : bv 32 := 0x0204b503.
Lemma F_3aaa8 : fetch_word Ubsan.M.loaded_segments (0x3aaa8 : word) = Some W_3aaa8.
Proof. vm_refl. Qed.
Lemma D_3aaa8 : decode_any W_3aaa8 = Some (Load SZ8 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aaac : bv 32 := 0x784010ef.
Lemma F_3aaac : fetch_word Ubsan.M.loaded_segments (0x3aaac : word) = Some W_3aaac.
Proof. vm_refl. Qed.
Lemma D_3aaac : decode_any W_3aaac = Some (Jal 1 6020, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aab0 : bv 32 := 0x0284b503.
Lemma F_3aab0 : fetch_word Ubsan.M.loaded_segments (0x3aab0 : word) = Some W_3aab0.
Proof. vm_refl. Qed.
Lemma D_3aab0 : decode_any W_3aab0 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aab4 : bv 32 := 0x77c010ef.
Lemma F_3aab4 : fetch_word Ubsan.M.loaded_segments (0x3aab4 : word) = Some W_3aab4.
Proof. vm_refl. Qed.
Lemma D_3aab4 : decode_any W_3aab4 = Some (Jal 1 6012, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aab8 : bv 32 := 0x0404b503.
Lemma F_3aab8 : fetch_word Ubsan.M.loaded_segments (0x3aab8 : word) = Some W_3aab8.
Proof. vm_refl. Qed.
Lemma D_3aab8 : decode_any W_3aab8 = Some (Load SZ8 true 10 9 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aabc : bv 32 := 0x774010ef.
Lemma F_3aabc : fetch_word Ubsan.M.loaded_segments (0x3aabc : word) = Some W_3aabc.
Proof. vm_refl. Qed.
Lemma D_3aabc : decode_any W_3aabc = Some (Jal 1 6004, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aac0 : bv 32 := 0x0484b503.
Lemma F_3aac0 : fetch_word Ubsan.M.loaded_segments (0x3aac0 : word) = Some W_3aac0.
Proof. vm_refl. Qed.
Lemma D_3aac0 : decode_any W_3aac0 = Some (Load SZ8 true 10 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aac4 : bv 32 := 0x76c010ef.
Lemma F_3aac4 : fetch_word Ubsan.M.loaded_segments (0x3aac4 : word) = Some W_3aac4.
Proof. vm_refl. Qed.
Lemma D_3aac4 : decode_any W_3aac4 = Some (Jal 1 5996, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aac8 : bv 32 := 0x0504b503.
Lemma F_3aac8 : fetch_word Ubsan.M.loaded_segments (0x3aac8 : word) = Some W_3aac8.
Proof. vm_refl. Qed.
Lemma D_3aac8 : decode_any W_3aac8 = Some (Load SZ8 true 10 9 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aacc : bv 32 := 0x764010ef.
Lemma F_3aacc : fetch_word Ubsan.M.loaded_segments (0x3aacc : word) = Some W_3aacc.
Proof. vm_refl. Qed.
Lemma D_3aacc : decode_any W_3aacc = Some (Jal 1 5988, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aad0 : bv 32 := 0x0384a503.
Lemma F_3aad0 : fetch_word Ubsan.M.loaded_segments (0x3aad0 : word) = Some W_3aad0.
Proof. vm_refl. Qed.
Lemma D_3aad0 : decode_any W_3aad0 = Some (Load SZ4 true 10 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aad4 : bv 32 := 0x04a05863.
Lemma F_3aad4 : fetch_word Ubsan.M.loaded_segments (0x3aad4 : word) = Some W_3aad4.
Proof. vm_refl. Qed.
Lemma D_3aad4 : decode_any W_3aad4 = Some (Branch BC_GE 0 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aad8 : bv 32 := 0x00000913.
Lemma F_3aad8 : fetch_word Ubsan.M.loaded_segments (0x3aad8 : word) = Some W_3aad8.
Proof. vm_refl. Qed.
Lemma D_3aad8 : decode_any W_3aad8 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aadc : bv 32 := 0x00000993.
Lemma F_3aadc : fetch_word Ubsan.M.loaded_segments (0x3aadc : word) = Some W_3aadc.
Proof. vm_refl. Qed.
Lemma D_3aadc : decode_any W_3aadc = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aae0 : bv 32 := 0x0604b583.
Lemma F_3aae0 : fetch_word Ubsan.M.loaded_segments (0x3aae0 : word) = Some W_3aae0.
Proof. vm_refl. Qed.
Lemma D_3aae0 : decode_any W_3aae0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aae4 : bv 32 := 0x01258533.
Lemma F_3aae4 : fetch_word Ubsan.M.loaded_segments (0x3aae4 : word) = Some W_3aae4.
Proof. vm_refl. Qed.
Lemma D_3aae4 : decode_any W_3aae4 = Some (Op ALU_ADD 10 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aae8 : bv 32 := 0x06b56663.
Lemma F_3aae8 : fetch_word Ubsan.M.loaded_segments (0x3aae8 : word) = Some W_3aae8.
Proof. vm_refl. Qed.
Lemma D_3aae8 : decode_any W_3aae8 = Some (Branch BC_LTU 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aaec : bv 32 := 0x00b03633.
Lemma F_3aaec : fetch_word Ubsan.M.loaded_segments (0x3aaec : word) = Some W_3aaec.
Proof. vm_refl. Qed.
Lemma D_3aaec : decode_any W_3aaec = Some (Op ALU_SLTU 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aaf0 : bv 32 := 0x00153693.
Lemma F_3aaf0 : fetch_word Ubsan.M.loaded_segments (0x3aaf0 : word) = Some W_3aaf0.
Proof. vm_refl. Qed.
Lemma D_3aaf0 : decode_any W_3aaf0 = Some (OpImm ALU_SLTU 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aaf4 : bv 32 := 0x00d64633.
Lemma F_3aaf4 : fetch_word Ubsan.M.loaded_segments (0x3aaf4 : word) = Some W_3aaf4.
Proof. vm_refl. Qed.
Lemma D_3aaf4 : decode_any W_3aaf4 = Some (Op ALU_XOR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aaf8 : bv 32 := 0x04060e63.
Lemma F_3aaf8 : fetch_word Ubsan.M.loaded_segments (0x3aaf8 : word) = Some W_3aaf8.
Proof. vm_refl. Qed.
Lemma D_3aaf8 : decode_any W_3aaf8 = Some (Branch BC_EQ 12 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aafc : bv 32 := 0x04058c63.
Lemma F_3aafc : fetch_word Ubsan.M.loaded_segments (0x3aafc : word) = Some W_3aafc.
Proof. vm_refl. Qed.
Lemma D_3aafc : decode_any W_3aafc = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab00 : bv 32 := 0x00b905b3.
Lemma F_3ab00 : fetch_word Ubsan.M.loaded_segments (0x3ab00 : word) = Some W_3ab00.
Proof. vm_refl. Qed.
Lemma D_3ab00 : decode_any W_3ab00 = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab04 : bv 32 := 0x0075f593.
Lemma F_3ab04 : fetch_word Ubsan.M.loaded_segments (0x3ab04 : word) = Some W_3ab04.
Proof. vm_refl. Qed.
Lemma D_3ab04 : decode_any W_3ab04 = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab08 : bv 32 := 0x04059663.
Lemma F_3ab08 : fetch_word Ubsan.M.loaded_segments (0x3ab08 : word) = Some W_3ab08.
Proof. vm_refl. Qed.
Lemma D_3ab08 : decode_any W_3ab08 = Some (Branch BC_NE 11 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab0c : bv 32 := 0x00053503.
Lemma F_3ab0c : fetch_word Ubsan.M.loaded_segments (0x3ab0c : word) = Some W_3ab0c.
Proof. vm_refl. Qed.
Lemma D_3ab0c : decode_any W_3ab0c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab10 : bv 32 := 0x720010ef.
Lemma F_3ab10 : fetch_word Ubsan.M.loaded_segments (0x3ab10 : word) = Some W_3ab10.
Proof. vm_refl. Qed.
Lemma D_3ab10 : decode_any W_3ab10 = Some (Jal 1 5920, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab14 : bv 32 := 0x0384a503.
Lemma F_3ab14 : fetch_word Ubsan.M.loaded_segments (0x3ab14 : word) = Some W_3ab14.
Proof. vm_refl. Qed.
Lemma D_3ab14 : decode_any W_3ab14 = Some (Load SZ4 true 10 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab18 : bv 32 := 0x00198993.
Lemma F_3ab18 : fetch_word Ubsan.M.loaded_segments (0x3ab18 : word) = Some W_3ab18.
Proof. vm_refl. Qed.
Lemma D_3ab18 : decode_any W_3ab18 = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab1c : bv 32 := 0x00890913.
Lemma F_3ab1c : fetch_word Ubsan.M.loaded_segments (0x3ab1c : word) = Some W_3ab1c.
Proof. vm_refl. Qed.
Lemma D_3ab1c : decode_any W_3ab1c = Some (OpImm ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab20 : bv 32 := 0xfca9c0e3.
Lemma F_3ab20 : fetch_word Ubsan.M.loaded_segments (0x3ab20 : word) = Some W_3ab20.
Proof. vm_refl. Qed.
Lemma D_3ab20 : decode_any W_3ab20 = Some (Branch BC_LT 19 10 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab24 : bv 32 := 0x0604b503.
Lemma F_3ab24 : fetch_word Ubsan.M.loaded_segments (0x3ab24 : word) = Some W_3ab24.
Proof. vm_refl. Qed.
Lemma D_3ab24 : decode_any W_3ab24 = Some (Load SZ8 true 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab28 : bv 32 := 0x708010ef.
Lemma F_3ab28 : fetch_word Ubsan.M.loaded_segments (0x3ab28 : word) = Some W_3ab28.
Proof. vm_refl. Qed.
Lemma D_3ab28 : decode_any W_3ab28 = Some (Jal 1 5896, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab2c : bv 32 := 0x00048513.
Lemma F_3ab2c : fetch_word Ubsan.M.loaded_segments (0x3ab2c : word) = Some W_3ab2c.
Proof. vm_refl. Qed.
Lemma D_3ab2c : decode_any W_3ab2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab30 : bv 32 := 0x700010ef.
Lemma F_3ab30 : fetch_word Ubsan.M.loaded_segments (0x3ab30 : word) = Some W_3ab30.
Proof. vm_refl. Qed.
Lemma D_3ab30 : decode_any W_3ab30 = Some (Jal 1 5888, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab34 : bv 32 := 0x00043023.
Lemma F_3ab34 : fetch_word Ubsan.M.loaded_segments (0x3ab34 : word) = Some W_3ab34.
Proof. vm_refl. Qed.
Lemma D_3ab34 : decode_any W_3ab34 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab38 : bv 32 := 0x02813083.
Lemma F_3ab38 : fetch_word Ubsan.M.loaded_segments (0x3ab38 : word) = Some W_3ab38.
Proof. vm_refl. Qed.
Lemma D_3ab38 : decode_any W_3ab38 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab3c : bv 32 := 0x02013403.
Lemma F_3ab3c : fetch_word Ubsan.M.loaded_segments (0x3ab3c : word) = Some W_3ab3c.
Proof. vm_refl. Qed.
Lemma D_3ab3c : decode_any W_3ab3c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab40 : bv 32 := 0x01813483.
Lemma F_3ab40 : fetch_word Ubsan.M.loaded_segments (0x3ab40 : word) = Some W_3ab40.
Proof. vm_refl. Qed.
Lemma D_3ab40 : decode_any W_3ab40 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab44 : bv 32 := 0x01013903.
Lemma F_3ab44 : fetch_word Ubsan.M.loaded_segments (0x3ab44 : word) = Some W_3ab44.
Proof. vm_refl. Qed.
Lemma D_3ab44 : decode_any W_3ab44 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab48 : bv 32 := 0x00813983.
Lemma F_3ab48 : fetch_word Ubsan.M.loaded_segments (0x3ab48 : word) = Some W_3ab48.
Proof. vm_refl. Qed.
Lemma D_3ab48 : decode_any W_3ab48 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab4c : bv 32 := 0x03010113.
Lemma F_3ab4c : fetch_word Ubsan.M.loaded_segments (0x3ab4c : word) = Some W_3ab4c.
Proof. vm_refl. Qed.
Lemma D_3ab4c : decode_any W_3ab4c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab50 : bv 32 := 0x00008067.
Lemma F_3ab50 : fetch_word Ubsan.M.loaded_segments (0x3ab50 : word) = Some W_3ab50.
Proof. vm_refl. Qed.
Lemma D_3ab50 : decode_any W_3ab50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ab54 : bv 32 := 0xc0001073.
Lemma F_3ab54 : fetch_word Ubsan.M.loaded_segments (0x3ab54 : word) = Some W_3ab54.
Proof. vm_refl. Qed.
Lemma D_3ab54 : decode_any W_3ab54 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
