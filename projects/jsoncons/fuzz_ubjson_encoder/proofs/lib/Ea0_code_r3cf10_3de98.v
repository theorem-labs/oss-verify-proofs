(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_52a40 : bv 32 := 0x00060793.
Lemma F_52a40 : fetch_word Asan.M.loaded_segments (0x52a90 : word) = Some W_52a40.
Proof. vm_refl. Qed.
Lemma D_52a40 : decode_any W_52a40 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a44 : bv 32 := 0x00058713.
Lemma F_52a44 : fetch_word Asan.M.loaded_segments (0x52a94 : word) = Some W_52a44.
Proof. vm_refl. Qed.
Lemma D_52a44 : decode_any W_52a44 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a48 : bv 32 := 0x000ec597.
Lemma F_52a48 : fetch_word Asan.M.loaded_segments (0x52a98 : word) = Some W_52a48.
Proof. vm_refl. Qed.
Lemma D_52a48 : decode_any W_52a48 = Some (Auipc 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a4c : bv 32 := 0x90058593.
Lemma F_52a4c : fetch_word Asan.M.loaded_segments (0x52a9c : word) = Some W_52a4c.
Proof. vm_refl. Qed.
Lemma D_52a4c : decode_any W_52a4c = Some (OpImm ALU_ADD 11 11 2304, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a50 : bv 32 := 0x00050613.
Lemma F_52a50 : fetch_word Asan.M.loaded_segments (0x52aa0 : word) = Some W_52a50.
Proof. vm_refl. Qed.
Lemma D_52a50 : decode_any W_52a50 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a54 : bv 32 := 0x00058513.
Lemma F_52a54 : fetch_word Asan.M.loaded_segments (0x52aa4 : word) = Some W_52a54.
Proof. vm_refl. Qed.
Lemma D_52a54 : decode_any W_52a54 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a58 : bv 32 := 0x00060593.
Lemma F_52a58 : fetch_word Asan.M.loaded_segments (0x52aa8 : word) = Some W_52a58.
Proof. vm_refl. Qed.
Lemma D_52a58 : decode_any W_52a58 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a5c : bv 32 := 0x00000613.
Lemma F_52a5c : fetch_word Asan.M.loaded_segments (0x52aac : word) = Some W_52a5c.
Proof. vm_refl. Qed.
Lemma D_52a5c : decode_any W_52a5c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a60 : bv 32 := 0x00000693.
Lemma F_52a60 : fetch_word Asan.M.loaded_segments (0x52ab0 : word) = Some W_52a60.
Proof. vm_refl. Qed.
Lemma D_52a60 : decode_any W_52a60 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a64 : bv 32 := 0x0040006f.
Lemma F_52a64 : fetch_word Asan.M.loaded_segments (0x52ab4 : word) = Some W_52a64.
Proof. vm_refl. Qed.
Lemma D_52a64 : decode_any W_52a64 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a68 : bv 32 := 0xfc010113.
Lemma F_52a68 : fetch_word Asan.M.loaded_segments (0x52ab8 : word) = Some W_52a68.
Proof. vm_refl. Qed.
Lemma D_52a68 : decode_any W_52a68 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a6c : bv 32 := 0x02113c23.
Lemma F_52a6c : fetch_word Asan.M.loaded_segments (0x52abc : word) = Some W_52a6c.
Proof. vm_refl. Qed.
Lemma D_52a6c : decode_any W_52a6c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a70 : bv 32 := 0x02813823.
Lemma F_52a70 : fetch_word Asan.M.loaded_segments (0x52ac0 : word) = Some W_52a70.
Proof. vm_refl. Qed.
Lemma D_52a70 : decode_any W_52a70 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a74 : bv 32 := 0x02913423.
Lemma F_52a74 : fetch_word Asan.M.loaded_segments (0x52ac4 : word) = Some W_52a74.
Proof. vm_refl. Qed.
Lemma D_52a74 : decode_any W_52a74 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a78 : bv 32 := 0x03213023.
Lemma F_52a78 : fetch_word Asan.M.loaded_segments (0x52ac8 : word) = Some W_52a78.
Proof. vm_refl. Qed.
Lemma D_52a78 : decode_any W_52a78 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a7c : bv 32 := 0x01313c23.
Lemma F_52a7c : fetch_word Asan.M.loaded_segments (0x52acc : word) = Some W_52a7c.
Proof. vm_refl. Qed.
Lemma D_52a7c : decode_any W_52a7c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a80 : bv 32 := 0x01413823.
Lemma F_52a80 : fetch_word Asan.M.loaded_segments (0x52ad0 : word) = Some W_52a80.
Proof. vm_refl. Qed.
Lemma D_52a80 : decode_any W_52a80 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a84 : bv 32 := 0x01513423.
Lemma F_52a84 : fetch_word Asan.M.loaded_segments (0x52ad4 : word) = Some W_52a84.
Proof. vm_refl. Qed.
Lemma D_52a84 : decode_any W_52a84 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a88 : bv 32 := 0x01613023.
Lemma F_52a88 : fetch_word Asan.M.loaded_segments (0x52ad8 : word) = Some W_52a88.
Proof. vm_refl. Qed.
Lemma D_52a88 : decode_any W_52a88 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a8c : bv 32 := 0x02058e63.
Lemma F_52a8c : fetch_word Asan.M.loaded_segments (0x52adc : word) = Some W_52a8c.
Proof. vm_refl. Qed.
Lemma D_52a8c : decode_any W_52a8c = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a90 : bv 32 := 0x00078a13.
Lemma F_52a90 : fetch_word Asan.M.loaded_segments (0x52ae0 : word) = Some W_52a90.
Proof. vm_refl. Qed.
Lemma D_52a90 : decode_any W_52a90 = Some (OpImm ALU_ADD 20 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a94 : bv 32 := 0x00070413.
Lemma F_52a94 : fetch_word Asan.M.loaded_segments (0x52ae4 : word) = Some W_52a94.
Proof. vm_refl. Qed.
Lemma D_52a94 : decode_any W_52a94 = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a98 : bv 32 := 0x00058493.
Lemma F_52a98 : fetch_word Asan.M.loaded_segments (0x52ae8 : word) = Some W_52a98.
Proof. vm_refl. Qed.
Lemma D_52a98 : decode_any W_52a98 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a9c : bv 32 := 0x00050993.
Lemma F_52a9c : fetch_word Asan.M.loaded_segments (0x52aec : word) = Some W_52a9c.
Proof. vm_refl. Qed.
Lemma D_52a9c : decode_any W_52a9c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aa0 : bv 32 := 0x00060a93.
Lemma F_52aa0 : fetch_word Asan.M.loaded_segments (0x52af0 : word) = Some W_52aa0.
Proof. vm_refl. Qed.
Lemma D_52aa0 : decode_any W_52aa0 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aa4 : bv 32 := 0x00068b13.
Lemma F_52aa4 : fetch_word Asan.M.loaded_segments (0x52af4 : word) = Some W_52aa4.
Proof. vm_refl. Qed.
Lemma D_52aa4 : decode_any W_52aa4 = Some (OpImm ALU_ADD 22 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aa8 : bv 32 := 0xff058913.
Lemma F_52aa8 : fetch_word Asan.M.loaded_segments (0x52af8 : word) = Some W_52aa8.
Proof. vm_refl. Qed.
Lemma D_52aa8 : decode_any W_52aa8 = Some (OpImm ALU_ADD 18 11 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aac : bv 32 := 0x00058513.
Lemma F_52aac : fetch_word Asan.M.loaded_segments (0x52afc : word) = Some W_52aac.
Proof. vm_refl. Qed.
Lemma D_52aac : decode_any W_52aac = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ab0 : bv 32 := 0x7f9350ef.
Lemma F_52ab0 : fetch_word Asan.M.loaded_segments (0x52b00 : word) = Some W_52ab0.
Proof. vm_refl. Qed.
Lemma D_52ab0 : decode_any W_52ab0 = Some (Jal 1 221176, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ab4 : bv 32 := 0x02050e63.
Lemma F_52ab4 : fetch_word Asan.M.loaded_segments (0x52b04 : word) = Some W_52ab4.
Proof. vm_refl. Qed.
Lemma D_52ab4 : decode_any W_52ab4 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ac8 : bv 32 := 0x03813083.
Lemma F_52ac8 : fetch_word Asan.M.loaded_segments (0x52b18 : word) = Some W_52ac8.
Proof. vm_refl. Qed.
Lemma D_52ac8 : decode_any W_52ac8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_52acc : bv 32 := 0x03013403.
Lemma F_52acc : fetch_word Asan.M.loaded_segments (0x52b1c : word) = Some W_52acc.
Proof. vm_refl. Qed.
Lemma D_52acc : decode_any W_52acc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ad0 : bv 32 := 0x02813483.
Lemma F_52ad0 : fetch_word Asan.M.loaded_segments (0x52b20 : word) = Some W_52ad0.
Proof. vm_refl. Qed.
Lemma D_52ad0 : decode_any W_52ad0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ad4 : bv 32 := 0x02013903.
Lemma F_52ad4 : fetch_word Asan.M.loaded_segments (0x52b24 : word) = Some W_52ad4.
Proof. vm_refl. Qed.
Lemma D_52ad4 : decode_any W_52ad4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ad8 : bv 32 := 0x01813983.
Lemma F_52ad8 : fetch_word Asan.M.loaded_segments (0x52b28 : word) = Some W_52ad8.
Proof. vm_refl. Qed.
Lemma D_52ad8 : decode_any W_52ad8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52adc : bv 32 := 0x01013a03.
Lemma F_52adc : fetch_word Asan.M.loaded_segments (0x52b2c : word) = Some W_52adc.
Proof. vm_refl. Qed.
Lemma D_52adc : decode_any W_52adc = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ae0 : bv 32 := 0x00813a83.
Lemma F_52ae0 : fetch_word Asan.M.loaded_segments (0x52b30 : word) = Some W_52ae0.
Proof. vm_refl. Qed.
Lemma D_52ae0 : decode_any W_52ae0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ae4 : bv 32 := 0x00013b03.
Lemma F_52ae4 : fetch_word Asan.M.loaded_segments (0x52b34 : word) = Some W_52ae4.
Proof. vm_refl. Qed.
Lemma D_52ae4 : decode_any W_52ae4 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ae8 : bv 32 := 0x04010113.
Lemma F_52ae8 : fetch_word Asan.M.loaded_segments (0x52b38 : word) = Some W_52ae8.
Proof. vm_refl. Qed.
Lemma D_52ae8 : decode_any W_52ae8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aec : bv 32 := 0x00008067.
Lemma F_52aec : fetch_word Asan.M.loaded_segments (0x52b3c : word) = Some W_52aec.
Proof. vm_refl. Qed.
Lemma D_52aec : decode_any W_52aec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52af0 : bv 32 := 0xffc97693.
Lemma F_52af0 : fetch_word Asan.M.loaded_segments (0x52b40 : word) = Some W_52af0.
Proof. vm_refl. Qed.
Lemma D_52af0 : decode_any W_52af0 = Some (OpImm ALU_AND 13 18 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_52af4 : bv 32 := 0x00391513.
Lemma F_52af4 : fetch_word Asan.M.loaded_segments (0x52b44 : word) = Some W_52af4.
Proof. vm_refl. Qed.
Lemma D_52af4 : decode_any W_52af4 = Some (ShiftImm ALU_SLL 10 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_52af8 : bv 32 := 0x0ff00613.
Lemma F_52af8 : fetch_word Asan.M.loaded_segments (0x52b48 : word) = Some W_52af8.
Proof. vm_refl. Qed.
Lemma D_52af8 : decode_any W_52af8 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_52afc : bv 32 := 0x00200713.
Lemma F_52afc : fetch_word Asan.M.loaded_segments (0x52b4c : word) = Some W_52afc.
Proof. vm_refl. Qed.
Lemma D_52afc : decode_any W_52afc = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b00 : bv 32 := 0x00300593.
Lemma F_52b00 : fetch_word Asan.M.loaded_segments (0x52b50 : word) = Some W_52b00.
Proof. vm_refl. Qed.
Lemma D_52b00 : decode_any W_52b00 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b04 : bv 32 := 0x00a617bb.
Lemma F_52b04 : fetch_word Asan.M.loaded_segments (0x52b54 : word) = Some W_52b04.
Proof. vm_refl. Qed.
Lemma D_52b04 : decode_any W_52b04 = Some (Op32 ALU_SLL 15 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b08 : bv 32 := 0x00a7173b.
Lemma F_52b08 : fetch_word Asan.M.loaded_segments (0x52b58 : word) = Some W_52b08.
Proof. vm_refl. Qed.
Lemma D_52b08 : decode_any W_52b08 = Some (Op32 ALU_SLL 14 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b0c : bv 32 := 0x00a5983b.
Lemma F_52b0c : fetch_word Asan.M.loaded_segments (0x52b5c : word) = Some W_52b0c.
Proof. vm_refl. Qed.
Lemma D_52b0c : decode_any W_52b0c = Some (Op32 ALU_SLL 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b10 : bv 32 := 0x1606a62f.
Lemma F_52b10 : fetch_word Asan.M.loaded_segments (0x52b60 : word) = Some W_52b10.
Proof. vm_refl. Qed.
Lemma D_52b10 : decode_any W_52b10 = Some (Lr AW true true 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b14 : bv 32 := 0x00f678b3.
Lemma F_52b14 : fetch_word Asan.M.loaded_segments (0x52b64 : word) = Some W_52b14.
Proof. vm_refl. Qed.
Lemma D_52b14 : decode_any W_52b14 = Some (Op ALU_AND 17 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b18 : bv 32 := 0x08e89063.
Lemma F_52b18 : fetch_word Asan.M.loaded_segments (0x52b68 : word) = Some W_52b18.
Proof. vm_refl. Qed.
Lemma D_52b18 : decode_any W_52b18 = Some (Branch BC_NE 17 14 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b1c : bv 32 := 0x010648b3.
Lemma F_52b1c : fetch_word Asan.M.loaded_segments (0x52b6c : word) = Some W_52b1c.
Proof. vm_refl. Qed.
Lemma D_52b1c : decode_any W_52b1c = Some (Op ALU_XOR 17 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b20 : bv 32 := 0x00f8f8b3.
Lemma F_52b20 : fetch_word Asan.M.loaded_segments (0x52b70 : word) = Some W_52b20.
Proof. vm_refl. Qed.
Lemma D_52b20 : decode_any W_52b20 = Some (Op ALU_AND 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b24 : bv 32 := 0x011648b3.
Lemma F_52b24 : fetch_word Asan.M.loaded_segments (0x52b74 : word) = Some W_52b24.
Proof. vm_refl. Qed.
Lemma D_52b24 : decode_any W_52b24 = Some (Op ALU_XOR 17 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b28 : bv 32 := 0x1b16a8af.
Lemma F_52b28 : fetch_word Asan.M.loaded_segments (0x52b78 : word) = Some W_52b28.
Proof. vm_refl. Qed.
Lemma D_52b28 : decode_any W_52b28 = Some (Sc AW false true 17 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b2c : bv 32 := 0xfe0892e3.
Lemma F_52b2c : fetch_word Asan.M.loaded_segments (0x52b7c : word) = Some W_52b2c.
Proof. vm_refl. Qed.
Lemma D_52b2c : decode_any W_52b2c = Some (Branch BC_NE 17 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b30 : bv 32 := 0xfff00513.
Lemma F_52b30 : fetch_word Asan.M.loaded_segments (0x52b80 : word) = Some W_52b30.
Proof. vm_refl. Qed.
Lemma D_52b30 : decode_any W_52b30 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b34 : bv 32 := 0x02051513.
Lemma F_52b34 : fetch_word Asan.M.loaded_segments (0x52b84 : word) = Some W_52b34.
Proof. vm_refl. Qed.
Lemma D_52b34 : decode_any W_52b34 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b38 : bv 32 := 0x00a93823.
Lemma F_52b38 : fetch_word Asan.M.loaded_segments (0x52b88 : word) = Some W_52b38.
Proof. vm_refl. Qed.
Lemma D_52b38 : decode_any W_52b38 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b3c : bv 32 := 0x00194503.
Lemma F_52b3c : fetch_word Asan.M.loaded_segments (0x52b8c : word) = Some W_52b3c.
Proof. vm_refl. Qed.
Lemma D_52b3c : decode_any W_52b3c = Some (Load SZ1 false 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b40 : bv 32 := 0x00357593.
Lemma F_52b40 : fetch_word Asan.M.loaded_segments (0x52b90 : word) = Some W_52b40.
Proof. vm_refl. Qed.
Lemma D_52b40 : decode_any W_52b40 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b44 : bv 32 := 0x08ba1863.
Lemma F_52b44 : fetch_word Asan.M.loaded_segments (0x52b94 : word) = Some W_52b44.
Proof. vm_refl. Qed.
Lemma D_52b44 : decode_any W_52b44 = Some (Branch BC_NE 20 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b48 : bv 32 := 0xffea7693.
Lemma F_52b48 : fetch_word Asan.M.loaded_segments (0x52b98 : word) = Some W_52b48.
Proof. vm_refl. Qed.
Lemma D_52b48 : decode_any W_52b48 = Some (OpImm ALU_AND 13 20 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b4c : bv 32 := 0x00200713.
Lemma F_52b4c : fetch_word Asan.M.loaded_segments (0x52b9c : word) = Some W_52b4c.
Proof. vm_refl. Qed.
Lemma D_52b4c : decode_any W_52b4c = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_52b50 : bv 32 := 0x14e69663.
Lemma F_52b50 : fetch_word Asan.M.loaded_segments (0x52ba0 : word) = Some W_52b50.
Proof. vm_refl. Qed.
Lemma D_52b50 : decode_any W_52b50 = Some (Branch BC_NE 13 14 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_52c9c : bv 32 := 0x748300ef.
Lemma F_52c9c : fetch_word Asan.M.loaded_segments (0x52cec : word) = Some W_52c9c.
Proof. vm_refl. Qed.
Lemma D_52c9c : decode_any W_52c9c = Some (Jal 1 198472, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ca0 : bv 32 := 0xff24d583.
Lemma F_52ca0 : fetch_word Asan.M.loaded_segments (0x52cf0 : word) = Some W_52ca0.
Proof. vm_refl. Qed.
Lemma D_52ca0 : decode_any W_52ca0 = Some (Load SZ2 false 11 9 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ca4 : bv 32 := 0xff44e603.
Lemma F_52ca4 : fetch_word Asan.M.loaded_segments (0x52cf4 : word) = Some W_52ca4.
Proof. vm_refl. Qed.
Lemma D_52ca4 : decode_any W_52ca4 = Some (Load SZ4 false 12 9 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ca8 : bv 32 := 0x02053683.
Lemma F_52ca8 : fetch_word Asan.M.loaded_segments (0x52cf8 : word) = Some W_52ca8.
Proof. vm_refl. Qed.
Lemma D_52ca8 : decode_any W_52ca8 = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cac : bv 32 := 0x01853703.
Lemma F_52cac : fetch_word Asan.M.loaded_segments (0x52cfc : word) = Some W_52cac.
Proof. vm_refl. Qed.
Lemma D_52cac : decode_any W_52cac = Some (Load SZ8 true 14 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cb0 : bv 32 := 0x02059593.
Lemma F_52cb0 : fetch_word Asan.M.loaded_segments (0x52d00 : word) = Some W_52cb0.
Proof. vm_refl. Qed.
Lemma D_52cb0 : decode_any W_52cb0 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cb4 : bv 32 := 0x00c5e5b3.
Lemma F_52cb4 : fetch_word Asan.M.loaded_segments (0x52d04 : word) = Some W_52cb4.
Proof. vm_refl. Qed.
Lemma D_52cb4 : decode_any W_52cb4 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cb8 : bv 32 := 0x00d585b3.
Lemma F_52cb8 : fetch_word Asan.M.loaded_segments (0x52d08 : word) = Some W_52cb8.
Proof. vm_refl. Qed.
Lemma D_52cb8 : decode_any W_52cb8 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cbc : bv 32 := 0x00170713.
Lemma F_52cbc : fetch_word Asan.M.loaded_segments (0x52d0c : word) = Some W_52cbc.
Proof. vm_refl. Qed.
Lemma D_52cbc : decode_any W_52cbc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cc0 : bv 32 := 0x00e53c23.
Lemma F_52cc0 : fetch_word Asan.M.loaded_segments (0x52d10 : word) = Some W_52cc0.
Proof. vm_refl. Qed.
Lemma D_52cc0 : decode_any W_52cc0 = Some (Store SZ8 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cc4 : bv 32 := 0x02b53023.
Lemma F_52cc4 : fetch_word Asan.M.loaded_segments (0x52d14 : word) = Some W_52cc4.
Proof. vm_refl. Qed.
Lemma D_52cc4 : decode_any W_52cc4 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cc8 : bv 32 := 0x00098513.
Lemma F_52cc8 : fetch_word Asan.M.loaded_segments (0x52d18 : word) = Some W_52cc8.
Proof. vm_refl. Qed.
Lemma D_52cc8 : decode_any W_52cc8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ccc : bv 32 := 0x00090593.
Lemma F_52ccc : fetch_word Asan.M.loaded_segments (0x52d1c : word) = Some W_52ccc.
Proof. vm_refl. Qed.
Lemma D_52ccc : decode_any W_52ccc = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cd0 : bv 32 := 0x00048613.
Lemma F_52cd0 : fetch_word Asan.M.loaded_segments (0x52d20 : word) = Some W_52cd0.
Proof. vm_refl. Qed.
Lemma D_52cd0 : decode_any W_52cd0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cd4 : bv 32 := 0x00040693.
Lemma F_52cd4 : fetch_word Asan.M.loaded_segments (0x52d24 : word) = Some W_52cd4.
Proof. vm_refl. Qed.
Lemma D_52cd4 : decode_any W_52cd4 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cd8 : bv 32 := 0x03813083.
Lemma F_52cd8 : fetch_word Asan.M.loaded_segments (0x52d28 : word) = Some W_52cd8.
Proof. vm_refl. Qed.
Lemma D_52cd8 : decode_any W_52cd8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cdc : bv 32 := 0x03013403.
Lemma F_52cdc : fetch_word Asan.M.loaded_segments (0x52d2c : word) = Some W_52cdc.
Proof. vm_refl. Qed.
Lemma D_52cdc : decode_any W_52cdc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ce0 : bv 32 := 0x02813483.
Lemma F_52ce0 : fetch_word Asan.M.loaded_segments (0x52d30 : word) = Some W_52ce0.
Proof. vm_refl. Qed.
Lemma D_52ce0 : decode_any W_52ce0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ce4 : bv 32 := 0x02013903.
Lemma F_52ce4 : fetch_word Asan.M.loaded_segments (0x52d34 : word) = Some W_52ce4.
Proof. vm_refl. Qed.
Lemma D_52ce4 : decode_any W_52ce4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ce8 : bv 32 := 0x01813983.
Lemma F_52ce8 : fetch_word Asan.M.loaded_segments (0x52d38 : word) = Some W_52ce8.
Proof. vm_refl. Qed.
Lemma D_52ce8 : decode_any W_52ce8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cec : bv 32 := 0x01013a03.
Lemma F_52cec : fetch_word Asan.M.loaded_segments (0x52d3c : word) = Some W_52cec.
Proof. vm_refl. Qed.
Lemma D_52cec : decode_any W_52cec = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cf0 : bv 32 := 0x00813a83.
Lemma F_52cf0 : fetch_word Asan.M.loaded_segments (0x52d40 : word) = Some W_52cf0.
Proof. vm_refl. Qed.
Lemma D_52cf0 : decode_any W_52cf0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cf4 : bv 32 := 0x00013b03.
Lemma F_52cf4 : fetch_word Asan.M.loaded_segments (0x52d44 : word) = Some W_52cf4.
Proof. vm_refl. Qed.
Lemma D_52cf4 : decode_any W_52cf4 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cf8 : bv 32 := 0x04010113.
Lemma F_52cf8 : fetch_word Asan.M.loaded_segments (0x52d48 : word) = Some W_52cf8.
Proof. vm_refl. Qed.
Lemma D_52cf8 : decode_any W_52cf8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_52cfc : bv 32 := 0x2cc0406f.
Lemma F_52cfc : fetch_word Asan.M.loaded_segments (0x52d4c : word) = Some W_52cfc.
Proof. vm_refl. Qed.
Lemma D_52cfc : decode_any W_52cfc = Some (Jal 0 17100, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d20 : bv 32 := 0xff010113.
Lemma F_52d20 : fetch_word Asan.M.loaded_segments (0x52d70 : word) = Some W_52d20.
Proof. vm_refl. Qed.
Lemma D_52d20 : decode_any W_52d20 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d24 : bv 32 := 0x00113423.
Lemma F_52d24 : fetch_word Asan.M.loaded_segments (0x52d74 : word) = Some W_52d24.
Proof. vm_refl. Qed.
Lemma D_52d24 : decode_any W_52d24 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d28 : bv 32 := 0x00813023.
Lemma F_52d28 : fetch_word Asan.M.loaded_segments (0x52d78 : word) = Some W_52d28.
Proof. vm_refl. Qed.
Lemma D_52d28 : decode_any W_52d28 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d2c : bv 32 := 0x00058693.
Lemma F_52d2c : fetch_word Asan.M.loaded_segments (0x52d7c : word) = Some W_52d2c.
Proof. vm_refl. Qed.
Lemma D_52d2c : decode_any W_52d2c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d30 : bv 32 := 0x00050593.
Lemma F_52d30 : fetch_word Asan.M.loaded_segments (0x52d80 : word) = Some W_52d30.
Proof. vm_refl. Qed.
Lemma D_52d30 : decode_any W_52d30 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d34 : bv 32 := 0x000eb517.
Lemma F_52d34 : fetch_word Asan.M.loaded_segments (0x52d84 : word) = Some W_52d34.
Proof. vm_refl. Qed.
Lemma D_52d34 : decode_any W_52d34 = Some (Auipc 10 235, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d38 : bv 32 := 0x00800613.
Lemma F_52d38 : fetch_word Asan.M.loaded_segments (0x52d88 : word) = Some W_52d38.
Proof. vm_refl. Qed.
Lemma D_52d38 : decode_any W_52d38 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d3c : bv 32 := 0x00100713.
Lemma F_52d3c : fetch_word Asan.M.loaded_segments (0x52d8c : word) = Some W_52d3c.
Proof. vm_refl. Qed.
Lemma D_52d3c : decode_any W_52d3c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d40 : bv 32 := 0x61450513.
Lemma F_52d40 : fetch_word Asan.M.loaded_segments (0x52d90 : word) = Some W_52d40.
Proof. vm_refl. Qed.
Lemma D_52d40 : decode_any W_52d40 = Some (OpImm ALU_ADD 10 10 1556, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d44 : bv 32 := 0x00100793.
Lemma F_52d44 : fetch_word Asan.M.loaded_segments (0x52d94 : word) = Some W_52d44.
Proof. vm_refl. Qed.
Lemma D_52d44 : decode_any W_52d44 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d48 : bv 32 := 0x034000ef.
Lemma F_52d48 : fetch_word Asan.M.loaded_segments (0x52d98 : word) = Some W_52d48.
Proof. vm_refl. Qed.
Lemma D_52d48 : decode_any W_52d48 = Some (Jal 1 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d4c : bv 32 := 0x00050a63.
Lemma F_52d4c : fetch_word Asan.M.loaded_segments (0x52d9c : word) = Some W_52d4c.
Proof. vm_refl. Qed.
Lemma D_52d4c : decode_any W_52d4c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d50 : bv 32 := 0x00813083.
Lemma F_52d50 : fetch_word Asan.M.loaded_segments (0x52da0 : word) = Some W_52d50.
Proof. vm_refl. Qed.
Lemma D_52d50 : decode_any W_52d50 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d54 : bv 32 := 0x00013403.
Lemma F_52d54 : fetch_word Asan.M.loaded_segments (0x52da4 : word) = Some W_52d54.
Proof. vm_refl. Qed.
Lemma D_52d54 : decode_any W_52d54 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d58 : bv 32 := 0x01010113.
Lemma F_52d58 : fetch_word Asan.M.loaded_segments (0x52da8 : word) = Some W_52d58.
Proof. vm_refl. Qed.
Lemma D_52d58 : decode_any W_52d58 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d5c : bv 32 := 0x00008067.
Lemma F_52d5c : fetch_word Asan.M.loaded_segments (0x52dac : word) = Some W_52d5c.
Proof. vm_refl. Qed.
Lemma D_52d5c : decode_any W_52d5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d7c : bv 32 := 0xf8010113.
Lemma F_52d7c : fetch_word Asan.M.loaded_segments (0x52dcc : word) = Some W_52d7c.
Proof. vm_refl. Qed.
Lemma D_52d7c : decode_any W_52d7c = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d80 : bv 32 := 0x06113c23.
Lemma F_52d80 : fetch_word Asan.M.loaded_segments (0x52dd0 : word) = Some W_52d80.
Proof. vm_refl. Qed.
Lemma D_52d80 : decode_any W_52d80 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d84 : bv 32 := 0x06813823.
Lemma F_52d84 : fetch_word Asan.M.loaded_segments (0x52dd4 : word) = Some W_52d84.
Proof. vm_refl. Qed.
Lemma D_52d84 : decode_any W_52d84 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d88 : bv 32 := 0x06913423.
Lemma F_52d88 : fetch_word Asan.M.loaded_segments (0x52dd8 : word) = Some W_52d88.
Proof. vm_refl. Qed.
Lemma D_52d88 : decode_any W_52d88 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d8c : bv 32 := 0x07213023.
Lemma F_52d8c : fetch_word Asan.M.loaded_segments (0x52ddc : word) = Some W_52d8c.
Proof. vm_refl. Qed.
Lemma D_52d8c : decode_any W_52d8c = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d90 : bv 32 := 0x05313c23.
Lemma F_52d90 : fetch_word Asan.M.loaded_segments (0x52de0 : word) = Some W_52d90.
Proof. vm_refl. Qed.
Lemma D_52d90 : decode_any W_52d90 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d94 : bv 32 := 0x05413823.
Lemma F_52d94 : fetch_word Asan.M.loaded_segments (0x52de4 : word) = Some W_52d94.
Proof. vm_refl. Qed.
Lemma D_52d94 : decode_any W_52d94 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d98 : bv 32 := 0x05513423.
Lemma F_52d98 : fetch_word Asan.M.loaded_segments (0x52de8 : word) = Some W_52d98.
Proof. vm_refl. Qed.
Lemma D_52d98 : decode_any W_52d98 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_52d9c : bv 32 := 0x05613023.
Lemma F_52d9c : fetch_word Asan.M.loaded_segments (0x52dec : word) = Some W_52d9c.
Proof. vm_refl. Qed.
Lemma D_52d9c : decode_any W_52d9c = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_52da0 : bv 32 := 0x03713c23.
Lemma F_52da0 : fetch_word Asan.M.loaded_segments (0x52df0 : word) = Some W_52da0.
Proof. vm_refl. Qed.
Lemma D_52da0 : decode_any W_52da0 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_52da4 : bv 32 := 0x03813823.
Lemma F_52da4 : fetch_word Asan.M.loaded_segments (0x52df4 : word) = Some W_52da4.
Proof. vm_refl. Qed.
Lemma D_52da4 : decode_any W_52da4 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_52da8 : bv 32 := 0x03913423.
Lemma F_52da8 : fetch_word Asan.M.loaded_segments (0x52df8 : word) = Some W_52da8.
Proof. vm_refl. Qed.
Lemma D_52da8 : decode_any W_52da8 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dac : bv 32 := 0x03a13023.
Lemma F_52dac : fetch_word Asan.M.loaded_segments (0x52dfc : word) = Some W_52dac.
Proof. vm_refl. Qed.
Lemma D_52dac : decode_any W_52dac = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52db0 : bv 32 := 0x01b13c23.
Lemma F_52db0 : fetch_word Asan.M.loaded_segments (0x52e00 : word) = Some W_52db0.
Proof. vm_refl. Qed.
Lemma D_52db0 : decode_any W_52db0 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52db4 : bv 32 := 0x00078493.
Lemma F_52db4 : fetch_word Asan.M.loaded_segments (0x52e04 : word) = Some W_52db4.
Proof. vm_refl. Qed.
Lemma D_52db4 : decode_any W_52db4 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52db8 : bv 32 := 0x00070d93.
Lemma F_52db8 : fetch_word Asan.M.loaded_segments (0x52e08 : word) = Some W_52db8.
Proof. vm_refl. Qed.
Lemma D_52db8 : decode_any W_52db8 = Some (OpImm ALU_ADD 27 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dbc : bv 32 := 0x00068b93.
Lemma F_52dbc : fetch_word Asan.M.loaded_segments (0x52e0c : word) = Some W_52dbc.
Proof. vm_refl. Qed.
Lemma D_52dbc : decode_any W_52dbc = Some (OpImm ALU_ADD 23 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dc0 : bv 32 := 0x00060913.
Lemma F_52dc0 : fetch_word Asan.M.loaded_segments (0x52e10 : word) = Some W_52dc0.
Proof. vm_refl. Qed.
Lemma D_52dc0 : decode_any W_52dc0 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dc4 : bv 32 := 0x00058a93.
Lemma F_52dc4 : fetch_word Asan.M.loaded_segments (0x52e14 : word) = Some W_52dc4.
Proof. vm_refl. Qed.
Lemma D_52dc4 : decode_any W_52dc4 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dc8 : bv 32 := 0x00050b13.
Lemma F_52dc8 : fetch_word Asan.M.loaded_segments (0x52e18 : word) = Some W_52dc8.
Proof. vm_refl. Qed.
Lemma D_52dc8 : decode_any W_52dc8 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dcc : bv 32 := 0x53d2d0ef.
Lemma F_52dcc : fetch_word Asan.M.loaded_segments (0x52e1c : word) = Some W_52dcc.
Proof. vm_refl. Qed.
Lemma D_52dcc : decode_any W_52dcc = Some (Jal 1 187708, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dd0 : bv 32 := 0x7e050463.
Lemma F_52dd0 : fetch_word Asan.M.loaded_segments (0x52e20 : word) = Some W_52dd0.
Proof. vm_refl. Qed.
Lemma D_52dd0 : decode_any W_52dd0 = Some (Branch BC_EQ 10 0 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dd4 : bv 32 := 0x1fd330ef.
Lemma F_52dd4 : fetch_word Asan.M.loaded_segments (0x52e24 : word) = Some W_52dd4.
Proof. vm_refl. Qed.
Lemma D_52dd4 : decode_any W_52dd4 = Some (Jal 1 211452, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dd8 : bv 32 := 0x7e051663.
Lemma F_52dd8 : fetch_word Asan.M.loaded_segments (0x52e28 : word) = Some W_52dd8.
Proof. vm_refl. Qed.
Lemma D_52dd8 : decode_any W_52dd8 = Some (Branch BC_NE 10 0 2028, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ddc : bv 32 := 0x080b86e3.
Lemma F_52ddc : fetch_word Asan.M.loaded_segments (0x52e2c : word) = Some W_52ddc.
Proof. vm_refl. Qed.
Lemma D_52ddc : decode_any W_52ddc = Some (Branch BC_EQ 23 0 2188, 4%Z).
Proof. vm_refl. Qed.

Definition W_52de0 : bv 32 := 0x00800513.
Lemma F_52de0 : fetch_word Asan.M.loaded_segments (0x52e30 : word) = Some W_52de0.
Proof. vm_refl. Qed.
Lemma D_52de0 : decode_any W_52de0 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52de4 : bv 32 := 0x02a97e63.
Lemma F_52de4 : fetch_word Asan.M.loaded_segments (0x52e34 : word) = Some W_52de4.
Proof. vm_refl. Qed.
Lemma D_52de4 : decode_any W_52de4 = Some (Branch BC_GEU 18 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_52df4 : bv 32 := 0x00800413.
Lemma F_52df4 : fetch_word Asan.M.loaded_segments (0x52e44 : word) = Some W_52df4.
Proof. vm_refl. Qed.
Lemma D_52df4 : decode_any W_52df4 = Some (OpImm ALU_ADD 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52df8 : bv 32 := 0xfff40c93.
Lemma F_52df8 : fetch_word Asan.M.loaded_segments (0x52e48 : word) = Some W_52df8.
Proof. vm_refl. Qed.
Lemma D_52df8 : decode_any W_52df8 = Some (OpImm ALU_ADD 25 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_52dfc : bv 32 := 0x01947533.
Lemma F_52dfc : fetch_word Asan.M.loaded_segments (0x52e4c : word) = Some W_52dfc.
Proof. vm_refl. Qed.
Lemma D_52dfc : decode_any W_52dfc = Some (Op ALU_AND 10 8 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e00 : bv 32 := 0x7c051a63.
Lemma F_52e00 : fetch_word Asan.M.loaded_segments (0x52e50 : word) = Some W_52e00.
Proof. vm_refl. Qed.
Lemma D_52e00 : decode_any W_52e00 = Some (Branch BC_NE 10 0 2004, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e04 : bv 32 := 0x03100513.
Lemma F_52e04 : fetch_word Asan.M.loaded_segments (0x52e54 : word) = Some W_52e04.
Proof. vm_refl. Qed.
Lemma D_52e04 : decode_any W_52e04 = Some (OpImm ALU_ADD 10 0 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e08 : bv 32 := 0x7ffb0d13.
Lemma F_52e08 : fetch_word Asan.M.loaded_segments (0x52e58 : word) = Some W_52e08.
Proof. vm_refl. Qed.
Lemma D_52e08 : decode_any W_52e08 = Some (OpImm ALU_ADD 26 22 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e0c : bv 32 := 0x00913423.
Lemma F_52e0c : fetch_word Asan.M.loaded_segments (0x52e5c : word) = Some W_52e0c.
Proof. vm_refl. Qed.
Lemma D_52e0c : decode_any W_52e0c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e10 : bv 32 := 0x00b13823.
Lemma F_52e10 : fetch_word Asan.M.loaded_segments (0x52e60 : word) = Some W_52e10.
Proof. vm_refl. Qed.
Lemma D_52e10 : decode_any W_52e10 = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e14 : bv 32 := 0x06aaf463.
Lemma F_52e14 : fetch_word Asan.M.loaded_segments (0x52e64 : word) = Some W_52e14.
Proof. vm_refl. Qed.
Lemma D_52e14 : decode_any W_52e14 = Some (Branch BC_GEU 21 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e18 : bv 32 := 0x00000993.
Lemma F_52e18 : fetch_word Asan.M.loaded_segments (0x52e68 : word) = Some W_52e18.
Proof. vm_refl. Qed.
Lemma D_52e18 : decode_any W_52e18 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e1c : bv 32 := 0x0cc0006f.
Lemma F_52e1c : fetch_word Asan.M.loaded_segments (0x52e6c : word) = Some W_52e1c.
Proof. vm_refl. Qed.
Lemma D_52e1c : decode_any W_52e1c = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e20 : bv 32 := 0x20000613.
Lemma F_52e20 : fetch_word Asan.M.loaded_segments (0x52e70 : word) = Some W_52e20.
Proof. vm_refl. Qed.
Lemma D_52e20 : decode_any W_52e20 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e24 : bv 32 := 0x00090593.
Lemma F_52e24 : fetch_word Asan.M.loaded_segments (0x52e74 : word) = Some W_52e24.
Proof. vm_refl. Qed.
Lemma D_52e24 : decode_any W_52e24 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e28 : bv 32 := 0x00c96463.
Lemma F_52e28 : fetch_word Asan.M.loaded_segments (0x52e78 : word) = Some W_52e28.
Proof. vm_refl. Qed.
Lemma D_52e28 : decode_any W_52e28 = Some (Branch BC_LTU 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e30 : bv 32 := 0xfff58613.
Lemma F_52e30 : fetch_word Asan.M.loaded_segments (0x52e80 : word) = Some W_52e30.
Proof. vm_refl. Qed.
Lemma D_52e30 : decode_any W_52e30 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e34 : bv 32 := 0x00c5f633.
Lemma F_52e34 : fetch_word Asan.M.loaded_segments (0x52e84 : word) = Some W_52e34.
Proof. vm_refl. Qed.
Lemma D_52e34 : decode_any W_52e34 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e38 : bv 32 := 0x040618e3.
Lemma F_52e38 : fetch_word Asan.M.loaded_segments (0x52e88 : word) = Some W_52e38.
Proof. vm_refl. Qed.
Lemma D_52e38 : decode_any W_52e38 = Some (Branch BC_NE 12 0 2128, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e3c : bv 32 := 0xfffbd617.
Lemma F_52e3c : fetch_word Asan.M.loaded_segments (0x52e8c : word) = Some W_52e3c.
Proof. vm_refl. Qed.
Lemma D_52e3c : decode_any W_52e3c = Some (Auipc 12 1048509, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e40 : bv 32 := 0x5bc63603.
Lemma F_52e40 : fetch_word Asan.M.loaded_segments (0x52e90 : word) = Some W_52e40.
Proof. vm_refl. Qed.
Lemma D_52e40 : decode_any W_52e40 = Some (Load SZ8 true 12 12 1468, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e44 : bv 32 := 0x40b006b3.
Lemma F_52e44 : fetch_word Asan.M.loaded_segments (0x52e94 : word) = Some W_52e44.
Proof. vm_refl. Qed.
Lemma D_52e44 : decode_any W_52e44 = Some (Op ALU_SUB 13 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e48 : bv 32 := 0x00d5f5b3.
Lemma F_52e48 : fetch_word Asan.M.loaded_segments (0x52e98 : word) = Some W_52e48.
Proof. vm_refl. Qed.
Lemma D_52e48 : decode_any W_52e48 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e4c : bv 32 := 0x02c585b3.
Lemma F_52e4c : fetch_word Asan.M.loaded_segments (0x52e9c : word) = Some W_52e4c.
Proof. vm_refl. Qed.
Lemma D_52e4c : decode_any W_52e4c = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e50 : bv 32 := 0xfffbd617.
Lemma F_52e50 : fetch_word Asan.M.loaded_segments (0x52ea0 : word) = Some W_52e50.
Proof. vm_refl. Qed.
Lemma D_52e50 : decode_any W_52e50 = Some (Auipc 12 1048509, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e54 : bv 32 := 0x03a5d593.
Lemma F_52e54 : fetch_word Asan.M.loaded_segments (0x52ea4 : word) = Some W_52e54.
Proof. vm_refl. Qed.
Lemma D_52e54 : decode_any W_52e54 = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e58 : bv 32 := 0x62060613.
Lemma F_52e58 : fetch_word Asan.M.loaded_segments (0x52ea8 : word) = Some W_52e58.
Proof. vm_refl. Qed.
Lemma D_52e58 : decode_any W_52e58 = Some (OpImm ALU_ADD 12 12 1568, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e5c : bv 32 := 0x00b605b3.
Lemma F_52e5c : fetch_word Asan.M.loaded_segments (0x52eac : word) = Some W_52e5c.
Proof. vm_refl. Qed.
Lemma D_52e5c : decode_any W_52e5c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e60 : bv 32 := 0x0005c583.
Lemma F_52e60 : fetch_word Asan.M.loaded_segments (0x52eb0 : word) = Some W_52e60.
Proof. vm_refl. Qed.
Lemma D_52e60 : decode_any W_52e60 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e64 : bv 32 := 0x00459593.
Lemma F_52e64 : fetch_word Asan.M.loaded_segments (0x52eb4 : word) = Some W_52e64.
Proof. vm_refl. Qed.
Lemma D_52e64 : decode_any W_52e64 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e68 : bv 32 := 0x06058593.
Lemma F_52e68 : fetch_word Asan.M.loaded_segments (0x52eb8 : word) = Some W_52e68.
Proof. vm_refl. Qed.
Lemma D_52e68 : decode_any W_52e68 = Some (OpImm ALU_ADD 11 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e6c : bv 32 := 0x0705f593.
Lemma F_52e6c : fetch_word Asan.M.loaded_segments (0x52ebc : word) = Some W_52e6c.
Proof. vm_refl. Qed.
Lemma D_52e6c : decode_any W_52e6c = Some (OpImm ALU_AND 11 11 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e70 : bv 32 := 0x00090413.
Lemma F_52e70 : fetch_word Asan.M.loaded_segments (0x52ec0 : word) = Some W_52e70.
Proof. vm_refl. Qed.
Lemma D_52e70 : decode_any W_52e70 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e74 : bv 32 := 0xf92570e3.
Lemma F_52e74 : fetch_word Asan.M.loaded_segments (0x52ec4 : word) = Some W_52e74.
Proof. vm_refl. Qed.
Lemma D_52e74 : decode_any W_52e74 = Some (Branch BC_GEU 10 18 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e78 : bv 32 := 0xf81ff06f.
Lemma F_52e78 : fetch_word Asan.M.loaded_segments (0x52ec8 : word) = Some W_52e78.
Proof. vm_refl. Qed.
Lemma D_52e78 : decode_any W_52e78 = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e7c : bv 32 := 0x06100513.
Lemma F_52e7c : fetch_word Asan.M.loaded_segments (0x52ecc : word) = Some W_52e7c.
Proof. vm_refl. Qed.
Lemma D_52e7c : decode_any W_52e7c = Some (OpImm ALU_ADD 10 0 97, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e80 : bv 32 := 0x00aaf663.
Lemma F_52e80 : fetch_word Asan.M.loaded_segments (0x52ed0 : word) = Some W_52e80.
Proof. vm_refl. Qed.
Lemma D_52e80 : decode_any W_52e80 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e84 : bv 32 := 0x00100993.
Lemma F_52e84 : fetch_word Asan.M.loaded_segments (0x52ed4 : word) = Some W_52e84.
Proof. vm_refl. Qed.
Lemma D_52e84 : decode_any W_52e84 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e88 : bv 32 := 0x0600006f.
Lemma F_52e88 : fetch_word Asan.M.loaded_segments (0x52ed8 : word) = Some W_52e88.
Proof. vm_refl. Qed.
Lemma D_52e88 : decode_any W_52e88 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e8c : bv 32 := 0x1c100513.
Lemma F_52e8c : fetch_word Asan.M.loaded_segments (0x52edc : word) = Some W_52e8c.
Proof. vm_refl. Qed.
Lemma D_52e8c : decode_any W_52e8c = Some (OpImm ALU_ADD 10 0 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e90 : bv 32 := 0x00aaf663.
Lemma F_52e90 : fetch_word Asan.M.loaded_segments (0x52ee0 : word) = Some W_52e90.
Proof. vm_refl. Qed.
Lemma D_52e90 : decode_any W_52e90 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e94 : bv 32 := 0x00200993.
Lemma F_52e94 : fetch_word Asan.M.loaded_segments (0x52ee4 : word) = Some W_52e94.
Proof. vm_refl. Qed.
Lemma D_52e94 : decode_any W_52e94 = Some (OpImm ALU_ADD 19 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e98 : bv 32 := 0x0500006f.
Lemma F_52e98 : fetch_word Asan.M.loaded_segments (0x52ee8 : word) = Some W_52e98.
Proof. vm_refl. Qed.
Lemma D_52e98 : decode_any W_52e98 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_52e9c : bv 32 := 0x00001537.
Lemma F_52e9c : fetch_word Asan.M.loaded_segments (0x52eec : word) = Some W_52e9c.
Proof. vm_refl. Qed.
Lemma D_52e9c : decode_any W_52e9c = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ea0 : bv 32 := 0xf815051b.
Lemma F_52ea0 : fetch_word Asan.M.loaded_segments (0x52ef0 : word) = Some W_52ea0.
Proof. vm_refl. Qed.
Lemma D_52ea0 : decode_any W_52ea0 = Some (OpImm32 10 10 3969, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ea4 : bv 32 := 0x00aaf663.
Lemma F_52ea4 : fetch_word Asan.M.loaded_segments (0x52ef4 : word) = Some W_52ea4.
Proof. vm_refl. Qed.
Lemma D_52ea4 : decode_any W_52ea4 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ea8 : bv 32 := 0x00300993.
Lemma F_52ea8 : fetch_word Asan.M.loaded_segments (0x52ef8 : word) = Some W_52ea8.
Proof. vm_refl. Qed.
Lemma D_52ea8 : decode_any W_52ea8 = Some (OpImm ALU_ADD 19 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_52eac : bv 32 := 0x03c0006f.
Lemma F_52eac : fetch_word Asan.M.loaded_segments (0x52efc : word) = Some W_52eac.
Proof. vm_refl. Qed.
Lemma D_52eac : decode_any W_52eac = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_52eb0 : bv 32 := 0x00004537.
Lemma F_52eb0 : fetch_word Asan.M.loaded_segments (0x52f00 : word) = Some W_52eb0.
Proof. vm_refl. Qed.
Lemma D_52eb0 : decode_any W_52eb0 = Some (Lui 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52eb4 : bv 32 := 0xf015051b.
Lemma F_52eb4 : fetch_word Asan.M.loaded_segments (0x52f04 : word) = Some W_52eb4.
Proof. vm_refl. Qed.
Lemma D_52eb4 : decode_any W_52eb4 = Some (OpImm32 10 10 3841, 4%Z).
Proof. vm_refl. Qed.

Definition W_52eb8 : bv 32 := 0x00aaf663.
Lemma F_52eb8 : fetch_word Asan.M.loaded_segments (0x52f08 : word) = Some W_52eb8.
Proof. vm_refl. Qed.
Lemma D_52eb8 : decode_any W_52eb8 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ebc : bv 32 := 0x00400993.
Lemma F_52ebc : fetch_word Asan.M.loaded_segments (0x52f0c : word) = Some W_52ebc.
Proof. vm_refl. Qed.
Lemma D_52ebc : decode_any W_52ebc = Some (OpImm ALU_ADD 19 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ec0 : bv 32 := 0x0280006f.
Lemma F_52ec0 : fetch_word Asan.M.loaded_segments (0x52f10 : word) = Some W_52ec0.
Proof. vm_refl. Qed.
Lemma D_52ec0 : decode_any W_52ec0 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ec4 : bv 32 := 0x00008537.
Lemma F_52ec4 : fetch_word Asan.M.loaded_segments (0x52f14 : word) = Some W_52ec4.
Proof. vm_refl. Qed.
Lemma D_52ec4 : decode_any W_52ec4 = Some (Lui 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ec8 : bv 32 := 0xe015051b.
Lemma F_52ec8 : fetch_word Asan.M.loaded_segments (0x52f18 : word) = Some W_52ec8.
Proof. vm_refl. Qed.
Lemma D_52ec8 : decode_any W_52ec8 = Some (OpImm32 10 10 3585, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ecc : bv 32 := 0x00aaf663.
Lemma F_52ecc : fetch_word Asan.M.loaded_segments (0x52f1c : word) = Some W_52ecc.
Proof. vm_refl. Qed.
Lemma D_52ecc : decode_any W_52ecc = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ed0 : bv 32 := 0x00500993.
Lemma F_52ed0 : fetch_word Asan.M.loaded_segments (0x52f20 : word) = Some W_52ed0.
Proof. vm_refl. Qed.
Lemma D_52ed0 : decode_any W_52ed0 = Some (OpImm ALU_ADD 19 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ed4 : bv 32 := 0x0140006f.
Lemma F_52ed4 : fetch_word Asan.M.loaded_segments (0x52f24 : word) = Some W_52ed4.
Proof. vm_refl. Qed.
Lemma D_52ed4 : decode_any W_52ed4 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ed8 : bv 32 := 0x00010537.
Lemma F_52ed8 : fetch_word Asan.M.loaded_segments (0x52f28 : word) = Some W_52ed8.
Proof. vm_refl. Qed.
Lemma D_52ed8 : decode_any W_52ed8 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52edc : bv 32 := 0xc015051b.
Lemma F_52edc : fetch_word Asan.M.loaded_segments (0x52f2c : word) = Some W_52edc.
Proof. vm_refl. Qed.
Lemma D_52edc : decode_any W_52edc = Some (OpImm32 10 10 3073, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ee0 : bv 32 := 0x00aab533.
Lemma F_52ee0 : fetch_word Asan.M.loaded_segments (0x52f30 : word) = Some W_52ee0.
Proof. vm_refl. Qed.
Lemma D_52ee0 : decode_any W_52ee0 = Some (Op ALU_SLTU 10 21 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ee4 : bv 32 := 0x00754993.
Lemma F_52ee4 : fetch_word Asan.M.loaded_segments (0x52f34 : word) = Some W_52ee4.
Proof. vm_refl. Qed.
Lemma D_52ee4 : decode_any W_52ee4 = Some (OpImm ALU_XOR 19 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ee8 : bv 32 := 0x629d1503.
Lemma F_52ee8 : fetch_word Asan.M.loaded_segments (0x52f38 : word) = Some W_52ee8.
Proof. vm_refl. Qed.
Lemma D_52ee8 : decode_any W_52ee8 = Some (Load SZ2 true 10 26 1577, 4%Z).
Proof. vm_refl. Qed.

Definition W_52eec : bv 32 := 0x0230000f.
Lemma F_52eec : fetch_word Asan.M.loaded_segments (0x52f3c : word) = Some W_52eec.
Proof. vm_refl. Qed.
Lemma D_52eec : decode_any W_52eec = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ef0 : bv 32 := 0x00010a37.
Lemma F_52ef0 : fetch_word Asan.M.loaded_segments (0x52f40 : word) = Some W_52ef0.
Proof. vm_refl. Qed.
Lemma D_52ef0 : decode_any W_52ef0 = Some (Lui 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ef4 : bv 32 := 0xfffa0c1b.
Lemma F_52ef4 : fetch_word Asan.M.loaded_segments (0x52f44 : word) = Some W_52ef4.
Proof. vm_refl. Qed.
Lemma D_52ef4 : decode_any W_52ef4 = Some (OpImm32 24 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ef8 : bv 32 := 0x01857533.
Lemma F_52ef8 : fetch_word Asan.M.loaded_segments (0x52f48 : word) = Some W_52ef8.
Proof. vm_refl. Qed.
Lemma D_52ef8 : decode_any W_52ef8 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52efc : bv 32 := 0x4a0050ef.
Lemma F_52efc : fetch_word Asan.M.loaded_segments (0x52f4c : word) = Some W_52efc.
Proof. vm_refl. Qed.
Lemma D_52efc : decode_any W_52efc = Some (Jal 1 21664, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f00 : bv 32 := 0x00050493.
Lemma F_52f00 : fetch_word Asan.M.loaded_segments (0x52f50 : word) = Some W_52f00.
Proof. vm_refl. Qed.
Lemma D_52f00 : decode_any W_52f00 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f04 : bv 32 := 0x62bd1503.
Lemma F_52f04 : fetch_word Asan.M.loaded_segments (0x52f54 : word) = Some W_52f04.
Proof. vm_refl. Qed.
Lemma D_52f04 : decode_any W_52f04 = Some (Load SZ2 true 10 26 1579, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f08 : bv 32 := 0x0230000f.
Lemma F_52f08 : fetch_word Asan.M.loaded_segments (0x52f58 : word) = Some W_52f08.
Proof. vm_refl. Qed.
Lemma D_52f08 : decode_any W_52f08 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f0c : bv 32 := 0x01857533.
Lemma F_52f0c : fetch_word Asan.M.loaded_segments (0x52f5c : word) = Some W_52f0c.
Proof. vm_refl. Qed.
Lemma D_52f0c : decode_any W_52f0c = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f10 : bv 32 := 0x48c050ef.
Lemma F_52f10 : fetch_word Asan.M.loaded_segments (0x52f60 : word) = Some W_52f10.
Proof. vm_refl. Qed.
Lemma D_52f10 : decode_any W_52f10 = Some (Jal 1 21644, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f14 : bv 32 := 0x0b34e663.
Lemma F_52f14 : fetch_word Asan.M.loaded_segments (0x52f64 : word) = Some W_52f14.
Proof. vm_refl. Qed.
Lemma D_52f14 : decode_any W_52f14 = Some (Branch BC_LTU 9 19 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f18 : bv 32 := 0x00048993.
Lemma F_52f18 : fetch_word Asan.M.loaded_segments (0x52f68 : word) = Some W_52f18.
Proof. vm_refl. Qed.
Lemma D_52f18 : decode_any W_52f18 = Some (OpImm ALU_ADD 19 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f1c : bv 32 := 0x0aa4f463.
Lemma F_52f1c : fetch_word Asan.M.loaded_segments (0x52f6c : word) = Some W_52f1c.
Proof. vm_refl. Qed.
Lemma D_52f1c : decode_any W_52f1c = Some (Branch BC_GEU 9 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f20 : bv 32 := 0x00800593.
Lemma F_52f20 : fetch_word Asan.M.loaded_segments (0x52f70 : word) = Some W_52f20.
Proof. vm_refl. Qed.
Lemma D_52f20 : decode_any W_52f20 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f24 : bv 32 := 0x000a8513.
Lemma F_52f24 : fetch_word Asan.M.loaded_segments (0x52f74 : word) = Some W_52f24.
Proof. vm_refl. Qed.
Lemma D_52f24 : decode_any W_52f24 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f28 : bv 32 := 0x0155e463.
Lemma F_52f28 : fetch_word Asan.M.loaded_segments (0x52f78 : word) = Some W_52f28.
Proof. vm_refl. Qed.
Lemma D_52f28 : decode_any W_52f28 = Some (Branch BC_LTU 11 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f2c : bv 32 := 0x00800513.
Lemma F_52f2c : fetch_word Asan.M.loaded_segments (0x52f7c : word) = Some W_52f2c.
Proof. vm_refl. Qed.
Lemma D_52f2c : decode_any W_52f2c = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f30 : bv 32 := 0x00850533.
Lemma F_52f30 : fetch_word Asan.M.loaded_segments (0x52f80 : word) = Some W_52f30.
Proof. vm_refl. Qed.
Lemma D_52f30 : decode_any W_52f30 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f34 : bv 32 := 0x40800c33.
Lemma F_52f34 : fetch_word Asan.M.loaded_segments (0x52f84 : word) = Some W_52f34.
Proof. vm_refl. Qed.
Lemma D_52f34 : decode_any W_52f34 = Some (Op ALU_SUB 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f38 : bv 32 := 0x00993593.
Lemma F_52f38 : fetch_word Asan.M.loaded_segments (0x52f88 : word) = Some W_52f38.
Proof. vm_refl. Qed.
Lemma D_52f38 : decode_any W_52f38 = Some (OpImm ALU_SLTU 11 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f3c : bv 32 := 0xfff50513.
Lemma F_52f3c : fetch_word Asan.M.loaded_segments (0x52f8c : word) = Some W_52f3c.
Proof. vm_refl. Qed.
Lemma D_52f3c : decode_any W_52f3c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f40 : bv 32 := 0xfff58593.
Lemma F_52f40 : fetch_word Asan.M.loaded_segments (0x52f90 : word) = Some W_52f40.
Proof. vm_refl. Qed.
Lemma D_52f40 : decode_any W_52f40 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f44 : bv 32 := 0x01857533.
Lemma F_52f44 : fetch_word Asan.M.loaded_segments (0x52f94 : word) = Some W_52f44.
Proof. vm_refl. Qed.
Lemma D_52f44 : decode_any W_52f44 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f48 : bv 32 := 0x0085f5b3.
Lemma F_52f48 : fetch_word Asan.M.loaded_segments (0x52f98 : word) = Some W_52f48.
Proof. vm_refl. Qed.
Lemma D_52f48 : decode_any W_52f48 = Some (Op ALU_AND 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f4c : bv 32 := 0x00b50533.
Lemma F_52f4c : fetch_word Asan.M.loaded_segments (0x52f9c : word) = Some W_52f4c.
Proof. vm_refl. Qed.
Lemma D_52f4c : decode_any W_52f4c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f50 : bv 32 := 0x00757593.
Lemma F_52f50 : fetch_word Asan.M.loaded_segments (0x52fa0 : word) = Some W_52f50.
Proof. vm_refl. Qed.
Lemma D_52f50 : decode_any W_52f50 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f54 : bv 32 := 0x6a059063.
Lemma F_52f54 : fetch_word Asan.M.loaded_segments (0x52fa4 : word) = Some W_52f54.
Proof. vm_refl. Qed.
Lemma D_52f54 : decode_any W_52f54 = Some (Branch BC_NE 11 0 1696, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f58 : bv 32 := 0x01000593.
Lemma F_52f58 : fetch_word Asan.M.loaded_segments (0x52fa8 : word) = Some W_52f58.
Proof. vm_refl. Qed.
Lemma D_52f58 : decode_any W_52f58 = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f5c : bv 32 := 0x001ab493.
Lemma F_52f5c : fetch_word Asan.M.loaded_segments (0x52fac : word) = Some W_52f5c.
Proof. vm_refl. Qed.
Lemma D_52f5c : decode_any W_52f5c = Some (OpImm ALU_SLTU 9 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f60 : bv 32 := 0x001a061b.
Lemma F_52f60 : fetch_word Asan.M.loaded_segments (0x52fb0 : word) = Some W_52f60.
Proof. vm_refl. Qed.
Lemma D_52f60 : decode_any W_52f60 = Some (OpImm32 12 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f64 : bv 32 := 0x01359a3b.
Lemma F_52f64 : fetch_word Asan.M.loaded_segments (0x52fb4 : word) = Some W_52f64.
Proof. vm_refl. Qed.
Lemma D_52f64 : decode_any W_52f64 = Some (Op32 ALU_SLL 20 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f68 : bv 32 := 0x00100593.
Lemma F_52f68 : fetch_word Asan.M.loaded_segments (0x52fb8 : word) = Some W_52f68.
Proof. vm_refl. Qed.
Lemma D_52f68 : decode_any W_52f68 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f6c : bv 32 := 0x009a84b3.
Lemma F_52f6c : fetch_word Asan.M.loaded_segments (0x52fbc : word) = Some W_52f6c.
Proof. vm_refl. Qed.
Lemma D_52f6c : decode_any W_52f6c = Some (Op ALU_ADD 9 21 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f70 : bv 32 := 0x00c936b3.
Lemma F_52f70 : fetch_word Asan.M.loaded_segments (0x52fc0 : word) = Some W_52f70.
Proof. vm_refl. Qed.
Lemma D_52f70 : decode_any W_52f70 = Some (Op ALU_SLTU 13 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f74 : bv 32 := 0x014509b3.
Lemma F_52f74 : fetch_word Asan.M.loaded_segments (0x52fc4 : word) = Some W_52f74.
Proof. vm_refl. Qed.
Lemma D_52f74 : decode_any W_52f74 = Some (Op ALU_ADD 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f78 : bv 32 := 0x00c9b433.
Lemma F_52f78 : fetch_word Asan.M.loaded_segments (0x52fc8 : word) = Some W_52f78.
Proof. vm_refl. Qed.
Lemma D_52f78 : decode_any W_52f78 = Some (Op ALU_SLTU 8 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f7c : bv 32 := 0x0086f433.
Lemma F_52f7c : fetch_word Asan.M.loaded_segments (0x52fcc : word) = Some W_52f7c.
Proof. vm_refl. Qed.
Lemma D_52f7c : decode_any W_52f7c = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f80 : bv 32 := 0xfff40513.
Lemma F_52f80 : fetch_word Asan.M.loaded_segments (0x52fd0 : word) = Some W_52f80.
Proof. vm_refl. Qed.
Lemma D_52f80 : decode_any W_52f80 = Some (OpImm ALU_ADD 10 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f84 : bv 32 := 0x01457633.
Lemma F_52f84 : fetch_word Asan.M.loaded_segments (0x52fd4 : word) = Some W_52f84.
Proof. vm_refl. Qed.
Lemma D_52f84 : decode_any W_52f84 = Some (Op ALU_AND 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f88 : bv 32 := 0x02859513.
Lemma F_52f88 : fetch_word Asan.M.loaded_segments (0x52fd8 : word) = Some W_52f88.
Proof. vm_refl. Qed.
Lemma D_52f88 : decode_any W_52f88 = Some (ShiftImm ALU_SLL 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f8c : bv 32 := 0x013609b3.
Lemma F_52f8c : fetch_word Asan.M.loaded_segments (0x52fdc : word) = Some W_52f8c.
Proof. vm_refl. Qed.
Lemma D_52f8c : decode_any W_52f8c = Some (Op ALU_ADD 19 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f90 : bv 32 := 0x01556863.
Lemma F_52f90 : fetch_word Asan.M.loaded_segments (0x52fe0 : word) = Some W_52f90.
Proof. vm_refl. Qed.
Lemma D_52f90 : decode_any W_52f90 = Some (Branch BC_LTU 10 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f94 : bv 32 := 0x01356663.
Lemma F_52f94 : fetch_word Asan.M.loaded_segments (0x52fe4 : word) = Some W_52f94.
Proof. vm_refl. Qed.
Lemma D_52f94 : decode_any W_52f94 = Some (Branch BC_LTU 10 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f98 : bv 32 := 0x621d3503.
Lemma F_52f98 : fetch_word Asan.M.loaded_segments (0x52fe8 : word) = Some W_52f98.
Proof. vm_refl. Qed.
Lemma D_52f98 : decode_any W_52f98 = Some (Load SZ8 true 10 26 1569, 4%Z).
Proof. vm_refl. Qed.

Definition W_52f9c : bv 32 := 0x06957063.
Lemma F_52f9c : fetch_word Asan.M.loaded_segments (0x52fec : word) = Some W_52f9c.
Proof. vm_refl. Qed.
Lemma D_52f9c : decode_any W_52f9c = Some (Branch BC_GEU 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fc0 : bv 32 := 0xf6a9e0e3.
Lemma F_52fc0 : fetch_word Asan.M.loaded_segments (0x53010 : word) = Some W_52fc0.
Proof. vm_refl. Qed.
Lemma D_52fc0 : decode_any W_52fc0 = Some (Branch BC_LTU 19 10 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fc4 : bv 32 := 0x00050993.
Lemma F_52fc4 : fetch_word Asan.M.loaded_segments (0x53014 : word) = Some W_52fc4.
Proof. vm_refl. Qed.
Lemma D_52fc4 : decode_any W_52fc4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fc8 : bv 32 := 0x00800593.
Lemma F_52fc8 : fetch_word Asan.M.loaded_segments (0x53018 : word) = Some W_52fc8.
Proof. vm_refl. Qed.
Lemma D_52fc8 : decode_any W_52fc8 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fcc : bv 32 := 0x000a8513.
Lemma F_52fcc : fetch_word Asan.M.loaded_segments (0x5301c : word) = Some W_52fcc.
Proof. vm_refl. Qed.
Lemma D_52fcc : decode_any W_52fcc = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fd0 : bv 32 := 0xf555fee3.
Lemma F_52fd0 : fetch_word Asan.M.loaded_segments (0x53020 : word) = Some W_52fd0.
Proof. vm_refl. Qed.
Lemma D_52fd0 : decode_any W_52fd0 = Some (Branch BC_GEU 11 21 8028, 4%Z).
Proof. vm_refl. Qed.

Definition W_52fd4 : bv 32 := 0xf5dff06f.
Lemma F_52fd4 : fetch_word Asan.M.loaded_segments (0x53024 : word) = Some W_52fd4.
Proof. vm_refl. Qed.
Lemma D_52fd4 : decode_any W_52fd4 = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ffc : bv 32 := 0x21c310ef.
Lemma F_52ffc : fetch_word Asan.M.loaded_segments (0x5304c : word) = Some W_52ffc.
Proof. vm_refl. Qed.
Lemma D_52ffc : decode_any W_52ffc = Some (Jal 1 201244, 4%Z).
Proof. vm_refl. Qed.

Definition W_53000 : bv 32 := 0x00050d13.
Lemma F_53000 : fetch_word Asan.M.loaded_segments (0x53050 : word) = Some W_53000.
Proof. vm_refl. Qed.
Lemma D_53000 : decode_any W_53000 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53004 : bv 32 := 0x08050863.
Lemma F_53004 : fetch_word Asan.M.loaded_segments (0x53054 : word) = Some W_53004.
Proof. vm_refl. Qed.
Lemma D_53004 : decode_any W_53004 = Some (Branch BC_EQ 10 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_53008 : bv 32 := 0x0d0d0593.
Lemma F_53008 : fetch_word Asan.M.loaded_segments (0x53058 : word) = Some W_53008.
Proof. vm_refl. Qed.
Lemma D_53008 : decode_any W_53008 = Some (OpImm ALU_ADD 11 26 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_5300c : bv 32 := 0x00800693.
Lemma F_5300c : fetch_word Asan.M.loaded_segments (0x5305c : word) = Some W_5300c.
Proof. vm_refl. Qed.
Lemma D_5300c : decode_any W_5300c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53010 : bv 32 := 0x000b0513.
Lemma F_53010 : fetch_word Asan.M.loaded_segments (0x53060 : word) = Some W_53010.
Proof. vm_refl. Qed.
Lemma D_53010 : decode_any W_53010 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53014 : bv 32 := 0x00098613.
Lemma F_53014 : fetch_word Asan.M.loaded_segments (0x53064 : word) = Some W_53014.
Proof. vm_refl. Qed.
Lemma D_53014 : decode_any W_53014 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53018 : bv 32 := 0x4bc040ef.
Lemma F_53018 : fetch_word Asan.M.loaded_segments (0x53068 : word) = Some W_53018.
Proof. vm_refl. Qed.
Lemma D_53018 : decode_any W_53018 = Some (Jal 1 17596, 4%Z).
Proof. vm_refl. Qed.

Definition W_5301c : bv 32 := 0x00050913.
Lemma F_5301c : fetch_word Asan.M.loaded_segments (0x5306c : word) = Some W_5301c.
Proof. vm_refl. Qed.
Lemma D_5301c : decode_any W_5301c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53020 : bv 32 := 0x0c050663.
Lemma F_53020 : fetch_word Asan.M.loaded_segments (0x53070 : word) = Some W_53020.
Proof. vm_refl. Qed.
Lemma D_53020 : decode_any W_53020 = Some (Branch BC_EQ 10 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_53024 : bv 32 := 0x01490a33.
Lemma F_53024 : fetch_word Asan.M.loaded_segments (0x53074 : word) = Some W_53024.
Proof. vm_refl. Qed.
Lemma D_53024 : decode_any W_53024 = Some (Op ALU_ADD 20 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_53028 : bv 32 := 0x019a7533.
Lemma F_53028 : fetch_word Asan.M.loaded_segments (0x53078 : word) = Some W_53028.
Proof. vm_refl. Qed.
Lemma D_53028 : decode_any W_53028 = Some (Op ALU_AND 10 20 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_5302c : bv 32 := 0x01298733.
Lemma F_5302c : fetch_word Asan.M.loaded_segments (0x5307c : word) = Some W_5302c.
Proof. vm_refl. Qed.
Lemma D_5302c : decode_any W_5302c = Some (Op ALU_ADD 14 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_53030 : bv 32 := 0x00050663.
Lemma F_53030 : fetch_word Asan.M.loaded_segments (0x53080 : word) = Some W_53030.
Proof. vm_refl. Qed.
Lemma D_53030 : decode_any W_53030 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5303c : bv 32 := 0x009a0cb3.
Lemma F_5303c : fetch_word Asan.M.loaded_segments (0x5308c : word) = Some W_5303c.
Proof. vm_refl. Qed.
Lemma D_5303c : decode_any W_5303c = Some (Op ALU_ADD 25 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_53040 : bv 32 := 0x5d976a63.
Lemma F_53040 : fetch_word Asan.M.loaded_segments (0x53090 : word) = Some W_53040.
Proof. vm_refl. Qed.
Lemma D_53040 : decode_any W_53040 = Some (Branch BC_LTU 14 25 1492, 4%Z).
Proof. vm_refl. Qed.

Definition W_53044 : bv 32 := 0xff1a4503.
Lemma F_53044 : fetch_word Asan.M.loaded_segments (0x53094 : word) = Some W_53044.
Proof. vm_refl. Qed.
Lemma D_53044 : decode_any W_53044 = Some (Load SZ1 false 10 20 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_53048 : bv 32 := 0x003df593.
Lemma F_53048 : fetch_word Asan.M.loaded_segments (0x53098 : word) = Some W_53048.
Proof. vm_refl. Qed.
Lemma D_53048 : decode_any W_53048 = Some (OpImm ALU_AND 11 27 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5304c : bv 32 := 0xffc57513.
Lemma F_5304c : fetch_word Asan.M.loaded_segments (0x5309c : word) = Some W_5304c.
Proof. vm_refl. Qed.
Lemma D_5304c : decode_any W_5304c = Some (OpImm ALU_AND 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_53050 : bv 32 := 0x00b56533.
Lemma F_53050 : fetch_word Asan.M.loaded_segments (0x530a0 : word) = Some W_53050.
Proof. vm_refl. Qed.
Lemma D_53050 : decode_any W_53050 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_53054 : bv 32 := 0x0204d593.
Lemma F_53054 : fetch_word Asan.M.loaded_segments (0x530a4 : word) = Some W_53054.
Proof. vm_refl. Qed.
Lemma D_53054 : decode_any W_53054 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_53058 : bv 32 := 0x030ad613.
Lemma F_53058 : fetch_word Asan.M.loaded_segments (0x530a8 : word) = Some W_53058.
Proof. vm_refl. Qed.
Lemma D_53058 : decode_any W_53058 = Some (ShiftImm ALU_SRL 12 21 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5305c : bv 32 := 0xfeaa08a3.
Lemma F_5305c : fetch_word Asan.M.loaded_segments (0x530ac : word) = Some W_5305c.
Proof. vm_refl. Qed.
Lemma D_5305c : decode_any W_5305c = Some (Store SZ1 20 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_53060 : bv 32 := 0xfeba1923.
Lemma F_53060 : fetch_word Asan.M.loaded_segments (0x530b0 : word) = Some W_53060.
Proof. vm_refl. Qed.
Lemma D_53060 : decode_any W_53060 = Some (Store SZ2 20 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_53064 : bv 32 := 0xfe9a2a23.
Lemma F_53064 : fetch_word Asan.M.loaded_segments (0x530b4 : word) = Some W_53064.
Proof. vm_refl. Qed.
Lemma D_53064 : decode_any W_53064 = Some (Store SZ4 20 9 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_53068 : bv 32 := 0x5c061463.
Lemma F_53068 : fetch_word Asan.M.loaded_segments (0x530b8 : word) = Some W_53068.
Proof. vm_refl. Qed.
Lemma D_53068 : decode_any W_53068 = Some (Branch BC_NE 12 0 1480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5306c : bv 32 := 0xff0a0a93.
Lemma F_5306c : fetch_word Asan.M.loaded_segments (0x530bc : word) = Some W_5306c.
Proof. vm_refl. Qed.
Lemma D_5306c : decode_any W_5306c = Some (OpImm ALU_ADD 21 20 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_53070 : bv 32 := 0x08f57513.
Lemma F_53070 : fetch_word Asan.M.loaded_segments (0x530c0 : word) = Some W_53070.
Proof. vm_refl. Qed.
Lemma D_53070 : decode_any W_53070 = Some (OpImm ALU_AND 10 10 143, 4%Z).
Proof. vm_refl. Qed.

Definition W_53074 : bv 32 := 0x01013583.
Lemma F_53074 : fetch_word Asan.M.loaded_segments (0x530c4 : word) = Some W_53074.
Proof. vm_refl. Qed.
Lemma D_53074 : decode_any W_53074 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53078 : bv 32 := 0x00b56533.
Lemma F_53078 : fetch_word Asan.M.loaded_segments (0x530c8 : word) = Some W_53078.
Proof. vm_refl. Qed.
Lemma D_53078 : decode_any W_53078 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5307c : bv 32 := 0x00aa80a3.
Lemma F_5307c : fetch_word Asan.M.loaded_segments (0x530cc : word) = Some W_5307c.
Proof. vm_refl. Qed.
Lemma D_5307c : decode_any W_5307c = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_53080 : bv 32 := 0x080d0c63.
Lemma F_53080 : fetch_word Asan.M.loaded_segments (0x530d0 : word) = Some W_53080.
Proof. vm_refl. Qed.
Lemma D_53080 : decode_any W_53080 = Some (Branch BC_EQ 26 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_53084 : bv 32 := 0x000d3503.
Lemma F_53084 : fetch_word Asan.M.loaded_segments (0x530d4 : word) = Some W_53084.
Proof. vm_refl. Qed.
Lemma D_53084 : decode_any W_53084 = Some (Load SZ8 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53088 : bv 32 := 0x00852c03.
Lemma F_53088 : fetch_word Asan.M.loaded_segments (0x530d8 : word) = Some W_53088.
Proof. vm_refl. Qed.
Lemma D_53088 : decode_any W_53088 = Some (Load SZ4 true 24 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5308c : bv 32 := 0x020c1c13.
Lemma F_5308c : fetch_word Asan.M.loaded_segments (0x530dc : word) = Some W_5308c.
Proof. vm_refl. Qed.
Lemma D_5308c : decode_any W_5308c = Some (ShiftImm ALU_SLL 24 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_53090 : bv 32 := 0x08c0006f.
Lemma F_53090 : fetch_word Asan.M.loaded_segments (0x530e0 : word) = Some W_53090.
Proof. vm_refl. Qed.
Lemma D_53090 : decode_any W_53090 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_5311c : bv 32 := 0x000bb503.
Lemma F_5311c : fetch_word Asan.M.loaded_segments (0x5316c : word) = Some W_5311c.
Proof. vm_refl. Qed.
Lemma D_5311c : decode_any W_5311c = Some (Load SZ8 true 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53120 : bv 32 := 0x008bb583.
Lemma F_53120 : fetch_word Asan.M.loaded_segments (0x53170 : word) = Some W_53120.
Proof. vm_refl. Qed.
Lemma D_53120 : decode_any W_53120 = Some (Load SZ8 true 11 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53124 : bv 32 := 0x7d4470ef.
Lemma F_53124 : fetch_word Asan.M.loaded_segments (0x53174 : word) = Some W_53124.
Proof. vm_refl. Qed.
Lemma D_53124 : decode_any W_53124 = Some (Jal 1 292820, 4%Z).
Proof. vm_refl. Qed.

Definition W_53128 : bv 32 := 0x02051513.
Lemma F_53128 : fetch_word Asan.M.loaded_segments (0x53178 : word) = Some W_53128.
Proof. vm_refl. Qed.
Lemma D_53128 : decode_any W_53128 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5312c : bv 32 := 0x02055513.
Lemma F_5312c : fetch_word Asan.M.loaded_segments (0x5317c : word) = Some W_5312c.
Proof. vm_refl. Qed.
Lemma D_5312c : decode_any W_5312c = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_53130 : bv 32 := 0x00ac6533.
Lemma F_53130 : fetch_word Asan.M.loaded_segments (0x53180 : word) = Some W_53130.
Proof. vm_refl. Qed.
Lemma D_53130 : decode_any W_53130 = Some (Op ALU_OR 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_53134 : bv 32 := 0x00aab423.
Lemma F_53134 : fetch_word Asan.M.loaded_segments (0x53184 : word) = Some W_53134.
Proof. vm_refl. Qed.
Lemma D_53134 : decode_any W_53134 = Some (Store SZ8 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53138 : bv 32 := 0x02040063.
Lemma F_53138 : fetch_word Asan.M.loaded_segments (0x53188 : word) = Some W_53138.
Proof. vm_refl. Qed.
Lemma D_53138 : decode_any W_53138 = Some (Branch BC_EQ 8 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5313c : bv 32 := 0x000e6517.
Lemma F_5313c : fetch_word Asan.M.loaded_segments (0x5318c : word) = Some W_5313c.
Proof. vm_refl. Qed.
Lemma D_5313c : decode_any W_5313c = Some (Auipc 10 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_53140 : bv 32 := 0x02c53503.
Lemma F_53140 : fetch_word Asan.M.loaded_segments (0x53190 : word) = Some W_53140.
Proof. vm_refl. Qed.
Lemma D_53140 : decode_any W_53140 = Some (Load SZ8 true 10 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_53144 : bv 32 := 0x00053503.
Lemma F_53144 : fetch_word Asan.M.loaded_segments (0x53194 : word) = Some W_53144.
Proof. vm_refl. Qed.
Lemma D_53144 : decode_any W_53144 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53148 : bv 32 := 0x00395593.
Lemma F_53148 : fetch_word Asan.M.loaded_segments (0x53198 : word) = Some W_53148.
Proof. vm_refl. Qed.
Lemma D_53148 : decode_any W_53148 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5314c : bv 32 := 0x00b50533.
Lemma F_5314c : fetch_word Asan.M.loaded_segments (0x5319c : word) = Some W_5314c.
Proof. vm_refl. Qed.
Lemma D_5314c : decode_any W_5314c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_53150 : bv 32 := 0x00054503.
Lemma F_53150 : fetch_word Asan.M.loaded_segments (0x531a0 : word) = Some W_53150.
Proof. vm_refl. Qed.
Lemma D_53150 : decode_any W_53150 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53154 : bv 32 := 0x0c051063.
Lemma F_53154 : fetch_word Asan.M.loaded_segments (0x531a4 : word) = Some W_53154.
Proof. vm_refl. Qed.
Lemma D_53154 : decode_any W_53154 = Some (Branch BC_NE 10 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_53158 : bv 32 := 0x020b3503.
Lemma F_53158 : fetch_word Asan.M.loaded_segments (0x531a8 : word) = Some W_53158.
Proof. vm_refl. Qed.
Lemma D_53158 : decode_any W_53158 = Some (Load SZ8 true 10 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5315c : bv 32 := 0x02a96c63.
Lemma F_5315c : fetch_word Asan.M.loaded_segments (0x531ac : word) = Some W_5315c.
Proof. vm_refl. Qed.
Lemma D_5315c : decode_any W_5315c = Some (Branch BC_LTU 18 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_53160 : bv 32 := 0x00100593.
Lemma F_53160 : fetch_word Asan.M.loaded_segments (0x531b0 : word) = Some W_53160.
Proof. vm_refl. Qed.
Lemma D_53160 : decode_any W_53160 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_53164 : bv 32 := 0x02559593.
Lemma F_53164 : fetch_word Asan.M.loaded_segments (0x531b4 : word) = Some W_53164.
Proof. vm_refl. Qed.
Lemma D_53164 : decode_any W_53164 = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_53168 : bv 32 := 0x00b505b3.
Lemma F_53168 : fetch_word Asan.M.loaded_segments (0x531b8 : word) = Some W_53168.
Proof. vm_refl. Qed.
Lemma D_53168 : decode_any W_53168 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5316c : bv 32 := 0x02b97463.
Lemma F_5316c : fetch_word Asan.M.loaded_segments (0x531bc : word) = Some W_5316c.
Proof. vm_refl. Qed.
Lemma D_5316c : decode_any W_5316c = Some (Branch BC_GEU 18 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_53194 : bv 32 := 0x040b3503.
Lemma F_53194 : fetch_word Asan.M.loaded_segments (0x531e4 : word) = Some W_53194.
Proof. vm_refl. Qed.
Lemma D_53194 : decode_any W_53194 = Some (Load SZ8 true 10 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_53198 : bv 32 := 0xfff50593.
Lemma F_53198 : fetch_word Asan.M.loaded_segments (0x531e8 : word) = Some W_53198.
Proof. vm_refl. Qed.
Lemma D_53198 : decode_any W_53198 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5319c : bv 32 := 0x0125f633.
Lemma F_5319c : fetch_word Asan.M.loaded_segments (0x531ec : word) = Some W_5319c.
Proof. vm_refl. Qed.
Lemma D_5319c : decode_any W_5319c = Some (Op ALU_AND 12 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_531a0 : bv 32 := 0x52061663.
Lemma F_531a0 : fetch_word Asan.M.loaded_segments (0x531f0 : word) = Some W_531a0.
Proof. vm_refl. Qed.
Lemma D_531a0 : decode_any W_531a0 = Some (Branch BC_NE 12 0 1324, 4%Z).
Proof. vm_refl. Qed.

Definition W_531a4 : bv 32 := 0x00b57633.
Lemma F_531a4 : fetch_word Asan.M.loaded_segments (0x531f4 : word) = Some W_531a4.
Proof. vm_refl. Qed.
Lemma D_531a4 : decode_any W_531a4 = Some (Op ALU_AND 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_531a8 : bv 32 := 0x54061663.
Lemma F_531a8 : fetch_word Asan.M.loaded_segments (0x531f8 : word) = Some W_531a8.
Proof. vm_refl. Qed.
Lemma D_531a8 : decode_any W_531a8 = Some (Branch BC_NE 12 0 1356, 4%Z).
Proof. vm_refl. Qed.

Definition W_531ac : bv 32 := 0x40a90633.
Lemma F_531ac : fetch_word Asan.M.loaded_segments (0x531fc : word) = Some W_531ac.
Proof. vm_refl. Qed.
Lemma D_531ac : decode_any W_531ac = Some (Op ALU_SUB 12 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_531b0 : bv 32 := 0x01063603.
Lemma F_531b0 : fetch_word Asan.M.loaded_segments (0x53200 : word) = Some W_531b0.
Proof. vm_refl. Qed.
Lemma D_531b0 : decode_any W_531b0 = Some (Load SZ8 true 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_531b4 : bv 32 := 0x00b605b3.
Lemma F_531b4 : fetch_word Asan.M.loaded_segments (0x53204 : word) = Some W_531b4.
Proof. vm_refl. Qed.
Lemma D_531b4 : decode_any W_531b4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_531b8 : bv 32 := 0x40a00433.
Lemma F_531b8 : fetch_word Asan.M.loaded_segments (0x53208 : word) = Some W_531b8.
Proof. vm_refl. Qed.
Lemma D_531b8 : decode_any W_531b8 = Some (Op ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_531bc : bv 32 := 0x0085f433.
Lemma F_531bc : fetch_word Asan.M.loaded_segments (0x5320c : word) = Some W_531bc.
Proof. vm_refl. Qed.
Lemma D_531bc : decode_any W_531bc = Some (Op ALU_AND 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_531c0 : bv 32 := 0x0280006f.
Lemma F_531c0 : fetch_word Asan.M.loaded_segments (0x53210 : word) = Some W_531c0.
Proof. vm_refl. Qed.
Lemma D_531c0 : decode_any W_531c0 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_531e8 : bv 32 := 0x007c8c93.
Lemma F_531e8 : fetch_word Asan.M.loaded_segments (0x53238 : word) = Some W_531e8.
Proof. vm_refl. Qed.
Lemma D_531e8 : decode_any W_531e8 = Some (OpImm ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_531ec : bv 32 := 0xff8cfb13.
Lemma F_531ec : fetch_word Asan.M.loaded_segments (0x5323c : word) = Some W_531ec.
Proof. vm_refl. Qed.
Lemma D_531ec : decode_any W_531ec = Some (OpImm ALU_AND 22 25 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_531f0 : bv 32 := 0x412a05b3.
Lemma F_531f0 : fetch_word Asan.M.loaded_segments (0x53240 : word) = Some W_531f0.
Proof. vm_refl. Qed.
Lemma D_531f0 : decode_any W_531f0 = Some (Op ALU_SUB 11 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_531f4 : bv 32 := 0x0fa00613.
Lemma F_531f4 : fetch_word Asan.M.loaded_segments (0x53244 : word) = Some W_531f4.
Proof. vm_refl. Qed.
Lemma D_531f4 : decode_any W_531f4 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_531f8 : bv 32 := 0x00090513.
Lemma F_531f8 : fetch_word Asan.M.loaded_segments (0x53248 : word) = Some W_531f8.
Proof. vm_refl. Qed.
Lemma D_531f8 : decode_any W_531f8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_531fc : bv 32 := 0x270280ef.
Lemma F_531fc : fetch_word Asan.M.loaded_segments (0x5324c : word) = Some W_531fc.
Proof. vm_refl. Qed.
Lemma D_531fc : decode_any W_531fc = Some (Jal 1 164464, 4%Z).
Proof. vm_refl. Qed.

Definition W_53200 : bv 32 := 0x416905b3.
Lemma F_53200 : fetch_word Asan.M.loaded_segments (0x53250 : word) = Some W_53200.
Proof. vm_refl. Qed.
Lemma D_53200 : decode_any W_53200 = Some (Op ALU_SUB 11 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_53204 : bv 32 := 0x008585b3.
Lemma F_53204 : fetch_word Asan.M.loaded_segments (0x53254 : word) = Some W_53204.
Proof. vm_refl. Qed.
Lemma D_53204 : decode_any W_53204 = Some (Op ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53208 : bv 32 := 0x0fa00613.
Lemma F_53208 : fetch_word Asan.M.loaded_segments (0x53258 : word) = Some W_53208.
Proof. vm_refl. Qed.
Lemma D_53208 : decode_any W_53208 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5320c : bv 32 := 0x000b0513.
Lemma F_5320c : fetch_word Asan.M.loaded_segments (0x5325c : word) = Some W_5320c.
Proof. vm_refl. Qed.
Lemma D_5320c : decode_any W_5320c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53210 : bv 32 := 0x25c280ef.
Lemma F_53210 : fetch_word Asan.M.loaded_segments (0x53260 : word) = Some W_53210.
Proof. vm_refl. Qed.
Lemma D_53210 : decode_any W_53210 = Some (Jal 1 164444, 4%Z).
Proof. vm_refl. Qed.

Definition W_53214 : bv 32 := 0xfff80537.
Lemma F_53214 : fetch_word Asan.M.loaded_segments (0x53264 : word) = Some W_53214.
Proof. vm_refl. Qed.
Lemma D_53214 : decode_any W_53214 = Some (Lui 10 1048448, 4%Z).
Proof. vm_refl. Qed.

Definition W_53218 : bv 32 := 0x01055513.
Lemma F_53218 : fetch_word Asan.M.loaded_segments (0x53268 : word) = Some W_53218.
Proof. vm_refl. Qed.
Lemma D_53218 : decode_any W_53218 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5321c : bv 32 := 0x00a4fb33.
Lemma F_5321c : fetch_word Asan.M.loaded_segments (0x5326c : word) = Some W_5321c.
Proof. vm_refl. Qed.
Lemma D_5321c : decode_any W_5321c = Some (Op ALU_AND 22 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_53220 : bv 32 := 0x000b0a63.
Lemma F_53220 : fetch_word Asan.M.loaded_segments (0x53270 : word) = Some W_53220.
Proof. vm_refl. Qed.
Lemma D_53220 : decode_any W_53220 = Some (Branch BC_EQ 22 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_53224 : bv 32 := 0x000a0513.
Lemma F_53224 : fetch_word Asan.M.loaded_segments (0x53274 : word) = Some W_53224.
Proof. vm_refl. Qed.
Lemma D_53224 : decode_any W_53224 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53228 : bv 32 := 0x000b0593.
Lemma F_53228 : fetch_word Asan.M.loaded_segments (0x53278 : word) = Some W_53228.
Proof. vm_refl. Qed.
Lemma D_53228 : decode_any W_53228 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5322c : bv 32 := 0x00000613.
Lemma F_5322c : fetch_word Asan.M.loaded_segments (0x5327c : word) = Some W_5322c.
Proof. vm_refl. Qed.
Lemma D_5322c : decode_any W_5322c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53230 : bv 32 := 0x23c280ef.
Lemma F_53230 : fetch_word Asan.M.loaded_segments (0x53280 : word) = Some W_53230.
Proof. vm_refl. Qed.
Lemma D_53230 : decode_any W_53230 = Some (Jal 1 164412, 4%Z).
Proof. vm_refl. Qed.

Definition W_53234 : bv 32 := 0x09648a63.
Lemma F_53234 : fetch_word Asan.M.loaded_segments (0x53284 : word) = Some W_53234.
Proof. vm_refl. Qed.
Lemma D_53234 : decode_any W_53234 = Some (Branch BC_EQ 9 22 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_53238 : bv 32 := 0x220280ef.
Lemma F_53238 : fetch_word Asan.M.loaded_segments (0x53288 : word) = Some W_53238.
Proof. vm_refl. Qed.
Lemma D_53238 : decode_any W_53238 = Some (Jal 1 164384, 4%Z).
Proof. vm_refl. Qed.

Definition W_5323c : bv 32 := 0x08050663.
Lemma F_5323c : fetch_word Asan.M.loaded_segments (0x5328c : word) = Some W_5323c.
Proof. vm_refl. Qed.
Lemma D_5323c : decode_any W_5323c = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_53240 : bv 32 := 0x000e6517.
Lemma F_53240 : fetch_word Asan.M.loaded_segments (0x53290 : word) = Some W_53240.
Proof. vm_refl. Qed.
Lemma D_53240 : decode_any W_53240 = Some (Auipc 10 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_53244 : bv 32 := 0xf2853503.
Lemma F_53244 : fetch_word Asan.M.loaded_segments (0x53294 : word) = Some W_53244.
Proof. vm_refl. Qed.
Lemma D_53244 : decode_any W_53244 = Some (Load SZ8 true 10 10 3880, 4%Z).
Proof. vm_refl. Qed.

Definition W_53248 : bv 32 := 0x00053503.
Lemma F_53248 : fetch_word Asan.M.loaded_segments (0x53298 : word) = Some W_53248.
Proof. vm_refl. Qed.
Lemma D_53248 : decode_any W_53248 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5324c : bv 32 := 0x016a0b33.
Lemma F_5324c : fetch_word Asan.M.loaded_segments (0x5329c : word) = Some W_5324c.
Proof. vm_refl. Qed.
Lemma D_5324c : decode_any W_5324c = Some (Op ALU_ADD 22 20 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_53250 : bv 32 := 0xfff50593.
Lemma F_53250 : fetch_word Asan.M.loaded_segments (0x532a0 : word) = Some W_53250.
Proof. vm_refl. Qed.
Lemma D_53250 : decode_any W_53250 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_53254 : bv 32 := 0x00b53633.
Lemma F_53254 : fetch_word Asan.M.loaded_segments (0x532a4 : word) = Some W_53254.
Proof. vm_refl. Qed.
Lemma D_53254 : decode_any W_53254 = Some (Op ALU_SLTU 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_53258 : bv 32 := 0xfff60613.
Lemma F_53258 : fetch_word Asan.M.loaded_segments (0x532a8 : word) = Some W_53258.
Proof. vm_refl. Qed.
Lemma D_53258 : decode_any W_53258 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5325c : bv 32 := 0x00b67633.
Lemma F_5325c : fetch_word Asan.M.loaded_segments (0x532ac : word) = Some W_5325c.
Proof. vm_refl. Qed.
Lemma D_5325c : decode_any W_5325c = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_53260 : bv 32 := 0x05667263.
Lemma F_53260 : fetch_word Asan.M.loaded_segments (0x532b0 : word) = Some W_53260.
Proof. vm_refl. Qed.
Lemma D_53260 : decode_any W_53260 = Some (Branch BC_GEU 12 22 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_53264 : bv 32 := 0x000e6617.
Lemma F_53264 : fetch_word Asan.M.loaded_segments (0x532b4 : word) = Some W_53264.
Proof. vm_refl. Qed.
Lemma D_53264 : decode_any W_53264 = Some (Auipc 12 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_53268 : bv 32 := 0xf0c63603.
Lemma F_53268 : fetch_word Asan.M.loaded_segments (0x532b8 : word) = Some W_53268.
Proof. vm_refl. Qed.
Lemma D_53268 : decode_any W_53268 = Some (Load SZ8 true 12 12 3852, 4%Z).
Proof. vm_refl. Qed.

Definition W_5326c : bv 32 := 0x000e6697.
Lemma F_5326c : fetch_word Asan.M.loaded_segments (0x532bc : word) = Some W_5326c.
Proof. vm_refl. Qed.
Lemma D_5326c : decode_any W_5326c = Some (Auipc 13 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_53270 : bv 32 := 0xf0c6b683.
Lemma F_53270 : fetch_word Asan.M.loaded_segments (0x532c0 : word) = Some W_53270.
Proof. vm_refl. Qed.
Lemma D_53270 : decode_any W_53270 = Some (Load SZ8 true 13 13 3852, 4%Z).
Proof. vm_refl. Qed.

Definition W_53274 : bv 32 := 0x00063783.
Lemma F_53274 : fetch_word Asan.M.loaded_segments (0x532c4 : word) = Some W_53274.
Proof. vm_refl. Qed.
Lemma D_53274 : decode_any W_53274 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53278 : bv 32 := 0x0006b603.
Lemma F_53278 : fetch_word Asan.M.loaded_segments (0x532c8 : word) = Some W_53278.
Proof. vm_refl. Qed.
Lemma D_53278 : decode_any W_53278 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5327c : bv 32 := 0xfff78713.
Lemma F_5327c : fetch_word Asan.M.loaded_segments (0x532cc : word) = Some W_5327c.
Proof. vm_refl. Qed.
Lemma D_5327c : decode_any W_5327c = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_53280 : bv 32 := 0x01677463.
Lemma F_53280 : fetch_word Asan.M.loaded_segments (0x532d0 : word) = Some W_53280.
Proof. vm_refl. Qed.
Lemma D_53280 : decode_any W_53280 = Some (Branch BC_GEU 14 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53288 : bv 32 := 0x000e6697.
Lemma F_53288 : fetch_word Asan.M.loaded_segments (0x532d8 : word) = Some W_53288.
Proof. vm_refl. Qed.
Lemma D_53288 : decode_any W_53288 = Some (Auipc 13 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_5328c : bv 32 := 0xef86b683.
Lemma F_5328c : fetch_word Asan.M.loaded_segments (0x532dc : word) = Some W_5328c.
Proof. vm_refl. Qed.
Lemma D_5328c : decode_any W_5328c = Some (Load SZ8 true 13 13 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_53290 : bv 32 := 0x0006b883.
Lemma F_53290 : fetch_word Asan.M.loaded_segments (0x532e0 : word) = Some W_53290.
Proof. vm_refl. Qed.
Lemma D_53290 : decode_any W_53290 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53294 : bv 32 := 0x0038d693.
Lemma F_53294 : fetch_word Asan.M.loaded_segments (0x532e4 : word) = Some W_53294.
Proof. vm_refl. Qed.
Lemma D_53294 : decode_any W_53294 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_53298 : bv 32 := 0x00a68833.
Lemma F_53298 : fetch_word Asan.M.loaded_segments (0x532e8 : word) = Some W_53298.
Proof. vm_refl. Qed.
Lemma D_53298 : decode_any W_53298 = Some (Op ALU_ADD 16 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5329c : bv 32 := 0x2568ea63.
Lemma F_5329c : fetch_word Asan.M.loaded_segments (0x532ec : word) = Some W_5329c.
Proof. vm_refl. Qed.
Lemma D_5329c : decode_any W_5329c = Some (Branch BC_LTU 17 22 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_532a0 : bv 32 := 0x25687863.
Lemma F_532a0 : fetch_word Asan.M.loaded_segments (0x532f0 : word) = Some W_532a0.
Proof. vm_refl. Qed.
Lemma D_532a0 : decode_any W_532a0 = Some (Branch BC_GEU 16 22 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_532a4 : bv 32 := 0x000e6597.
Lemma F_532a4 : fetch_word Asan.M.loaded_segments (0x532f4 : word) = Some W_532a4.
Proof. vm_refl. Qed.
Lemma D_532a4 : decode_any W_532a4 = Some (Auipc 11 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_532a8 : bv 32 := 0xebc5b583.
Lemma F_532a8 : fetch_word Asan.M.loaded_segments (0x532f8 : word) = Some W_532a8.
Proof. vm_refl. Qed.
Lemma D_532a8 : decode_any W_532a8 = Some (Load SZ8 true 11 11 3772, 4%Z).
Proof. vm_refl. Qed.

Definition W_532ac : bv 32 := 0x0555c583.
Lemma F_532ac : fetch_word Asan.M.loaded_segments (0x532fc : word) = Some W_532ac.
Proof. vm_refl. Qed.
Lemma D_532ac : decode_any W_532ac = Some (Load SZ1 false 11 11 85, 4%Z).
Proof. vm_refl. Qed.

Definition W_532b0 : bv 32 := 0x003b5613.
Lemma F_532b0 : fetch_word Asan.M.loaded_segments (0x53300 : word) = Some W_532b0.
Proof. vm_refl. Qed.
Lemma D_532b0 : decode_any W_532b0 = Some (ShiftImm ALU_SRL 12 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_532b4 : bv 32 := 0x00c50533.
Lemma F_532b4 : fetch_word Asan.M.loaded_segments (0x53304 : word) = Some W_532b4.
Proof. vm_refl. Qed.
Lemma D_532b4 : decode_any W_532b4 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_532b8 : bv 32 := 0x40b005bb.
Lemma F_532b8 : fetch_word Asan.M.loaded_segments (0x53308 : word) = Some W_532b8.
Proof. vm_refl. Qed.
Lemma D_532b8 : decode_any W_532b8 = Some (Op32 ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_532bc : bv 32 := 0x00b4f5b3.
Lemma F_532bc : fetch_word Asan.M.loaded_segments (0x5330c : word) = Some W_532bc.
Proof. vm_refl. Qed.
Lemma D_532bc : decode_any W_532bc = Some (Op ALU_AND 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_532c0 : bv 32 := 0x0075f593.
Lemma F_532c0 : fetch_word Asan.M.loaded_segments (0x53310 : word) = Some W_532c0.
Proof. vm_refl. Qed.
Lemma D_532c0 : decode_any W_532c0 = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_532c4 : bv 32 := 0x00b50023.
Lemma F_532c4 : fetch_word Asan.M.loaded_segments (0x53314 : word) = Some W_532c4.
Proof. vm_refl. Qed.
Lemma D_532c4 : decode_any W_532c4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_532c8 : bv 32 := 0x11c300ef.
Lemma F_532c8 : fetch_word Asan.M.loaded_segments (0x53318 : word) = Some W_532c8.
Proof. vm_refl. Qed.
Lemma D_532c8 : decode_any W_532c8 = Some (Jal 1 196892, 4%Z).
Proof. vm_refl. Qed.

Definition W_532cc : bv 32 := 0x01053583.
Lemma F_532cc : fetch_word Asan.M.loaded_segments (0x5331c : word) = Some W_532cc.
Proof. vm_refl. Qed.
Lemma D_532cc : decode_any W_532cc = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_532d0 : bv 32 := 0x00053603.
Lemma F_532d0 : fetch_word Asan.M.loaded_segments (0x53320 : word) = Some W_532d0.
Proof. vm_refl. Qed.
Lemma D_532d0 : decode_any W_532d0 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_532d4 : bv 32 := 0x00853683.
Lemma F_532d4 : fetch_word Asan.M.loaded_segments (0x53324 : word) = Some W_532d4.
Proof. vm_refl. Qed.
Lemma D_532d4 : decode_any W_532d4 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_532d8 : bv 32 := 0x40998733.
Lemma F_532d8 : fetch_word Asan.M.loaded_segments (0x53328 : word) = Some W_532d8.
Proof. vm_refl. Qed.
Lemma D_532d8 : decode_any W_532d8 = Some (Op ALU_SUB 14 19 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_532dc : bv 32 := 0x00b705b3.
Lemma F_532dc : fetch_word Asan.M.loaded_segments (0x5332c : word) = Some W_532dc.
Proof. vm_refl. Qed.
Lemma D_532dc : decode_any W_532dc = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_532e0 : bv 32 := 0x00010737.
Lemma F_532e0 : fetch_word Asan.M.loaded_segments (0x53330 : word) = Some W_532e0.
Proof. vm_refl. Qed.
Lemma D_532e0 : decode_any W_532e0 = Some (Lui 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_532e4 : bv 32 := 0x0017071b.
Lemma F_532e4 : fetch_word Asan.M.loaded_segments (0x53334 : word) = Some W_532e4.
Proof. vm_refl. Qed.
Lemma D_532e4 : decode_any W_532e4 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_532e8 : bv 32 := 0x00160613.
Lemma F_532e8 : fetch_word Asan.M.loaded_segments (0x53338 : word) = Some W_532e8.
Proof. vm_refl. Qed.
Lemma D_532e8 : decode_any W_532e8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_532ec : bv 32 := 0x009686b3.
Lemma F_532ec : fetch_word Asan.M.loaded_segments (0x5333c : word) = Some W_532ec.
Proof. vm_refl. Qed.
Lemma D_532ec : decode_any W_532ec = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_532f0 : bv 32 := 0x00c53023.
Lemma F_532f0 : fetch_word Asan.M.loaded_segments (0x53340 : word) = Some W_532f0.
Proof. vm_refl. Qed.
Lemma D_532f0 : decode_any W_532f0 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_532f4 : bv 32 := 0x00d53423.
Lemma F_532f4 : fetch_word Asan.M.loaded_segments (0x53344 : word) = Some W_532f4.
Proof. vm_refl. Qed.
Lemma D_532f4 : decode_any W_532f4 = Some (Store SZ8 10 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_532f8 : bv 32 := 0x00b53823.
Lemma F_532f8 : fetch_word Asan.M.loaded_segments (0x53348 : word) = Some W_532f8.
Proof. vm_refl. Qed.
Lemma D_532f8 : decode_any W_532f8 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_532fc : bv 32 := 0x00e9ee63.
Lemma F_532fc : fetch_word Asan.M.loaded_segments (0x5334c : word) = Some W_532fc.
Proof. vm_refl. Qed.
Lemma D_532fc : decode_any W_532fc = Some (Branch BC_LTU 19 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_53300 : bv 32 := 0x06853583.
Lemma F_53300 : fetch_word Asan.M.loaded_segments (0x53350 : word) = Some W_53300.
Proof. vm_refl. Qed.
Lemma D_53300 : decode_any W_53300 = Some (Load SZ8 true 11 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_53304 : bv 32 := 0x00158593.
Lemma F_53304 : fetch_word Asan.M.loaded_segments (0x53354 : word) = Some W_53304.
Proof. vm_refl. Qed.
Lemma D_53304 : decode_any W_53304 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_53308 : bv 32 := 0x06b53423.
Lemma F_53308 : fetch_word Asan.M.loaded_segments (0x53358 : word) = Some W_53308.
Proof. vm_refl. Qed.
Lemma D_53308 : decode_any W_53308 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5330c : bv 32 := 0x00813503.
Lemma F_5330c : fetch_word Asan.M.loaded_segments (0x5335c : word) = Some W_5330c.
Proof. vm_refl. Qed.
Lemma D_5330c : decode_any W_5330c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53310 : bv 32 := 0x10051c63.
Lemma F_53310 : fetch_word Asan.M.loaded_segments (0x53360 : word) = Some W_53310.
Proof. vm_refl. Qed.
Lemma D_53310 : decode_any W_53310 = Some (Branch BC_NE 10 0 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_53318 : bv 32 := 0x20000593.
Lemma F_53318 : fetch_word Asan.M.loaded_segments (0x53368 : word) = Some W_53318.
Proof. vm_refl. Qed.
Lemma D_53318 : decode_any W_53318 = Some (OpImm ALU_ADD 11 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5331c : bv 32 := 0x07050513.
Lemma F_5331c : fetch_word Asan.M.loaded_segments (0x5336c : word) = Some W_5331c.
Proof. vm_refl. Qed.
Lemma D_5331c : decode_any W_5331c = Some (OpImm ALU_ADD 10 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_53320 : bv 32 := 0x0135e863.
Lemma F_53320 : fetch_word Asan.M.loaded_segments (0x53370 : word) = Some W_53320.
Proof. vm_refl. Qed.
Lemma D_53320 : decode_any W_53320 = Some (Branch BC_LTU 11 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53324 : bv 32 := 0x01f98593.
Lemma F_53324 : fetch_word Asan.M.loaded_segments (0x53374 : word) = Some W_53324.
Proof. vm_refl. Qed.
Lemma D_53324 : decode_any W_53324 = Some (OpImm ALU_ADD 11 19 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_53328 : bv 32 := 0x0055d593.
Lemma F_53328 : fetch_word Asan.M.loaded_segments (0x53378 : word) = Some W_53328.
Proof. vm_refl. Qed.
Lemma D_53328 : decode_any W_53328 = Some (ShiftImm ALU_SRL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5332c : bv 32 := 0x0e00006f.
Lemma F_5332c : fetch_word Asan.M.loaded_segments (0x5337c : word) = Some W_5332c.
Proof. vm_refl. Qed.
Lemma D_5332c : decode_any W_5332c = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_53330 : bv 32 := 0x0019d593.
Lemma F_53330 : fetch_word Asan.M.loaded_segments (0x53380 : word) = Some W_53330.
Proof. vm_refl. Qed.
Lemma D_53330 : decode_any W_53330 = Some (ShiftImm ALU_SRL 11 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_53334 : bv 32 := 0x55555637.
Lemma F_53334 : fetch_word Asan.M.loaded_segments (0x53384 : word) = Some W_53334.
Proof. vm_refl. Qed.
Lemma D_53334 : decode_any W_53334 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_53338 : bv 32 := 0x333336b7.
Lemma F_53338 : fetch_word Asan.M.loaded_segments (0x53388 : word) = Some W_53338.
Proof. vm_refl. Qed.
Lemma D_53338 : decode_any W_53338 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_5333c : bv 32 := 0x0f0f1737.
Lemma F_5333c : fetch_word Asan.M.loaded_segments (0x5338c : word) = Some W_5333c.
Proof. vm_refl. Qed.
Lemma D_5333c : decode_any W_5333c = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_53340 : bv 32 := 0x010107b7.
Lemma F_53340 : fetch_word Asan.M.loaded_segments (0x53390 : word) = Some W_53340.
Proof. vm_refl. Qed.
Lemma D_53340 : decode_any W_53340 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_53344 : bv 32 := 0x00b9e5b3.
Lemma F_53344 : fetch_word Asan.M.loaded_segments (0x53394 : word) = Some W_53344.
Proof. vm_refl. Qed.
Lemma D_53344 : decode_any W_53344 = Some (Op ALU_OR 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_53348 : bv 32 := 0x5556061b.
Lemma F_53348 : fetch_word Asan.M.loaded_segments (0x53398 : word) = Some W_53348.
Proof. vm_refl. Qed.
Lemma D_53348 : decode_any W_53348 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_5334c : bv 32 := 0x3336869b.
Lemma F_5334c : fetch_word Asan.M.loaded_segments (0x5339c : word) = Some W_5334c.
Proof. vm_refl. Qed.
Lemma D_5334c : decode_any W_5334c = Some (OpImm32 13 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_53350 : bv 32 := 0xf0f7071b.
Lemma F_53350 : fetch_word Asan.M.loaded_segments (0x533a0 : word) = Some W_53350.
Proof. vm_refl. Qed.
Lemma D_53350 : decode_any W_53350 = Some (OpImm32 14 14 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_53354 : bv 32 := 0x1017879b.
Lemma F_53354 : fetch_word Asan.M.loaded_segments (0x533a4 : word) = Some W_53354.
Proof. vm_refl. Qed.
Lemma D_53354 : decode_any W_53354 = Some (OpImm32 15 15 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_53358 : bv 32 := 0x0025d813.
Lemma F_53358 : fetch_word Asan.M.loaded_segments (0x533a8 : word) = Some W_53358.
Proof. vm_refl. Qed.
Lemma D_53358 : decode_any W_53358 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5335c : bv 32 := 0x0105e5b3.
Lemma F_5335c : fetch_word Asan.M.loaded_segments (0x533ac : word) = Some W_5335c.
Proof. vm_refl. Qed.
Lemma D_5335c : decode_any W_5335c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53360 : bv 32 := 0x02061813.
Lemma F_53360 : fetch_word Asan.M.loaded_segments (0x533b0 : word) = Some W_53360.
Proof. vm_refl. Qed.
Lemma D_53360 : decode_any W_53360 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_53364 : bv 32 := 0x01060633.
Lemma F_53364 : fetch_word Asan.M.loaded_segments (0x533b4 : word) = Some W_53364.
Proof. vm_refl. Qed.
Lemma D_53364 : decode_any W_53364 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53368 : bv 32 := 0x02069813.
Lemma F_53368 : fetch_word Asan.M.loaded_segments (0x533b8 : word) = Some W_53368.
Proof. vm_refl. Qed.
Lemma D_53368 : decode_any W_53368 = Some (ShiftImm ALU_SLL 16 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5336c : bv 32 := 0x010686b3.
Lemma F_5336c : fetch_word Asan.M.loaded_segments (0x533bc : word) = Some W_5336c.
Proof. vm_refl. Qed.
Lemma D_5336c : decode_any W_5336c = Some (Op ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53370 : bv 32 := 0x02071813.
Lemma F_53370 : fetch_word Asan.M.loaded_segments (0x533c0 : word) = Some W_53370.
Proof. vm_refl. Qed.
Lemma D_53370 : decode_any W_53370 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_53374 : bv 32 := 0x01070733.
Lemma F_53374 : fetch_word Asan.M.loaded_segments (0x533c4 : word) = Some W_53374.
Proof. vm_refl. Qed.
Lemma D_53374 : decode_any W_53374 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53378 : bv 32 := 0x02079813.
Lemma F_53378 : fetch_word Asan.M.loaded_segments (0x533c8 : word) = Some W_53378.
Proof. vm_refl. Qed.
Lemma D_53378 : decode_any W_53378 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5337c : bv 32 := 0x010787b3.
Lemma F_5337c : fetch_word Asan.M.loaded_segments (0x533cc : word) = Some W_5337c.
Proof. vm_refl. Qed.
Lemma D_5337c : decode_any W_5337c = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53380 : bv 32 := 0x0045d813.
Lemma F_53380 : fetch_word Asan.M.loaded_segments (0x533d0 : word) = Some W_53380.
Proof. vm_refl. Qed.
Lemma D_53380 : decode_any W_53380 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_53384 : bv 32 := 0x0105e5b3.
Lemma F_53384 : fetch_word Asan.M.loaded_segments (0x533d4 : word) = Some W_53384.
Proof. vm_refl. Qed.
Lemma D_53384 : decode_any W_53384 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53388 : bv 32 := 0x0085d813.
Lemma F_53388 : fetch_word Asan.M.loaded_segments (0x533d8 : word) = Some W_53388.
Proof. vm_refl. Qed.
Lemma D_53388 : decode_any W_53388 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5338c : bv 32 := 0x0105e5b3.
Lemma F_5338c : fetch_word Asan.M.loaded_segments (0x533dc : word) = Some W_5338c.
Proof. vm_refl. Qed.
Lemma D_5338c : decode_any W_5338c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53390 : bv 32 := 0x0105d813.
Lemma F_53390 : fetch_word Asan.M.loaded_segments (0x533e0 : word) = Some W_53390.
Proof. vm_refl. Qed.
Lemma D_53390 : decode_any W_53390 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53394 : bv 32 := 0x0105e5b3.
Lemma F_53394 : fetch_word Asan.M.loaded_segments (0x533e4 : word) = Some W_53394.
Proof. vm_refl. Qed.
Lemma D_53394 : decode_any W_53394 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53398 : bv 32 := 0x0205d813.
Lemma F_53398 : fetch_word Asan.M.loaded_segments (0x533e8 : word) = Some W_53398.
Proof. vm_refl. Qed.
Lemma D_53398 : decode_any W_53398 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5339c : bv 32 := 0x0105e5b3.
Lemma F_5339c : fetch_word Asan.M.loaded_segments (0x533ec : word) = Some W_5339c.
Proof. vm_refl. Qed.
Lemma D_5339c : decode_any W_5339c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_533a0 : bv 32 := 0xfff5c593.
Lemma F_533a0 : fetch_word Asan.M.loaded_segments (0x533f0 : word) = Some W_533a0.
Proof. vm_refl. Qed.
Lemma D_533a0 : decode_any W_533a0 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_533a4 : bv 32 := 0x0015d813.
Lemma F_533a4 : fetch_word Asan.M.loaded_segments (0x533f4 : word) = Some W_533a4.
Proof. vm_refl. Qed.
Lemma D_533a4 : decode_any W_533a4 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_533a8 : bv 32 := 0x00c87633.
Lemma F_533a8 : fetch_word Asan.M.loaded_segments (0x533f8 : word) = Some W_533a8.
Proof. vm_refl. Qed.
Lemma D_533a8 : decode_any W_533a8 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_533ac : bv 32 := 0x40c585b3.
Lemma F_533ac : fetch_word Asan.M.loaded_segments (0x533fc : word) = Some W_533ac.
Proof. vm_refl. Qed.
Lemma D_533ac : decode_any W_533ac = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_533b0 : bv 32 := 0x00d5f633.
Lemma F_533b0 : fetch_word Asan.M.loaded_segments (0x53400 : word) = Some W_533b0.
Proof. vm_refl. Qed.
Lemma D_533b0 : decode_any W_533b0 = Some (Op ALU_AND 12 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_533b4 : bv 32 := 0x0025d593.
Lemma F_533b4 : fetch_word Asan.M.loaded_segments (0x53404 : word) = Some W_533b4.
Proof. vm_refl. Qed.
Lemma D_533b4 : decode_any W_533b4 = Some (ShiftImm ALU_SRL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_533b8 : bv 32 := 0x00d5f5b3.
Lemma F_533b8 : fetch_word Asan.M.loaded_segments (0x53408 : word) = Some W_533b8.
Proof. vm_refl. Qed.
Lemma D_533b8 : decode_any W_533b8 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_533bc : bv 32 := 0x00b605b3.
Lemma F_533bc : fetch_word Asan.M.loaded_segments (0x5340c : word) = Some W_533bc.
Proof. vm_refl. Qed.
Lemma D_533bc : decode_any W_533bc = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_533c0 : bv 32 := 0x0045d613.
Lemma F_533c0 : fetch_word Asan.M.loaded_segments (0x53410 : word) = Some W_533c0.
Proof. vm_refl. Qed.
Lemma D_533c0 : decode_any W_533c0 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_533c4 : bv 32 := 0x00c585b3.
Lemma F_533c4 : fetch_word Asan.M.loaded_segments (0x53414 : word) = Some W_533c4.
Proof. vm_refl. Qed.
Lemma D_533c4 : decode_any W_533c4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_533c8 : bv 32 := 0x03e00613.
Lemma F_533c8 : fetch_word Asan.M.loaded_segments (0x53418 : word) = Some W_533c8.
Proof. vm_refl. Qed.
Lemma D_533c8 : decode_any W_533c8 = Some (OpImm ALU_ADD 12 0 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_533cc : bv 32 := 0x00e5f5b3.
Lemma F_533cc : fetch_word Asan.M.loaded_segments (0x5341c : word) = Some W_533cc.
Proof. vm_refl. Qed.
Lemma D_533cc : decode_any W_533cc = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_533d0 : bv 32 := 0xfff00693.
Lemma F_533d0 : fetch_word Asan.M.loaded_segments (0x53420 : word) = Some W_533d0.
Proof. vm_refl. Qed.
Lemma D_533d0 : decode_any W_533d0 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_533d4 : bv 32 := 0x02f585b3.
Lemma F_533d4 : fetch_word Asan.M.loaded_segments (0x53424 : word) = Some W_533d4.
Proof. vm_refl. Qed.
Lemma D_533d4 : decode_any W_533d4 = Some (Mul M_MUL 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_533d8 : bv 32 := 0x0385d593.
Lemma F_533d8 : fetch_word Asan.M.loaded_segments (0x53428 : word) = Some W_533d8.
Proof. vm_refl. Qed.
Lemma D_533d8 : decode_any W_533d8 = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_533dc : bv 32 := 0x40b6063b.
Lemma F_533dc : fetch_word Asan.M.loaded_segments (0x5342c : word) = Some W_533dc.
Proof. vm_refl. Qed.
Lemma D_533dc : decode_any W_533dc = Some (Op32 ALU_SUB 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_533e0 : bv 32 := 0x00159593.
Lemma F_533e0 : fetch_word Asan.M.loaded_segments (0x53430 : word) = Some W_533e0.
Proof. vm_refl. Qed.
Lemma D_533e0 : decode_any W_533e0 = Some (ShiftImm ALU_SLL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_533e4 : bv 32 := 0x00c9d733.
Lemma F_533e4 : fetch_word Asan.M.loaded_segments (0x53434 : word) = Some W_533e4.
Proof. vm_refl. Qed.
Lemma D_533e4 : decode_any W_533e4 = Some (Op ALU_SRL 14 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_533e8 : bv 32 := 0x00c6963b.
Lemma F_533e8 : fetch_word Asan.M.loaded_segments (0x53438 : word) = Some W_533e8.
Proof. vm_refl. Qed.
Lemma D_533e8 : decode_any W_533e8 = Some (Op32 ALU_SLL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_533ec : bv 32 := 0x07e5c593.
Lemma F_533ec : fetch_word Asan.M.loaded_segments (0x5343c : word) = Some W_533ec.
Proof. vm_refl. Qed.
Lemma D_533ec : decode_any W_533ec = Some (OpImm ALU_XOR 11 11 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_533f0 : bv 32 := 0x00177713.
Lemma F_533f0 : fetch_word Asan.M.loaded_segments (0x53440 : word) = Some W_533f0.
Proof. vm_refl. Qed.
Lemma D_533f0 : decode_any W_533f0 = Some (OpImm ALU_AND 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_533f4 : bv 32 := 0xfff64613.
Lemma F_533f4 : fetch_word Asan.M.loaded_segments (0x53444 : word) = Some W_533f4.
Proof. vm_refl. Qed.
Lemma D_533f4 : decode_any W_533f4 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_533f8 : bv 32 := 0x00c9f633.
Lemma F_533f8 : fetch_word Asan.M.loaded_segments (0x53448 : word) = Some W_533f8.
Proof. vm_refl. Qed.
Lemma D_533f8 : decode_any W_533f8 = Some (Op ALU_AND 12 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_533fc : bv 32 := 0x00e5e5b3.
Lemma F_533fc : fetch_word Asan.M.loaded_segments (0x5344c : word) = Some W_533fc.
Proof. vm_refl. Qed.
Lemma D_533fc : decode_any W_533fc = Some (Op ALU_OR 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_53400 : bv 32 := 0x00c03633.
Lemma F_53400 : fetch_word Asan.M.loaded_segments (0x53450 : word) = Some W_53400.
Proof. vm_refl. Qed.
Lemma D_53400 : decode_any W_53400 = Some (Op ALU_SLTU 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_53404 : bv 32 := 0x00c585b3.
Lemma F_53404 : fetch_word Asan.M.loaded_segments (0x53454 : word) = Some W_53404.
Proof. vm_refl. Qed.
Lemma D_53404 : decode_any W_53404 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_53408 : bv 32 := 0xffe58593.
Lemma F_53408 : fetch_word Asan.M.loaded_segments (0x53458 : word) = Some W_53408.
Proof. vm_refl. Qed.
Lemma D_53408 : decode_any W_53408 = Some (OpImm ALU_ADD 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_5340c : bv 32 := 0x00359593.
Lemma F_5340c : fetch_word Asan.M.loaded_segments (0x5345c : word) = Some W_5340c.
Proof. vm_refl. Qed.
Lemma D_5340c : decode_any W_5340c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_53410 : bv 32 := 0x00b50533.
Lemma F_53410 : fetch_word Asan.M.loaded_segments (0x53460 : word) = Some W_53410.
Proof. vm_refl. Qed.
Lemma D_53410 : decode_any W_53410 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_53414 : bv 32 := 0x00053583.
Lemma F_53414 : fetch_word Asan.M.loaded_segments (0x53464 : word) = Some W_53414.
Proof. vm_refl. Qed.
Lemma D_53414 : decode_any W_53414 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53418 : bv 32 := 0x00158593.
Lemma F_53418 : fetch_word Asan.M.loaded_segments (0x53468 : word) = Some W_53418.
Proof. vm_refl. Qed.
Lemma D_53418 : decode_any W_53418 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5341c : bv 32 := 0x00b53023.
Lemma F_5341c : fetch_word Asan.M.loaded_segments (0x5346c : word) = Some W_5341c.
Proof. vm_refl. Qed.
Lemma D_5341c : decode_any W_5341c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53420 : bv 32 := 0x00813503.
Lemma F_53420 : fetch_word Asan.M.loaded_segments (0x53470 : word) = Some W_53420.
Proof. vm_refl. Qed.
Lemma D_53420 : decode_any W_53420 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53424 : bv 32 := 0x02050c63.
Lemma F_53424 : fetch_word Asan.M.loaded_segments (0x53474 : word) = Some W_53424.
Proof. vm_refl. Qed.
Lemma D_53424 : decode_any W_53424 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_53428 : bv 32 := 0x000e6517.
Lemma F_53428 : fetch_word Asan.M.loaded_segments (0x53478 : word) = Some W_53428.
Proof. vm_refl. Qed.
Lemma D_53428 : decode_any W_53428 = Some (Auipc 10 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_5342c : bv 32 := 0xd3853503.
Lemma F_5342c : fetch_word Asan.M.loaded_segments (0x5347c : word) = Some W_5342c.
Proof. vm_refl. Qed.
Lemma D_5342c : decode_any W_5342c = Some (Load SZ8 true 10 10 3384, 4%Z).
Proof. vm_refl. Qed.

Definition W_53430 : bv 32 := 0x02c52583.
Lemma F_53430 : fetch_word Asan.M.loaded_segments (0x53480 : word) = Some W_53430.
Proof. vm_refl. Qed.
Lemma D_53430 : decode_any W_53430 = Some (Load SZ4 true 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_53434 : bv 32 := 0x02058463.
Lemma F_53434 : fetch_word Asan.M.loaded_segments (0x53484 : word) = Some W_53434.
Proof. vm_refl. Qed.
Lemma D_53434 : decode_any W_53434 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_53438 : bv 32 := 0x00048613.
Lemma F_53438 : fetch_word Asan.M.loaded_segments (0x53488 : word) = Some W_53438.
Proof. vm_refl. Qed.
Lemma D_53438 : decode_any W_53438 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5343c : bv 32 := 0x00b4e463.
Lemma F_5343c : fetch_word Asan.M.loaded_segments (0x5348c : word) = Some W_5343c.
Proof. vm_refl. Qed.
Lemma D_5343c : decode_any W_5343c = Some (Branch BC_LTU 9 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53440 : bv 32 := 0x00058613.
Lemma F_53440 : fetch_word Asan.M.loaded_segments (0x53490 : word) = Some W_53440.
Proof. vm_refl. Qed.
Lemma D_53440 : decode_any W_53440 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53444 : bv 32 := 0x000e6597.
Lemma F_53444 : fetch_word Asan.M.loaded_segments (0x53494 : word) = Some W_53444.
Proof. vm_refl. Qed.
Lemma D_53444 : decode_any W_53444 = Some (Auipc 11 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_53448 : bv 32 := 0xd445b583.
Lemma F_53448 : fetch_word Asan.M.loaded_segments (0x53498 : word) = Some W_53448.
Proof. vm_refl. Qed.
Lemma D_53448 : decode_any W_53448 = Some (Load SZ8 true 11 11 3396, 4%Z).
Proof. vm_refl. Qed.

Definition W_5344c : bv 32 := 0x0005b683.
Lemma F_5344c : fetch_word Asan.M.loaded_segments (0x5349c : word) = Some W_5344c.
Proof. vm_refl. Qed.
Lemma D_5344c : decode_any W_5344c = Some (Load SZ8 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53450 : bv 32 := 0x03452583.
Lemma F_53450 : fetch_word Asan.M.loaded_segments (0x534a0 : word) = Some W_53450.
Proof. vm_refl. Qed.
Lemma D_53450 : decode_any W_53450 = Some (Load SZ4 true 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_53454 : bv 32 := 0x000a0513.
Lemma F_53454 : fetch_word Asan.M.loaded_segments (0x534a4 : word) = Some W_53454.
Proof. vm_refl. Qed.
Lemma D_53454 : decode_any W_53454 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53458 : bv 32 := 0x000680e7.
Lemma F_53458 : fetch_word Asan.M.loaded_segments (0x534a8 : word) = Some W_53458.
Proof. vm_refl. Qed.
Lemma D_53458 : decode_any W_53458 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5345c : bv 32 := 0x19d540ef.
Lemma F_5345c : fetch_word Asan.M.loaded_segments (0x534ac : word) = Some W_5345c.
Proof. vm_refl. Qed.
Lemma D_5345c : decode_any W_5345c = Some (Jal 1 346524, 4%Z).
Proof. vm_refl. Qed.

Definition W_53460 : bv 32 := 0x001ac583.
Lemma F_53460 : fetch_word Asan.M.loaded_segments (0x534b0 : word) = Some W_53460.
Proof. vm_refl. Qed.
Lemma D_53460 : decode_any W_53460 = Some (Load SZ1 false 11 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_53464 : bv 32 := 0x40a0053b.
Lemma F_53464 : fetch_word Asan.M.loaded_segments (0x534b4 : word) = Some W_53464.
Proof. vm_refl. Qed.
Lemma D_53464 : decode_any W_53464 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_53468 : bv 32 := 0x00c57513.
Lemma F_53468 : fetch_word Asan.M.loaded_segments (0x534b8 : word) = Some W_53468.
Proof. vm_refl. Qed.
Lemma D_53468 : decode_any W_53468 = Some (OpImm ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5346c : bv 32 := 0x0f35f593.
Lemma F_5346c : fetch_word Asan.M.loaded_segments (0x534bc : word) = Some W_5346c.
Proof. vm_refl. Qed.
Lemma D_5346c : decode_any W_5346c = Some (OpImm ALU_AND 11 11 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_53470 : bv 32 := 0x00a5e533.
Lemma F_53470 : fetch_word Asan.M.loaded_segments (0x534c0 : word) = Some W_53470.
Proof. vm_refl. Qed.
Lemma D_53470 : decode_any W_53470 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_53474 : bv 32 := 0x00200593.
Lemma F_53474 : fetch_word Asan.M.loaded_segments (0x534c4 : word) = Some W_53474.
Proof. vm_refl. Qed.
Lemma D_53474 : decode_any W_53474 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_53478 : bv 32 := 0x00aa80a3.
Lemma F_53478 : fetch_word Asan.M.loaded_segments (0x534c8 : word) = Some W_53478.
Proof. vm_refl. Qed.
Lemma D_53478 : decode_any W_53478 = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5347c : bv 32 := 0x0310000f.
Lemma F_5347c : fetch_word Asan.M.loaded_segments (0x534cc : word) = Some W_5347c.
Proof. vm_refl. Qed.
Lemma D_5347c : decode_any W_5347c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53480 : bv 32 := 0x00ba8023.
Lemma F_53480 : fetch_word Asan.M.loaded_segments (0x534d0 : word) = Some W_53480.
Proof. vm_refl. Qed.
Lemma D_53480 : decode_any W_53480 = Some (Store SZ1 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53484 : bv 32 := 0x032a8063.
Lemma F_53484 : fetch_word Asan.M.loaded_segments (0x534d4 : word) = Some W_53484.
Proof. vm_refl. Qed.
Lemma D_53484 : decode_any W_53484 = Some (Branch BC_EQ 21 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_53488 : bv 32 := 0x01090693.
Lemma F_53488 : fetch_word Asan.M.loaded_segments (0x534d8 : word) = Some W_53488.
Proof. vm_refl. Qed.
Lemma D_53488 : decode_any W_53488 = Some (OpImm ALU_ADD 13 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5348c : bv 32 := 0x20daee63.
Lemma F_5348c : fetch_word Asan.M.loaded_segments (0x534dc : word) = Some W_5348c.
Proof. vm_refl. Qed.
Lemma D_5348c : decode_any W_5348c = Some (Branch BC_LTU 21 13 540, 4%Z).
Proof. vm_refl. Qed.

Definition W_53490 : bv 32 := 0xfffbd517.
Lemma F_53490 : fetch_word Asan.M.loaded_segments (0x534e0 : word) = Some W_53490.
Proof. vm_refl. Qed.
Lemma D_53490 : decode_any W_53490 = Some (Auipc 10 1048509, 4%Z).
Proof. vm_refl. Qed.

Definition W_53494 : bv 32 := 0xe9053503.
Lemma F_53494 : fetch_word Asan.M.loaded_segments (0x534e4 : word) = Some W_53494.
Proof. vm_refl. Qed.
Lemma D_53494 : decode_any W_53494 = Some (Load SZ8 true 10 10 3728, 4%Z).
Proof. vm_refl. Qed.

Definition W_53498 : bv 32 := 0x01593423.
Lemma F_53498 : fetch_word Asan.M.loaded_segments (0x534e8 : word) = Some W_53498.
Proof. vm_refl. Qed.
Lemma D_53498 : decode_any W_53498 = Some (Store SZ8 18 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5349c : bv 32 := 0x0310000f.
Lemma F_5349c : fetch_word Asan.M.loaded_segments (0x534ec : word) = Some W_5349c.
Proof. vm_refl. Qed.
Lemma D_5349c : decode_any W_5349c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534a0 : bv 32 := 0x00a93023.
Lemma F_534a0 : fetch_word Asan.M.loaded_segments (0x534f0 : word) = Some W_534a0.
Proof. vm_refl. Qed.
Lemma D_534a0 : decode_any W_534a0 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534a4 : bv 32 := 0x000a0513.
Lemma F_534a4 : fetch_word Asan.M.loaded_segments (0x534f4 : word) = Some W_534a4.
Proof. vm_refl. Qed.
Lemma D_534a4 : decode_any W_534a4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534a8 : bv 32 := 0x00048593.
Lemma F_534a8 : fetch_word Asan.M.loaded_segments (0x534f8 : word) = Some W_534a8.
Proof. vm_refl. Qed.
Lemma D_534a8 : decode_any W_534a8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534ac : bv 32 := 0x540350ef.
Lemma F_534ac : fetch_word Asan.M.loaded_segments (0x534fc : word) = Some W_534ac.
Proof. vm_refl. Qed.
Lemma D_534ac : decode_any W_534ac = Some (Jal 1 218432, 4%Z).
Proof. vm_refl. Qed.

Definition W_534b0 : bv 32 := 0x000a0513.
Lemma F_534b0 : fetch_word Asan.M.loaded_segments (0x53500 : word) = Some W_534b0.
Proof. vm_refl. Qed.
Lemma D_534b0 : decode_any W_534b0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_534b4 : bv 32 := 0x07813083.
Lemma F_534b4 : fetch_word Asan.M.loaded_segments (0x53504 : word) = Some W_534b4.
Proof. vm_refl. Qed.
Lemma D_534b4 : decode_any W_534b4 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_534b8 : bv 32 := 0x07013403.
Lemma F_534b8 : fetch_word Asan.M.loaded_segments (0x53508 : word) = Some W_534b8.
Proof. vm_refl. Qed.
Lemma D_534b8 : decode_any W_534b8 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_534bc : bv 32 := 0x06813483.
Lemma F_534bc : fetch_word Asan.M.loaded_segments (0x5350c : word) = Some W_534bc.
Proof. vm_refl. Qed.
Lemma D_534bc : decode_any W_534bc = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_534c0 : bv 32 := 0x06013903.
Lemma F_534c0 : fetch_word Asan.M.loaded_segments (0x53510 : word) = Some W_534c0.
Proof. vm_refl. Qed.
Lemma D_534c0 : decode_any W_534c0 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_534c4 : bv 32 := 0x05813983.
Lemma F_534c4 : fetch_word Asan.M.loaded_segments (0x53514 : word) = Some W_534c4.
Proof. vm_refl. Qed.
Lemma D_534c4 : decode_any W_534c4 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_534c8 : bv 32 := 0x05013a03.
Lemma F_534c8 : fetch_word Asan.M.loaded_segments (0x53518 : word) = Some W_534c8.
Proof. vm_refl. Qed.
Lemma D_534c8 : decode_any W_534c8 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_534cc : bv 32 := 0x04813a83.
Lemma F_534cc : fetch_word Asan.M.loaded_segments (0x5351c : word) = Some W_534cc.
Proof. vm_refl. Qed.
Lemma D_534cc : decode_any W_534cc = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_534d0 : bv 32 := 0x04013b03.
Lemma F_534d0 : fetch_word Asan.M.loaded_segments (0x53520 : word) = Some W_534d0.
Proof. vm_refl. Qed.
Lemma D_534d0 : decode_any W_534d0 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_534d4 : bv 32 := 0x03813b83.
Lemma F_534d4 : fetch_word Asan.M.loaded_segments (0x53524 : word) = Some W_534d4.
Proof. vm_refl. Qed.
Lemma D_534d4 : decode_any W_534d4 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_534d8 : bv 32 := 0x03013c03.
Lemma F_534d8 : fetch_word Asan.M.loaded_segments (0x53528 : word) = Some W_534d8.
Proof. vm_refl. Qed.
Lemma D_534d8 : decode_any W_534d8 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_534dc : bv 32 := 0x02813c83.
Lemma F_534dc : fetch_word Asan.M.loaded_segments (0x5352c : word) = Some W_534dc.
Proof. vm_refl. Qed.
Lemma D_534dc : decode_any W_534dc = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_534e0 : bv 32 := 0x02013d03.
Lemma F_534e0 : fetch_word Asan.M.loaded_segments (0x53530 : word) = Some W_534e0.
Proof. vm_refl. Qed.
Lemma D_534e0 : decode_any W_534e0 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_534e4 : bv 32 := 0x01813d83.
Lemma F_534e4 : fetch_word Asan.M.loaded_segments (0x53534 : word) = Some W_534e4.
Proof. vm_refl. Qed.
Lemma D_534e4 : decode_any W_534e4 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_534e8 : bv 32 := 0x08010113.
Lemma F_534e8 : fetch_word Asan.M.loaded_segments (0x53538 : word) = Some W_534e8.
Proof. vm_refl. Qed.
Lemma D_534e8 : decode_any W_534e8 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_534ec : bv 32 := 0x00008067.
Lemma F_534ec : fetch_word Asan.M.loaded_segments (0x5353c : word) = Some W_534ec.
Proof. vm_refl. Qed.
Lemma D_534ec : decode_any W_534ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53910 : bv 32 := 0xfe010113.
Lemma F_53910 : fetch_word Asan.M.loaded_segments (0x53960 : word) = Some W_53910.
Proof. vm_refl. Qed.
Lemma D_53910 : decode_any W_53910 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_53914 : bv 32 := 0x00113c23.
Lemma F_53914 : fetch_word Asan.M.loaded_segments (0x53964 : word) = Some W_53914.
Proof. vm_refl. Qed.
Lemma D_53914 : decode_any W_53914 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_53918 : bv 32 := 0x00813823.
Lemma F_53918 : fetch_word Asan.M.loaded_segments (0x53968 : word) = Some W_53918.
Proof. vm_refl. Qed.
Lemma D_53918 : decode_any W_53918 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5391c : bv 32 := 0x00913423.
Lemma F_5391c : fetch_word Asan.M.loaded_segments (0x5396c : word) = Some W_5391c.
Proof. vm_refl. Qed.
Lemma D_5391c : decode_any W_5391c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_53920 : bv 32 := 0x01213023.
Lemma F_53920 : fetch_word Asan.M.loaded_segments (0x53970 : word) = Some W_53920.
Proof. vm_refl. Qed.
Lemma D_53920 : decode_any W_53920 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53924 : bv 32 := 0x00060413.
Lemma F_53924 : fetch_word Asan.M.loaded_segments (0x53974 : word) = Some W_53924.
Proof. vm_refl. Qed.
Lemma D_53924 : decode_any W_53924 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53928 : bv 32 := 0x00050493.
Lemma F_53928 : fetch_word Asan.M.loaded_segments (0x53978 : word) = Some W_53928.
Proof. vm_refl. Qed.
Lemma D_53928 : decode_any W_53928 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5392c : bv 32 := 0xfff50513.
Lemma F_5392c : fetch_word Asan.M.loaded_segments (0x5397c : word) = Some W_5392c.
Proof. vm_refl. Qed.
Lemma D_5392c : decode_any W_5392c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_53930 : bv 32 := 0x00a4c633.
Lemma F_53930 : fetch_word Asan.M.loaded_segments (0x53980 : word) = Some W_53930.
Proof. vm_refl. Qed.
Lemma D_53930 : decode_any W_53930 = Some (Op ALU_XOR 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_53934 : bv 32 := 0x04c57263.
Lemma F_53934 : fetch_word Asan.M.loaded_segments (0x53984 : word) = Some W_53934.
Proof. vm_refl. Qed.
Lemma D_53934 : decode_any W_53934 = Some (Branch BC_GEU 10 12 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_53938 : bv 32 := 0x00a5f533.
Lemma F_53938 : fetch_word Asan.M.loaded_segments (0x53988 : word) = Some W_53938.
Proof. vm_refl. Qed.
Lemma D_53938 : decode_any W_53938 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5393c : bv 32 := 0x02051e63.
Lemma F_5393c : fetch_word Asan.M.loaded_segments (0x5398c : word) = Some W_5393c.
Proof. vm_refl. Qed.
Lemma D_5393c : decode_any W_5393c = Some (Branch BC_NE 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_53940 : bv 32 := 0x000eb517.
Lemma F_53940 : fetch_word Asan.M.loaded_segments (0x53990 : word) = Some W_53940.
Proof. vm_refl. Qed.
Lemma D_53940 : decode_any W_53940 = Some (Auipc 10 235, 4%Z).
Proof. vm_refl. Qed.

Definition W_53944 : bv 32 := 0x00100713.
Lemma F_53944 : fetch_word Asan.M.loaded_segments (0x53994 : word) = Some W_53944.
Proof. vm_refl. Qed.
Lemma D_53944 : decode_any W_53944 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_53948 : bv 32 := 0xa0850513.
Lemma F_53948 : fetch_word Asan.M.loaded_segments (0x53998 : word) = Some W_53948.
Proof. vm_refl. Qed.
Lemma D_53948 : decode_any W_53948 = Some (OpImm ALU_ADD 10 10 2568, 4%Z).
Proof. vm_refl. Qed.

Definition W_5394c : bv 32 := 0x00100793.
Lemma F_5394c : fetch_word Asan.M.loaded_segments (0x5399c : word) = Some W_5394c.
Proof. vm_refl. Qed.
Lemma D_5394c : decode_any W_5394c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_53950 : bv 32 := 0x00048613.
Lemma F_53950 : fetch_word Asan.M.loaded_segments (0x539a0 : word) = Some W_53950.
Proof. vm_refl. Qed.
Lemma D_53950 : decode_any W_53950 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53954 : bv 32 := 0x00040693.
Lemma F_53954 : fetch_word Asan.M.loaded_segments (0x539a4 : word) = Some W_53954.
Proof. vm_refl. Qed.
Lemma D_53954 : decode_any W_53954 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53958 : bv 32 := 0xc24ff0ef.
Lemma F_53958 : fetch_word Asan.M.loaded_segments (0x539a8 : word) = Some W_53958.
Proof. vm_refl. Qed.
Lemma D_53958 : decode_any W_53958 = Some (Jal 1 2094116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5395c : bv 32 := 0x04050663.
Lemma F_5395c : fetch_word Asan.M.loaded_segments (0x539ac : word) = Some W_5395c.
Proof. vm_refl. Qed.
Lemma D_5395c : decode_any W_5395c = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_53960 : bv 32 := 0x01813083.
Lemma F_53960 : fetch_word Asan.M.loaded_segments (0x539b0 : word) = Some W_53960.
Proof. vm_refl. Qed.
Lemma D_53960 : decode_any W_53960 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_53964 : bv 32 := 0x01013403.
Lemma F_53964 : fetch_word Asan.M.loaded_segments (0x539b4 : word) = Some W_53964.
Proof. vm_refl. Qed.
Lemma D_53964 : decode_any W_53964 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_53968 : bv 32 := 0x00813483.
Lemma F_53968 : fetch_word Asan.M.loaded_segments (0x539b8 : word) = Some W_53968.
Proof. vm_refl. Qed.
Lemma D_53968 : decode_any W_53968 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5396c : bv 32 := 0x00013903.
Lemma F_5396c : fetch_word Asan.M.loaded_segments (0x539bc : word) = Some W_5396c.
Proof. vm_refl. Qed.
Lemma D_5396c : decode_any W_5396c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_53970 : bv 32 := 0x02010113.
Lemma F_53970 : fetch_word Asan.M.loaded_segments (0x539c0 : word) = Some W_53970.
Proof. vm_refl. Qed.
Lemma D_53970 : decode_any W_53970 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_53974 : bv 32 := 0x00008067.
Lemma F_53974 : fetch_word Asan.M.loaded_segments (0x539c4 : word) = Some W_53974.
Proof. vm_refl. Qed.
Lemma D_53974 : decode_any W_53974 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
