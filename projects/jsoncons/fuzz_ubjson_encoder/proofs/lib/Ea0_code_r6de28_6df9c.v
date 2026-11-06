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

Definition W_889ec : bv 32 := 0xfe010113.
Lemma F_889ec : fetch_word Asan.M.loaded_segments (0x88a3c : word) = Some W_889ec.
Proof. vm_refl. Qed.
Lemma D_889ec : decode_any W_889ec = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_889f0 : bv 32 := 0x00113c23.
Lemma F_889f0 : fetch_word Asan.M.loaded_segments (0x88a40 : word) = Some W_889f0.
Proof. vm_refl. Qed.
Lemma D_889f0 : decode_any W_889f0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_889f4 : bv 32 := 0x00813823.
Lemma F_889f4 : fetch_word Asan.M.loaded_segments (0x88a44 : word) = Some W_889f4.
Proof. vm_refl. Qed.
Lemma D_889f4 : decode_any W_889f4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_889f8 : bv 32 := 0x00913423.
Lemma F_889f8 : fetch_word Asan.M.loaded_segments (0x88a48 : word) = Some W_889f8.
Proof. vm_refl. Qed.
Lemma D_889f8 : decode_any W_889f8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_889fc : bv 32 := 0x01213023.
Lemma F_889fc : fetch_word Asan.M.loaded_segments (0x88a4c : word) = Some W_889fc.
Proof. vm_refl. Qed.
Lemma D_889fc : decode_any W_889fc = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a00 : bv 32 := 0x00058413.
Lemma F_88a00 : fetch_word Asan.M.loaded_segments (0x88a50 : word) = Some W_88a00.
Proof. vm_refl. Qed.
Lemma D_88a00 : decode_any W_88a00 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a04 : bv 32 := 0x00050493.
Lemma F_88a04 : fetch_word Asan.M.loaded_segments (0x88a54 : word) = Some W_88a04.
Proof. vm_refl. Qed.
Lemma D_88a04 : decode_any W_88a04 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a08 : bv 32 := 0x09c000ef.
Lemma F_88a08 : fetch_word Asan.M.loaded_segments (0x88a58 : word) = Some W_88a08.
Proof. vm_refl. Qed.
Lemma D_88a08 : decode_any W_88a08 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a0c : bv 32 := 0x0014b517.
Lemma F_88a0c : fetch_word Asan.M.loaded_segments (0x88a5c : word) = Some W_88a0c.
Proof. vm_refl. Qed.
Lemma D_88a0c : decode_any W_88a0c = Some (Auipc 10 331, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a10 : bv 32 := 0xa6450913.
Lemma F_88a10 : fetch_word Asan.M.loaded_segments (0x88a60 : word) = Some W_88a10.
Proof. vm_refl. Qed.
Lemma D_88a10 : decode_any W_88a10 = Some (OpImm ALU_ADD 18 10 2660, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a14 : bv 32 := 0x00093603.
Lemma F_88a14 : fetch_word Asan.M.loaded_segments (0x88a64 : word) = Some W_88a14.
Proof. vm_refl. Qed.
Lemma D_88a14 : decode_any W_88a14 = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a18 : bv 32 := 0x06060a63.
Lemma F_88a18 : fetch_word Asan.M.loaded_segments (0x88a68 : word) = Some W_88a18.
Proof. vm_refl. Qed.
Lemma D_88a18 : decode_any W_88a18 = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a8c : bv 32 := 0x01813083.
Lemma F_88a8c : fetch_word Asan.M.loaded_segments (0x88adc : word) = Some W_88a8c.
Proof. vm_refl. Qed.
Lemma D_88a8c : decode_any W_88a8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a90 : bv 32 := 0x01013403.
Lemma F_88a90 : fetch_word Asan.M.loaded_segments (0x88ae0 : word) = Some W_88a90.
Proof. vm_refl. Qed.
Lemma D_88a90 : decode_any W_88a90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a94 : bv 32 := 0x00813483.
Lemma F_88a94 : fetch_word Asan.M.loaded_segments (0x88ae4 : word) = Some W_88a94.
Proof. vm_refl. Qed.
Lemma D_88a94 : decode_any W_88a94 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a98 : bv 32 := 0x00013903.
Lemma F_88a98 : fetch_word Asan.M.loaded_segments (0x88ae8 : word) = Some W_88a98.
Proof. vm_refl. Qed.
Lemma D_88a98 : decode_any W_88a98 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a9c : bv 32 := 0x02010113.
Lemma F_88a9c : fetch_word Asan.M.loaded_segments (0x88aec : word) = Some W_88a9c.
Proof. vm_refl. Qed.
Lemma D_88a9c : decode_any W_88a9c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_88aa0 : bv 32 := 0x00008067.
Lemma F_88aa0 : fetch_word Asan.M.loaded_segments (0x88af0 : word) = Some W_88aa0.
Proof. vm_refl. Qed.
Lemma D_88aa0 : decode_any W_88aa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88aa4 : bv 32 := 0x00008067.
Lemma F_88aa4 : fetch_word Asan.M.loaded_segments (0x88af4 : word) = Some W_88aa4.
Proof. vm_refl. Qed.
Lemma D_88aa4 : decode_any W_88aa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88aa8 : bv 32 := 0xfe010113.
Lemma F_88aa8 : fetch_word Asan.M.loaded_segments (0x88af8 : word) = Some W_88aa8.
Proof. vm_refl. Qed.
Lemma D_88aa8 : decode_any W_88aa8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_88aac : bv 32 := 0x00113c23.
Lemma F_88aac : fetch_word Asan.M.loaded_segments (0x88afc : word) = Some W_88aac.
Proof. vm_refl. Qed.
Lemma D_88aac : decode_any W_88aac = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ab0 : bv 32 := 0x00813823.
Lemma F_88ab0 : fetch_word Asan.M.loaded_segments (0x88b00 : word) = Some W_88ab0.
Proof. vm_refl. Qed.
Lemma D_88ab0 : decode_any W_88ab0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ab4 : bv 32 := 0x00913423.
Lemma F_88ab4 : fetch_word Asan.M.loaded_segments (0x88b04 : word) = Some W_88ab4.
Proof. vm_refl. Qed.
Lemma D_88ab4 : decode_any W_88ab4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ab8 : bv 32 := 0x00050413.
Lemma F_88ab8 : fetch_word Asan.M.loaded_segments (0x88b08 : word) = Some W_88ab8.
Proof. vm_refl. Qed.
Lemma D_88ab8 : decode_any W_88ab8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88abc : bv 32 := 0x098000ef.
Lemma F_88abc : fetch_word Asan.M.loaded_segments (0x88b0c : word) = Some W_88abc.
Proof. vm_refl. Qed.
Lemma D_88abc : decode_any W_88abc = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ac0 : bv 32 := 0x00050e63.
Lemma F_88ac0 : fetch_word Asan.M.loaded_segments (0x88b10 : word) = Some W_88ac0.
Proof. vm_refl. Qed.
Lemma D_88ac0 : decode_any W_88ac0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_88adc : bv 32 := 0x00040513.
Lemma F_88adc : fetch_word Asan.M.loaded_segments (0x88b2c : word) = Some W_88adc.
Proof. vm_refl. Qed.
Lemma D_88adc : decode_any W_88adc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ae0 : bv 32 := 0x07c000ef.
Lemma F_88ae0 : fetch_word Asan.M.loaded_segments (0x88b30 : word) = Some W_88ae0.
Proof. vm_refl. Qed.
Lemma D_88ae0 : decode_any W_88ae0 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ae4 : bv 32 := 0x0014b517.
Lemma F_88ae4 : fetch_word Asan.M.loaded_segments (0x88b34 : word) = Some W_88ae4.
Proof. vm_refl. Qed.
Lemma D_88ae4 : decode_any W_88ae4 = Some (Auipc 10 331, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ae8 : bv 32 := 0x98c50493.
Lemma F_88ae8 : fetch_word Asan.M.loaded_segments (0x88b38 : word) = Some W_88ae8.
Proof. vm_refl. Qed.
Lemma D_88ae8 : decode_any W_88ae8 = Some (OpImm ALU_ADD 9 10 2444, 4%Z).
Proof. vm_refl. Qed.

Definition W_88aec : bv 32 := 0x0084b583.
Lemma F_88aec : fetch_word Asan.M.loaded_segments (0x88b3c : word) = Some W_88aec.
Proof. vm_refl. Qed.
Lemma D_88aec : decode_any W_88aec = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88af0 : bv 32 := 0x04058663.
Lemma F_88af0 : fetch_word Asan.M.loaded_segments (0x88b40 : word) = Some W_88af0.
Proof. vm_refl. Qed.
Lemma D_88af0 : decode_any W_88af0 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b3c : bv 32 := 0x00000513.
Lemma F_88b3c : fetch_word Asan.M.loaded_segments (0x88b8c : word) = Some W_88b3c.
Proof. vm_refl. Qed.
Lemma D_88b3c : decode_any W_88b3c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b40 : bv 32 := 0x01813083.
Lemma F_88b40 : fetch_word Asan.M.loaded_segments (0x88b90 : word) = Some W_88b40.
Proof. vm_refl. Qed.
Lemma D_88b40 : decode_any W_88b40 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b44 : bv 32 := 0x01013403.
Lemma F_88b44 : fetch_word Asan.M.loaded_segments (0x88b94 : word) = Some W_88b44.
Proof. vm_refl. Qed.
Lemma D_88b44 : decode_any W_88b44 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b48 : bv 32 := 0x00813483.
Lemma F_88b48 : fetch_word Asan.M.loaded_segments (0x88b98 : word) = Some W_88b48.
Proof. vm_refl. Qed.
Lemma D_88b48 : decode_any W_88b48 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b4c : bv 32 := 0x02010113.
Lemma F_88b4c : fetch_word Asan.M.loaded_segments (0x88b9c : word) = Some W_88b4c.
Proof. vm_refl. Qed.
Lemma D_88b4c : decode_any W_88b4c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b50 : bv 32 := 0x00008067.
Lemma F_88b50 : fetch_word Asan.M.loaded_segments (0x88ba0 : word) = Some W_88b50.
Proof. vm_refl. Qed.
Lemma D_88b50 : decode_any W_88b50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b54 : bv 32 := 0x00000513.
Lemma F_88b54 : fetch_word Asan.M.loaded_segments (0x88ba4 : word) = Some W_88b54.
Proof. vm_refl. Qed.
Lemma D_88b54 : decode_any W_88b54 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b58 : bv 32 := 0x00008067.
Lemma F_88b58 : fetch_word Asan.M.loaded_segments (0x88ba8 : word) = Some W_88b58.
Proof. vm_refl. Qed.
Lemma D_88b58 : decode_any W_88b58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b5c : bv 32 := 0x00008067.
Lemma F_88b5c : fetch_word Asan.M.loaded_segments (0x88bac : word) = Some W_88b5c.
Proof. vm_refl. Qed.
Lemma D_88b5c : decode_any W_88b5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
