(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_e7a60 : bv 32 := 0xff010113.

Definition W_e7a64 : bv 32 := 0x00113423.

Definition W_e7a68 : bv 32 := 0x8c0ea0ef.

Definition W_e7a6c : bv 32 := 0xff010113.
Lemma F_e7a6c : fetch_word Ubsan.M.loaded_segments (0xe7aa0 : word) = Some W_e7a6c.
Proof. vm_refl. Qed.
Lemma D_e7a6c : decode_any W_e7a6c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a70 : bv 32 := 0x00113423.
Lemma F_e7a70 : fetch_word Ubsan.M.loaded_segments (0xe7aa4 : word) = Some W_e7a70.
Proof. vm_refl. Qed.
Lemma D_e7a70 : decode_any W_e7a70 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a74 : bv 32 := 0xfc4ef0ef.
Lemma F_e7a74 : fetch_word Ubsan.M.loaded_segments (0xe7aa8 : word) = Some W_e7a74.
Proof. vm_refl. Qed.
Lemma D_e7a74 : decode_any W_e7a74 = Some (Jal 1 2029508, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a78 : bv 32 := 0x00050593.
Lemma F_e7a78 : fetch_word Ubsan.M.loaded_segments (0xe7aac : word) = Some W_e7a78.
Proof. vm_refl. Qed.
Lemma D_e7a78 : decode_any W_e7a78 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a7c : bv 32 := 0x03900513.
Lemma F_e7a7c : fetch_word Ubsan.M.loaded_segments (0xe7ab0 : word) = Some W_e7a7c.
Proof. vm_refl. Qed.
Lemma D_e7a7c : decode_any W_e7a7c = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a80 : bv 32 := 0x00000613.
Lemma F_e7a80 : fetch_word Ubsan.M.loaded_segments (0xe7ab4 : word) = Some W_e7a80.
Proof. vm_refl. Qed.
Lemma D_e7a80 : decode_any W_e7a80 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a84 : bv 32 := 0x00000693.
Lemma F_e7a84 : fetch_word Ubsan.M.loaded_segments (0xe7ab8 : word) = Some W_e7a84.
Proof. vm_refl. Qed.
Lemma D_e7a84 : decode_any W_e7a84 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a88 : bv 32 := 0x00000713.
Lemma F_e7a88 : fetch_word Ubsan.M.loaded_segments (0xe7abc : word) = Some W_e7a88.
Proof. vm_refl. Qed.
Lemma D_e7a88 : decode_any W_e7a88 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a8c : bv 32 := 0x00000793.
Lemma F_e7a8c : fetch_word Ubsan.M.loaded_segments (0xe7ac0 : word) = Some W_e7a8c.
Proof. vm_refl. Qed.
Lemma D_e7a8c : decode_any W_e7a8c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a90 : bv 32 := 0x00000813.
Lemma F_e7a90 : fetch_word Ubsan.M.loaded_segments (0xe7ac4 : word) = Some W_e7a90.
Proof. vm_refl. Qed.
Lemma D_e7a90 : decode_any W_e7a90 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a94 : bv 32 := 0x8e4fc0ef.
Lemma F_e7a94 : fetch_word Ubsan.M.loaded_segments (0xe7ac8 : word) = Some W_e7a94.
Proof. vm_refl. Qed.
Lemma D_e7a94 : decode_any W_e7a94 = Some (Jal 1 2080996, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a98 : bv 32 := 0x0005051b.
Lemma F_e7a98 : fetch_word Ubsan.M.loaded_segments (0xe7acc : word) = Some W_e7a98.
Proof. vm_refl. Qed.
Lemma D_e7a98 : decode_any W_e7a98 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7a9c : bv 32 := 0x00450593.
Lemma F_e7a9c : fetch_word Ubsan.M.loaded_segments (0xe7ad0 : word) = Some W_e7a9c.
Proof. vm_refl. Qed.
Lemma D_e7a9c : decode_any W_e7a9c = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7aa0 : bv 32 := 0x0015b593.
Lemma F_e7aa0 : fetch_word Ubsan.M.loaded_segments (0xe7ad4 : word) = Some W_e7aa0.
Proof. vm_refl. Qed.
Lemma D_e7aa0 : decode_any W_e7aa0 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7aa4 : bv 32 := 0xfff58593.
Lemma F_e7aa4 : fetch_word Ubsan.M.loaded_segments (0xe7ad8 : word) = Some W_e7aa4.
Proof. vm_refl. Qed.
Lemma D_e7aa4 : decode_any W_e7aa4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7aa8 : bv 32 := 0x00a5f533.
Lemma F_e7aa8 : fetch_word Ubsan.M.loaded_segments (0xe7adc : word) = Some W_e7aa8.
Proof. vm_refl. Qed.
Lemma D_e7aa8 : decode_any W_e7aa8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7aac : bv 32 := 0xd34ea0ef.
Lemma F_e7aac : fetch_word Ubsan.M.loaded_segments (0xe7ae0 : word) = Some W_e7aac.
Proof. vm_refl. Qed.
Lemma D_e7aac : decode_any W_e7aac = Some (Jal 1 2008372, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ab0 : bv 32 := 0x0005051b.
Lemma F_e7ab0 : fetch_word Ubsan.M.loaded_segments (0xe7ae4 : word) = Some W_e7ab0.
Proof. vm_refl. Qed.
Lemma D_e7ab0 : decode_any W_e7ab0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ab4 : bv 32 := 0x00813083.
Lemma F_e7ab4 : fetch_word Ubsan.M.loaded_segments (0xe7ae8 : word) = Some W_e7ab4.
Proof. vm_refl. Qed.
Lemma D_e7ab4 : decode_any W_e7ab4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ab8 : bv 32 := 0x01010113.
Lemma F_e7ab8 : fetch_word Ubsan.M.loaded_segments (0xe7aec : word) = Some W_e7ab8.
Proof. vm_refl. Qed.
Lemma D_e7ab8 : decode_any W_e7ab8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7abc : bv 32 := 0x00008067.
Lemma F_e7abc : fetch_word Ubsan.M.loaded_segments (0xe7af0 : word) = Some W_e7abc.
Proof. vm_refl. Qed.
Lemma D_e7abc : decode_any W_e7abc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7acc : bv 32 := 0xff010113.
Lemma F_e7acc : fetch_word Ubsan.M.loaded_segments (0xe7b00 : word) = Some W_e7acc.
Proof. vm_refl. Qed.
Lemma D_e7acc : decode_any W_e7acc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ad0 : bv 32 := 0x00113423.
Lemma F_e7ad0 : fetch_word Ubsan.M.loaded_segments (0xe7b04 : word) = Some W_e7ad0.
Proof. vm_refl. Qed.
Lemma D_e7ad0 : decode_any W_e7ad0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ad4 : bv 32 := 0x00060693.
Lemma F_e7ad4 : fetch_word Ubsan.M.loaded_segments (0xe7b08 : word) = Some W_e7ad4.
Proof. vm_refl. Qed.
Lemma D_e7ad4 : decode_any W_e7ad4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ad8 : bv 32 := 0x00058613.
Lemma F_e7ad8 : fetch_word Ubsan.M.loaded_segments (0xe7b0c : word) = Some W_e7ad8.
Proof. vm_refl. Qed.
Lemma D_e7ad8 : decode_any W_e7ad8 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7adc : bv 32 := 0x00050593.
Lemma F_e7adc : fetch_word Ubsan.M.loaded_segments (0xe7b10 : word) = Some W_e7adc.
Proof. vm_refl. Qed.
Lemma D_e7adc : decode_any W_e7adc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ae0 : bv 32 := 0x03f00513.
Lemma F_e7ae0 : fetch_word Ubsan.M.loaded_segments (0xe7b14 : word) = Some W_e7ae0.
Proof. vm_refl. Qed.
Lemma D_e7ae0 : decode_any W_e7ae0 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ae4 : bv 32 := 0x00000713.
Lemma F_e7ae4 : fetch_word Ubsan.M.loaded_segments (0xe7b18 : word) = Some W_e7ae4.
Proof. vm_refl. Qed.
Lemma D_e7ae4 : decode_any W_e7ae4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7ae8 : bv 32 := 0x00000793.
Lemma F_e7ae8 : fetch_word Ubsan.M.loaded_segments (0xe7b1c : word) = Some W_e7ae8.
Proof. vm_refl. Qed.
Lemma D_e7ae8 : decode_any W_e7ae8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7aec : bv 32 := 0x00000813.
Lemma F_e7aec : fetch_word Ubsan.M.loaded_segments (0xe7b20 : word) = Some W_e7aec.
Proof. vm_refl. Qed.
Lemma D_e7aec : decode_any W_e7aec = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7af0 : bv 32 := 0x888fc0ef.
Lemma F_e7af0 : fetch_word Ubsan.M.loaded_segments (0xe7b24 : word) = Some W_e7af0.
Proof. vm_refl. Qed.
Lemma D_e7af0 : decode_any W_e7af0 = Some (Jal 1 2080904, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7af4 : bv 32 := 0x00813083.
Lemma F_e7af4 : fetch_word Ubsan.M.loaded_segments (0xe7b28 : word) = Some W_e7af4.
Proof. vm_refl. Qed.
Lemma D_e7af4 : decode_any W_e7af4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7af8 : bv 32 := 0x01010113.
Lemma F_e7af8 : fetch_word Ubsan.M.loaded_segments (0xe7b2c : word) = Some W_e7af8.
Proof. vm_refl. Qed.
Lemma D_e7af8 : decode_any W_e7af8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7afc : bv 32 := 0xce4ea06f.
Lemma F_e7afc : fetch_word Ubsan.M.loaded_segments (0xe7b30 : word) = Some W_e7afc.
Proof. vm_refl. Qed.
Lemma D_e7afc : decode_any W_e7afc = Some (Jal 0 2008292, 4%Z).
Proof. vm_refl. Qed.

Definition W_e7b00 : bv 32 := 0xff010113.

Definition W_e7b04 : bv 32 := 0x00113423.

Definition W_e7b08 : bv 32 := 0x00813023.

Definition W_e7b0c : bv 32 := 0x00153413.

Definition W_e7b10 : bv 32 := 0x00850433.

Definition W_e7b14 : bv 32 := 0x00040513.

Definition W_e7b18 : bv 32 := 0xaecec0ef.

Definition W_e7b1c : bv 32 := 0x00051e63.

Definition W_e7b38 : bv 32 := 0x00813083.

Definition W_e7b3c : bv 32 := 0x00013403.

Definition W_e7b40 : bv 32 := 0x01010113.

Definition W_e7b44 : bv 32 := 0x00008067.

