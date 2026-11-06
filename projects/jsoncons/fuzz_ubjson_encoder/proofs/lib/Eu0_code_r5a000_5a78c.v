(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b067c : bv 32 := 0x00050213.
Lemma F_b067c : fetch_word Ubsan.M.loaded_segments (0xb06c8 : word) = Some W_b067c.
Proof. vm_refl. Qed.
Lemma D_b067c : decode_any W_b067c = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b0680 : bv 32 := 0x00000513.
Lemma F_b0680 : fetch_word Ubsan.M.loaded_segments (0xb06cc : word) = Some W_b0680.
Proof. vm_refl. Qed.
Lemma D_b0680 : decode_any W_b0680 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b0684 : bv 32 := 0x00008067.
Lemma F_b0684 : fetch_word Ubsan.M.loaded_segments (0xb06d0 : word) = Some W_b0684.
Proof. vm_refl. Qed.
Lemma D_b0684 : decode_any W_b0684 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e60 : bv 32 := 0xff010113.
Lemma F_b2e60 : fetch_word Ubsan.M.loaded_segments (0xb2eac : word) = Some W_b2e60.
Proof. vm_refl. Qed.
Lemma D_b2e60 : decode_any W_b2e60 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e64 : bv 32 := 0x00113423.
Lemma F_b2e64 : fetch_word Ubsan.M.loaded_segments (0xb2eb0 : word) = Some W_b2e64.
Proof. vm_refl. Qed.
Lemma D_b2e64 : decode_any W_b2e64 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e68 : bv 32 := 0xe5def0ef.
Lemma F_b2e68 : fetch_word Ubsan.M.loaded_segments (0xb2eb4 : word) = Some W_b2e68.
Proof. vm_refl. Qed.
Lemma D_b2e68 : decode_any W_b2e68 = Some (Jal 1 2031196, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e6c : bv 32 := 0x00050593.
Lemma F_b2e6c : fetch_word Ubsan.M.loaded_segments (0xb2eb8 : word) = Some W_b2e6c.
Proof. vm_refl. Qed.
Lemma D_b2e6c : decode_any W_b2e6c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e70 : bv 32 := 0x03900513.
Lemma F_b2e70 : fetch_word Ubsan.M.loaded_segments (0xb2ebc : word) = Some W_b2e70.
Proof. vm_refl. Qed.
Lemma D_b2e70 : decode_any W_b2e70 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e74 : bv 32 := 0x00000613.
Lemma F_b2e74 : fetch_word Ubsan.M.loaded_segments (0xb2ec0 : word) = Some W_b2e74.
Proof. vm_refl. Qed.
Lemma D_b2e74 : decode_any W_b2e74 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e78 : bv 32 := 0x00000693.
Lemma F_b2e78 : fetch_word Ubsan.M.loaded_segments (0xb2ec4 : word) = Some W_b2e78.
Proof. vm_refl. Qed.
Lemma D_b2e78 : decode_any W_b2e78 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e7c : bv 32 := 0x00000713.
Lemma F_b2e7c : fetch_word Ubsan.M.loaded_segments (0xb2ec8 : word) = Some W_b2e7c.
Proof. vm_refl. Qed.
Lemma D_b2e7c : decode_any W_b2e7c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e80 : bv 32 := 0x00000793.
Lemma F_b2e80 : fetch_word Ubsan.M.loaded_segments (0xb2ecc : word) = Some W_b2e80.
Proof. vm_refl. Qed.
Lemma D_b2e80 : decode_any W_b2e80 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e84 : bv 32 := 0x00000813.
Lemma F_b2e84 : fetch_word Ubsan.M.loaded_segments (0xb2ed0 : word) = Some W_b2e84.
Proof. vm_refl. Qed.
Lemma D_b2e84 : decode_any W_b2e84 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e88 : bv 32 := 0x8e4fc0ef.
Lemma F_b2e88 : fetch_word Ubsan.M.loaded_segments (0xb2ed4 : word) = Some W_b2e88.
Proof. vm_refl. Qed.
Lemma D_b2e88 : decode_any W_b2e88 = Some (Jal 1 2080996, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e8c : bv 32 := 0x0005051b.
Lemma F_b2e8c : fetch_word Ubsan.M.loaded_segments (0xb2ed8 : word) = Some W_b2e8c.
Proof. vm_refl. Qed.
Lemma D_b2e8c : decode_any W_b2e8c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e90 : bv 32 := 0x00450593.
Lemma F_b2e90 : fetch_word Ubsan.M.loaded_segments (0xb2edc : word) = Some W_b2e90.
Proof. vm_refl. Qed.
Lemma D_b2e90 : decode_any W_b2e90 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e94 : bv 32 := 0x0015b593.
Lemma F_b2e94 : fetch_word Ubsan.M.loaded_segments (0xb2ee0 : word) = Some W_b2e94.
Proof. vm_refl. Qed.
Lemma D_b2e94 : decode_any W_b2e94 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e98 : bv 32 := 0xfff58593.
Lemma F_b2e98 : fetch_word Ubsan.M.loaded_segments (0xb2ee4 : word) = Some W_b2e98.
Proof. vm_refl. Qed.
Lemma D_b2e98 : decode_any W_b2e98 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2e9c : bv 32 := 0x00a5f533.
Lemma F_b2e9c : fetch_word Ubsan.M.loaded_segments (0xb2ee8 : word) = Some W_b2e9c.
Proof. vm_refl. Qed.
Lemma D_b2e9c : decode_any W_b2e9c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ea0 : bv 32 := 0xc49ea0ef.
Lemma F_b2ea0 : fetch_word Ubsan.M.loaded_segments (0xb2eec : word) = Some W_b2ea0.
Proof. vm_refl. Qed.
Lemma D_b2ea0 : decode_any W_b2ea0 = Some (Jal 1 2010184, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ea4 : bv 32 := 0x0005051b.
Lemma F_b2ea4 : fetch_word Ubsan.M.loaded_segments (0xb2ef0 : word) = Some W_b2ea4.
Proof. vm_refl. Qed.
Lemma D_b2ea4 : decode_any W_b2ea4 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ea8 : bv 32 := 0x00813083.
Lemma F_b2ea8 : fetch_word Ubsan.M.loaded_segments (0xb2ef4 : word) = Some W_b2ea8.
Proof. vm_refl. Qed.
Lemma D_b2ea8 : decode_any W_b2ea8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2eac : bv 32 := 0x01010113.
Lemma F_b2eac : fetch_word Ubsan.M.loaded_segments (0xb2ef8 : word) = Some W_b2eac.
Proof. vm_refl. Qed.
Lemma D_b2eac : decode_any W_b2eac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2eb0 : bv 32 := 0x00008067.
Lemma F_b2eb0 : fetch_word Ubsan.M.loaded_segments (0xb2efc : word) = Some W_b2eb0.
Proof. vm_refl. Qed.
Lemma D_b2eb0 : decode_any W_b2eb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ec0 : bv 32 := 0xff010113.
Lemma F_b2ec0 : fetch_word Ubsan.M.loaded_segments (0xb2f0c : word) = Some W_b2ec0.
Proof. vm_refl. Qed.
Lemma D_b2ec0 : decode_any W_b2ec0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ec4 : bv 32 := 0x00113423.
Lemma F_b2ec4 : fetch_word Ubsan.M.loaded_segments (0xb2f10 : word) = Some W_b2ec4.
Proof. vm_refl. Qed.
Lemma D_b2ec4 : decode_any W_b2ec4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ec8 : bv 32 := 0x00060693.
Lemma F_b2ec8 : fetch_word Ubsan.M.loaded_segments (0xb2f14 : word) = Some W_b2ec8.
Proof. vm_refl. Qed.
Lemma D_b2ec8 : decode_any W_b2ec8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ecc : bv 32 := 0x00058613.
Lemma F_b2ecc : fetch_word Ubsan.M.loaded_segments (0xb2f18 : word) = Some W_b2ecc.
Proof. vm_refl. Qed.
Lemma D_b2ecc : decode_any W_b2ecc = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ed0 : bv 32 := 0x00050593.
Lemma F_b2ed0 : fetch_word Ubsan.M.loaded_segments (0xb2f1c : word) = Some W_b2ed0.
Proof. vm_refl. Qed.
Lemma D_b2ed0 : decode_any W_b2ed0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ed4 : bv 32 := 0x03f00513.
Lemma F_b2ed4 : fetch_word Ubsan.M.loaded_segments (0xb2f20 : word) = Some W_b2ed4.
Proof. vm_refl. Qed.
Lemma D_b2ed4 : decode_any W_b2ed4 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ed8 : bv 32 := 0x00000713.
Lemma F_b2ed8 : fetch_word Ubsan.M.loaded_segments (0xb2f24 : word) = Some W_b2ed8.
Proof. vm_refl. Qed.
Lemma D_b2ed8 : decode_any W_b2ed8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2edc : bv 32 := 0x00000793.
Lemma F_b2edc : fetch_word Ubsan.M.loaded_segments (0xb2f28 : word) = Some W_b2edc.
Proof. vm_refl. Qed.
Lemma D_b2edc : decode_any W_b2edc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ee0 : bv 32 := 0x00000813.
Lemma F_b2ee0 : fetch_word Ubsan.M.loaded_segments (0xb2f2c : word) = Some W_b2ee0.
Proof. vm_refl. Qed.
Lemma D_b2ee0 : decode_any W_b2ee0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ee4 : bv 32 := 0x888fc0ef.
Lemma F_b2ee4 : fetch_word Ubsan.M.loaded_segments (0xb2f30 : word) = Some W_b2ee4.
Proof. vm_refl. Qed.
Lemma D_b2ee4 : decode_any W_b2ee4 = Some (Jal 1 2080904, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ee8 : bv 32 := 0x00813083.
Lemma F_b2ee8 : fetch_word Ubsan.M.loaded_segments (0xb2f34 : word) = Some W_b2ee8.
Proof. vm_refl. Qed.
Lemma D_b2ee8 : decode_any W_b2ee8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2eec : bv 32 := 0x01010113.
Lemma F_b2eec : fetch_word Ubsan.M.loaded_segments (0xb2f38 : word) = Some W_b2eec.
Proof. vm_refl. Qed.
Lemma D_b2eec : decode_any W_b2eec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2ef0 : bv 32 := 0xbf9ea06f.
Lemma F_b2ef0 : fetch_word Ubsan.M.loaded_segments (0xb2f3c : word) = Some W_b2ef0.
Proof. vm_refl. Qed.
Lemma D_b2ef0 : decode_any W_b2ef0 = Some (Jal 0 2010104, 4%Z).
Proof. vm_refl. Qed.

Definition W_b2f38 : bv 32 := 0x00008067.
Lemma F_b2f38 : fetch_word Ubsan.M.loaded_segments (0xb2f84 : word) = Some W_b2f38.
Proof. vm_refl. Qed.
Lemma D_b2f38 : decode_any W_b2f38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
