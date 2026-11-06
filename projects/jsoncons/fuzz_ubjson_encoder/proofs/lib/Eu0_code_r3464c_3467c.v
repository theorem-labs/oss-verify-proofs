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

Definition W_34e1c : bv 32 := 0x00096517.
Lemma F_34e1c : fetch_word Ubsan.M.loaded_segments (0x34e74 : word) = Some W_34e1c.
Proof. vm_refl. Qed.
Lemma D_34e1c : decode_any W_34e1c = Some (Auipc 10 150, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e20 : bv 32 := 0x32054503.
Lemma F_34e20 : fetch_word Ubsan.M.loaded_segments (0x34e78 : word) = Some W_34e20.
Proof. vm_refl. Qed.
Lemma D_34e20 : decode_any W_34e20 = Some (Load SZ1 false 10 10 800, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e24 : bv 32 := 0x00051463.
Lemma F_34e24 : fetch_word Ubsan.M.loaded_segments (0x34e7c : word) = Some W_34e24.
Proof. vm_refl. Qed.
Lemma D_34e24 : decode_any W_34e24 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e28 : bv 32 := 0x00008067.
Lemma F_34e28 : fetch_word Ubsan.M.loaded_segments (0x34e80 : word) = Some W_34e28.
Proof. vm_refl. Qed.
Lemma D_34e28 : decode_any W_34e28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e2c : bv 32 := 0xff010113.
Lemma F_34e2c : fetch_word Ubsan.M.loaded_segments (0x34e84 : word) = Some W_34e2c.
Proof. vm_refl. Qed.
Lemma D_34e2c : decode_any W_34e2c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e30 : bv 32 := 0x00113423.
Lemma F_34e30 : fetch_word Ubsan.M.loaded_segments (0x34e88 : word) = Some W_34e30.
Proof. vm_refl. Qed.
Lemma D_34e30 : decode_any W_34e30 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e34 : bv 32 := 0x00085517.
Lemma F_34e34 : fetch_word Ubsan.M.loaded_segments (0x34e8c : word) = Some W_34e34.
Proof. vm_refl. Qed.
Lemma D_34e34 : decode_any W_34e34 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e38 : bv 32 := 0xe5453503.
Lemma F_34e38 : fetch_word Ubsan.M.loaded_segments (0x34e90 : word) = Some W_34e38.
Proof. vm_refl. Qed.
Lemma D_34e38 : decode_any W_34e38 = Some (Load SZ8 true 10 10 3668, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e3c : bv 32 := 0x00053503.
Lemma F_34e3c : fetch_word Ubsan.M.loaded_segments (0x34e94 : word) = Some W_34e3c.
Proof. vm_refl. Qed.
Lemma D_34e3c : decode_any W_34e3c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e40 : bv 32 := 0x2156d0ef.
Lemma F_34e40 : fetch_word Ubsan.M.loaded_segments (0x34e98 : word) = Some W_34e40.
Proof. vm_refl. Qed.
Lemma D_34e40 : decode_any W_34e40 = Some (Jal 1 449044, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e44 : bv 32 := 0x04d00513.
Lemma F_34e44 : fetch_word Ubsan.M.loaded_segments (0x34e9c : word) = Some W_34e44.
Proof. vm_refl. Qed.
Lemma D_34e44 : decode_any W_34e44 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_34e48 : bv 32 := 0x0007e0ef.
Lemma F_34e48 : fetch_word Ubsan.M.loaded_segments (0x34ea0 : word) = Some W_34e48.
Proof. vm_refl. Qed.
Lemma D_34e48 : decode_any W_34e48 = Some (Jal 1 516096, 4%Z).
Proof. vm_refl. Qed.
