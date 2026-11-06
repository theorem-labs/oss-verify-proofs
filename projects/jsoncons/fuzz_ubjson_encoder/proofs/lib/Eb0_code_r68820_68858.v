(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_83c0c : bv 32 := 0xff010113.
Lemma F_83c0c : fetch_word AsanUbsan.M.loaded_segments (0x83c5c : word) = Some W_83c0c.
Proof. vm_refl. Qed.
Lemma D_83c0c : decode_any W_83c0c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_83c10 : bv 32 := 0x00113423.
Lemma F_83c10 : fetch_word AsanUbsan.M.loaded_segments (0x83c60 : word) = Some W_83c10.
Proof. vm_refl. Qed.
Lemma D_83c10 : decode_any W_83c10 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_83c14 : bv 32 := 0x62d000ef.
Lemma F_83c14 : fetch_word AsanUbsan.M.loaded_segments (0x83c64 : word) = Some W_83c14.
Proof. vm_refl. Qed.
Lemma D_83c14 : decode_any W_83c14 = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_83c18 : bv 32 := 0x00050c63.
Lemma F_83c18 : fetch_word AsanUbsan.M.loaded_segments (0x83c68 : word) = Some W_83c18.
Proof. vm_refl. Qed.
Lemma D_83c18 : decode_any W_83c18 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_83c1c : bv 32 := 0x7ff50513.
Lemma F_83c1c : fetch_word AsanUbsan.M.loaded_segments (0x83c6c : word) = Some W_83c1c.
Proof. vm_refl. Qed.
Lemma D_83c1c : decode_any W_83c1c = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_83c20 : bv 32 := 0x2f150513.
Lemma F_83c20 : fetch_word AsanUbsan.M.loaded_segments (0x83c70 : word) = Some W_83c20.
Proof. vm_refl. Qed.
Lemma D_83c20 : decode_any W_83c20 = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

Definition W_83c24 : bv 32 := 0x00813083.
Lemma F_83c24 : fetch_word AsanUbsan.M.loaded_segments (0x83c74 : word) = Some W_83c24.
Proof. vm_refl. Qed.
Lemma D_83c24 : decode_any W_83c24 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_83c28 : bv 32 := 0x01010113.
Lemma F_83c28 : fetch_word AsanUbsan.M.loaded_segments (0x83c78 : word) = Some W_83c28.
Proof. vm_refl. Qed.
Lemma D_83c28 : decode_any W_83c28 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_83c2c : bv 32 := 0x00008067.
Lemma F_83c2c : fetch_word AsanUbsan.M.loaded_segments (0x83c7c : word) = Some W_83c2c.
Proof. vm_refl. Qed.
Lemma D_83c2c : decode_any W_83c2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
