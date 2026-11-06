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

Definition W_130bd0 : bv 32 := 0x00020593.
Lemma F_130bd0 : fetch_word AsanUbsan.M.loaded_segments (0x130c14 : word) = Some W_130bd0.
Proof. vm_refl. Qed.
Lemma D_130bd0 : decode_any W_130bd0 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bd4 : bv 32 := 0x00053603.
Lemma F_130bd4 : fetch_word AsanUbsan.M.loaded_segments (0x130c18 : word) = Some W_130bd4.
Proof. vm_refl. Qed.
Lemma D_130bd4 : decode_any W_130bd4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bd8 : bv 32 := 0xff85b583.
Lemma F_130bd8 : fetch_word AsanUbsan.M.loaded_segments (0x130c1c : word) = Some W_130bd8.
Proof. vm_refl. Qed.
Lemma D_130bd8 : decode_any W_130bd8 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bdc : bv 32 := 0x00853503.
Lemma F_130bdc : fetch_word AsanUbsan.M.loaded_segments (0x130c20 : word) = Some W_130bdc.
Proof. vm_refl. Qed.
Lemma D_130bdc : decode_any W_130bdc = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_130be0 : bv 32 := 0x00361613.
Lemma F_130be0 : fetch_word AsanUbsan.M.loaded_segments (0x130c24 : word) = Some W_130be0.
Proof. vm_refl. Qed.
Lemma D_130be0 : decode_any W_130be0 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_130be4 : bv 32 := 0x00c585b3.
Lemma F_130be4 : fetch_word AsanUbsan.M.loaded_segments (0x130c28 : word) = Some W_130be4.
Proof. vm_refl. Qed.
Lemma D_130be4 : decode_any W_130be4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_130be8 : bv 32 := 0x0005b583.
Lemma F_130be8 : fetch_word AsanUbsan.M.loaded_segments (0x130c2c : word) = Some W_130be8.
Proof. vm_refl. Qed.
Lemma D_130be8 : decode_any W_130be8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bec : bv 32 := 0x00b50533.
Lemma F_130bec : fetch_word AsanUbsan.M.loaded_segments (0x130c30 : word) = Some W_130bec.
Proof. vm_refl. Qed.
Lemma D_130bec : decode_any W_130bec = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bf0 : bv 32 := 0x00008067.
Lemma F_130bf0 : fetch_word AsanUbsan.M.loaded_segments (0x130c34 : word) = Some W_130bf0.
Proof. vm_refl. Qed.
Lemma D_130bf0 : decode_any W_130bf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
