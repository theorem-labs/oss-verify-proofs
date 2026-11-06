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

Definition W_b0aac : bv 32 := 0x03161633.
Lemma F_b0aac : fetch_word AsanUbsan.M.loaded_segments (0xb0afc : word) = Some W_b0aac.
Proof. vm_refl. Qed.
Lemma D_b0aac : decode_any W_b0aac = Some (Mul M_MULH 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_b0ab0 : bv 32 := 0x43f85813.
Lemma F_b0ab0 : fetch_word AsanUbsan.M.loaded_segments (0xb0b00 : word) = Some W_b0ab0.
Proof. vm_refl. Qed.
Lemma D_b0ab0 : decode_any W_b0ab0 = Some (ShiftImm ALU_SRA 16 16 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_b0ab4 : bv 32 := 0x01064633.
Lemma F_b0ab4 : fetch_word AsanUbsan.M.loaded_segments (0xb0b04 : word) = Some W_b0ab4.
Proof. vm_refl. Qed.
Lemma D_b0ab4 : decode_any W_b0ab4 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b0ab8 : bv 32 := 0x00c03633.
Lemma F_b0ab8 : fetch_word AsanUbsan.M.loaded_segments (0xb0b08 : word) = Some W_b0ab8.
Proof. vm_refl. Qed.
Lemma D_b0ab8 : decode_any W_b0ab8 = Some (Op ALU_SLTU 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b0abc : bv 32 := 0x04061063.
Lemma F_b0abc : fetch_word AsanUbsan.M.loaded_segments (0xb0b0c : word) = Some W_b0abc.
Proof. vm_refl. Qed.
Lemma D_b0abc : decode_any W_b0abc = Some (Branch BC_NE 12 0 64, 4%Z).
Proof. vm_refl. Qed.
