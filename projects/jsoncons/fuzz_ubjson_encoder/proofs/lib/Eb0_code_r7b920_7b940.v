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

Definition W_96d28 : bv 32 := 0xfe010113.
Lemma F_96d28 : fetch_word AsanUbsan.M.loaded_segments (0x96d78 : word) = Some W_96d28.
Proof. vm_refl. Qed.
Lemma D_96d28 : decode_any W_96d28 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_96e74 : bv 32 := 0x00058513.
Lemma F_96e74 : fetch_word AsanUbsan.M.loaded_segments (0x96ec4 : word) = Some W_96e74.
Proof. vm_refl. Qed.
Lemma D_96e74 : decode_any W_96e74 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96e78 : bv 32 := 0x00060593.
Lemma F_96e78 : fetch_word AsanUbsan.M.loaded_segments (0x96ec8 : word) = Some W_96e78.
Proof. vm_refl. Qed.
Lemma D_96e78 : decode_any W_96e78 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96e7c : bv 32 := 0x00068613.
Lemma F_96e7c : fetch_word AsanUbsan.M.loaded_segments (0x96ecc : word) = Some W_96e7c.
Proof. vm_refl. Qed.
Lemma D_96e7c : decode_any W_96e7c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96e80 : bv 32 := 0xc65f706f.
Lemma F_96e80 : fetch_word AsanUbsan.M.loaded_segments (0x96ed0 : word) = Some W_96e80.
Proof. vm_refl. Qed.
Lemma D_96e80 : decode_any W_96e80 = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.
