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

Definition W_ad9ac : bv 32 := 0x00395593.
Lemma F_ad9ac : fetch_word AsanUbsan.M.loaded_segments (0xad9fc : word) = Some W_ad9ac.
Proof. vm_refl. Qed.
Lemma D_ad9ac : decode_any W_ad9ac = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad9b0 : bv 32 := 0x015585b3.
Lemma F_ad9b0 : fetch_word AsanUbsan.M.loaded_segments (0xada00 : word) = Some W_ad9b0.
Proof. vm_refl. Qed.
Lemma D_ad9b0 : decode_any W_ad9b0 = Some (Op ALU_ADD 11 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad9b4 : bv 32 := 0x00058583.
Lemma F_ad9b4 : fetch_word AsanUbsan.M.loaded_segments (0xada04 : word) = Some W_ad9b4.
Proof. vm_refl. Qed.
Lemma D_ad9b4 : decode_any W_ad9b4 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad9b8 : bv 32 := 0x02059663.
Lemma F_ad9b8 : fetch_word AsanUbsan.M.loaded_segments (0xada08 : word) = Some W_ad9b8.
Proof. vm_refl. Qed.
Lemma D_ad9b8 : decode_any W_ad9b8 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.
