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

Definition W_ad9e4 : bv 32 := 0x00797613.
Lemma F_ad9e4 : fetch_word AsanUbsan.M.loaded_segments (0xada34 : word) = Some W_ad9e4.
Proof. vm_refl. Qed.
Lemma D_ad9e4 : decode_any W_ad9e4 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad9e8 : bv 32 := 0xfcb64ae3.
Lemma F_ad9e8 : fetch_word AsanUbsan.M.loaded_segments (0xada38 : word) = Some W_ad9e8.
Proof. vm_refl. Qed.
Lemma D_ad9e8 : decode_any W_ad9e8 = Some (Branch BC_LT 12 11 8148, 4%Z).
Proof. vm_refl. Qed.
