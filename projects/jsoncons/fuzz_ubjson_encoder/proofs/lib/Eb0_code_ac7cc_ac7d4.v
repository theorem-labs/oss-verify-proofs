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

Definition W_ac7cc : bv 32 := 0x00813c27.
Lemma F_ac7cc : fetch_word AsanUbsan.M.loaded_segments (0xac81c : word) = Some W_ac7cc.
Proof. vm_refl. Qed.
Lemma D_ac7cc : decode_any W_ac7cc = Some (FStore FMT_D 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac7d0 : bv 32 := 0x00913827.
Lemma F_ac7d0 : fetch_word AsanUbsan.M.loaded_segments (0xac820 : word) = Some W_ac7d0.
Proof. vm_refl. Qed.
Lemma D_ac7d0 : decode_any W_ac7d0 = Some (FStore FMT_D 2 9 16, 4%Z).
Proof. vm_refl. Qed.
