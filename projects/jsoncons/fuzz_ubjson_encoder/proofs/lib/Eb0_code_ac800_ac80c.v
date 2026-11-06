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

Definition W_ac800 : bv 32 := 0x401574d3.
Lemma F_ac800 : fetch_word AsanUbsan.M.loaded_segments (0xac850 : word) = Some W_ac800.
Proof. vm_refl. Qed.
Lemma D_ac800 : decode_any W_ac800 = Some (Fcvt FC_S FC_D 9 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac804 : bv 32 := 0x420487d3.
Lemma F_ac804 : fetch_word AsanUbsan.M.loaded_segments (0xac854 : word) = Some W_ac804.
Proof. vm_refl. Qed.
Lemma D_ac804 : decode_any W_ac804 = Some (Fcvt FC_D FC_S 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac808 : bv 32 := 0xa2f52653.
Lemma F_ac808 : fetch_word AsanUbsan.M.loaded_segments (0xac858 : word) = Some W_ac808.
Proof. vm_refl. Qed.
Lemma D_ac808 : decode_any W_ac808 = Some (Fcmp F_EQ FMT_D 12 10 15, 4%Z).
Proof. vm_refl. Qed.
