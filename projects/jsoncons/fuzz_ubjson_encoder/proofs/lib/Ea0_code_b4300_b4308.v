(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b4300 : bv 32 := 0xf00587d3.
Lemma F_b4300 : fetch_word Asan.M.loaded_segments (0xb4350 : word) = Some W_b4300.
Proof. vm_refl. Qed.
Lemma D_b4300 : decode_any W_b4300 = Some (Fmv FMV_F_X FMT_S 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_b4304 : bv 32 := 0x42078553.
Lemma F_b4304 : fetch_word Asan.M.loaded_segments (0xb4354 : word) = Some W_b4304.
Proof. vm_refl. Qed.
Lemma D_b4304 : decode_any W_b4304 = Some (Fcvt FC_D FC_S 10 15 0, 4%Z).
Proof. vm_refl. Qed.
