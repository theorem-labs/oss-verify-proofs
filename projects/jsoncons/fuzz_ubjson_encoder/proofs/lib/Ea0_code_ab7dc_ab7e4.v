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

Definition W_ab7dc : bv 32 := 0x420487d3.
Lemma F_ab7dc : fetch_word Asan.M.loaded_segments (0xab82c : word) = Some W_ab7dc.
Proof. vm_refl. Qed.
Lemma D_ab7dc : decode_any W_ab7dc = Some (Fcvt FC_D FC_S 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ab7e0 : bv 32 := 0xa2f525d3.
Lemma F_ab7e0 : fetch_word Asan.M.loaded_segments (0xab830 : word) = Some W_ab7e0.
Proof. vm_refl. Qed.
Lemma D_ab7e0 : decode_any W_ab7e0 = Some (Fcmp F_EQ FMT_D 11 10 15, 4%Z).
Proof. vm_refl. Qed.
