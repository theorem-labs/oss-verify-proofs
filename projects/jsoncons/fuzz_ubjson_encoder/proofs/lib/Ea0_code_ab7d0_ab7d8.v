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

Definition W_ab7d0 : bv 32 := 0x22a50453.
Lemma F_ab7d0 : fetch_word Asan.M.loaded_segments (0xab820 : word) = Some W_ab7d0.
Proof. vm_refl. Qed.
Lemma D_ab7d0 : decode_any W_ab7d0 = Some (Fsgnj F_SGNJ FMT_D 8 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ab7d4 : bv 32 := 0x401574d3.
Lemma F_ab7d4 : fetch_word Asan.M.loaded_segments (0xab824 : word) = Some W_ab7d4.
Proof. vm_refl. Qed.
Lemma D_ab7d4 : decode_any W_ab7d4 = Some (Fcvt FC_S FC_D 9 10 7, 4%Z).
Proof. vm_refl. Qed.
