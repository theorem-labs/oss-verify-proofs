(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3a550 : bv 32 := 0xf00507d3.
Lemma F_3a550 : fetch_word Ubsan.M.loaded_segments (0x3a5a8 : word) = Some W_3a550.
Proof. vm_refl. Qed.
Lemma D_3a550 : decode_any W_3a550 = Some (Fmv FMV_F_X FMT_S 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3a554 : bv 32 := 0x42078553.
Lemma F_3a554 : fetch_word Ubsan.M.loaded_segments (0x3a5ac : word) = Some W_3a554.
Proof. vm_refl. Qed.
Lemma D_3a554 : decode_any W_3a554 = Some (Fcvt FC_D FC_S 10 15 0, 4%Z).
Proof. vm_refl. Qed.
