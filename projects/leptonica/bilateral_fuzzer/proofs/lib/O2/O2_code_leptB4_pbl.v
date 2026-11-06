(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2d2ec : bv 32 := 0xd014f7d3.
Lemma F_2d2ec : fetch_word Plain.M.loaded_segments (0x2d344 : word) = Some W_2d2ec.
Proof. vm_refl. Qed.
Lemma D_2d2ec : decode_any W_2d2ec = Some (Fcvt FC_S FC_WU 15 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d428 : bv 32 := 0xd01977d3.
Lemma F_2d428 : fetch_word Plain.M.loaded_segments (0x2d480 : word) = Some W_2d428.
Proof. vm_refl. Qed.
Lemma D_2d428 : decode_any W_2d428 = Some (Fcvt FC_S FC_WU 15 18 7, 4%Z).
Proof. vm_refl. Qed.

