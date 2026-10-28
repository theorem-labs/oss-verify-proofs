(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2d634 : bv 32 := 0xd01477d3.
Lemma F_2d634 : fetch_word Ubsan.M.loaded_segments (0x39724 : word) = Some W_2d634.
Proof. vm_refl. Qed.
Lemma D_2d634 : decode_any W_2d634 = Some (Fcvt FC_S FC_WU 15 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d730 : bv 32 := 0xd014f7d3.
Lemma F_2d730 : fetch_word Ubsan.M.loaded_segments (0x39820 : word) = Some W_2d730.
Proof. vm_refl. Qed.
Lemma D_2d730 : decode_any W_2d730 = Some (Fcvt FC_S FC_WU 15 9 7, 4%Z).
Proof. vm_refl. Qed.

