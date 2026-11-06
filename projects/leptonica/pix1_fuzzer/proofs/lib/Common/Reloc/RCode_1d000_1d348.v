(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode CanonCode RelocSites CanonSites.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1d17c : bv 32 := 0x00008067.
Lemma D_1d17c : decode_any W_1d17c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1d2a8 : bv 32 := 0x00050213.
Lemma D_1d2a8 : decode_any W_1d2a8 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1d2ac : bv 32 := 0x00000513.
Lemma D_1d2ac : decode_any W_1d2ac = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1d2b0 : bv 32 := 0x00008067.
Lemma D_1d2b0 : decode_any W_1d2b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Section F.
Context {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
Lemma F_1d17c : fetch_word rl_segs (rl (rl_delta 1094%positive) 0x1d17c) = Some W_1d17c.
Proof. rl_F 94%nat cc_1cf84. Qed.
Lemma F_1d2a8 : fetch_word rl_segs (rl (rl_delta 1098%positive) 0x1d2a8) = Some W_1d2a8.
Proof. rl_F 98%nat cc_1d2a8. Qed.
Lemma F_1d2ac : fetch_word rl_segs (rl (rl_delta 1098%positive) 0x1d2ac) = Some W_1d2ac.
Proof. rl_F 98%nat cc_1d2a8. Qed.
Lemma F_1d2b0 : fetch_word rl_segs (rl (rl_delta 1098%positive) 0x1d2b0) = Some W_1d2b0.
Proof. rl_F 98%nat cc_1d2a8. Qed.
End F.
