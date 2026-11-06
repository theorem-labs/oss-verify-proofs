(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.double_conversion.string_to_double_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) =>
(lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Local Notation "'F!' a w" := (fetch_word Ubsan.M.loaded_segments (a : word) = Some w) (at level 200, a at level 0, w at level 0, only parsing).
Local Notation "'D!' w i" := (decode_any w = Some (i, 4%Z)) (at level 200, w at level 0, i at level 0, only parsing).
Local Notation "'D2!' w i" := (decode_any w = Some (i, 2%Z)) (at level 200, w at level 0, i at level 0, only parsing).
Definition W_a9448 : bv 32 := 0x00050213.
Lemma F_a9448 : F! 0xa9448 W_a9448.
Proof. vm_refl. Qed.
Lemma D_a9448 : D! W_a9448 (OpImm ALU_ADD 4 10 0).
Proof. vm_refl. Qed.
Definition W_a944c : bv 32 := 0x00000513.
Lemma F_a944c : F! 0xa944c W_a944c.
Proof. vm_refl. Qed.
Lemma D_a944c : D! W_a944c (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_a9450 : bv 32 := 0x00008067.
Lemma F_a9450 : F! 0xa9450 W_a9450.
Proof. vm_refl. Qed.
Lemma D_a9450 : D! W_a9450 (Jalr 0 1 0).
Proof. vm_refl. Qed.
