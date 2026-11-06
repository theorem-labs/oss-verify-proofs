(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) =>
(lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Local Notation "'F!' a w" := (fetch_word Plain.M.loaded_segments (a : word) = Some w) (at level 200, a at level 0, w at level 0, only parsing).
Local Notation "'D!' w i" := (decode_any w = Some (i, 4%Z)) (at level 200, w at level 0, i at level 0, only parsing).
Local Notation "'D2!' w i" := (decode_any w = Some (i, 2%Z)) (at level 200, w at level 0, i at level 0, only parsing).
Definition W_6fdcc : bv 32 := 0x00050213.
Lemma F_6fdcc : F! 0x6fdcc W_6fdcc.
Proof. vm_refl. Qed.
Lemma D_6fdcc : D! W_6fdcc (OpImm ALU_ADD 4 10 0).
Proof. vm_refl. Qed.
Definition W_6fdd0 : bv 32 := 0x00000513.
Lemma F_6fdd0 : F! 0x6fdd0 W_6fdd0.
Proof. vm_refl. Qed.
Lemma D_6fdd0 : D! W_6fdd0 (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_6fdd4 : bv 32 := 0x00008067.
Lemma F_6fdd4 : F! 0x6fdd4 W_6fdd4.
Proof. vm_refl. Qed.
Lemma D_6fdd4 : D! W_6fdd4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
