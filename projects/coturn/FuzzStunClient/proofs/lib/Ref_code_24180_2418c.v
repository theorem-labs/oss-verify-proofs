(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
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
Definition W_24180 : bv 32 := 0x00050213.
Lemma F_24180 : F! 0x24180 W_24180.
Proof. vm_refl. Qed.
Lemma D_24180 : D! W_24180 (OpImm ALU_ADD 4 10 0).
Proof. vm_refl. Qed.
Definition W_24184 : bv 32 := 0x00000513.
Lemma F_24184 : F! 0x24184 W_24184.
Proof. vm_refl. Qed.
Lemma D_24184 : D! W_24184 (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_24188 : bv 32 := 0x00008067.
Lemma F_24188 : F! 0x24188 W_24188.
Proof. vm_refl. Qed.
Lemma D_24188 : D! W_24188 (Jalr 0 1 0).
Proof. vm_refl. Qed.
