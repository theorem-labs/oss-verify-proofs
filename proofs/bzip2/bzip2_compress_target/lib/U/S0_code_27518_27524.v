From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
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
Definition W_27518 : bv 32 := 0x00050213.
Lemma F_27518 : F! 0x30fdc W_27518.
Proof. vm_refl. Qed.
Lemma D_27518 : D! W_27518 (OpImm ALU_ADD 4 10 0).
Proof. vm_refl. Qed.
Definition W_2751c : bv 32 := 0x00000513.
Lemma F_2751c : F! 0x30fe0 W_2751c.
Proof. vm_refl. Qed.
Lemma D_2751c : D! W_2751c (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_27520 : bv 32 := 0x00008067.
Lemma F_27520 : F! 0x30fe4 W_27520.
Proof. vm_refl. Qed.
Lemma D_27520 : D! W_27520 (Jalr 0 1 0).
Proof. vm_refl. Qed.
