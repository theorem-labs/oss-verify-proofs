From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
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
Definition W_b8100 : bv 32 := 0x00050213.
Lemma F_b8100 : F! 0xb9f54 W_b8100.
Proof. vm_refl. Qed.
Lemma D_b8100 : D! W_b8100 (OpImm ALU_ADD 4 10 0).
Proof. vm_refl. Qed.
Definition W_b8104 : bv 32 := 0x00000513.
Lemma F_b8104 : F! 0xb9f58 W_b8104.
Proof. vm_refl. Qed.
Lemma D_b8104 : D! W_b8104 (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_b8108 : bv 32 := 0x00008067.
Lemma F_b8108 : F! 0xb9f5c W_b8108.
Proof. vm_refl. Qed.
Lemma D_b8108 : D! W_b8108 (Jalr 0 1 0).
Proof. vm_refl. Qed.
