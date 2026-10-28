From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Export V2LeptUb.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Lemma kal8_mul : forall p i, p mod 8 = 0 -> (p + 8 * i) mod 8 = 0.
Proof. intros p i Hp. rewrite Z.mul_comm, Z_mod_plus_full. exact Hp. Qed.

Lemma kal4_mul : forall p i, p mod 4 = 0 -> (p + 4 * i) mod 4 = 0.
Proof. intros p i Hp. rewrite Z.mul_comm, Z_mod_plus_full. exact Hp. Qed.

Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac snez1 F D := stepat F D (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; apply zbv_snez; lia).
Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac sltu0 F D := stepat F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_sltu_ge; lia).
Ltac slti0 F D := stepat F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_slti0; lia).
Ltac zlitv F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
