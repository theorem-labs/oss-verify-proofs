(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_pn_casan_T Cut_pn_casan_D Cut_pn_casan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import ParseNumberChkCA.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PNX.
Import PNA.

Lemma kwrF_all : forallb (fun i => CC.has_cell (CC.cp_know (nth i G.CPS CA.dummy_cp)) (KWr (SA (CHA.SRL3 FE) SBz) (ELit 16))) (seq 1 73) = true.
Proof. vmc_refl. Qed.
Lemma flc_all : forallb (fun i => CC.has_cell (CC.cp_know (nth i G.CPS CA.dummy_cp)) (KWord (SA FE 120) 8 FLE)) (seq 1 73) = true.
Proof. vmc_refl. Qed.

Lemma retbls_k : forallb (fun r : nat * nat * nat * Z => let '(j, i, _, _) := r in
   if (kind_eqb (kind_of j) KErrh || kind_eqb (kind_of j) KSetec)%bool then CH2.blocks_eqb (nth j G.BLS []) (nth i G.BLS []) else true) G.RETS = true.
Proof. vmc_refl. Qed.

Definition gA (j : nat) : nat := (CC.cp_nx (nth j G.CPS CA.dummy_cp) - APC.NCS - 2)%nat.
Definition gE (j : nat) : nat := (CC.cp_nx (nth j G.CPS CA.dummy_cp) - APC.NCS - 5)%nat.
Lemma retbls_s : forallb (fun r : nat * nat * nat * Z => let '(j, i, _, _) := r in
   match kind_of j with
   | KAppr => CH2.blocks_eqb (nth j G.BLS []) [(EVar (gA j), EMd Instr.M_MUL (ELit 2) (EVar (gA j + 1)%nat)); blk1 i]
   | KEnd => CH2.blocks_eqb (nth j G.BLS []) [(EVar (gE j + 1)%nat, EMd Instr.M_MUL (ELit 2) (EVar (gE j + 2)%nat)); (EVar (gE j + 3)%nat, EVar (gE j + 4)%nat)]
   | _ => true
   end) G.RETS = true.
Proof. vmc_refl. Qed.

Lemma bls_pre : forallb (fun i => match kind_of i with
   | KEntry | KDecl | KSm | KErrh | KSetec => CH2.blocks_eqb (nth i G.BLS []) [(EVar 36, EMd Instr.M_MUL (ELit 2) (EVar 34)); (EVar 37, EVar 39)]
   | KAppr => match nth i G.BLS [] with [_; b1] => CH2.blocks_eqb [b1] [(EVar 37, EVar 39)] | _ => false end
   | _ => true end) (seq 0 74) = true.
Proof. vmc_refl. Qed.

Lemma ecv_end : forallb (fun i => match kind_of i with KEnd => match CAX.cell_at (CC.cp_know (nth i G.CPS CA.dummy_cp)) EE 0 4 with Some (EVar g) => Nat.eqb g (gE i) | _ => false end | _ => true end) (seq 0 74) = true.
Proof. vmc_refl. Qed.
End PNX.
