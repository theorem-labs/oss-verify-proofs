(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_ps_casan_T Cut_ps_casan_D Cut_ps_casan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import ParseStringChkCA.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSX.
Import PSA.

Lemma kwrF_all : forallb (fun i => CC.has_cell (CC.cp_know (nth i G.CPS CA.dummy_cp)) (KWr (SA (CHA.SRL3 FE) SBz) (ELit 16))) (seq 1 78) = true.
Proof. vmc_refl. Qed.
Lemma flc_all : forallb (fun i => CC.has_cell (CC.cp_know (nth i G.CPS CA.dummy_cp)) (KWord (SA FE 120) 8 FLE)) (seq 1 78) = true.
Proof. vmc_refl. Qed.

Lemma retbls_all : forallb (fun r : nat * nat * nat * Z => let '(j, i, _, pc) := r in
   if (Z.eqb pc PC_ERRH || Z.eqb pc PC_SETEC || Z.eqb pc PC_ATC)%bool then CH2.blocks_eqb (nth j G.BLS []) (nth i G.BLS []) else true) G.RETS = true.
Proof. vmc_refl. Qed.

Lemma retbls_k : forallb (fun r : nat * nat * nat * Z => let '(j, i, _, _) := r in
   if (kind_eqb (kind_of j) KErrh || kind_eqb (kind_of j) KSetec || kind_eqb (kind_of j) KAtc)%bool then CH2.blocks_eqb (nth j G.BLS []) (nth i G.BLS []) else true) G.RETS = true.
Proof. vmc_refl. Qed.

Definition auxp (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc => ((if (Z.eqb pc PC_ERRH || Z.eqb pc PC_APPEND || Z.eqb pc PC_ESV)%bool then negb (kind_eqb (kind_of i) KErrh) else true)
                     && (if (Z.eqb pc PC_PUSHB || Z.eqb pc PC_APPEND || Z.eqb pc PC_CONVERT)%bool then isSome (CAX.cell_at (SR.ps_cells ps) PE 232 8) else true)
                     && (if Z.eqb pc PC_CONVERT then CC.has_cell (CC.cp_know c) (KRange JV 1 16384) else true))%bool
  | _ => true
  end.
Lemma aux_ok : CH2.leaves_all G.CPS G.TAGS auxp = true.
Proof. vmc_refl. Qed.

Definition sng (k : kind) : nat := match k with KPushb | KAppend => 2 | KConvert => 3 | _ => 0 end.
Lemma retbls_s : forallb (fun r : nat * nat * nat * Z => let '(j, i, _, _) := r in
   match kind_of j with
   | KPushb | KAppend | KConvert =>
       let g := (CC.cp_nx (nth j G.CPS CA.dummy_cp) - APC.NCS - sng (kind_of j))%nat in
       CH2.blocks_eqb (nth j G.BLS []) [(EVar g, EMd Instr.M_MUL (ELit 2) (EVar (g + 1)%nat)); blk1 i]
   | KEsv => let g := ecv j in CH2.blocks_eqb (nth j G.BLS []) [(EVar (g + 1)%nat, EMd Instr.M_MUL (ELit 2) (EVar (g + 2)%nat)); (EVar (g + 3)%nat, EVar (g + 4)%nat)]
   | _ => true
   end) G.RETS = true.
Proof. vmc_refl. Qed.
End PSX.
