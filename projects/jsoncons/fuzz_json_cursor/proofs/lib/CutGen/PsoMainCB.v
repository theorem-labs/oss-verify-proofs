(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_cboth_T Cut_psome_cboth_D Cut_psome_cboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCB PsoSemA PsoSemCA PsoKnCB PsoBaseCB ParseSomeChkCB PsoLeafCB PsoAuxCB PsoXiCB PsoFrmCB PsoExitCB PsoSmCB PsoCallCB PsoCallPCB PsoPtCB PsoPtICB PsoAt0CB PsoGotoCB PsoGxCB PsoCslCB PsoVisCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.

Module PSOM.

Definition LEAFC {SCFG_P : ScfgP} (I : PSOI.inst) (pc : Z) : Prop :=
  forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
    CCA.leaf_ok (hl_segs (PSOI.iL I)) G.CPS (AMBX I) (PSOI.iK I) PMSA.fp_ok i c ps0.

Definition OPEN_CALLS : list Z := [].

Lemma blk01 : PSO.blk0 0 = (EVar 56, EMd Instr.M_MUL (ELit 2) (EVar 54)) /\ PSO.blk1 0 = (EVar 57, EVar 59) /\
              PSO.blk0 1 = (EVar 56, EMd Instr.M_MUL (ELit 2) (EVar 54)) /\ PSO.blk1 1 = (EVar 57, EVar 59).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma pc01 : CC.cp_pc (nth 0 G.CPS CA.dummy_cp) = PC /\ CC.cp_pc (nth 1 G.CPS CA.dummy_cp) = PC.
Proof. vm_compute. split; reflexivity. Qed.
Lemma t01 : CC.cp_regs (nth 0 G.CPS CA.dummy_cp) = CC.cp_regs GT.t0 /\ CC.cp_know (nth 0 G.CPS CA.dummy_cp) = CC.cp_know GT.t0 /\
            CC.cp_regs (nth 1 G.CPS CA.dummy_cp) = CC.cp_regs GT.t1 /\ CC.cp_know (nth 1 G.CPS CA.dummy_cp) = CC.cp_know GT.t1.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section M.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation cr := (PSOI.icr I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation E := (PSOI.iE I).
Local Abbreviation R := (PSOI.iR I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation model := (PSOI.imodel I). Local Abbreviation ps := (PSOI.ips I).
Local Abbreviation K := (PSOI.iK I).     Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation HH := (PSOI.iHH I). Local Abbreviation E0 := (PSOI.E0 I).

Hypothesis HCALL : forall pc, In pc OPEN_CALLS -> LEAFC I pc.

Lemma LEAVES : forall i c k ps0 pc, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  intros i c k ps0 pc IL.
  destruct (PSO.dead_chk i ps0 pc) eqn:DC; [exact (PSOCS.L_DEAD I i c k ps0 pc IL DC)|].
  pose proof (PSOL.LEAFOK_all i c k ps0 _ IL) as X. cbn [PSO.leaf_chk] in X. rewrite DC in X.
  destruct (Z.eq_dec pc RET) as [->|N1]; [rewrite Z.eqb_refl in X; exact (L_EXIT I i c k ps0 IL X)|]. rewrite (proj2 (Z.eqb_neq pc RET) N1) in X.
  destruct (Z.eq_dec pc SETSH) as [->|N2]; [rewrite Z.eqb_refl in X; exact (L_SETSH I i c k ps0 IL X)|]. rewrite (proj2 (Z.eqb_neq pc SETSH) N2) in X.
  destruct (Z.eq_dec pc SM4) as [->|N3]; [rewrite Z.eqb_refl in X; exact (L_SM I i c k ps0 IL X)|]. rewrite (proj2 (Z.eqb_neq pc SM4) N3) in X.
  destruct (PSO.inb pc PSO.CALLEES) eqn:N4; [|exact (PSOCS.L_CSL I i c k ps0 pc IL DC N1 N2 N3 N4)].
  destruct (Z.eq_dec pc ERRH) as [->|N5]; [exact (PSOCALL.L_ERRH I i c k ps0 IL X DC)|].
  destruct (Z.eq_dec pc SETEC) as [->|N6]; [exact (PSOCALL.L_SETEC I i c k ps0 IL X DC)|].
  destruct (Z.eq_dec pc PARENT) as [->|N7]; [exact (PSOCALL.L_PARENT I i c k ps0 IL X DC)|].
  destruct (Z.eq_dec pc POPST) as [->|N8]; [exact (PSOCALL.L_POPST I i c k ps0 IL X DC)|].
  destruct (Z.eq_dec pc VPUSH) as [->|N9]; [exact (PSOCALL.L_VPUSH I i c k ps0 IL X DC)|].
  destruct (Z.eq_dec pc PUSHB) as [->|N10]; [exact (PSOCALLP.L_PUSHB I i c k ps0 IL X DC)|].
  destruct (Z.eq_dec pc VNULL) as [->|N11]; [exact (PSOVIS.L_VNULL I i c k ps0 IL X DC)|].
  destruct (Z.eq_dec pc VBOOL) as [->|N12]; [exact (PSOVIS.L_VBOOL I i c k ps0 IL X DC)|].
  destruct (in_dec Z.eq_dec pc PSOP.PT) as [HPT|NPT]; [exact (PSOPI.L_PT I pc HPT i c k ps0 IL X DC)|].
  assert (HO : In pc OPEN_CALLS).
  { unfold PSO.inb in N4. apply existsb_exists in N4 as (x & HIN & EX). apply Z.eqb_eq in EX. subst x.
    unfold PSO.CALLEES in HIN. cbn [In] in HIN.
    repeat (destruct HIN as [HIN|HIN]; [subst pc; first [solve [exfalso; congruence]
                                                        | solve [exfalso; apply NPT; unfold PSOP.PT; cbn [In]; repeat (first [left; reflexivity | right])]
                                                        | solve [unfold OPEN_CALLS; cbn [In]; repeat (first [left; reflexivity | right])]] |]). destruct HIN. }
  exact (HCALL pc HO i c k ps0 IL X DC).
Qed.

Lemma XI01 : forall i, (i = 0 \/ i = 1)%nat -> PSOX.XI I i E0 A M model.
Proof.
  intros i Hi. assert (KE : PSO.kind_of i = PSO.KEntry) by (destruct Hi as [-> | ->]; [exact (proj1 kind01) | exact (proj2 kind01)]).
  unfold PSOX.XI. constructor.
  - intros H2. exfalso. destruct Hi as [-> | ->]; lia.
  - intros _. split; [apply CC.env_agree_refl | reflexivity].
  - rewrite KE. intros X; discriminate X.
  - rewrite KE. intros X; discriminate X.
  - rewrite KE. intros [X|X]; discriminate X.
  - rewrite KE. intros X; discriminate X.
  - rewrite KE. intros X; discriminate X.
  - intros pc. rewrite KE. intros X; discriminate X.
  - rewrite KE. intros X; discriminate X.
  - rewrite KE. intros X; discriminate X.
  - rewrite KE. intros X; discriminate X.
  - rewrite KE. intros [X|X]; discriminate X.
  - rewrite KE. intros X; discriminate X.
  - rewrite KE. intros X; discriminate X.
Qed.

Lemma AMB01 : forall i, (i = 0 \/ i = 1)%nat -> AAMB I i E0 A M model.
Proof.
  intros i Hi. pose_facts I. pose_U I.
  assert (Hin : (i < PSO.NCUT)%nat) by (unfold PSO.NCUT; destruct Hi as [-> | ->]; lia).
  assert (BL : PSO.blk0 i = (EVar 56, EMd Instr.M_MUL (ELit 2) (EVar 54)) /\ PSO.blk1 i = (EVar 57, EVar 59))
    by (destruct blk01 as (B0 & B1 & B2 & B3); destruct Hi as [-> | ->]; split; assumption).
  assert (FS : nth i PSO.FFS [] = []) by (destruct Hi as [-> | ->]; [exact ffs_0 | exact ffs_1]).
  unfold AAMB, CHA.aamb.
  split; [exact (PSOI.iHmo I)|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
  split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
  exists cr, LK. unfold CHA.curB, CHA.curF. rewrite (bls_i i Hin), FS. cbn [CHA.denF map app length Z.of_nat Z.sub].
  destruct BL as (B0 & B1). rewrite B0, B1. unfold CH2.den. cbn [map fst snd].
  pose proof UBC as UBC'. cbn [edenot] in UBC' |- *. rewrite UBC', U56, U57, U59.
  split; [exact HH|]. split; [apply incl_refl|]. split; [|replace (6 - Z.of_nat 0) with 6 by (clear; lia); exact (PSOI.iHroom I)].
  unfold PSOX.Cred, PSOX.bcapI, PSOX.scapI. rewrite B0, B1. cbn [fst snd].
  unfold CL5A.uv. cbn [edenot]. rewrite UBC', U59. apply (proj1 (pcredit_bufcred I cr ps WF4)). exact (PSOI.iHPC I).
Qed.

Lemma AMBX01 : forall i, (i = 0 \/ i = 1)%nat -> AMBX I i E0 A M model.
Proof. intros i Hi. split; [exact (AMB01 i Hi) | exact (XI01 i Hi)]. Qed.

Lemma SOUND : forall i, (i = 0 \/ i = 1)%nat -> CCA.AtV (hl_segs L) (nth i G.CPS CA.dummy_cp) E0 R A M model ->
  srealizes (hl_segs L) SCFG (@PMSA.cfg L (PSOI.ifx I) R PC M model) K.
Proof.
  intros i Hi HAt. pose_facts I. pose_U I.
  assert (Hc : nth_error G.CPS i = Some (nth i G.CPS CA.dummy_cp)) by (destruct Hi as [-> | ->]; reflexivity).
  assert (PCi : CC.cp_pc (nth i G.CPS CA.dummy_cp) = PC) by (destruct Hi as [-> | ->]; [exact (proj1 pc01) | exact (proj2 pc01)]).
  rewrite <- PCi. unfold PMSA.cfg.
  refine (CHA.cert_soundA L ar C HI HIok (LYI I) (LYR I) (LYB I) (LYN I) GT.NF E0 M model A LBo FF LK sp G.HDECL (WW I) (Wo I) G.BLS PSO.FFS (PSOX.Cred I) 6
            (STKF I) SCRP NF32 U2 (WINC I) (WOKo I) (WRS_OK I) G.CPS K PMSA.fp_ok (PSOX.XI I) G.TAGS (PSOI.iFPM I) _ G.tags_ok PSOA.heap_ok _ _ LEAVES
            i _ (PSOI.ifx I) E0 R A M model Hc HAt (AMBX01 i Hi) (PSOI.iHfp I)).
  - rewrite LS. exact G.plans.
  -   intros i1 c k ps0 j s IL E1 E' R' M1 M' cr1 Hag0 Hag HLF HC.
    pose proof (PSOL.LEAFOK_all i1 c k ps0 _ IL) as X. cbn [PSO.leaf_chk] in X. apply andb_prop in X as [Hj _]. apply Nat.ltb_lt in Hj.
    exact (PSOG.G_CRED I i1 c k ps0 j s IL Hj E1 E' R' M1 M' cr1 Hag0 Hag HLF HC).
  -   intros i1 c k ps0 j s IL E1 R1 E' R' A1 M1 m1 M' m' HAt1 HA1 Hag HLF HXI.
    exact (PSOGX.G_XI I i1 c k ps0 j s IL E1 R1 E' R' A1 M1 m1 M' m' HAt1 HA1 Hag HLF HXI).
Qed.

Lemma main_open : srealizes (hl_segs L) SCFG (@PMSA.cfg L (PSOI.ifx I) R PC M model) K.
Proof.
  destruct (PML.ps_win ps) as [[p e]|] eqn:Hw.
  - apply (SOUND 0 (or_introl eq_refl)). destruct (PSOAT.At0 I p e Hw) as [AR AK]. destruct t01 as (T0 & T1 & _). split; [rewrite T0; exact AR | rewrite T1; exact AK].
  - apply (SOUND 1 (or_intror eq_refl)). destruct (PSOAT.At1 I Hw) as [AR AK]. destruct t01 as (_ & _ & T0 & T1). split; [rewrite T0; exact AR | rewrite T1; exact AK].
Qed.
End M.
End PSOM.
