(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefXA PmLibSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_psome_xasan_T Cut_psome_xasan_D Cut_psome_xasan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import XKitXA PsoInstXA PsoSemXA PsoKnXA ParseSomeChkXA PsoLeafXA PsoAuxXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import PsoInstXAW PsoBaseXAW PsoXiXAW PsoFrmXAW PsoExitXAW PsoSmXAW PsoCallXAW PsoCallPXAW PsoPtXAW PsoPtIW PsoVisXAW PsoAt0XAW PsoGotoXAW PsoGxXAW PsoCslXAW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_xasan.

Module PSOM.

(* [comment removed for export] *)
Definition LEAFC {SCFG_P : ScfgP} (I : PSOIW.inst) (pc : Z) : Prop :=
  forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
    CCA.leaf_ok (hl_segs (PSOIW.iL I)) G.CPS (AMBX I) (PSOIW.iK I) PMSA.fp_ok i c ps0.
(* [comment removed for export] *)
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
Variable I : PSOIW.inst.
Local Abbreviation L := (PSOIW.iL I).     Local Abbreviation ar := (PSOIW.iar I).    Local Abbreviation C := (PSOIW.iC I).     Local Abbreviation HI := (PSOIW.iHI I).
Local Abbreviation LBo := (PSOIW.iLBo I). Local Abbreviation FF := (PSOIW.iFF I).    Local Abbreviation LK := (PSOIW.iLK I).   Local Abbreviation cr := (PSOIW.icr I).   Local Abbreviation A := (PSOIW.iA I).
Local Abbreviation sp := (PSOIW.isp I).   Local Abbreviation P := (PSOIW.iP I).      Local Abbreviation E := (PSOIW.iE I).
Local Abbreviation R := (PSOIW.iR I).     Local Abbreviation M := (PSOIW.iM I).      Local Abbreviation model := (PSOIW.imodel I). Local Abbreviation ps := (PSOIW.ips I).
Local Abbreviation K := (PSOIW.iK I).     Local Abbreviation HIok := (PSOIW.iHIok I). Local Abbreviation HH := (PSOIW.iHH I). Local Abbreviation E0 := (PSOIW.E0 I).
Local Abbreviation WW := (PSOIW.WW I).

Hypothesis HCALL : forall pc, In pc OPEN_CALLS -> forall g, LEAFC (PSOIW.setg I g) pc.

(* [comment removed for export] *)
Definition J (g : PMES.eghost) : PSOIW.inst := PSOIW.setg I g.
Definition CredV (g : PMES.eghost) := PSOX.Cred (J g).
Definition XIv (g : PMES.eghost) := PSOX.XI (J g).
Definition LEAFOKV (g : PMES.eghost) (M0c : mem) (i : nat) (c : CC.cutpoint) (ps0 : SR.post_spec) : Prop :=
  CHV.leaf_okV L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS 11 PMES.eghost PMES.g_lbv CredV XIv G.CPS K PMSA.fp_ok g M0c i c ps0.
Lemma JETA : forall g, PSOIW.setg (J g) (PSOIW.ig1 (J g)) = J g. Proof. intros g. reflexivity. Qed.

(* [comment removed for export] *)
Lemma LEAF_of : forall g i c ps0, CCA.leaf_ok (hl_segs L) G.CPS (AMBX (J g)) K PMSA.fp_ok i c ps0 -> forall M0c, OKVt I M0c -> LEAFOKV g M0c i c ps0.
Proof.
  intros g i c ps0 HL M0c OKV fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH.
  apply (HL fx' E1 R1 A1 M1 m1 E' R' M' m' HAt (ex_intro _ M0c (conj OKV HAX)) HFP Hag HLF).
  intros j cj fx2 E2 R2 A2 M2 m2 Hcj HAt2 (M0d & OKV2 & HAX2) HFP2 Hlt.
  exact (HIH j cj fx2 E2 R2 A2 M2 m2 Hcj HAt2 (CHV.ambV_intro L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS 11 PMES.eghost PMES.g_lbv CredV XIv (PSOIW.ig1 (J g)) M0d j E2 A2 M2 m2 OKV2 HAX2) HFP2 Hlt).
Qed.

(* [comment removed for export] *)
Lemma LEAVES : forall i c k ps0 pc, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> forall g M0c, OKVt I M0c -> LEAFOKV g M0c i c ps0.
Proof.
  intros i c k ps0 pc IL g M0c OKV. assert (OKVJ : OKVt (J g) M0c) by exact OKV.
  destruct (PSO.dead_chk i ps0 pc) eqn:DC; [exact (LEAF_of g i c ps0 (PSOCS.L_DEAD (J g) i c k ps0 pc IL DC) M0c OKV)|].
  pose proof (PSOL.LEAFOK_all i c k ps0 _ IL) as X. cbn [PSO.leaf_chk] in X. rewrite DC in X.
  destruct (Z.eq_dec pc RET) as [->|N1]; [rewrite Z.eqb_refl in X; exact (LEAF_of g i c ps0 (L_EXIT (J g) i c k ps0 IL X) M0c OKV)|]. rewrite (proj2 (Z.eqb_neq pc RET) N1) in X.
  destruct (Z.eq_dec pc SETSH) as [->|N2]; [rewrite Z.eqb_refl in X; exact (LEAF_of g i c ps0 (L_SETSH (J g) i c k ps0 IL X) M0c OKV)|]. rewrite (proj2 (Z.eqb_neq pc SETSH) N2) in X.
  destruct (Z.eq_dec pc SM4) as [->|N3]; [rewrite Z.eqb_refl in X; exact (LEAF_of g i c ps0 (L_SM (J g) i c k ps0 IL X) M0c OKV)|]. rewrite (proj2 (Z.eqb_neq pc SM4) N3) in X.
  destruct (PSO.inb pc PSO.CALLEES) eqn:N4; [|exact (LEAF_of g i c ps0 (PSOCS.L_CSL (J g) i c k ps0 pc IL DC N1 N2 N3 N4) M0c OKV)].
  destruct (Z.eq_dec pc ERRH) as [->|N5]; [exact (LEAF_of g i c ps0 (PSOCALL.L_ERRH (J g) i c k ps0 IL X DC) M0c OKV)|].
  destruct (Z.eq_dec pc SETEC) as [->|N6]; [exact (LEAF_of g i c ps0 (PSOCALL.L_SETEC (J g) i c k ps0 IL X DC) M0c OKV)|].
  destruct (Z.eq_dec pc PARENT) as [->|N7]; [exact (LEAF_of g i c ps0 (PSOCALL.L_PARENT (J g) i c k ps0 IL X DC) M0c OKV)|].
  destruct (Z.eq_dec pc POPST) as [->|N8]; [exact (LEAF_of g i c ps0 (PSOCALL.L_POPST (J g) i c k ps0 IL X DC) M0c OKV)|].
  destruct (Z.eq_dec pc VPUSH) as [->|N9]; [exact (LEAF_of g i c ps0 (PSOCALL.L_VPUSH (J g) i c k ps0 IL X DC) M0c OKV)|].
  destruct (Z.eq_dec pc PUSHB) as [->|N10]; [exact (LEAF_of g i c ps0 (PSOCALLP.L_PUSHB (J g) i c k ps0 IL X DC) M0c OKV)|].
  destruct (in_dec Z.eq_dec pc PSOPI.PTA) as [HPT|NPT]; [exact (LEAF_of g i c ps0 (PSOPI.L_PTA (J g) (JETA g) pc HPT i c k ps0 IL X DC) M0c OKV)|].
  destruct (in_dec Z.eq_dec pc PSOPI.PTX) as [HPX|NPX]; [exact (PSOPI.L_PTX (J g) (JETA g) pc HPX i c k ps0 IL X DC M0c OKVJ)|].
  destruct (in_dec Z.eq_dec pc PSOVIS.PTV) as [HPV|NPV]; [exact (PSOVIS.L_VIS (J g) (JETA g) pc HPV i c k ps0 IL X DC M0c OKVJ)|].
  assert (HO : In pc OPEN_CALLS).
  { unfold PSO.inb in N4. apply existsb_exists in N4 as (x & HIN & EX). apply Z.eqb_eq in EX. subst x.
    unfold PSO.CALLEES in HIN. cbn [In] in HIN.
    repeat (destruct HIN as [HIN|HIN]; [subst pc; first [solve [exfalso; congruence]
                                                        | solve [exfalso; apply NPT; unfold PSOPI.PTA; cbn [In]; repeat (first [left; reflexivity | right])]
                                                        | solve [exfalso; apply NPX; unfold PSOPI.PTX; cbn [In]; repeat (first [left; reflexivity | right])]
                                                        | solve [exfalso; apply NPV; unfold PSOVIS.PTV; cbn [In]; repeat (first [left; reflexivity | right])]
                                                        | solve [unfold OPEN_CALLS; cbn [In]; repeat (first [left; reflexivity | right])]] |]). destruct HIN. }
  exact (LEAF_of g i c ps0 (HCALL pc HO g i c k ps0 IL X DC) M0c OKV).
Qed.

(* [comment removed for export] *)
Definition J0 : PSOIW.inst := J (PSOIW.ieg I).
Lemma XI01 : forall i, (i = 0 \/ i = 1)%nat -> PSOX.XI J0 i E0 A M model.
Proof.
  intros i Hi. assert (KE : PSO.kind_of i = PSO.KEntry) by (destruct Hi as [-> | ->]; [exact (proj1 kind01) | exact (proj2 kind01)]).
  unfold PSOX.XI. constructor; try (rewrite KE; first [intros X; discriminate X | intros [X|X]; discriminate X | intros pc0 X; discriminate X]).
  - intros H2. exfalso. destruct Hi as [-> | ->]; lia.
  - intros _. split; [apply CC.env_agree_refl | split; reflexivity].
Qed.

Lemma AMB01 : forall i, (i = 0 \/ i = 1)%nat -> AAMBc J0 M i E0 A M model.
Proof.
  intros i Hi. pose_facts I. pose_U I.
  assert (Hin : (i < PSO.NCUT)%nat) by (unfold PSO.NCUT; destruct Hi as [-> | ->]; lia).
  assert (BL : PSO.blk0 i = (EVar 56, EMd Instr.M_MUL (ELit 2) (EVar 54)) /\ PSO.blk1 i = (EVar 57, EVar 59))
    by (destruct blk01 as (B0 & B1 & B2 & B3); destruct Hi as [-> | ->]; split; assumption).
  assert (FS : nth i PSO.FFS [] = []) by (destruct Hi as [-> | ->]; [exact ffs_0 | exact ffs_1]).
  unfold AAMBc, CHA.aamb.
  split; [exact (PSOIW.iHmo I)|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
  split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
  exists cr, LK. unfold CHA.curB, CHA.curF. rewrite (bls_i i Hin), FS. cbn [CHA.denF map app length Z.of_nat Z.sub].
  destruct BL as (B0 & B1). rewrite B0, B1. unfold CH2.den. cbn [map fst snd].
  pose proof UBC as UBC'. cbn [edenot] in UBC' |- *. rewrite UBC', U56, U57, U59.
  split; [exact HH|]. split; [apply incl_refl|]. split; [|replace (11 - Z.of_nat 0) with 11 by (clear; lia); exact (PSOIW.iHroom I)].
  unfold PSOX.Cred, PSOX.bcapI, PSOX.scapI. rewrite B0, B1. cbn [fst snd].
  unfold CL5A.uv. cbn [edenot]. rewrite UBC', U59. apply (proj1 (pcredit_bufcred J0 cr ps WF4)). exact (PSOIW.iHPC I).
Qed.

(* [comment removed for export] *)
Lemma SOUND : forall i, (i = 0 \/ i = 1)%nat -> CCA.AtV (hl_segs L) (nth i G.CPS CA.dummy_cp) E0 R A M model ->
  srealizes (hl_segs L) SCFG (@PMSA.cfg L (PSOIW.ifx I) R PC M model) K.
Proof.
  intros i Hi HAt. pose_facts I. pose_U I.
  assert (Hc : nth_error G.CPS i = Some (nth i G.CPS CA.dummy_cp)) by (destruct Hi as [-> | ->]; reflexivity).
  assert (PCi : CC.cp_pc (nth i G.CPS CA.dummy_cp) = PC) by (destruct Hi as [-> | ->]; [exact (proj1 pc01) | exact (proj2 pc01)]).
  rewrite <- PCi. unfold PMSA.cfg.
  refine (CHV.cert_soundV L ar C HI HIok (LYI I) (LYR I) (LYB I) (LYN I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW (Wo I) G.BLS PSO.FFS 11 PMES.eghost PMES.g_lbv CredV XIv
            (STKF I) SCRP NF32 U2 (WINC I) (WOKo I) (WRS_OK I) G.CPS K PMSA.fp_ok G.TAGS (PSOIW.iFPM I) _ G.tags_ok PSOA.heap_ok _ _ LEAVES
            i _ (PSOIW.ifx I) E0 R A M model Hc HAt _ (PSOIW.iHfp I)).
  - rewrite LS. exact G.plans.
  - (* [comment removed for export] *) intros g i1 c k ps0 j s IL E1 E' R' M1 M' cr1 Hag0 Hag HLF HC.
    pose proof (PSOL.LEAFOK_all i1 c k ps0 _ IL) as X. cbn [PSO.leaf_chk] in X. apply andb_prop in X as [Hj _]. apply Nat.ltb_lt in Hj.
    exact (PSOG.G_CRED (J g) i1 c k ps0 j s IL Hj E1 E' R' M1 M' cr1 Hag0 Hag HLF HC).
  - (* [comment removed for export] *) intros g M0c OKV i1 c k ps0 j s IL E1 R1 E' R' A1 M1 m1 M' m' HAt1 HA1 Hag HLF HXI.
    exact (PSOGX.G_XI (J g) i1 c k ps0 j s IL E1 R1 E' R' A1 M1 m1 M' m' HAt1 (ex_intro _ M0c (conj OKV HA1)) Hag HLF HXI).
  - (* [comment removed for export] *)
    apply (CHV.ambV_intro L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS 11 PMES.eghost PMES.g_lbv CredV XIv (PSOIW.ieg I) M i E0 A M model (OKV0 I)).
    split; [exact (AMB01 i Hi) | exact (XI01 i Hi)].
Qed.

(* [comment removed for export] *)
Lemma main_open : srealizes (hl_segs L) SCFG (@PMSA.cfg L (PSOIW.ifx I) R PC M model) K.
Proof.
  destruct (PML.ps_win ps) as [[p e]|] eqn:Hw.
  - apply (SOUND 0 (or_introl eq_refl)). destruct (PSOAT.At0 I p e Hw) as [AR AK]. destruct t01 as (T0 & T1 & _). split; [rewrite T0; exact AR | rewrite T1; exact AK].
  - apply (SOUND 1 (or_intror eq_refl)). destruct (PSOAT.At1 I Hw) as [AR AK]. destruct t01 as (_ & _ & T0 & T1). split; [rewrite T0; exact AR | rewrite T1; exact AK].
Qed.
End M.
End PSOM.
