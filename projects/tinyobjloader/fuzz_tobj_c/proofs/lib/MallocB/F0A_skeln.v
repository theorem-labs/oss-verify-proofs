(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "ss_next"; "sprop"; "sprop_eqb"; "ss_facts"; "ss_lenient"; "sv"; "SLit"; "SVar"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "list"; "true"; "nil"; "false"; "pair"; "prod"; "nat"; "Some"; "option"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "UStopLe"; "Wcan"; "AE_A"; "client_addrA"; "client_shadowA"; "JL_free"; "J_free_preT"; "L_free"; "Pre_freeI"; "ulink"; "ustop"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "junkF"; "j_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "BIGX"; "PSE"; "XDr"; "leaves_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@Stdlib.Lists.List"; "In"; "existsb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "QFN"; "RCYE"; "small_fact"; "contN"; "econtN"; "entry_pureN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "instG_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVN"; "VFN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition RCYE : Z := 0x3e764.

Definition small_fact : sprop := SPBranch BC_GEU (SLit 268435456) big_size.

Definition Erc_of (L : axst) (facts0 : list sprop) : axst := ltac2:(tb__ "0|2|
S28VL;A1S17S29VL;S10S14R1A1S6bS15R1A1S1bS21S22SdA2M0S20S22SdUdSfS8R1A1M1A1A4S1eG0A1A3A2S12R1A1S11R1A1S16R1A1S13R1A1Vfacts0;S69G1A1ScR1A1A9A2TS;").

Section SmallNo.
Variables (nW : nat) (st : ustop) (bud : bool).
Lemma small_leaf_absurd : ltac2:(tb__ "0|1|
S2eS38S6S6S27S6S1cS26Q40M0A1A1S46S1S1aS5aS9SaS60A1SbS28R4A1A1A3S1dA3S34R7R6A2S45S36S25G0S7R7PdA2A2A2S2bS18S33VnW;Vst;Vbud;RbRaR8A6R7R6R5R4A6S5F_;F_;F_;F_;Fw;FtpE;FrhoE;FE;Frho1';Frho;FKc;FA';").
Proof.
  intros A' Kc rho rho1' E rhoE tpE w HB R Hn Hw. pose proof Hw as [Hsm HJ].
  pose proof (smatchA_facts segsA rhoE tpE E w Hsm) as HF.
  apply existsb_exists in HB as (f & Hf & Ef). apply sprop_eqb_sound in Ef. subst f.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as HBF.
  pose proof (JF_agreeG nW st bud A' Kc rho1' E rhoE tpE w Hw) as Hag.
  destruct (rig_at rho rho1' rhoE R Hag) as (t & HH).
  pose proof (sem_usz rhoE t HH) as EV. change usz_e with big_size in EV.
  assert (A13 : rw rhoE 13%positive = rw rho1' 13%positive) by (symmetry; apply (proj1 Hag); reflexivity).
  unfold small_fact in HBF. apply (proj1 (holds_bgeu _ _ _)) in HBF. rewrite EV, A13 in HBF.
  rewrite CursorGlue.U_lit in HBF. unfold M64v in HBF. rewrite Z.mod_small in HBF by lia. unfold kQuarantineMax in Hn. lia.
Qed.
End SmallNo.

Section S3N.
Let segs : list Segment := segsA.
Variables (nW : nat) (st : ustop).
Variables (TD TDr CD Eps Ebg Erc : axst) (l3 : list leafA).
Hypothesis AXDr : ltac2:(tb__ "0|0|
S1S24S27A1S6dVTD;S56A2S23S27VTDr;A2A3").
Hypothesis ENTD : ltac2:(tb__ "0|0|
S1S1aS72VTDr;VCD;A2S1dA3").
Hypothesis RUN3 : ltac2:(tb__ "0|0|
S1S1cS2aA1S65S53S1bS0S55S1bS0S54S1eS0A1A3A3VCD;A3Vl3;A3").
Hypothesis L3 : ltac2:(tb__ "0|0|
S2S1S1aS57Vl3;S1bS0S55S1bS0S54S1eS0A1A3A3A2S1dA3S2S1S27S64U0Vl3;A2VEps;A3S1S27S64U1Vl3;A2VEbg;A3A2A2").
Hypothesis NX3 : ltac2:(tb__ "0|1|
S2S1S1aS68S19S8S28VCD;A1M0A1A2S1dA3S1S1aScG0A1S1fA3A2").
Hypothesis SMF : ltac2:(tb__ "0|0|
S1S1aS5aS9SaS60A1SbS28VEps;A1A1A3S1dA3").
Hypothesis NXB : ltac2:(tb__ "0|0|
S1S1aS68S19S8S28VEbg;A1A1A2S1dA3").
Hypothesis CertR : ltac2:(tb__ "0|1|
S1S1aS4fS18S53S1bS0S5fS1eS0A1A3S19S1bS27VEbg;S1eS27A1M0A3S1bS27VErc;G0A3A6S1dA3").
Hypothesis ECertR : ltac2:(tb__ "0|3|
S1S1aS50S18S53S1bS0S5fS1eS0A1A3S19S1bS4dS4eVEbg;Z1SeZ0M0A1M1A3S1eS4dA1M2A3S1bS4dS4eVErc;G0G1A3G2A3A6S1dA3").

Theorem f0_s3n : ltac2:(tb__ "0|1|
S46OF_;S2eS38S6S6S1cS26Q40M0A1A1S49S66S3bVnW;A1Vst;A2S39R6A1S2dVsegs;R9S2cR7A1A3S34R7R6A2S45S36S25G0S7R7PdA2A2A2S6S48Vsegs;RdS2bVsegs;S33VnW;Vst;S1fRcRbR9A6VErc;R1R8A5R7A4FrhoE;S6S48Vsegs;ReS2bVsegs;S33VnW;Vst;S1fRdRcRaA6VTD;R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;").
Proof using AXDr ENTD RUN3 L3 NX3 SMF CertR.
  intros ok A Kc rho rho1 tp Q HUS HKc Hok HR Hn HC.
  apply (f0_s3 nW st false TD TDr CD Eps Ebg l3 AXDr ENTD RUN3 L3 NX3 ok A Kc rho1 tp Q HUS HKc Hok).
  - intros rhoE k Hg w Hw. exfalso. exact (small_leaf_absurd nW st false A Kc rho rho1 Eps rhoE tp w SMF HR Hn Hw).
  - intros rhoE.
    apply (cfg_soundA segs FUELF [RCYE] GW [Ebg] [Erc] (JF nW st false A Kc rho1) ok Q tp).
    + apply JF_okf. exact Hok.
    + apply JF_stable; assumption.
    + exact CertR.
    + intros E rhoX HinE. destruct HinE as [<-|[]].
      eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HC rhoX)].
    + left. reflexivity.
Qed.
Theorem ef0_s3n : ltac2:(tb__ "0|1|
S2eS38S6S6S1cS26Q40M0A1A1S46OF_;S66S3bVnW;A1Vst;A2S39R6A1S34R6R5A2S45S36S25G0S7R6PdA2A2A2S6S47Vsegs;S2bVsegs;S33VnW;Vst;S1fRbRaR8A6VErc;R1R7A5R6A3FrhoE;S6S47Vsegs;S2bVsegs;S33VnW;Vst;S1fRcRbR9A6VTD;R1R8A5R7A3FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;").
Proof using AXDr ENTD RUN3 L3 NX3 SMF NXB ECertR.
  intros A Kc rho rho1 tp Q HUS HKc HR Hn HC.
  apply (ef0_s3 nW st false TD TDr CD Eps Ebg l3 AXDr ENTD RUN3 L3 NX3 A Kc rho1 tp Q HUS HKc).
  - intros rhoE w Hw. exfalso. exact (small_leaf_absurd nW st false A Kc rho rho1 Eps rhoE tp w SMF HR Hn Hw).
  - intros rhoE.
    change Ebg with (vna_state (mkVNA Ebg 1 (SLit 0))).
    apply (cfg_complete_autoA segs FUELF [RCYE] GW [mkVNA Ebg 1 (SLit 0)] [mkVNA Erc 0 (SLit 0)] (JF nW st false A Kc rho1) Q tp).
    + apply JF_stable; assumption.
    + intros n [<-|[]]. cbn [vna_state]. apply Pos.leb_le. exact NXB.
    + exact ECertR.
    + intros E rhoX HinE. destruct HinE as [<-|[]]. cbn [vna_state].
      eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HC rhoX)].
    + left. reflexivity.
Qed.
End S3N.

Definition entry_pureN (khi : bool) (W : list ulink) (st : ustop) (A : AA) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S25Q40M0S7Vrho;PcA2A2S0S25G0S7Vrho;PdA2A2S0S2S59S21S0S0A2S20S0S0R2R1A4S30VA;A1A3S2S3S1cS26G0A1A1M1G1S3S5bS5bS58S18VA;Vrho;R2R1A5Lmd0;A2Ltp0;A2S3S0S0S3S4bS4bS2S52VA;Vrho;R4R3R2R1A6S2S1S0S4cR1A1S37A3S6eVkhi;VW;Vst;S6fS70S4aVA;Vrho;R4R3R2R1A6R4R3S71R3A1S32S31VA;A1A1AaA2A2Ljv;A2Lt;A2A2A2Tn;Tp;").
Lemma entry_pure_N : ltac2:(tb__ "0|2|
S1aS1cS43A1S44S2eS38S6S1cS26Q40M0A1A1S46S51R8S25G0S7R3PcA2A2S25G0S7R3PdM1A2A2A3S1S1aS2fR6A1S1dA3S45S36S25G0S7R5G1A2A2A2S2bS18S40S58S18A1RaR9R8R7A5S42S3cRaR9A3R6R5R4A6S63RcRbRaR9R7A5F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;Fkhi;").
Proof.
  intros khi W st A Kc rho tp w HK Hii HBG [_ HJ]. destruct HJ as (HA & _ & HL & _).
  split; [exact HL|]. split; [exists tp, (cfg_model (w_cfg w)); exact HA|].
  pose proof (cls_hyp_blk khi _ _ HK) as HCL.
  destruct (blkF_mem A rho tp _ _ _ HA HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp _ HA) as (jv & JM & Hjv).
  exists t, jv. split; [exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv)|]. split; [exact JM|].
  exact (instG_here_N A rho tp _ _ _ HA HL HCL Hii eq_refl eq_refl t (conj T1 (conj T2 (conj T3 T4))) jv Hjv khi W st HK HBG).
Qed.

Definition QFN (CST XGL : list (Z * Z)) (nW : nat) (A : AA) (Kc : KcA) (rho : valuation) (tp : list word) : assn := ltac2:(tb__ "0|1|
S5dS18S6aVrho;Vtp;S1bS21S27S5cA2M0S20S27S5cS41S3cS3bVnW;A1S3aA3S3fS58S18A1VCST;VXGL;VA;VKc;A5A4S1eG0A1A3A5").

Definition contN (nW : nat) (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S2eS6S6S1cS26Q40A1A1S35VA;R4A2S67Vkeep;Vrho1;R4A3S48S18Vok;S2bS18S33VnW;S3aS1fR6VKc;R5A6VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtN (nW : nat) (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S2eS6S6S1cS26Q40A1A1S35VA;R4A2S67Vkeep;Vrho1;R4A3S47S18S2bS18S33VnW;S3aS1fR6VKc;R5A6VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Definition HBIGN_stmt (CST XGL : list (Z * Z)) (khi : bool) (nW : nat) (E : axst) : Prop := ltac2:(tb__ "0|1|
S46OF_;S2eS38S6S1cS26Q40M0A1A1S0S0S0S4bS0OF_;S39R8A1S2dS18RbS2cR9A1A3S6cS18RcS2cRaA1A3S1S0S25G0S7RaPcA2A2R8A3S1S0S25G0S7RbPdA2A2R8A3S59S21S0S0A2S20S0S0RaR9A4S30ReA1A3S51Vkhi;RbRaA3S1S1aS2fR10A1S1dA3S45S36RcA2S52R12R10ReRdRcRbA6S34R11S4aR13R11RfReRdRcA6A2S1S0S4cRdA1S37A3S0S4S3dVCST;R16R1A3S3eVCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S61VnW;ReR17R16R15S4aR16R14R12R11R10RfA6VE;S5eVCST;VXGL;VnW;R16R15R14R13A7A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition HBIGNE_stmt (CST XGL : list (Z * Z)) (khi : bool) (nW : nat) (E : axst) : Prop := ltac2:(tb__ "0|1|
S2eS38S6S1cS26Q40M0A1A1S0S0S0S4bS0OF_;S39R8A1S1S0S25G0S7R8PcA2A2R6A3S1S0S25G0S7R9PdA2A2R6A3S59S21S0S0A2S20S0S0R8R7A4S30RcA1A3S51Vkhi;R9R8A3S1S1aS2fReA1S1dA3S45S36RaA2S52R10ReRcRbRaR9A6S34RfS4aR11RfRdRcRbRaA6A2S1S0S4cRbA1S37A3S0S4S3dVCST;R14R1A3S3eVCST;VXGL;R14R1A4A2RdR2A1F_;Fa;S62VnW;RcR14R13S4aR14R12R10RfReRdA6VE;S5eVCST;VXGL;VnW;R14R13R12R11A7A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
