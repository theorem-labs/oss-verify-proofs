(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke l1 kr l5.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j6 kz iw l8 kl l9.

(* [comment removed for export] *)
Module F0T_aTBe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe"; "q_TBe"; "Ebg_TBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "L_free_tol"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "VFACT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTBe"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "FACTS_Tg"; "P0T_c"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xiTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kr.F0T_dTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTBe.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_TBe : ltac2:(tb__ "0|0|
S0S7S1cS3dS15U0A1A1A1S6A3"). Proof. vmr. Qed.
Lemma Da_TBe : ltac2:(tb__ "0|4|
S0SeSbS8SbS1bS1bA2M0A1M1S8S1dA1M2A2M3A1S4aS14S2cS16A1A1S3dS15U0A1A1A2SdG3SaG1G2ScG0SaS1bS1bS20P18A1S1fS4fA1A4S9G0A1A3S9S1dA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_TBe : ltac2:(tb__ "0|0|
S0S7S1cS3eS15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Wc_TBe : ltac2:(tb__ "0|0|
S0S7S1cS3fS15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Wd_TBe : ltac2:(tb__ "0|0|
S0S7S1cS40S15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Fb_TBe : ltac2:(tb__ "0|0|
S0S7S5aS1dS21S4eA1S58S6S3cS11A1A2A3S6A3"). Proof. vmr. Qed.
Lemma XI_TBe : ltac2:(tb__ "0|2|
S0SeS13A1S4cS41S6S15U0M0A1S24S11A1M1S3cS11A1A4S50G0SfS4dG1A2A2A2SdS13S59S6S11A2A2A3"). Proof. vmr. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S4S29S51R2A2S3S2eS45R2A2S30R2S46A2A2A2S2F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S1S57R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S1S56R2A1A1F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Theorem free_hi_TBe : ltac2:(tb__ "0|2|
S34OF_;S47S18S1eS8S2bQ40M0A1A1S2aG0S1aR2PcA2A2S5S2aG0S1aR3PdA2A2S5S23S10S35R4R3ScSbS13S22A2M1SaS13S22S2dS16A1S17S44S10A1VCST;VXGL;R6R5A5A4S9G1A1A3A5S31S19R6A1S38S10R9S37R7A1A3S4bS10RaS37R8A1A3S2eS42S2fR6Z10A2A2S0S7S48RbA1S6A3S28S11RcA2S5S27S3aRfRdRbRaR2R1A6S0S5S26R2A1S43A3S3bRfS25R11RfRdRcR4R3A6A2S54S39VCST;VXGL;R12A3R13R12R11S25R12R10ReRdR5R4A6S12RcA7F_;F_;F_;Fjv;Ft;S52RfRdA2S33S10R10S36S10S49RfReA2S2cS16A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF true (Wcan 0) UStopLe q_TBe A rho)); [intros w Hw; exact (entry_pure_T true _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (tq_instantiate true q_TBe Wa_TBe Da_TBe Wb_TBe Wc_TBe Wd_TBe Fb_TBe XI_TBe A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (free_spine_TBe (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR (conj HO (conj E153 HST))
           (hdf_TBe HSEG CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_TBe CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_TBe CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_TBe : ltac2:(tb__ "0|2|
S47S18S1eS8S2bQ40M0A1A1S2aG0S1aR2PcA2A2S5S2aG0S1aR3PdA2A2S5S23S10S35R4R3ScSbS13S22A2M1SaS13S22S2dS16A1S17S44S10A1VCST;VXGL;R6R5A5A4S9G1A1A3A5S31S19R6A1S2eS42S2fR4Z10A2A2S0S7S48R9A1S6A3S28S11RaA2S5S27S3aRdRbR9R8R2R1A6S0S5S26R2A1S43A3S3bRdS25RfRdRbRaR4R3A6A2S55S39VCST;VXGL;R10A3R10RfS25R10ReRcRbR5R4A6S12RaA6F_;F_;F_;Fjv;Ft;S53RbA1S32S10S36S10S49RdRcA2S2cS16A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureF true (Wcan 0) UStopLe q_TBe A rho)); [intros w Hw; exact (entry_pure_T true _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (tq_instantiate true q_TBe Wa_TBe Da_TBe Wb_TBe Wc_TBe Wd_TBe Fb_TBe XI_TBe A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (efree_spine_TBe (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR (conj HO (conj E153 HST))
           (hdfe_TBe HSEGE CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_TBe CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_TBe CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.
End F0T_aTBe.

(* [comment removed for export] *)
Module F0T_aTBf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf"; "q_TBf"; "Ebg_TBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "L_free_tol"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "VFACT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTBf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "FACTS_Tg"; "P0T_c"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l1.F0T_xiTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kr.F0T_dTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qTBf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_TBf : ltac2:(tb__ "0|0|
S0S7S1cS3dS15U0A1A1A1S6A3"). Proof. vmr. Qed.
Lemma Da_TBf : ltac2:(tb__ "0|4|
S0SeSbS8SbS1bS1bA2M0A1M1S8S1dA1M2A2M3A1S4aS14S2cS16A1A1S3dS15U0A1A1A2SdG3SaG1G2ScG0SaS1bS1bS20P18A1S1fS4fA1A4S9G0A1A3S9S1dA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_TBf : ltac2:(tb__ "0|0|
S0S7S1cS3eS15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Wc_TBf : ltac2:(tb__ "0|0|
S0S7S1cS3fS15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Wd_TBf : ltac2:(tb__ "0|0|
S0S7S1cS40S15U0A1S24S11A1A2A1S6A3"). Proof. vmr. Qed.
Lemma Fb_TBf : ltac2:(tb__ "0|0|
S0S7S5aS1dS21S4eA1S58S6S3cS11A1A2A3S6A3"). Proof. vmr. Qed.
Lemma XI_TBf : ltac2:(tb__ "0|2|
S0SeS13A1S4cS41S6S15U0M0A1S24S11A1M1S3cS11A1A4S50G0SfS4dG1A2A2A2SdS13S59S6S11A2A2A3"). Proof. vmr. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S4S29S51R2A2S3S2eS45R2A2S30R2S46A2A2A2S2F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S1S57R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S5S29VCST;R1A2S1S56R2A1A1F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Theorem free_hi_TBf : ltac2:(tb__ "0|2|
S34OF_;S47S18S1eS8S2bQ40M0A1A1S2aG0S1aR2PcA2A2S5S2aG0S1aR3PdA2A2S5S23S10S35R4R3ScSbS13S22A2M1SaS13S22S2dS16A1S17S44S10A1VCST;VXGL;R6R5A5A4S9G1A1A3A5S31S19R6A1S38S10R9S37R7A1A3S4bS10RaS37R8A1A3S2eS42S2fR6Z10A2A2S0S7S48RbA1S6A3S28S11RcA2S5S27S3aRfRdRbRaR2R1A6S0S5S26R2A1S43A3S3bRfS25R11RfRdRcR4R3A6A2S54S39VCST;VXGL;R12A3R13R12R11S25R12R10ReRdR5R4A6S12RcA7F_;F_;F_;Fjv;Ft;S52RfRdA2S33S10R10S36S10S49RfReA2S2cS16A1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF true (Wcan 0) UStopLe q_TBf A rho)); [intros w Hw; exact (entry_pure_T true _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (tq_instantiate true q_TBf Wa_TBf Da_TBf Wb_TBf Wc_TBf Wd_TBf Fb_TBf XI_TBf A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (free_spine_TBf (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR (conj HO (conj E153 HST))
           (hdf_TBf HSEG CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_TBf CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_TBf CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_TBf : ltac2:(tb__ "0|2|
S47S18S1eS8S2bQ40M0A1A1S2aG0S1aR2PcA2A2S5S2aG0S1aR3PdA2A2S5S23S10S35R4R3ScSbS13S22A2M1SaS13S22S2dS16A1S17S44S10A1VCST;VXGL;R6R5A5A4S9G1A1A3A5S31S19R6A1S2eS42S2fR4Z10A2A2S0S7S48R9A1S6A3S28S11RaA2S5S27S3aRdRbR9R8R2R1A6S0S5S26R2A1S43A3S3bRdS25RfRdRbRaR4R3A6A2S55S39VCST;VXGL;R10A3R10RfS25R10ReRcRbR5R4A6S12RaA6F_;F_;F_;Fjv;Ft;S53RbA1S32S10S36S10S49RdRcA2S2cS16A1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (entry_pureF true (Wcan 0) UStopLe q_TBf A rho)); [intros w Hw; exact (entry_pure_T true _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (tq_instantiate true q_TBf Wa_TBf Da_TBf Wb_TBf Wc_TBf Wd_TBf Fb_TBf XI_TBf A Kc rho tp w p n t jv IFF Hw) as (HR & Hw1 & HO & E153).
  exact (efree_spine_TBf (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR (conj HO (conj E153 HST))
           (hdfe_TBf HSEGE CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HKM HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_TBf CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_TBf CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.
End F0T_aTBf.

(* [comment removed for export] *)
Module F0T_mLTA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "False"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "andb"; "cons"; "false"; "nil"; "negb"; "pair"; "prod"; "option"; "orb"; "Some"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0T_mLTA"; "MT_LTA"; "m1_LTA"; "PMID_LTA"; "MX_LTA"; "MH0_LTA"; "m2_LTA"; "m3_LTA"; "m4_LTA"; "m1okb_LTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_lenient"; "ss_next"; "swf"; "sv"; "rw"; "SVar"; "sprop"; "ss_objs"; "SLit"; "sobj"; "sv_below"; "sprop_below"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA"; "q_LTA"; "Ebg_LTA"; "S1c_LTA"; "ED_LTA"; "Edr_LTA"; "TD_LTA"; "Xf_LTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "FUELF"; "CASX"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "atpc"; "LOOPX"; "FACTS_Tc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTA"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_geom"; "ag_stack_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "L_free_tol"; "HBz"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0T_mLTA.MLTA"; "side_pure_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "carve_link_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "J_free_tol_preT"; "obnd"; "objs_le"; "side_chkb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j1.UnwT_pres OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kr.F0T_dLTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_LTA : ltac2:(tb__ "0|0|
S0S5S2cS73S19U0A1S18A2A1S6A3"). Proof. vmr. Qed.
Lemma Dai_LTA : ltac2:(tb__ "0|4|
S0SfSeS7SeS2dS2dA2M0A1M1S7S30A1M2A2M3A1S94S14S77S1aA1A1S73S19U0A1S18A2A2S11G3SdG1G2S9G0SdS2dS2dS2fP18A1S32S99A1A4SbG0A1A3SbS30A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_LTA : ltac2:(tb__ "0|0|
S0S5S2cS75S19U0A1S18A2A1S6A3"). Proof. vmr. Qed.
Lemma Wci_LTA : ltac2:(tb__ "0|0|
S0S5S2cS76S19U0A1S18A2A1S6A3"). Proof. vmr. Qed.
Definition Certi_LTA__runs : ltac2:(tb__ "0|0|
S7SfS7S13A1A1A1") := ltac2:(tb__ "0|0|
S95S1eUbb8S70S72U0S18A2A4").
Lemma Certi_LTA : ltac2:(tb__ "0|1|
S0S5S7dS1eUbb8S70S1fS72U0M0S18A2S9S15S71S19G0A1S18A2SbS15A1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_LTA__runs); [unfold Certi_LTA__runs; reflexivity | vmr]. Qed.
Lemma ECerti_LTA : ltac2:(tb__ "0|2|
S0S5S7eS1eUbb8S70S1fS74U0M0S18A2S9S7cS7fS71S19G0A1S18A2Z0M1S32G1A1A3SbS7cA1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_LTA__runs); [unfold Certi_LTA__runs; reflexivity | vmr]. Qed.

Definition PMID_LTA : axst := ltac2:(tb__ "0|0|
S84SaS19U0A1S18S37A4").
Lemma Wbm_LTA : ltac2:(tb__ "0|0|
S0S5S2cS85S19U0A1S18S37A3A1S6A3"). Proof. vmr. Qed.
Lemma Wcm_LTA : ltac2:(tb__ "0|0|
S0S5S2cS86S19U0A1S18S37A3A1S6A3"). Proof. vmr. Qed.
Lemma Wdm_LTA : ltac2:(tb__ "0|0|
S0S5S2cS87S19U0A1S18S37A3A1S6A3"). Proof. vmr. Qed.
Lemma Fbm_LTA : ltac2:(tb__ "0|0|
S0S5S41S30S35S98A1S47SaS37A2A3S6A3"). Proof. vmr. Qed.
Lemma XIm_LTA : ltac2:(tb__ "0|2|
S0SfS15A1S97S88SaS19U0M0A1M1S18S37A4S9aG0S37A2A2S11S15S84SaG1S18S37A4A2A3"). Proof. vmr. Qed.

Definition m1_LTA : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] PMID_LTA.
Definition MH0_LTA : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m1_LTA) DUMMY).
Definition m2_LTA : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] MH0_LTA.
Definition MH1_LTA : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m2_LTA) DUMMY).
Definition MT_LTA : axst := Eval vm_compute in LT_ofg MH1_LTA F0_LTA.
Definition MX_LTA : axst := Eval vm_compute in EX_ofg MH1_LTA F0_LTA.
Definition m3_LTA : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state MT_LTA (SVar pFR)).
Definition m4_LTA : list leafA := Eval vm_compute in runA FUELF [CASX] MX_LTA.
Lemma RUN1m_LTA : ltac2:(tb__ "0|0|
S0S7S13A1S68S3fS9S17S43S9S17S40SbS17A1A3A3S22A3S21A3"). Proof. Time vmr. Qed.
Lemma RUN2m_LTA : ltac2:(tb__ "0|0|
S0S7S13A1S68S3fS9S17S43S9S17S46SbS17A1A3A3S24A3S25A3"). Proof. Time vmr. Qed.
Lemma RUN3m_LTA : ltac2:(tb__ "0|0|
S0S7S13A1S68S3fS9S17S43S9S17S46SbS17A1A3A3S8dS20S2fS44A1A2A3S26A3"). Proof. Time vmr. Qed.
Lemma RUN4m_LTA : ltac2:(tb__ "0|0|
S0S7S13A1S68S3fS9S17S40SbS17A1A3S23A3S27A3"). Proof. Time vmr. Qed.
Definition m1okb_LTA (l : list leafA) : bool := ltac2:(tb__ "0|1|
S41S13S13S10S4bS36S14S16R1A1M0A1A1S43A2S3eG0S39A2A2LL;Vl;A3").
Lemma chkm_LTA : ltac2:(tb__ "0|a|
S0S5S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8ScS7S13A1M0S5Lx;M1S21S6S13G0SaLl0;Ll;M2X7x2A1ScG1S25S6G2X7x2A1A2ScG1S26S6G2X7x2A1A2ScG1S27S6G2X7x2A1A2S28S21A1A2S93S12S13S45S43S21A2A2U1A2A2S41S13S13S10S3eS16R1A1M3S20A2S3eG3S23A2A2LL;S25A3A2S2cS14S8cS20S2fS44A1M4A2A1A1A2S34S2bS14S20A1M5A1M6G4A2A2S41S13S8bS20S23S44A3S26A3A2S41S13S13S3eG3S39A2LL;S27A3A2S6bS1fS2bS14S22A1M7A1A2A2S6bS1fS2bS14S24A1M8A1A2A2S6bS1fG6A2A2S6bS1fS2bS14S23A1M9A1A2A2ScS2aG7A1A1A2ScS2aG8A1A1A2ScS2aG5A1A1A2ScS2aG9A1A1A2S6A3").
Proof. Time vmr. Qed.
Lemma MH0eq_LTA : ltac2:(tb__ "0|0|
S0S15S16S7bS13U0S45S43S21A2S69A4A1S24A3"). Proof. vmr. Qed.
Lemma SIDEm_LTA : ltac2:(tb__ "0|0|
S0S5S92S22S20A2S6A3"). Proof. Time vmr. Qed.
Lemma OBNDm_LTA : ltac2:(tb__ "0|1|
S0S7SeSeS2dS2dA2S2dA2M0A1S7aS33G0S90S31S14S20A1A1A4S7aS33G0S90S31S14S22A1A1A4A3"). Proof. Time vmr. Qed.

Lemma chkm_split_LTA : ltac2:(tb__ "0|9|
S1S1S2S0S7S13A1M0S21SbS13A1M1A3A1S1S2S0G0S25G1A3A1S1S2S0G0S26G1A3A1S2S0G0S27G1A3A1A2A2A2S1S0S5S28S21A1S6A3S1S0S5S93S12S13S45S43S21A2A2U1A2S6A3S1S0S5S41S13S13S10S3eS16R1A1M2S20A2S3eG2S23A2A2LL;S25A3S6A3S1S0S5S2cS14S8cS20S2fS44A1M3A2A1A1S6A3S1S0S5S34S2bS14S20A1M4A1M5G3A2S6A3S1S0S5S41S13S8bS20S23S44A3S26A3S6A3S1S0S5S41S13S13S3eG2S39A2LL;S27A3S6A3S1S1S6aS1fS2bS14S22A1M6A1A2S1S6aS1fS2bS14S24A1M7A1A2S1S6aS1fG5A2S6aS1fS2bS14S23A1M8A1A2A2A2A2S1S0S5S2aG6A1SaA3S1S0S5S2aG7A1SaA3S1S0S5S2aG4A1SaA3S0S5S2aG8A1SaA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkm_LTA as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma M1ok_LTA : ltac2:(tb__ "0|1|
S13S42S13R1S21A3S3S0S15S16R2A1M0S24A3S0S5S3eG0S39A2S6A3A2F_;FL;").
Proof.
  destruct chkm_split_LTA as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH m1_LTA)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- MH0eq_LTA. destruct (atpc LOOPH m1_LTA) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section MLTA.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Definition side_pure_m (A : AA) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S1S91Vrho1;S58Q40M0S2eVrho1;PaA2A2S31S14S22A1A1A3S1S0S57G0A1S2eVrho1;P99A2S59G0S66S65VA;A1M1A1M2A2A3S1S48Z1G2A2S48G2S79S67G1A1A1A2A2A2A2").

Theorem free_spine_m_LTA : ltac2:(tb__ "0|0|
S17OF_;S6dOF_;S63S1cS29S29S7S57Q40A1A1S6cS1dR5A1S5dVsegs;R8S5cR6A1A3S5eR6R5A2S82R9R6A2S5fU0S18RcRbRaR9R7S3aS3cR5AaS61RdRcRbRaR8S38R6A7S61ReRdRcRbR9S3bR7A7S61RfReRdRcRaS3dR8A7S29S6fVsegs;R10S5bVsegs;S8eRfReRcA3S22R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chkm_split_LTA as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LTA MH0_LTA MT_LTA MX_LTA S1c_LTA pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LTA m2_LTA m3_LTA m4_LTA HNX HLEN
           (runT_some _ _ _ _ RUN1m_LTA NE1) M1ok_LTA (runT_some _ _ _ _ RUN2m_LTA NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LTA NE3) H3 (runT_some _ _ _ _ RUN4m_LTA NE4) H4
           (hside_of A Kc rho1 PMID_LTA MT_LTA tp SIDEm_LTA OBNDm_LTA HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_s1c_LTA keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF rhoE).
Qed.
Theorem efree_spine_m_LTA : ltac2:(tb__ "0|0|
S17OF_;S63S1cS29S29S7S57Q40A1A1S6dOF_;S1dR5A1S5eR5R4A2S82R8R5A2S60U0S18RaR9R8R6S3aS3cR4A9S62RbRaR9R7S38R5A6S62RcRbRaR8S3bR6A6S62RdRcRbR9S3dR7A6S29S6eVsegs;S5bVsegs;S8eReRdRbA3S22R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chkm_split_LTA as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LTA MH0_LTA MT_LTA MX_LTA S1c_LTA pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LTA m2_LTA m3_LTA m4_LTA HNX HLEN
           (runT_some _ _ _ _ RUN1m_LTA NE1) M1ok_LTA (runT_some _ _ _ _ RUN2m_LTA NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LTA NE3) H3 (runT_some _ _ _ _ RUN4m_LTA NE4) H4
           (hside_of A Kc rho1 PMID_LTA MT_LTA tp SIDEm_LTA OBNDm_LTA HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_s1c_LTA keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF rhoE).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S17S56VCST;R1A2S3S56S9bR2A2S1S48S54R2A2S49R2S55A2A2A2S4F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S17S56VCST;R1A2S2S9fR2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S17S56VCST;R1A2S2S9eR2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S17S56VCST;R1A2S1S2S1S48S54R2A2S49R2S55A2A2A1S2S1S48Z17db48R2A2S49R2Z17db4cA2A2A1A2F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Theorem free_lo_ia0_LTA : ltac2:(tb__ "0|6|
S6dOF_;S63S1cS29S7S57Q40M0A1A1S58G0S2eR2PcA2A2S17S58G0S2eR3PdA2A2S17S4dS1eS5aR4R3S9SeS15S4cA2M1SdS15S4cS78S1aA1M2S1bS53S1eA1M3VCST;VXGL;R6R5A5A4SbG1A1M4A3A5S6cS1dR6A1S5dS1eR9S5cR7A1A3S96S1eRaS5cR8A1A3S48S4aR6R5A2S89A2S0S5S64RbA1SaA3S51S37RcA2S29S17S50S83R10S4eR10ReRcRbR2R1A6R3A3S81S52R11A1R4RdRcR3R2A6S0S17S4fR3A1S8aA3S5eR6S4eS52R13A1R6RfReR5R4A6A2S61S80VCST;VXGL;S52R14A1M5A3R15G5R13S4eG5R7R10RfR6R5A6S38S4dS1eS5aR7R11S9G1SdS15S4cG2S1bG3VCST;VXGL;G5R13A5A4G4A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S9cRfRdA2S6fS1eR10S5bS1eS8fRfReA2S77S1aA1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix Wai_LTA Dai_LTA Wbi_LTA Wci_LTA Certi_LTA ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_LTA (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_LTA HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false q_LTA Wbm_LTA Wcm_LTA Wdm_LTA Fbm_LTA XIm_LTA A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n) AGB IFF Hw) as (HR & Hw1 & HO).
  exact (free_spine_m_LTA (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR (conj HO (conj eq_refl HST))
           (hdf_LTA HSEG CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_LTA CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_LTA CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_LTA : ltac2:(tb__ "0|6|
S63S1cS29S7S57Q40M0A1A1S58G0S2eR2PcA2A2S17S58G0S2eR3PdA2A2S17S4dS1eS5aR4R3S9SeS15S4cA2M1SdS15S4cS78S1aA1M2S1bS53S1eA1M3VCST;VXGL;R6R5A5A4SbG1A1M4A3A5S6cS1dR6A1S48S4aR4R3A2S89A2S0S5S64R9A1SaA3S51S37RaA2S29S17S50S83ReS4eReRcRaR9R2R1A6R3A3S81S52RfA1R4RbRaR3R2A6S0S17S4fR3A1S8aA3S5eR6S4eS52R11A1R6RdRcR5R4A6A2S62S80VCST;VXGL;S52R12A1M5A3G5R11S4eG5R7ReRdR6R5A6S38S4dS1eS5aR7RfS9G1SdS15S4cG2S1bG3VCST;VXGL;G5R11A5A4G4A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S9dRbA1S6eS1eS5bS1eS8fRdRcA2S77S1aA1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix Wai_LTA Dai_LTA Wbi_LTA Wci_LTA ECerti_LTA A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_LTA (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_LTA HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false q_LTA Wbm_LTA Wcm_LTA Wdm_LTA Fbm_LTA XIm_LTA A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n) AGB IFF Hw) as (HR & Hw1 & HO).
  exact (efree_spine_m_LTA (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR (conj HO (conj eq_refl HST))
           (hdfe_LTA HSEGE CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_LTA CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_LTA CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End MLTA.
End F0T_mLTA.

(* [comment removed for export] *)
Module F0T_mLTBe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "False"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "andb"; "cons"; "false"; "nil"; "negb"; "pair"; "prod"; "option"; "orb"; "Some"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0T_mLTBe"; "MT_LTBe"; "m1_LTBe"; "PMID_LTBe"; "MX_LTBe"; "MH0_LTBe"; "m2_LTBe"; "m3_LTBe"; "m4_LTBe"; "m1okb_LTBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_lenient"; "ss_next"; "swf"; "sv"; "rw"; "SVar"; "sprop"; "ss_objs"; "SLit"; "sobj"; "sv_below"; "sprop_below"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe"; "q_LTBe"; "Ebg_LTBe"; "S1c_LTBe"; "ED_LTBe"; "Edr_LTBe"; "TD_LTBe"; "Xf_LTBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "FUELF"; "CASX"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "atpc"; "LOOPX"; "FACTS_Tc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTBe"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_geom"; "ag_stack_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "DUMMY"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "L_free_tol"; "HBz"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lf.F0T_mLTBe.MLTBe"; "side_pure_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "carve_link_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "J_free_tol_preT"; "obnd"; "objs_le"; "side_chkb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "XI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j1.UnwT_pres OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0T_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0T_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kz.F0T_xiLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kr.F0T_dLTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l5.F0T_qLTBe.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_LTBe : ltac2:(tb__ "0|0|
S0S5S2cS73S19U0A1S18A2A1S6A3"). Proof. vmr. Qed.
Lemma Dai_LTBe : ltac2:(tb__ "0|4|
S0SfSeS7SeS2dS2dA2M0A1M1S7S30A1M2A2M3A1S94S14S77S1aA1A1S73S19U0A1S18A2A2S11G3SdG1G2S9G0SdS2dS2dS2fP18A1S32S99A1A4SbG0A1A3SbS30A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_LTBe : ltac2:(tb__ "0|0|
S0S5S2cS75S19U0A1S18A2A1S6A3"). Proof. vmr. Qed.
Lemma Wci_LTBe : ltac2:(tb__ "0|0|
S0S5S2cS76S19U0A1S18A2A1S6A3"). Proof. vmr. Qed.
Definition Certi_LTBe__runs : ltac2:(tb__ "0|0|
S7SfS7S13A1A1A1") := ltac2:(tb__ "0|0|
S95S1eUbb8S70S72U0S18A2A4").
Lemma Certi_LTBe : ltac2:(tb__ "0|1|
S0S5S7dS1eUbb8S70S1fS72U0M0S18A2S9S15S71S19G0A1S18A2SbS15A1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_LTBe__runs); [unfold Certi_LTBe__runs; reflexivity | vmr]. Qed.
Lemma ECerti_LTBe : ltac2:(tb__ "0|2|
S0S5S7eS1eUbb8S70S1fS74U0M0S18A2S9S7cS7fS71S19G0A1S18A2Z0M1S32G1A1A3SbS7cA1A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_LTBe__runs); [unfold Certi_LTBe__runs; reflexivity | vmr]. Qed.

Definition PMID_LTBe : axst := ltac2:(tb__ "0|0|
S84SaS19U0A1S18S37A4").
Lemma Wbm_LTBe : ltac2:(tb__ "0|0|
S0S5S2cS85S19U0A1S18S37A3A1S6A3"). Proof. vmr. Qed.
Lemma Wcm_LTBe : ltac2:(tb__ "0|0|
S0S5S2cS86S19U0A1S18S37A3A1S6A3"). Proof. vmr. Qed.
Lemma Wdm_LTBe : ltac2:(tb__ "0|0|
S0S5S2cS87S19U0A1S18S37A3A1S6A3"). Proof. vmr. Qed.
Lemma Fbm_LTBe : ltac2:(tb__ "0|0|
S0S5S41S30S35S98A1S47SaS37A2A3S6A3"). Proof. vmr. Qed.
Lemma XIm_LTBe : ltac2:(tb__ "0|2|
S0SfS15A1S97S88SaS19U0M0A1M1S18S37A4S9aG0S37A2A2S11S15S84SaG1S18S37A4A2A3"). Proof. vmr. Qed.

Definition m1_LTBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] PMID_LTBe.
Definition MH0_LTBe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m1_LTBe) DUMMY).
Definition m2_LTBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] MH0_LTBe.
Definition MH1_LTBe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH m2_LTBe) DUMMY).
Definition MT_LTBe : axst := Eval vm_compute in LT_ofg MH1_LTBe F0_LTBe.
Definition MX_LTBe : axst := Eval vm_compute in EX_ofg MH1_LTBe F0_LTBe.
Definition m3_LTBe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state MT_LTBe (SVar pFR)).
Definition m4_LTBe : list leafA := Eval vm_compute in runA FUELF [CASX] MX_LTBe.
Lemma RUN1m_LTBe : ltac2:(tb__ "0|0|
S0S7S13A1S68S3fS9S17S43S9S17S40SbS17A1A3A3S22A3S21A3"). Proof. Time vmr. Qed.
Lemma RUN2m_LTBe : ltac2:(tb__ "0|0|
S0S7S13A1S68S3fS9S17S43S9S17S46SbS17A1A3A3S24A3S25A3"). Proof. Time vmr. Qed.
Lemma RUN3m_LTBe : ltac2:(tb__ "0|0|
S0S7S13A1S68S3fS9S17S43S9S17S46SbS17A1A3A3S8dS20S2fS44A1A2A3S26A3"). Proof. Time vmr. Qed.
Lemma RUN4m_LTBe : ltac2:(tb__ "0|0|
S0S7S13A1S68S3fS9S17S40SbS17A1A3S23A3S27A3"). Proof. Time vmr. Qed.
Definition m1okb_LTBe (l : list leafA) : bool := ltac2:(tb__ "0|1|
S41S13S13S10S4bS36S14S16R1A1M0A1A1S43A2S3eG0S39A2A2LL;Vl;A3").
Lemma chkm_LTBe : ltac2:(tb__ "0|a|
S0S5S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8ScS7S13A1M0S5Lx;M1S21S6S13G0SaLl0;Ll;M2X7x2A1ScG1S25S6G2X7x2A1A2ScG1S26S6G2X7x2A1A2ScG1S27S6G2X7x2A1A2S28S21A1A2S93S12S13S45S43S21A2A2U1A2A2S41S13S13S10S3eS16R1A1M3S20A2S3eG3S23A2A2LL;S25A3A2S2cS14S8cS20S2fS44A1M4A2A1A1A2S34S2bS14S20A1M5A1M6G4A2A2S41S13S8bS20S23S44A3S26A3A2S41S13S13S3eG3S39A2LL;S27A3A2S6bS1fS2bS14S22A1M7A1A2A2S6bS1fS2bS14S24A1M8A1A2A2S6bS1fG6A2A2S6bS1fS2bS14S23A1M9A1A2A2ScS2aG7A1A1A2ScS2aG8A1A1A2ScS2aG5A1A1A2ScS2aG9A1A1A2S6A3").
Proof. Time vmr. Qed.
Lemma MH0eq_LTBe : ltac2:(tb__ "0|0|
S0S15S16S7bS13U0S45S43S21A2S69A4A1S24A3"). Proof. vmr. Qed.
Lemma SIDEm_LTBe : ltac2:(tb__ "0|0|
S0S5S92S22S20A2S6A3"). Proof. Time vmr. Qed.
Lemma OBNDm_LTBe : ltac2:(tb__ "0|1|
S0S7SeSeS2dS2dA2S2dA2M0A1S7aS33G0S90S31S14S20A1A1A4S7aS33G0S90S31S14S22A1A1A4A3"). Proof. Time vmr. Qed.

Lemma chkm_split_LTBe : ltac2:(tb__ "0|9|
S1S1S2S0S7S13A1M0S21SbS13A1M1A3A1S1S2S0G0S25G1A3A1S1S2S0G0S26G1A3A1S2S0G0S27G1A3A1A2A2A2S1S0S5S28S21A1S6A3S1S0S5S93S12S13S45S43S21A2A2U1A2S6A3S1S0S5S41S13S13S10S3eS16R1A1M2S20A2S3eG2S23A2A2LL;S25A3S6A3S1S0S5S2cS14S8cS20S2fS44A1M3A2A1A1S6A3S1S0S5S34S2bS14S20A1M4A1M5G3A2S6A3S1S0S5S41S13S8bS20S23S44A3S26A3S6A3S1S0S5S41S13S13S3eG2S39A2LL;S27A3S6A3S1S1S6aS1fS2bS14S22A1M6A1A2S1S6aS1fS2bS14S24A1M7A1A2S1S6aS1fG5A2S6aS1fS2bS14S23A1M8A1A2A2A2A2S1S0S5S2aG6A1SaA3S1S0S5S2aG7A1SaA3S1S0S5S2aG4A1SaA3S0S5S2aG8A1SaA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chkm_LTBe as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma M1ok_LTBe : ltac2:(tb__ "0|1|
S13S42S13R1S21A3S3S0S15S16R2A1M0S24A3S0S5S3eG0S39A2S6A3A2F_;FL;").
Proof.
  destruct chkm_split_LTBe as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH m1_LTBe)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- MH0eq_LTBe. destruct (atpc LOOPH m1_LTBe) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section MLTBe.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Definition side_pure_m (A : AA) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S1S91Vrho1;S58Q40M0S2eVrho1;PaA2A2S31S14S22A1A1A3S1S0S57G0A1S2eVrho1;P99A2S59G0S66S65VA;A1M1A1M2A2A3S1S48Z1G2A2S48G2S79S67G1A1A1A2A2A2A2").

Theorem free_spine_m_LTBe : ltac2:(tb__ "0|0|
S17OF_;S6dOF_;S63S1cS29S29S7S57Q40A1A1S6cS1dR5A1S5dVsegs;R8S5cR6A1A3S5eR6R5A2S82R9R6A2S5fU0S18RcRbRaR9R7S3aS3cR5AaS61RdRcRbRaR8S38R6A7S61ReRdRcRbR9S3bR7A7S61RfReRdRcRaS3dR8A7S29S6fVsegs;R10S5bVsegs;S8eRfReRcA3S22R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chkm_split_LTBe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LTBe MH0_LTBe MT_LTBe MX_LTBe S1c_LTBe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LTBe m2_LTBe m3_LTBe m4_LTBe HNX HLEN
           (runT_some _ _ _ _ RUN1m_LTBe NE1) M1ok_LTBe (runT_some _ _ _ _ RUN2m_LTBe NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LTBe NE3) H3 (runT_some _ _ _ _ RUN4m_LTBe NE4) H4
           (hside_of A Kc rho1 PMID_LTBe MT_LTBe tp SIDEm_LTBe OBNDm_LTBe HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_s1c_LTBe keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF rhoE).
Qed.
Theorem efree_spine_m_LTBe : ltac2:(tb__ "0|0|
S17OF_;S63S1cS29S29S7S57Q40A1A1S6dOF_;S1dR5A1S5eR5R4A2S82R8R5A2S60U0S18RaR9R8R6S3aS3cR4A9S62RbRaR9R7S38R5A6S62RcRbRaR8S3bR6A6S62RdRcRbR9S3dR7A6S29S6eVsegs;S5bVsegs;S8eReRdRbA3S22R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chkm_split_LTBe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) PMID_LTBe MH0_LTBe MT_LTBe MX_LTBe S1c_LTBe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           m1_LTBe m2_LTBe m3_LTBe m4_LTBe HNX HLEN
           (runT_some _ _ _ _ RUN1m_LTBe NE1) M1ok_LTBe (runT_some _ _ _ _ RUN2m_LTBe NE2) H2 HW HB (runT_some _ _ _ _ RUN3m_LTBe NE3) H3 (runT_some _ _ _ _ RUN4m_LTBe NE4) H4
           (hside_of A Kc rho1 PMID_LTBe MT_LTBe tp SIDEm_LTBe OBNDm_LTBe HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_s1c_LTBe keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF rhoE).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S17S56VCST;R1A2S3S56S9bR2A2S1S48S54R2A2S49R2S55A2A2A2S4F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S17S56VCST;R1A2S2S9fR2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S17S56VCST;R1A2S2S9eR2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S17S56VCST;R1A2S1S2S1S48S54R2A2S49R2S55A2A2A1S2S1S48Z17db48R2A2S49R2Z17db4cA2A2A1A2F_;Fa;").
Hypothesis HSEG : segD_T_stmt.
Hypothesis HSEGE : segD_TE_stmt.
Hypothesis HGEO : geomT_stmt.

Theorem free_lo_ia0_LTBe : ltac2:(tb__ "0|6|
S6dOF_;S63S1cS29S7S57Q40M0A1A1S58G0S2eR2PcA2A2S17S58G0S2eR3PdA2A2S17S4dS1eS5aR4R3S9SeS15S4cA2M1SdS15S4cS78S1aA1M2S1bS53S1eA1M3VCST;VXGL;R6R5A5A4SbG1A1M4A3A5S6cS1dR6A1S5dS1eR9S5cR7A1A3S96S1eRaS5cR8A1A3S48S4aR6R5A2S89A2S0S5S64RbA1SaA3S51S37RcA2S29S17S50S83R10S4eR10ReRcRbR2R1A6R3A3S81S52R11A1R4RdRcR3R2A6S0S17S4fR3A1S8aA3S5eR6S4eS52R13A1R6RfReR5R4A6A2S61S80VCST;VXGL;S52R14A1M5A3R15G5R13S4eG5R7R10RfR6R5A6S38S4dS1eS5aR7R11S9G1SdS15S4cG2S1bG3VCST;VXGL;G5R13A5A4G4A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S9cRfRdA2S6fS1eR10S5bS1eS8fRfReA2S77S1aA1RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (triple_pre_pure segsA ok _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix Wai_LTBe Dai_LTBe Wbi_LTBe Wci_LTBe Certi_LTBe ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_LTBe (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_LTBe HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false q_LTBe Wbm_LTBe Wcm_LTBe Wdm_LTBe Fbm_LTBe XIm_LTBe A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n) AGB IFF Hw) as (HR & Hw1 & HO).
  exact (free_spine_m_LTBe (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR (conj HO (conj eq_refl HST))
           (hdf_LTBe HSEG CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_LTBe CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_LTBe CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.
Theorem efree_lo_ia0_LTBe : ltac2:(tb__ "0|6|
S63S1cS29S7S57Q40M0A1A1S58G0S2eR2PcA2A2S17S58G0S2eR3PdA2A2S17S4dS1eS5aR4R3S9SeS15S4cA2M1SdS15S4cS78S1aA1M2S1bS53S1eA1M3VCST;VXGL;R6R5A5A4SbG1A1M4A3A5S6cS1dR6A1S48S4aR4R3A2S89A2S0S5S64R9A1SaA3S51S37RaA2S29S17S50S83ReS4eReRcRaR9R2R1A6R3A3S81S52RfA1R4RbRaR3R2A6S0S17S4fR3A1S8aA3S5eR6S4eS52R11A1R6RdRcR5R4A6A2S62S80VCST;VXGL;S52R12A1M5A3G5R11S4eG5R7ReRdR6R5A6S38S4dS1eS5aR7RfS9G1SdS15S4cG2S1bG3VCST;VXGL;G5R11A5A4G4A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S9dRbA1S6eS1eS5bS1eS8fRdRcA2S77S1aA1RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget_T A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (aa_Km A + aa_Kf A <= KMAX)); [intros w Hw; exact (entry_KM_T A Kc rho tp w Hw)|]. intros HKM.
  apply (etriple_pre_pure segsA _ _ (1 <= ag_stack_top (aa_geom A) <= HBz (topG (aa_geom A)))); [intros w Hw; exact (entry_geom_T HGEO A Kc rho tp w Hw)|]. intros HST.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix Wai_LTBe Dai_LTBe Wbi_LTBe Wci_LTBe ECerti_LTBe A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ [HJ _]]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_LTBe (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_LTBe HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false q_LTBe Wbm_LTBe Wcm_LTBe Wdm_LTBe Fbm_LTBe XIm_LTBe A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n) AGB IFF Hw) as (HR & Hw1 & HO).
  exact (efree_spine_m_LTBe (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR (conj HO (conj eq_refl HST))
           (hdfe_LTBe HSEGE CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HKM HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_LTBe CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_LTBe CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End MLTBe.
End F0T_mLTBe.

(* [comment removed for export] *)
Module F0A_a2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "JL_free"; "J_free_preT"; "KcA"; "Kc_ok"; "L_free"; "@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A"; "q_2A"; "Ebg_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "sa_f"; "XI"; "sb_f"; "sc_f"; "sd_f"; "se_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "FACTSc"; "P0_fc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_xi2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kl.F0A_d2A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_q2A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_2A : ltac2:(tb__ "0|0|
S9S10S1fS3bS1U2A1S0A2A1SfA3"). Proof. vmr. Qed.
Lemma Da_2A : ltac2:(tb__ "0|5|
S9S17S14S11S14S1eS1eA2M0A1M1S11S20A1M2A2M3A1S49S1cS3S2S1U2A1M4S0A3A1S3bG4S0A2A2S16G3S13G1G2S15G0S13S1eS1eS23P18A1S22S4dA1A4S12G0A1A3S12S20A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_2A : ltac2:(tb__ "0|0|
S9S10S1fS3dS1U2A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wc_2A : ltac2:(tb__ "0|0|
S9S10S1fS3eS1U2A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wd_2A : ltac2:(tb__ "0|0|
S9S10S1fS3fS1U2A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Fb_2A : ltac2:(tb__ "0|0|
S9S10S57S20S24S4cA1S4eSfS1U2A1S0S19A4A3SfA3"). Proof. vmr. Qed.
Lemma XI_2A : ltac2:(tb__ "0|2|
S9S17S1bA1S4bS40SfS1U2M0A1M1S0S19A4S3cG0S19A2A2S16S1bS4fSfG1S0S19A4A2A3"). Proof. vmr. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
SeS2bVCST;R1A2SdS2bS54R2A2ScS2eS45R2A2S30R2S46A2A2A2SbF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SeS2bVCST;R1A2SaS56R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
SeS2bVCST;R1A2SaS55R2A1A1F_;Fa;").

Theorem free_hi_2A : ltac2:(tb__ "0|4|
S34OF_;S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U2A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S38S18R9S37R7A1A3S4aS18RaS37R8A1A3S2eS42S2fR6Z10A2A2S9S10S48RbA1SfA3S2aS19RcA2SeS29S3aRfRdRbRaR2R1A6S9SeS28R2A1S43A3S41RfS27R11RfRdRcR4R3A6A2S52S39VCST;VXGL;R12A3R13R12R11S27R12R10ReRdR5R4A6S1aRcA7F_;F_;F_;Fjv;Ft;S50RfRdA2S33S18R10S36S18S5G3G2S0RfReA5S3S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF true (Wcan 2) UStopLe q_2A A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (f_instantiate true 2 UStopLe q_2A Wa_2A Da_2A Wb_2A Wc_2A Wd_2A Fb_2A XI_2A A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_2A (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR
           (hdf_2A_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_2A_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_2A_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_2A_4 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_2A CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_2A CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_2A : ltac2:(tb__ "0|4|
S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U2A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S2eS42S2fR4Z10A2A2S9S10S48R9A1SfA3S2aS19RaA2SeS29S3aRdRbR9R8R2R1A6S9SeS28R2A1S43A3S41RdS27RfRdRbRaR4R3A6A2S53S39VCST;VXGL;R10A3R10RfS27R10ReRcRbR5R4A6S1aRaA6F_;F_;F_;Fjv;Ft;S51RbA1S32S18S36S18S5G3G2S0RdRcA5S3S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (entry_pureF true (Wcan 2) UStopLe q_2A A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (f_instantiate true 2 UStopLe q_2A Wa_2A Da_2A Wb_2A Wc_2A Wd_2A Fb_2A XI_2A A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_2A (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR
           (hdfe_2A_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_2A_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_2A_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_2A_4 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_2A CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_2A CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.

End F0A_a2A.

(* [comment removed for export] *)
Module F0A_a2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "JL_free"; "J_free_preT"; "KcA"; "Kc_ok"; "L_free"; "@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be"; "q_2Be"; "Ebg_2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "sa_f"; "XI"; "sb_f"; "sc_f"; "sd_f"; "se_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "FACTSc"; "P0_fc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l8.F0A_xi2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kl.F0A_d2Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.F0A_q2Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_2Be : ltac2:(tb__ "0|0|
S9S10S1fS3bS1U2A1S0A2A1SfA3"). Proof. vmr. Qed.
Lemma Da_2Be : ltac2:(tb__ "0|5|
S9S17S14S11S14S1eS1eA2M0A1M1S11S20A1M2A2M3A1S49S1cS3S2S1U2A1M4S0A3A1S3bG4S0A2A2S16G3S13G1G2S15G0S13S1eS1eS23P18A1S22S4dA1A4S12G0A1A3S12S20A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_2Be : ltac2:(tb__ "0|0|
S9S10S1fS3dS1U2A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wc_2Be : ltac2:(tb__ "0|0|
S9S10S1fS3eS1U2A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wd_2Be : ltac2:(tb__ "0|0|
S9S10S1fS3fS1U2A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Fb_2Be : ltac2:(tb__ "0|0|
S9S10S57S20S24S4cA1S4eSfS1U2A1S0S19A4A3SfA3"). Proof. vmr. Qed.
Lemma XI_2Be : ltac2:(tb__ "0|2|
S9S17S1bA1S4bS40SfS1U2M0A1M1S0S19A4S3cG0S19A2A2S16S1bS4fSfG1S0S19A4A2A3"). Proof. vmr. Qed.

Section ASM.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
SeS2bVCST;R1A2SdS2bS54R2A2ScS2eS45R2A2S30R2S46A2A2A2SbF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SeS2bVCST;R1A2SaS56R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
SeS2bVCST;R1A2SaS55R2A1A1F_;Fa;").

Theorem free_hi_2Be : ltac2:(tb__ "0|4|
S34OF_;S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U2A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S38S18R9S37R7A1A3S4aS18RaS37R8A1A3S2eS42S2fR6Z10A2A2S9S10S48RbA1SfA3S2aS19RcA2SeS29S3aRfRdRbRaR2R1A6S9SeS28R2A1S43A3S41RfS27R11RfRdRcR4R3A6A2S52S39VCST;VXGL;R12A3R13R12R11S27R12R10ReRdR5R4A6S1aRcA7F_;F_;F_;Fjv;Ft;S50RfRdA2S33S18R10S36S18S5G3G2S0RfReA5S3S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF true (Wcan 2) UStopLe q_2Be A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (f_instantiate true 2 UStopLe q_2Be Wa_2Be Da_2Be Wb_2Be Wc_2Be Wd_2Be Fb_2Be XI_2Be A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_2Be (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR
           (hdf_2Be_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_2Be_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_2Be_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_2Be_4 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_2Be CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_2Be CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_2Be : ltac2:(tb__ "0|4|
S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U2A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S2eS42S2fR4Z10A2A2S9S10S48R9A1SfA3S2aS19RaA2SeS29S3aRdRbR9R8R2R1A6S9SeS28R2A1S43A3S41RdS27RfRdRbRaR4R3A6A2S53S39VCST;VXGL;R10A3R10RfS27R10ReRcRbR5R4A6S1aRaA6F_;F_;F_;Fjv;Ft;S51RbA1S32S18S36S18S5G3G2S0RdRcA5S3S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (entry_pureF true (Wcan 2) UStopLe q_2Be A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (f_instantiate true 2 UStopLe q_2Be Wa_2Be Da_2Be Wb_2Be Wc_2Be Wd_2Be Fb_2Be XI_2Be A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_2Be (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR
           (hdfe_2Be_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_2Be_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_2Be_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_2Be_4 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_2Be CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_2Be CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.

End F0A_a2Be.

