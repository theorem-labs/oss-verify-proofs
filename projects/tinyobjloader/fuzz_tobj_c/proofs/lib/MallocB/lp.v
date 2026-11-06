(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg iw l6 lj l7 kj.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics StackLayout Fs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartHandoffFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvInitB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvInitZ.

(* [comment removed for export] *)
Module F0A_a1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "JL_free"; "J_free_preT"; "KcA"; "Kc_ok"; "L_free"; "@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1A"; "q_1A"; "Ebg_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "sa_f"; "XI"; "sb_f"; "sc_f"; "sd_f"; "se_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "FACTSc"; "P0_fc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l6.F0A_xi1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_d1A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_1A : ltac2:(tb__ "0|0|
S9S10S1fS3bS1U1A1S0A2A1SfA3"). Proof. vmr. Qed.
Lemma Da_1A : ltac2:(tb__ "0|5|
S9S17S14S11S14S1eS1eA2M0A1M1S11S20A1M2A2M3A1S49S1cS3S2S1U1A1M4S0A3A1S3bG4S0A2A2S16G3S13G1G2S15G0S13S1eS1eS23P18A1S22S4dA1A4S12G0A1A3S12S20A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_1A : ltac2:(tb__ "0|0|
S9S10S1fS3dS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wc_1A : ltac2:(tb__ "0|0|
S9S10S1fS3eS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wd_1A : ltac2:(tb__ "0|0|
S9S10S1fS3fS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Fb_1A : ltac2:(tb__ "0|0|
S9S10S57S20S24S4cA1S4eSfS1U1A1S0S19A4A3SfA3"). Proof. vmr. Qed.
Lemma XI_1A : ltac2:(tb__ "0|2|
S9S17S1bA1S4bS40SfS1U1M0A1M1S0S19A4S3cG0S19A2A2S16S1bS4fSfG1S0S19A4A2A3"). Proof. vmr. Qed.

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

Theorem free_hi_1A : ltac2:(tb__ "0|4|
S34OF_;S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U1A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S38S18R9S37R7A1A3S4aS18RaS37R8A1A3S2eS42S2fR6Z10A2A2S9S10S48RbA1SfA3S2aS19RcA2SeS29S3aRfRdRbRaR2R1A6S9SeS28R2A1S43A3S41RfS27R11RfRdRcR4R3A6A2S52S39VCST;VXGL;R12A3R13R12R11S27R12R10ReRdR5R4A6S1aRcA7F_;F_;F_;Fjv;Ft;S50RfRdA2S33S18R10S36S18S5G3G2S0RfReA5S3S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF true (Wcan 1) UStopLe q_1A A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (f_instantiate true 1 UStopLe q_1A Wa_1A Da_1A Wb_1A Wc_1A Wd_1A Fb_1A XI_1A A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_1A (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR
           (hdf_1A_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_1A_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_1A_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_1A CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_1A CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_1A : ltac2:(tb__ "0|4|
S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U1A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S2eS42S2fR4Z10A2A2S9S10S48R9A1SfA3S2aS19RaA2SeS29S3aRdRbR9R8R2R1A6S9SeS28R2A1S43A3S41RdS27RfRdRbRaR4R3A6A2S53S39VCST;VXGL;R10A3R10RfS27R10ReRcRbR5R4A6S1aRaA6F_;F_;F_;Fjv;Ft;S51RbA1S32S18S36S18S5G3G2S0RdRcA5S3S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (entry_pureF true (Wcan 1) UStopLe q_1A A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (f_instantiate true 1 UStopLe q_1A Wa_1A Da_1A Wb_1A Wc_1A Wd_1A Fb_1A XI_1A A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_1A (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR
           (hdfe_1A_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_1A_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_1A_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_1A CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_1A CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.

End F0A_a1A.

(* [comment removed for export] *)
Module F0A_a1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "JL_free"; "J_free_preT"; "KcA"; "Kc_ok"; "L_free"; "@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be"; "q_1Be"; "Ebg_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "sa_f"; "XI"; "sb_f"; "sc_f"; "sd_f"; "se_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "FACTSc"; "P0_fc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_d1Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_1Be : ltac2:(tb__ "0|0|
S9S10S1fS3bS1U1A1S0A2A1SfA3"). Proof. vmr. Qed.
Lemma Da_1Be : ltac2:(tb__ "0|5|
S9S17S14S11S14S1eS1eA2M0A1M1S11S20A1M2A2M3A1S49S1cS3S2S1U1A1M4S0A3A1S3bG4S0A2A2S16G3S13G1G2S15G0S13S1eS1eS23P18A1S22S4dA1A4S12G0A1A3S12S20A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_1Be : ltac2:(tb__ "0|0|
S9S10S1fS3dS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wc_1Be : ltac2:(tb__ "0|0|
S9S10S1fS3eS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wd_1Be : ltac2:(tb__ "0|0|
S9S10S1fS3fS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Fb_1Be : ltac2:(tb__ "0|0|
S9S10S57S20S24S4cA1S4eSfS1U1A1S0S19A4A3SfA3"). Proof. vmr. Qed.
Lemma XI_1Be : ltac2:(tb__ "0|2|
S9S17S1bA1S4bS40SfS1U1M0A1M1S0S19A4S3cG0S19A2A2S16S1bS4fSfG1S0S19A4A2A3"). Proof. vmr. Qed.

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

Theorem free_hi_1Be : ltac2:(tb__ "0|4|
S34OF_;S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U1A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S38S18R9S37R7A1A3S4aS18RaS37R8A1A3S2eS42S2fR6Z10A2A2S9S10S48RbA1SfA3S2aS19RcA2SeS29S3aRfRdRbRaR2R1A6S9SeS28R2A1S43A3S41RfS27R11RfRdRcR4R3A6A2S52S39VCST;VXGL;R12A3R13R12R11S27R12R10ReRdR5R4A6S1aRcA7F_;F_;F_;Fjv;Ft;S50RfRdA2S33S18R10S36S18S5G3G2S0RfReA5S3S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF true (Wcan 1) UStopLe q_1Be A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (f_instantiate true 1 UStopLe q_1Be Wa_1Be Da_1Be Wb_1Be Wc_1Be Wd_1Be Fb_1Be XI_1Be A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_1Be (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR
           (hdf_1Be_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_1Be_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_1Be_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_1Be CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_1Be CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_1Be : ltac2:(tb__ "0|4|
S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U1A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S2eS42S2fR4Z10A2A2S9S10S48R9A1SfA3S2aS19RaA2SeS29S3aRdRbR9R8R2R1A6S9SeS28R2A1S43A3S41RdS27RfRdRbRaR4R3A6A2S53S39VCST;VXGL;R10A3R10RfS27R10ReRcRbR5R4A6S1aRaA6F_;F_;F_;Fjv;Ft;S51RbA1S32S18S36S18S5G3G2S0RdRcA5S3S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (entry_pureF true (Wcan 1) UStopLe q_1Be A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (f_instantiate true 1 UStopLe q_1Be Wa_1Be Da_1Be Wb_1Be Wc_1Be Wd_1Be Fb_1Be XI_1Be A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_1Be (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR
           (hdfe_1Be_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_1Be_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_1Be_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_1Be CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_1Be CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.

End F0A_a1Be.

(* [comment removed for export] *)
Module F0A_a1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "AE_A"; "Pre_freeI"; "JL_free"; "J_free_preT"; "KcA"; "Kc_ok"; "L_free"; "@Corelib.Init.Logic"; "eq"; "not"; "False"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "true"; "bool"; "list"; "nil"; "pair"; "prod"; "cons"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf"; "q_1Bf"; "Ebg_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "swf"; "sprop"; "valuation"; "SLit"; "SVar"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "sa_f"; "XI"; "sb_f"; "sc_f"; "sd_f"; "se_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "FACTSc"; "P0_fc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@Stdlib.Lists.List"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l7.F0A_xi1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_d1Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lj.F0A_q1Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wa_1Bf : ltac2:(tb__ "0|0|
S9S10S1fS3bS1U1A1S0A2A1SfA3"). Proof. vmr. Qed.
Lemma Da_1Bf : ltac2:(tb__ "0|5|
S9S17S14S11S14S1eS1eA2M0A1M1S11S20A1M2A2M3A1S49S1cS3S2S1U1A1M4S0A3A1S3bG4S0A2A2S16G3S13G1G2S15G0S13S1eS1eS23P18A1S22S4dA1A4S12G0A1A3S12S20A1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_1Bf : ltac2:(tb__ "0|0|
S9S10S1fS3dS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wc_1Bf : ltac2:(tb__ "0|0|
S9S10S1fS3eS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Wd_1Bf : ltac2:(tb__ "0|0|
S9S10S1fS3fS1U1A1S0S19A3A1SfA3"). Proof. vmr. Qed.
Lemma Fb_1Bf : ltac2:(tb__ "0|0|
S9S10S57S20S24S4cA1S4eSfS1U1A1S0S19A4A3SfA3"). Proof. vmr. Qed.
Lemma XI_1Bf : ltac2:(tb__ "0|2|
S9S17S1bA1S4bS40SfS1U1M0A1M1S0S19A4S3cG0S19A2A2S16S1bS4fSfG1S0S19A4A2A3"). Proof. vmr. Qed.

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

Theorem free_hi_1Bf : ltac2:(tb__ "0|4|
S34OF_;S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U1A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S38S18R9S37R7A1A3S4aS18RaS37R8A1A3S2eS42S2fR6Z10A2A2S9S10S48RbA1SfA3S2aS19RcA2SeS29S3aRfRdRbRaR2R1A6S9SeS28R2A1S43A3S41RfS27R11RfRdRcR4R3A6A2S52S39VCST;VXGL;R12A3R13R12R11S27R12R10ReRdR5R4A6S1aRcA7F_;F_;F_;Fjv;Ft;S50RfRdA2S33S18R10S36S18S5G3G2S0RfReA5S3S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (entry_pureF true (Wcan 1) UStopLe q_1Bf A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros k Hg w Hw.
  destruct (f_instantiate true 1 UStopLe q_1Bf Wa_1Bf Da_1Bf Wb_1Bf Wc_1Bf Wd_1Bf Fb_1Bf XI_1Bf A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (free_spine_1Bf (KEEPD CST XGL A) ok A Kc rho (rhoF_of A rho p n t jv) tp Q HKc Hok HR
           (hdf_1Bf_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_1Bf_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp) (hdf_1Bf_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC ok _ Hok Hokp)
           (HBIG t jv HTJ HJM HR)
           (f0_drain_1Bf CST XGL HCST HXGL HCSTQ HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) HKc Hok HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (f0_exit_1Bf CST XGL HCST HXGL HCSTF ok A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) k Hg w Hw1).
Qed.

Theorem efree_hi_1Bf : ltac2:(tb__ "0|4|
S47S6S21S11S2dQ40M0A1A1S2cG0S1dR2PcA2A2SeS2cG0S1dR3PdA2A2SeS26S18S35R4R3S15S14S1bS25A2M1S13S1bS25S8S2S1U1A1M2S0A3S4S44S18A1M3VCST;VXGL;R6R5A5A4S12G1A1A3A5S31S7R6A1S2eS42S2fR4Z10A2A2S9S10S48R9A1SfA3S2aS19RaA2SeS29S3aRdRbR9R8R2R1A6S9SeS28R2A1S43A3S41RdS27RfRdRbRaR4R3A6A2S53S39VCST;VXGL;R10A3R10RfS27R10ReRcRbR5R4A6S1aRaA6F_;F_;F_;Fjv;Ft;S51RbA1S32S18S36S18S5G3G2S0RdRcA5S3S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk true p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (entry_pureF true (Wcan 1) UStopLe q_1Bf A rho)); [intros w Hw; exact (entry_pure true _ _ _ A Kc rho tp w HHI Hii QC Hw)|].
  intros (HL & (tp0 & md0 & HA0) & t & jv & HTJ & HJM & IFF). fold p n in HL, HTJ, IFF.
  intros w Hw.
  destruct (f_instantiate true 1 UStopLe q_1Bf Wa_1Bf Da_1Bf Wb_1Bf Wc_1Bf Wd_1Bf Fb_1Bf XI_1Bf A Kc rho (rhoF_of A rho p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) (rhoF_agree A rho p n t jv) IFF Hw) as [HR Hw1].
  exact (efree_spine_1Bf (KEEPD CST XGL A) A Kc rho (rhoF_of A rho p n t jv) tp Q HKc HR
           (hdfe_1Bf_1 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_1Bf_2 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _) (hdfe_1Bf_3 CST XGL HCST HXGL HCSTD A Kc rho tp0 md0 _ _ t jv HKc HA0 HL HCL eq_refl HTJ QC _)
           (HBIG t jv HTJ HJM HR)
           (ef0_drain_1Bf CST XGL HCST HXGL HCSTQ HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) HKc HDS HBud eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (ef0_exit_1Bf CST XGL HCST HXGL HCSTF A Kc rho tp p n t jv (KEEPD CST XGL A) eq_refl eq_refl HL HCL Hii QC HR HJM (fun a H => H))
           (rhoF_of A rho p n t jv) w Hw1).
Qed.
End ASM.

End F0A_a1Bf.

(* [comment removed for export] *)
Module InvInitL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vm_lazy"; "m_vmmaps"; "page_in_ranges"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lp.InvInitL"; "HBL"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "prod"; "bool"; "list"; "app"; "false"; "pair"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff"; "sheet"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain"; "M1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes"; "eager_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3"; "null_rw_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop"; "Mmain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundI SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Placement KxA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartArgBytes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartTop StartMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require og.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.StartBD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartMainFds.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require og.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartHandoff StartHandoffFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartHandoffBlocks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.StartHandoffBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoffFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition HBL (mo : Model) : Prop := ltac2:(tb__ "0|1|
S6Q40M0A1S13Z2008fff7000S7G0R1A2A2S13S14S7G0R2A2Z1000A2S18A2S9ScS3R3S1Vmo;A1A2S11A3F_;F_;Fp;").

Lemma HBL_lazy_eq : ltac2:(tb__ "0|2|
S0S0S9SdSbS6Q40A1M0G0A2A1S1R1A1S1R2A1A3S5R3A1M1G1F_;F_;Fmo';Fmo;").
Proof. intros mo mo' E H p H1 H2. rewrite E. exact (H p H1 H2). Qed.
Lemma HBL_app : ltac2:(tb__ "0|4|
S0S0SdSbS6Q40A1M0G0A2M1A1M2S9G2S1R2A1SeG1R1S1R3A1A3A3S5R4A1M3G3F_;F_;Fl;Fmo';Fmo;").
Proof. intros mo mo' l E H p H1 H2. rewrite E. apply page_in_ranges_app_r. exact (H p H1 H2). Qed.
Lemma HBL_eager : ltac2:(tb__ "0|0|
S12S0S6Q40A1S5R2A1S5S1bR4R3R2A3A1F_;Fa;Fmo;FLz;").
Proof. intros Lz mo a H. apply (HBL_lazy_eq mo); [|exact H]. unfold eager_model. rewrite m_vm_lazy_with_vmmaps. reflexivity. Qed.
Lemma HBL_null_rw : ltac2:(tb__ "0|0|
S12S0S6Q40A1S5R2A1S5S1cR4R3R2A3A1F_;Fa;Fmo;FLz;").
Proof.
  intros Lz mo a H. apply (HBL_app mo _ (lazy_interior a (Z_to_bv 64 Lz))); [|exact H].
  unfold null_rw_model. rewrite m_vm_lazy_vm_add_lazy, m_vm_lazy_with_vmmaps. reflexivity.
Qed.

Section Facts.
Variables (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
S1fS17S16Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Variables (tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 : word) (x : Z) (o : out18) (v : bool) (rho4 rho' rho1 rhoM : valuation) (tp : list word) (w : world).
Hypothesis HS : ltac2:(tb__ "0|0|
S19Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vb10;Vb12;Vb13;Vb14;Vx;Vo;Vv;Vrho4;Vrho';Vrho1;VrhoM;Vtp;Vw;A1d").

Local Notation m1 := (StartMain.M1 sp brk mb draw lim inp tid).
Local Notation Mm := (StartTop.Mmain m1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14).
Local Notation mS1 := (StartTop.mS m1 a1 a2).
Local Notation mE := (Start7.mE mS1 P b4 b5 b6 b7 b8 b9 x b10).

Theorem HBL_main : HBL Mm.
Proof.
  pose proof HS as (Sfds & Sfs & Slim & SMI & Stid & Sx & G2 & G3 & HPL & HPL4 & HPL5 & HPL6 & HPL7 & HPL8 & HPL9 & HPL10 & Ho & _).
  pose proof (mS1_facts sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & Sx' & SLIM & SISP).
  pose proof (StartMain.M1_fields sp brk mb draw lim inp tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & _).
  pose proof (StartMain.brk_facts sp brk mb draw inp Hent) as [Hbrk Hbal].
  pose proof (mS_fields m1 Flz Fmaps Fna a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SBRK : 0x643000 <= bv_unsigned (vm_brk (m_vmmaps mS1)) <= 0x80643000) by (rewrite KS, Fbrk; exact Hbrk).

  assert (HE : HBL mE).
  { intros p H1 H2. pose proof (Start7.mE_fields mS1 P b4 b5 b6 b7 b8 b9 x b10) as (_ & _ & _ & _ & LZ & _). rewrite LZ.
    pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.m16_fields mS1 P b4 b5 b6 b7 b8 b9 x) as (_ & _ & _ & _ & LZ6 & _). rewrite LZ6.
    exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.high_shadow_lazy_mF mS1 a1 a2 SRES SMAPS LS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 p H1 H2). }
  pose proof (Start7.lazy_mE_facts mS1 a1 a2 SRES SMAPS LS STOP P b4 b5 b6 HPL HPL4 b7 b8 b9 x b10 Hx H16) as [WL _].
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.brk_mE mS1 SBRK P b4 b5 b6 b7 b8 b9 x b10 Hx H16 Hxtop) as (B1 & B2 & _).

  assert (HSUB : forall mo, m_vm_lazy mo = maps_subtract (m_vm_lazy mE) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.brk0 mE + 4096) -> HBL mo).
  { intros mo E p H1 H2. rewrite E. apply page_in_ranges_subtract_keep8; [exact WL | lia | exact (HE p H1 H2) | right; lia]. }

  assert (HO : HBL (Start7.out18_model mS1 P b4 b5 b6 b7 b8 b9 x b10 o)).
  { assert (H1c : forall o1, HBL (out1_model mE o1)).
    { intros [| | |a]; cbn [out1_model].
      - apply (HBL_lazy_eq mE); [exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.mg_shape mS1 SBRK P b4 b5 b6 b7 b8 b9 x b10 Hx H16 Hxtop)) | exact HE].
      - apply HSUB. exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.mg_ok_shape mS1 SBRK P b4 b5 b6 b7 b8 b9 x b10 Hx H16 Hxtop)).
      - apply HSUB. exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.mg_dead_shape mS1 SBRK P b4 b5 b6 b7 b8 b9 x b10 Hx H16 Hxtop)).
      - apply (HBL_lazy_eq mE); [|exact HE]. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.mf_exp_shape mS1 P b4 b5 b6 b7 b8 b9 x b10 a) as X. cbv zeta in X. exact (proj2 X). }
    destruct o as [o0|o1|o1 g]; cbn [Start7.out18_model].
    - destruct o0 as [|a]; cbn [out0_model]; [exact HE|].
      apply (HBL_lazy_eq mE); [exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.mf_res_shape mS1 P b4 b5 b6 b7 b8 b9 x b10 a)) | exact HE].
    - exact (H1c o1).
    - apply (HBL_lazy_eq (out1_model mE o1)); [exact (proj2 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.mgrant_shape _ g)) | exact (H1c o1)]. }
  unfold StartTop.Mmain, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m24, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m23a, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22.
  apply HBL_eager. apply HBL_null_rw. apply HBL_eager. exact HO.
Qed.

Theorem ss0_lazy_acc : ltac2:(tb__ "0|5|
SaS20SbS6Q40M0A1M1G1A2S10G1G1Vb13;S8G0Z800000M2A2A4S1S1dS1aVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10M3A1A3S12SaS13S7G0Vb13;A2M4R1A2S15R1S14G4G2A2A2A2S9ScS1eS4S2G3A1A1R2A2SfA3F_;Fz;A2").
Proof.
  pose proof HS as (Sfds & Sfs & Slim & SMI & Stid & Sx & G2 & G3 & HPL & HPL4 & HPL5 & HPL6 & HPL7 & HPL8 & HPL9 & HPL10 & Ho & HPL12 & HPL13 & HPL14 & _).
  pose proof (mS1_facts sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & Sx' & SLIM & SISP).
  pose proof (StartMain.M1_fields sp brk mb draw lim inp tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & _).
  pose proof (StartMain.brk_facts sp brk mb draw inp Hent) as [Hbrk Hbal].
  pose proof (mS_fields m1 Flz Fmaps Fna a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SNA : vm_noaccess (m_vmmaps mS1) = [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)]) by (rewrite NS; reflexivity).
  assert (SBRK : 0x643000 <= bv_unsigned (vm_brk (m_vmmaps mS1)) <= 0x80643000) by (rewrite KS, Fbrk; exact Hbrk).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.minv8_out18 mS1 a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16 Hxtop HPL10
                 (StartTop.apart_S m1 Flz Fres Fmaps Fna ltac:(clear - STOP IS; unfold init_sp_ok in *; rewrite <- IS; exact STOP) a1 a2 G2 G3) o Ho) as MI18.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.MI22 mS1 x Hxtop _ _ MI18 b12 HPL12) as (MI22' & _).
  assert (N8 : mmap_n (Z_to_bv 64 8388608) = Z_to_bv 64 8388608) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  assert (U8 : bv_unsigned (Z_to_bv 64 8388608) = 8388608) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof HPL13 as (A13 & P13 & T13 & F13). rewrite N8 in F13. rewrite (mi_res MI22'), (mi_maps MI22') in F13.
  split.
  - unfold StartTop.Mmain, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m24, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m23a. unfold eager_model at 1. rewrite m_vm_lazy_with_vmmaps.
    unfold null_rw_model. rewrite m_vm_lazy_vm_add_lazy, m_vm_lazy_with_vmmaps. apply in_or_app. left.
    rewrite (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.lazy_interior_lit b13 (Z_to_bv 64 8388608)); [left; reflexivity | exact A13 | rewrite U8; reflexivity | rewrite U8; lia |].
    rewrite U8. pose proof (alloc_top_lt (m_vmmaps (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22 (Start7.out18_model mS1 P b4 b5 b6 b7 b8 b9 x b10 o) b12))) as TL. unfold two_pow_64 in TL.
    assert (NZ : mmap_nZ (Z_to_bv 64 8388608) = 8388608) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite NZ in T13. lia.
  - intros z Hz.
    assert (EN : vm_noaccess (m_vmmaps Mm) = vm_noaccess (m_vmmaps (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m22 (Start7.out18_model mS1 P b4 b5 b6 b7 b8 b9 x b10 o) b12))).
    { unfold StartTop.Mmain, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m24, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.m23a. unfold eager_model at 1. rewrite m_vmmaps_with_vmmaps. unfold eager_h. cbn [vm_noaccess].
      unfold null_rw_model. rewrite m_vmmaps_vm_add_lazy, m_vmmaps_with_vmmaps. unfold null_rw_h. cbn [vm_noaccess]. reflexivity. }
    rewrite EN. apply (minv8_fresh_acc _ _ _ _ _ b13 (Z_to_bv 64 8388608) z MI22' F13). rewrite U8. exact Hz.
Qed.
End Facts.
End InvInitL.

(* [comment removed for export] *)
Module InvInitG.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "list"; "nil"; "fst"; "snd"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvInitP"; "grantZ"; "pairwiseZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "sub"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M"; "ranges_apart"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "FS_total"; "kPtrArrayReserve"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "FBSZ"; "NBSZ"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4"; "n7"; "n9"; "spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6"; "n17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff"; "sheet"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain"; "M1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop"; "Lmain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lp.InvInitG"; "subl"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundI SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvInitP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Placement KxA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartArgBytes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartTop StartMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require og.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.StartBD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartMainFds.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require og.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartHandoff StartHandoffFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartHandoffBlocks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.StartHandoffBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoffFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive subl {T} : list T -> list T -> Prop :=
| subl_nil : forall l, subl [] l
| subl_keep : forall x k l, subl k l -> subl (x :: k) (x :: l)
| subl_skip : forall x k l, subl k l -> subl k (x :: l).
Lemma subl_In : forall {T} (k l : list T), subl k l -> forall x, In x k -> In x l.
Proof. intros T k l H. induction H; intros y Hy; [destruct Hy | destruct Hy as [<-|Hy]; [left; reflexivity | right; apply IHsubl; exact Hy] | right; apply IHsubl; exact Hy]. Qed.
Lemma subl_app : forall {T} (k1 l1 k2 l2 : list T), subl k1 l1 -> subl k2 l2 -> subl (k1 ++ k2) (l1 ++ l2).
Proof.
  intros T k1 l1 k2 l2 H1 H2. induction H1; cbn [app].
  - induction l as [|x l IH]; [exact H2 | apply subl_skip; exact IH].
  - apply subl_keep. exact IHsubl.
  - apply subl_skip. exact IHsubl.
Qed.
Lemma ranges_apart_subl : ltac2:(tb__ "0|3|
S4S3SaQ40A1M0G0A2M1A1M2G2S27G1R2R1A3S15R2A1S15R4A1F_;F_;Fl;Fk;").
Proof.
  intros k l H. induction H; intros R; [exact I | |].
  - cbn in R |- *. destruct R as [F R]. split; [|exact (IHsubl R)].
    apply Forall_forall. intros y Hy. exact (proj1 (Forall_forall _ _) F y (subl_In _ _ H y Hy)).
  - cbn in R. exact (IHsubl (proj2 R)).
Qed.

Section Facts.
Variables (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
S26S1dS1cVsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Variables (tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 : word) (x : Z) (o : out18) (v : bool) (rho4 rho' rho1 rhoM : valuation) (tp : list word) (w : world).
Hypothesis HS : ltac2:(tb__ "0|0|
S23Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vb10;Vb12;Vb13;Vb14;Vx;Vo;Vv;Vrho4;Vrho';Vrho1;VrhoM;Vtp;Vw;A1d").

Local Notation m1 := (StartMain.M1 sp brk mb draw lim inp tid).
Local Notation Mm := (StartTop.Mmain m1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14).
Local Notation Lm := (StartTop.Lmain m1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14).
Local Notation mS1 := (StartTop.mS m1 a1 a2).
Local Notation U := bv_unsigned.
Local Notation TOPZ := (bv_unsigned sp - 8388608).

Definition K8 : list (word * word) := ltac2:(tb__ "0|4|
S2S3SaQ40M0A1M1G1A2M2S1G1G1Vb13;S9G0Z800000A2A4S2G2S1G1G1Vb12;S9G0Z100000A2A4S2G2S1G1G1Vb10;S9G0S22A2A4S2G2S1G1G1Vb8;S9G0Z1000A2M3A4S2G2S1G1G1Vb6;S9G0Z10000A2A4S2G2S1G1G1Vb5;G3A4S2G2S1G1G1Vb4;S20A4S2G2S1G1G1VP;S1fA4S5G2A1A3A3A3A3A3A3A3A3").

Lemma K8_apart : Start8M.ranges_apart K8.
Proof.
  pose proof HS as (_ & _ & _ & SMI & _).
  pose proof (mi_apart SMI) as R.
  rewrite (Lmain_explicit sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) in R.
  refine (ranges_apart_subl K8 _ _ R).
  apply (subl_app [] _ K8). { apply subl_nil. }
  change K8 with ([(b13, Z_to_bv 64 8388608); (b12, Z_to_bv 64 1048576)] ++ ([] ++ ([(b10, Z_to_bv 64 n17); (b8, Z_to_bv 64 4096); (b6, Z_to_bv 64 65536); (b5, Z_to_bv 64 4096); (b4, n9); (P, n7)] ++ []))).
  apply subl_app; [apply subl_skip; apply subl_keep; apply subl_keep; apply subl_nil|].
  apply subl_app; [apply subl_nil|].
  apply subl_app; [|apply subl_nil].
  apply subl_keep. apply subl_keep. apply subl_skip. apply subl_keep. apply subl_keep. apply subl_keep. apply subl_keep. apply subl_nil.
Qed.

Lemma img_avoid : ltac2:(tb__ "0|3|
SaQ40M0A1M1G1S28S3G1G1A2S1G1G1R2R1A4S25S24Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A3S14Z0S8G0R2A2A2SdS10S11S8G0R4A2M2S8G0R3A2A2Z10000A2S10Z643000G2A2A2F_;F_;Fs;Fb;").
Proof.
  intros b s Hin Hs. pose proof HS as (_ & _ & _ & SMI & _). pose proof (mi_apart SMI) as R.
  apply Start8M.ranges_apart_app in R as (_ & _ & X). rewrite StartLib.segments_reserved_A in X.
  pose proof (X _ _ (or_introl eq_refl) Hin) as A1. pose proof (X _ _ (or_intror (or_introl eq_refl)) Hin) as A2.
  pose proof (X _ _ (or_intror (or_intror (or_introl eq_refl))) Hin) as A3. pose proof (X _ _ (or_intror (or_intror (or_intror (or_introl eq_refl)))) Hin) as A4.
  unfold Start8M.apartW in A1, A2, A3, A4. cbn [fst snd] in A1, A2, A3, A4. rewrite !u64_of_lit in A1, A2, A3, A4 by lia. clear - A1 A2 A3 A4 Hs. lia.
Qed.

Lemma pw_of_apart : ltac2:(tb__ "0|3|
S4S3SaQ40M0A1M1G1A2M2A1S15R1A1SfS1bG2S3S0S0A2G2S1S0S0S8G0S6G1G1R1A3A2S8G0S7G1G1R1A3A2A4Le;R2A4A1F_;Fl;").
Proof.
  induction l as [|e l IH]; intros R; [exact I|]. cbn in R |- *. destruct R as [F R]. split; [|exact (IH R)].
  apply Forall_forall. intros y Hy. apply in_map_iff in Hy as (e' & <- & He'). exact (proj1 (Forall_forall _ _) F e' He').
Qed.

Theorem geo_main : ltac2:(tb__ "0|e|
SbSbS10Z7fff7f800000S13S8Q40M0Vsp;A2Z800000A2M1A2S10G1Z7fffff800000A2A2SbSbScS0S12S8G0VP;A2M2S18A2Z0A3SbS10S1eG2A2S10S11G2Z2000011000M3A2G1A2A2A2SbScS0S8G0S21VP;A1A2S13S11G2Z10000M4A2S12G2G4A2A2A3SbSeG1S8G0Vb5;A2M5Z1000M6A3SbSeG1S8G0Vb6;A2M7G4A3SbSeG1S8G0Vb8;A2M8G6A3SbSeG1S8G0Vb10;A2M9S16A3SbSeG1S8G0Vb4;A2MaS17A3SbSeG1S8G0Vb12;A2MbS1aA3SbSeG1S8G0Vb13;A2McS19A3SfS2S3S0S0A2MdS1S0S0GcS19A4S2GdS1S0S0GbS1aA4S2GdS1S0S0G9S16A4S2GdS1S0S0G8G6A4S2GdS1S0S0G7G4A4S2GdS1S0S0G5G6A4S2GdS1S0S0GaS17A4S2GdS1S0S0G2G3A4S5GdA1A3A3A3A3A3A3A3A3A1A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof HS as (Sfds & Sfs & Slim & SMI & Stid & Sx & G2 & G3 & HPL & HPL4 & HPL5 & HPL6 & HPL7 & HPL8 & HPL9 & HPL10 & Ho & HPL12 & HPL13 & HPL14 & _).
  pose proof (mS1_facts sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS)
    as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & Sx' & SLIM & SISP).
  pose proof (grants_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as GM. cbv zeta in GM.
  destruct GM as (Ga1 & Ga2 & GP & GSB & G4 & G5 & G6 & G7 & G8 & G10 & G12 & G13 & G14).
  pose proof (Lmain_explicit sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp w HS) as EL.
  assert (AL : forall (mo : Model) (len a : word), mmap_place_ok_none (Z_to_bv 64 0) mo len a -> U a mod 4096 = 0 /\ 0x1000 <= U a).
  { intros mo len a (H1 & H2 & _). unfold page_size in H1. split; [exact H1|]. pose proof (Z.div_mod (U a) 4096 ltac:(lia)) as D. rewrite H1 in D. lia. }
  assert (INL : forall e, In e ([(b14, Z_to_bv 64 4096); (b13, Z_to_bv 64 8388608); (b12, Z_to_bv 64 1048576)]
                               ++ [(b10, Z_to_bv 64 n17); (b8, Z_to_bv 64 4096); (b7, Z_to_bv 64 4096); (b6, Z_to_bv 64 65536); (b5, Z_to_bv 64 4096); (b4, n9); (P, n7)]) -> In e Lm).
  { intros e He. rewrite EL. apply in_app_or in He as [He|He]; [apply in_or_app; left; exact He|].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact He. }
  assert (IMG : forall b (s : Z), 0 < s < 2 ^ 64 -> In (b, Z_to_bv 64 s) Lm -> U b + s <= IMG_LO \/ IMG_HI <= U b).
  { intros b s Hs Hin. pose proof (img_avoid b (Z_to_bv 64 s) Hin) as X. rewrite u64_of_lit in X by lia. unfold IMG_LO, IMG_HI. apply X. lia. }
  assert (N17 : n17 = FS_total) by reflexivity.
  rewrite Sx' in Hx.
  split; [lia|]. split; [unfold PG; exact GP|]. split; [exact GSB|].
  split. { destruct (AL _ _ _ HPL5) as [A1 A2]. destruct G5 as (_ & B5 & T5). unfold grantZ, PG. split; [exact A1|]. split; [exact A2|]. split; [exact T5|].
           split; [apply (IMG b5 4096); [lia|]; apply INL; cbn [In app]; repeat (first [left; reflexivity | right]) | exact B5]. }
  split. { destruct (AL _ _ _ HPL6) as [A1 A2]. destruct G6 as (_ & B6 & T6). unfold grantZ, PG. split; [exact A1|]. split; [exact A2|]. split; [exact T6|].
           split; [apply (IMG b6 65536); [lia|]; apply INL; cbn [In app]; repeat (first [left; reflexivity | right]) | exact B6]. }
  split. { destruct (AL _ _ _ HPL8) as [A1 A2]. destruct G8 as (_ & B8 & T8). unfold grantZ, PG. split; [exact A1|]. split; [exact A2|]. split; [exact T8|].
           split; [apply (IMG b8 4096); [lia|]; apply INL; cbn [In app]; repeat (first [left; reflexivity | right]) | exact B8]. }
  split. { destruct (AL _ _ _ HPL10) as [A1 A2]. destruct G10 as (_ & B10 & T10). unfold grantZ, PG. rewrite <- N17. split; [exact A1|]. split; [exact A2|]. split; [exact T10|].
           split; [apply (IMG b10 n17); [unfold n17; lia|]; apply INL; cbn [In app]; repeat (first [left; reflexivity | right]) | exact B10]. }
  split. { destruct (AL _ _ _ HPL4) as [A1 A2]. destruct G4 as (_ & B4 & T4). unfold grantZ, PG. change kPtrArrayReserve with 0x800000. split; [exact A1|]. split; [exact A2|]. split; [exact T4|].
           split; [apply (IMG b4 0x800000); [lia|]; apply INL; cbn [In app]; repeat (first [left; reflexivity | right]) | exact B4]. }
  split. { destruct (AL _ _ _ HPL12) as [A1 A2]. destruct G12 as (B12 & T12). unfold grantZ, PG. change NBSZ with 1048576. split; [exact A1|]. split; [exact A2|]. split; [exact T12|].
           split; [apply (IMG b12 1048576); [lia|]; apply INL; cbn [In app]; repeat (first [left; reflexivity | right]) | exact B12]. }
  split. { destruct (AL _ _ _ HPL13) as [A1 A2]. destruct G13 as (B13 & T13). unfold grantZ, PG. change FBSZ with 8388608. split; [exact A1|]. split; [exact A2|]. split; [exact T13|].
           split; [apply (IMG b13 8388608); [lia|]; apply INL; cbn [In app]; repeat (first [left; reflexivity | right]) | exact B13]. }
  pose proof (pw_of_apart K8 K8_apart) as PW. unfold K8 in PW. cbn [map fst snd] in PW. unfold n9, n7 in PW. rewrite !u64_of_lit in PW by (unfold n17; lia).
  exact PW.
Qed.
End Facts.
End InvInitG.

(* [comment removed for export] *)
Module InvInitV0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "bool"; "prod"; "true"; "fst"; "snd"; "nil"; "Some"; "app"; "option"; "negb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "sub"; "to_N"; "mul"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "SAlu"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "acell"; "mkACell"; "ERRNO_A"; "c_addr"; "G0"; "RTC_A"; "c_val"; "c_w"; "rtc_cells_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lp.InvInitV0"; "objsV"; "bkV"; "LIT0"; "LITV"; "PRES0"; "PRESV"; "SYM0"; "SYMV"; "ZEROV"; "f0V"; "geo_addrs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "STORE"; "DEPOT"; "MAP1"; "MAP1N"; "NFBLK"; "TABSZ"; "NIDS"; "NODESMU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "QG"; "IA_BEG"; "IA_END"; "rtc_extra"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitB"; "range_info"; "range_present"; "range_zero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "binfo"; "BImg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.InvInitC"; "lit_cell_is"; "sym_cell_is"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvInitZ"; "zscanN"; "@OSSVerify.tinyobjloader.fuzz_tobj_c.images.AsanUbsan"; "AsanUbsan_seg_bytes_003"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "FS_LOG"; "PG"; "kPtrArrayReserve"; "kQuarantineMin"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundI SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import InvInitB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvInitZ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.InvInitC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvInitZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Placement KxA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartArgBytes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartTop StartMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require og.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.StartBD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartMainFds.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require og.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartHandoff StartHandoffFacts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartHandoffBlocks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.StartHandoffBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoffFacts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition objsV (v : bool) : list sobj := ss_objs (ax_S (MAIN_of v)).

Definition geo_addrs : list Z := ltac2:(tb__ "0|0|
S3S0Zeaa78S3S0Zeaa88S3S0Z1bff98S3S0Z5cffa8S3S0Z621278S3S0Z621280S3S0Z642620SaS0A1A3A3A3A3A3A3A3").
Definition LIT0 : list acell := ltac2:(tb__ "0|6|
ScS1aS3dS1aS1aSeS3cS0S13S1dR1A1A1S2dA3A1Lc;S22S1fS1eA2A3ScS1aS3aS3S1aS1bS36U8M0S49A3S3S1aS1bSfS36Z18M1A2G0S4aA3S3S1aS1bSfS36Z30A2G0Z0M2A3S3S1aS1bSfS36Z38A2G0G2A3S3S1aS1bZead00U4M3G2A3S3S1aS1bSfS37Z98A2G3G2A3S3S1aS1bSfS37Z48A2G0S4bA3S3S1aS1bSfS37Za0A2M4G0G2A3S3S1aS1bSfG4G1A2G0G2A3S3S1aS1bZ17db48U1M5G2A3S3S1aS1bZ17db49G5G2A3S3S1aS1bZ17db4aG5G2A3S3S1aS1bZ17db4bG5G2A3S3S1aS1bS35G3G2A3S3S1aS1bSfS2eZ1cA2G3G2A3SaS1aA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma LIT0_chk : ltac2:(tb__ "0|0|
S5S18S5S3bS1aS1aS44S23R2A1S16Z0A1S1dR1A1S21R1A1S20R1A1A5Lc;S25A3S7A3Fv';").
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Definition SYM0 : list (Z * nat * sv) := ltac2:(tb__ "0|5|
S3S6S6S0S4A2M0S14A2M1S2G0S14S2S0S4Zeaa78U8M2A4S15P1eA1M3A4S3G1S2G0S14S2S0S4Zeaa88G2A4S17S3eG3S16Z2000000000A1A3A4S3G1S2G0S14S2S0S4Z1bff98G2A4S15Pa0A1A4S3G1S2G0S14S2S0S4Z5cffa8G2A4S15P9fA1A4S3G1S2G0S14S2S0S4Z621278G2A4S15P53A1A4S3G1S2G0S14S2S0S4Z621280G2A4S15P4dA1A4S3G1S2G0S14S2S0S4Z642620G2A4S15P22A1A4S3G1S2G0S14S2S0S4SfS36Z8A2G2A4S15P20A1M4A4S3G1S2G0S14S2S0S4SfS36Z10A2G2A4G4A4S3G1S2G0S14S2S0S4S34U4A4S17S3eS16Z0A1S16Z1A1A3A4SaG1A1A3A3A3A3A3A3A3A3A3A3").
Lemma SYM0_chk : ltac2:(tb__ "0|3|
S5S18S5S3bS6S6S0S4A2M0S14A2M1G1S45S23R2A1S16Z0A1S8S0S4S8G0S14R1A3M2A3S9S0S4G2A3S9G0S14R1A3A5Lc;S29A3S7A3Fv';").
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Definition f0V (v : bool) : Z := if v then 2 else 3.
Definition bkV (v : bool) : Z := if v then 6057744 else 5054160.
Lemma DEP_chk : ltac2:(tb__ "0|9|
S5S19S18S5S45S23R1A1M0S16Z0A1M1S2eU8S17S3eG1S16S2cR1A1A1A3A5S7A3S19S18S5S44G0G1S24R1A1M2U4Z1A5S7A3S19S18SdS42A1M3S3fG0G1S2fG2A4SbS42S43A2M4A3S19S18G3S3fG0G1SfG2Z4M5A2SfS2fS12G5S33A2A2A4G4A3S19S18G3S3fG0G1SfS30Z8M6A2SfS30S12G6S31A2A2A4G4A3S19S18G3S3fG0G1SfS2eZ20A2SfSfS2eZ10M7A2M8S12G7S32A2A2A4G4A3S19S18S5S40G0G1SfS2eG6A2G8A4S7A3S18S5S40G0G1SfS2eZ18A2SfS2eZ1cA2A4S7A3A2A2A2A2A2A2A2Fv';").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition LITV : list (positive * Z * nat * Z) := ltac2:(tb__ "0|b|
S3S6S6S6S1S0A2M0S4A2M1S0A2M2S2G1S0S2G0S4S2S1S0P21M3Z28A4U1M4A4Z0M5A4S3G2S2G1S0S2G0S4S2S1S0G3Z30A4U8M6A4Z6219b0A4S3G2S2G1S0S2G0S4S2S1S0G3Z38A4G6A4Z621a8cA4S3G2S2G1S0S2G0S4S2S1S0G3Zc60A4G4A4G5A4S3G2S2G1S0S2G0S4S2S1S0G3Z50M7A4G6A4G5A4S3G2S2G1S0S2G0S4S2S1S0G3SfG7Z18M8A2A4G6A4G5A4S3G2S2G1S0S2G0S4S2S1S0P22Z8A4U4M9A4G5A4S3G2S2G1S0S2G0S4S2S1S0P4dG8A4G6A4Z621278A4S3G2S2G1S0S2G0S4S2S1S0P53MaZ58A4G6A4S48A4S3G2S2G1S0S2G0S4S2S1S0GaZ60A4G4A4G5A4S3G2S2G1S0S2G0S4S2S1S0P9fG8A4G9A4G5A4SaG2A1A3A3A3A3A3A3A3A3A3A3A3").
Lemma LITV_chk : ltac2:(tb__ "0|5|
S5S18S5S3bS6S6S6S1S0A2M0S4A2M1S0A2M2G2S44S23R2A1S15S8S1S0S8G0S4S8G1S0R1A3M3A3M4A3A1S9S1S0G4A3S9G0S4G3A3S9G1S0R1A3A5Lc;S26A3S7A3Fv';").
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Definition SYMV : list (positive * Z * nat * sv) := ltac2:(tb__ "0|7|
S3S6S6S6S1S0A2M0S4A2M1S14A2M2S2G1S14S2G0S4S2S1S0P21M3Z0A4U8M4A4S15P22M5A1A4S3G2S2G1S14S2G0S4S2S1S0G3Z8A4G4A4S15P51A1M6A4S3G2S2G1S14S2G0S4S2S1S0G3Z10A4G4A4S17S3eG6S16N800000A1A3A4S3G2S2G1S14S2G0S4S2S1S0G3Z48A4G4A4S15P53A1A4S3G2S2G1S14S2G0S4S2S1S0G5Z98A4G4A4S15G3A1A4SaG2A1A3A3A3A3A3").
Lemma SYMV_chk : ltac2:(tb__ "0|5|
S5S18S5S3bS6S6S6S1S0A2M0S4A2M1S14A2M2G2S45S23R2A1S15S8S1S0S8G0S4S8G1S14R1A3M3A3M4A3A1S9S1S0G4A3S9G0S4G3A3S9G1S14R1A3A5Lc;S2aA3S7A3Fv';").
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.

Definition ZEROV : list (positive * Z * Z) := ltac2:(tb__ "0|3|
S3S6S6S1S0A2M0S0A2M1S2G0S0S2S1S0P21Zd0A4Za80A4S3G1S2G0S0S2S1S0P53M2Z0A4Z58A4S3G1S2G0S0S2S1S0G2Z1000A4Z9000A4SaG1A1A3A3A3").
Definition PRESV : list (positive * Z * Z) := ltac2:(tb__ "0|4|
S3S6S6S1S0A2M0S0A2M1S2G0S0S2S1S0P21Z0M2A4Z1000M3A4S3G1S2G0S0S2S1S0P53Z9000A4Zb09000A4S3G1S2G0S0S2S1S0P9fG2A4Z100000A4S3G1S2G0S0S2S1S0Pa0G2A4G3A4SaG1A1A3A3A3A3").
Lemma RNGV_chk : ltac2:(tb__ "0|8|
S5S19S18S5S3bS6S6S1S0A2M0S0A2M1G1S41S23R2A1M2S15S8S1S0S8G0S0R1A3M3A3A1M4S9S1S0G3A3M5S9G0S0R1A3M6A4Lc;S2bA3S7A3S19S18S5S3bG1G1S40G2G4G5G6A4Lc;S28A3S7A3S19S18S5S41S23R1A1M7S17S3eS15P1eA1S16Z2000000000A1A3Z0Z1000A4S7A3S18S5S44G7S15P9fA1Z10U8S5S0Lv';R1Z5b9b89030b5fdbdeZbb925aa4f0fc07ceX5x2A5S7A3A2A2A2Fv';").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition PRES0 : list (Z * Z) := ltac2:(tb__ "0|2|
S3S6S0S0A2M0S2S0S0SfS36Z40A2Zead00A4S3G0S2S0S0Zead08Zead30A4S3G0S2S0S0SfSfS37Za0A2M1Z8A2SfG1Z18A2A4S3G0S2S0S0Z170320Z170321A4S3G0S2S0S0S1cSfS1cZ4A2A4SaG0A1A3A3A3A3A3").
Lemma PRES0_chk : ltac2:(tb__ "0|2|
S5S19S18S5S3bS6S0S0A2M0G0S40S23R2A1S16Z0A1M1S8S0S0R1A3S9S0S0R1A3A4Lc;S27A3S7A3S18SdS42A1S3fS23R1A1G1S38S39A4SbS42S43A2A3A2Fv';").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma zscan_tab1 : ltac2:(tb__ "0|0|
S5S18S5S46S47U40S11S10S2fZe6000A2A1S11S10S24R1A1S2fA2A1A4S7A3Fv';").
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma zscan_tab2 : ltac2:(tb__ "0|2|
S5S18S5S46S47U40S11S10SfS24R1A1Z4M0A2M1Ze6000A2A1S11S10SfS2fS12G0S33A2A2G1A2A1A4S7A3Fv';").
Proof. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma zscan_map1 : ltac2:(tb__ "0|1|
S18S5S46S47U40S11S10SfS30Z8M0A2Ze6000A2A1S11S10S12G0S31A2G0A2A1A4S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma zscan_blocks : ltac2:(tb__ "0|1|
S18S5S46S47U40S11S10SfS2eZ20A2Ze6000A2A1S11S10S12Z10M0S32A2G0A2A1A4S7A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

End InvInitV0.

