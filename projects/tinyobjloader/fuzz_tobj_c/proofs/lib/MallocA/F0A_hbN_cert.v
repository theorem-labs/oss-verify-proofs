(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "agree_below"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "app"; "bool"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "keepsM"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "VSXh"; "VS0h"; "hv_T5f"; "VSCh"; "hbfam_ok"; "hbvar_ok"; "hf_LA"; "hf_S0"; "hf_SC"; "hf_lPL"; "hv_AM"; "hv_AU"; "hv_C5"; "hv_E5"; "hv_EM"; "hv_EU"; "hv_EUs"; "hv_LR"; "hv_PT"; "hv_SX"; "hv_XF"; "nx_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states.
Import ListNotations.
Open Scope Z_scope.

Definition VS0h : list positive := ltac2:(tb__ "0|0|
SaS0Pc8SaS0Pc9SaS0Pc3ScS0A1A3A3A3").
Definition VSCh : list positive := ltac2:(tb__ "0|0|
SdS0S15SaS0Pd2SaS0Pd3SaS0Pd4SaS0Pd5SaS0Pc0SaS0Pc1SaS0Pc2SaS0PacScS0A1A3A3A3A3A3A3A3A3A3").
Definition VSXh : list positive := ltac2:(tb__ "0|0|
SdS0S15SaS0PcaSaS0PcbSaS0PccSaS0PcdSaS0PceScS0A1A3A3A3A3A3A3").

Record hbfam : Type := mkHBF { hf_S0 : axst; hf_lPA : list leafA; hf_LA : axst; hf_SC : axst; hf_lPL : list leafA }.
Record hbfam_ok (E : axst) (f : nat) (c : hbfam) : Prop := mkHBFok {
  f_S0 : hf_S0 c = S0_hb E f;
  f_runPA : runA 300 [GBSCAN; GBEXIT] (hf_S0 c) = hf_lPA c;
  f_chkPA : chkNM (ss_next (ax_S (hf_S0 c))) (hf_lPA c) [(hf_LA c, idm VS0h)] = true;
  f_nxS0 : ss_lenient (ax_S (hf_S0 c)) = false /\ (NPRE <=? ss_next (ax_S (hf_S0 c)))%positive = true;
  f_SC : hf_SC c = SC_hb (hf_LA c);
  f_runPL : runA 100 [GBSCAN; GBEXIT] (hf_SC c) = hf_lPL c;
  f_chkPL : chkNM (ss_next (ax_S (hf_SC c))) (hf_lPL c) (map (fun L => (la_state L, idm VSCh)) (hf_lPL c)) = true;
  f_nxSC : ss_lenient (ax_S (hf_SC c)) = false /\ (NPRE <=? ss_next (ax_S (hf_SC c)))%positive = true;
  f_pcsPL : pcs_of (hf_lPL c) = [GBEXIT; GBSCAN; GBEXIT; GBSCAN; GBEXIT; GBSCAN; GBEXIT; GBSCAN]
}.

Record hbvar : Type := mkHBV {
  hv_SX : axst; hv_lPB : list leafA; hv_E5 : axst; hv_C5 : axst; hv_R5 : list sobj; hv_T5 : axst; hv_T5f : axst; hv_lPC : list leafA;
  hv_EUs : axst; hv_EM : axst; hv_EMx : axst; hv_EMd : axst; hv_AM : axst; hv_lPD : list leafA;
  hv_EU : axst; hv_EUx : axst; hv_EUd : axst; hv_DUo : list sobj; hv_AU : axst; hv_lPE : list leafA;
  hv_LR : axst; hv_PT : axst; hv_lPT : list leafA; hv_XF : axst }.
Definition nx_ok (S : axst) : Prop := ltac2:(tb__ "0|1|
S2fS2eSeS4S2aVS;A1M0A1SfA3S2eSeS33S30S2G0A1A2S10A3A2").
Record hbvar_ok (SC : axst) (f : nat) (l : bool) (c : hbvar) : Prop := mkHBVok {
  v_SX : hv_SX c = SX_hb SC f l;
  v_runPB : runA 900 [MSENTS] (hv_SX c) = hv_lPB c;
  v_chkPB : chkNM (ss_next (ax_S (hv_SX c))) (hv_lPB c) [(hv_E5 c, idm VSXh)] = true;
  v_nxSX : nx_ok (hv_SX c);

  v_C5 : hv_C5 c = C5_hb (hv_E5 c);
  v_C5swf : swf (ax_S (hv_C5 c)) = true;
  v_C5diff : state_diff (ax_S (hv_E5 c)) (ax_S (hv_C5 c)) = Some ([(A2OLD, LENS vMS)], []);
  v_C5set : ax_setS (hv_E5 c) (ax_S (hv_C5 c)) = hv_C5 c;
  v_C5next : ss_next (ax_S (hv_C5 c)) = ss_next (ax_S (hv_E5 c));

  v_He5 : entails_frA (hv_C5 c) Pre_memsetA (s5_hb (hv_C5 c)) = Some (hv_R5 c);
  v_Hchk5 : call_checkA (hv_C5 c) Pre_memsetA (s5_hb (hv_C5 c)) (hv_R5 c) (map la_state Posts_memsetA) = true;
  v_T5 : import_postA (s5_hb (hv_C5 c)) Pre_memsetA (liftA (P_ret_memset memset_entryA)) (hv_C5 c) (hv_R5 c) = hv_T5 c;
  v_T5f : ax_with_facts (hv_T5 c) (ss_facts (ax_S (hv_C5 c))) = hv_T5f c;
  v_FBC5 : forallb (sprop_below (ss_next (ax_S (hv_C5 c)))) (ss_facts (ax_S (hv_C5 c))) = true;
  v_FBT5 : forallb (sprop_below (ss_next (ax_S (hv_T5 c)))) (ss_facts (ax_S (hv_C5 c))) = true;
  v_NXC5 : (NPRE <=? ss_next (ax_S (hv_C5 c)))%positive = true;

  v_runPC : runA 900 [] (hv_T5f c) = hv_lPC c;
  v_chkPC : chkNM (ss_next (ax_S (hv_T5f c))) (hv_lPC c) [(hv_EUs c, idm VSXh); (hv_EM c, idm VSXh)] = true;
  v_nxT5f : nx_ok (hv_T5f c);
  v_EUsfact : existsb (sprop_eqb (SPBranch BC_GEU EBEG EEND)) (ss_facts (ax_S (hv_EUs c))) = true;

  v_EMx : apply_axforms (hv_EM c) [AXSelect (sel_last (hv_EM c) [O_csh vH vMS])] = Some (hv_EMx c);
  v_EMxobjs : ss_objs (ax_S (hv_EMx c)) = ss_objs (ax_S (hv_EMd c)) ++ [O_csh vH vMS];
  v_EMdset : ax_setS (hv_EMx c) (set_objs (ax_S (hv_EMx c)) (ss_objs (ax_S (hv_EMd c)))) = hv_EMd c;
  v_EMdnode : instr_at segsA (ss_pc (ax_S (hv_EMd c))) = Some Ecall /\ reg_sv (ax_S (hv_EMd c)) 17 = SLit 233
              /\ reg_sv (ax_S (hv_EMd c)) 10 = EBEG /\ reg_sv (ax_S (hv_EMd c)) 11 = ELEN /\ reg_sv (ax_S (hv_EMd c)) 12 = SLit 4
              /\ ax_X (hv_EMd c) = [] /\ (NPRE <=? ss_next (ax_S (hv_EMd c)))%positive = true;
  v_AM : A_after (hv_EMd c) (SLit 0) = hv_AM c;

  v_runPD : runA 900 [] (hv_AM c) = hv_lPD c;
  v_chkPD : chkNM (ss_next (ax_S (hv_AM c))) (hv_lPD c) [(hv_EU c, idm VSXh)] = true;
  v_nxAM : nx_ok (hv_AM c);

  v_EUx : apply_axforms (hv_EU c) [AXSelect (sel_last (hv_EU c) (D_U_hb l))] = Some (hv_EUx c);
  v_EUxobjs : ss_objs (ax_S (hv_EUx c)) = ss_objs (ax_S (hv_EUd c)) ++ hv_DUo c;
  v_DUorng : forallb (fun o => existsb (same_rng o) (D_U_hb l)) (hv_DUo c) && (length (hv_DUo c) =? length (D_U_hb l))%nat = true;
  v_EUdset : ax_setS (hv_EUx c) (set_objs (ax_S (hv_EUx c)) (ss_objs (ax_S (hv_EUd c)))) = hv_EUd c;
  v_EUdnode : instr_at segsA (ss_pc (ax_S (hv_EUd c))) = Some Ecall /\ reg_sv (ax_S (hv_EUd c)) 17 = SLit 215
              /\ reg_sv (ax_S (hv_EUd c)) 10 = vH /\ reg_sv (ax_S (hv_EUd c)) 11 = vMS
              /\ ax_X (hv_EUd c) = [] /\ (NPRE <=? ss_next (ax_S (hv_EUd c)))%positive = true;
  v_AU : A_after (hv_EUd c) (SLit 0) = hv_AU c;

  v_runPE : runA 900 [RET_PUT] (hv_AU c) = hv_lPE c;
  v_chkPE : chkNM (ss_next (ax_S (hv_AU c))) (hv_lPE c) [(hv_LR c, idm VSXh)] = true;
  v_nxAU : nx_ok (hv_AU c);
  v_PT : hv_PT c = PT_hb (hv_LR c);
  v_runPT : runA FUELF [DRNE; RETF] (hv_PT c) = hv_lPT c;
  v_chkPT : chkNM (ss_next (ax_S (hv_PT c))) (hv_lPT c) [(hv_XF c, idm VSXh)] = true;
  v_nxPT : nx_ok (hv_PT c)
}.

Section TR.
Context {Q : assn} (X : trk Q).
Lemma nx_le : ltac2:(tb__ "0|0|
S2cS29R1A1S32S30S2S2aR2A1A1A2F_;FS;"). Proof. intros S [_ H]. apply Pos.leb_le. exact H. Qed.
Section Fam.
Variables (E : axst) (f : nat) (c : hbfam).
Hypothesis OK : ltac2:(tb__ "0|0|
S18VE;Vf;Vc;A3").
Theorem seg_PA : ltac2:(tb__ "0|0|
S6S1SbS12Q40A1A1S9VQ;VX;R3A3S1S11S13S15A1R4R1A3S8VQ;VX;S5S7R6S1aVc;A1R2R4A5A3F_;Frho';S8VQ;VX;S5S7R5S1bVc;A1R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HJ HC.
  apply (tr_piece X 300%nat _ (hf_S0 c) (hf_lPA c) _ (f_runPA E f c OK) (f_chkPA E f c OK) (proj1 (f_nxS0 E f c OK)) (nx_le _ (f_nxS0 E f c OK)) J rho tp HJ).
  intros T M rho' HIN HK. destruct HIN as [Eq|[]]. injection Eq as <- <-. exact (HC rho' HK).
Qed.
Theorem seg_PL : ltac2:(tb__ "0|0|
S6S1SbS12Q40A1A1S9VQ;VX;R3A3S2bS1S31S2bR2S1dVc;A1A3S11S13S17A1R6R2A3S8VQ;VX;S5S7R8S2dR4A1R3R6A5A3F_;F_;Frho';FL;S8VQ;VX;S5S7R5S1cVc;A1R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HJ HC.
  apply (tr_piece X 100%nat _ (hf_SC c) (hf_lPL c) _ (f_runPL E f c OK) (f_chkPL E f c OK) (proj1 (f_nxSC E f c OK)) (nx_le _ (f_nxSC E f c OK)) J rho tp HJ).
  intros T M rho' HIN HK. apply in_map_iff in HIN as (L & Eq & HL). injection Eq as <- <-. exact (HC L rho' HL HK).
Qed.
End Fam.
Section Var.
Variables (SC : axst) (f : nat) (l : bool) (c : hbvar).
Hypothesis OK : ltac2:(tb__ "0|0|
S19VSC;Vf;Vl;Vc;A4").
Theorem seg_PB : ltac2:(tb__ "0|0|
S6S1SbS12Q40A1A1S9VQ;VX;R3A3S1S11S13S14A1R4R1A3S8VQ;VX;S5S7R6S21Vc;A1R2R4A5A3F_;Frho';S8VQ;VX;S5S7R5S27Vc;A1R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HJ HC.
  apply (tr_piece X 900%nat _ (hv_SX c) (hv_lPB c) _ (v_runPB SC f l c OK) (v_chkPB SC f l c OK) (proj1 (v_nxSX SC f l c OK)) (nx_le _ (v_nxSX SC f l c OK)) J rho tp HJ).
  intros T M rho' HIN HK. destruct HIN as [Eq|[]]. injection Eq as <- <-. exact (HC rho' HK).
Qed.

Theorem seg_memset : ltac2:(tb__ "0|1|
S6S1SbS12Q40A1A1S9VQ;VX;R3A3S1S3S2S2aS20Vc;A1M0A1A1R4R1A3S8VQ;VX;S5S7R6S16Vc;A1R2R4A5A3F_;Frho';S8VQ;VX;S5S7R5G0R4R3A5A3F_;F_;Ftp;FrhoE;FJ;").
Proof.
  intros J rhoE tp HJ HC.
  apply (tr_call X (hv_C5 c) Pre_memsetA Posts_memsetA (s5_hb (hv_C5 c)) (hv_R5 c) (hv_T5 c)
           (fun ok Jx rho tp0 Hok Hst => memset_sumA ok Jx rho tp0 Hok Hst) (fun Jx rho tp0 Hst => memset_sumA_ex Jx rho tp0 Hst)
           (v_He5 SC f l c OK) (v_Hchk5 SC f l c OK)); [| exact (v_FBC5 SC f l c OK) | exact (v_FBT5 SC f l c OK) | apply Pos.leb_le; exact (v_NXC5 SC f l c OK) | exact HJ |].
  - intros P [<-|[]]. exact (v_T5 SC f l c OK).
  - intros rho' Hag. rewrite (v_T5f SC f l c OK). exact (HC rho' Hag).
Qed.
Theorem seg_PC : ltac2:(tb__ "0|1|
S6S1SbS12Q40A1A1S9VQ;VX;R3A3S1S11S13S14A1M0R4R1A3S8VQ;VX;S5S7R6S24Vc;A1R2R4A5A3F_;Frho';S1S11G0R5R1A3S8VQ;VX;S5S7R7S22Vc;A1R2R5A5A3F_;Frho';S8VQ;VX;S5S7R6S16Vc;A1R5R4A5A3F_;F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HJ HC1 HC2.
  apply (tr_piece X 900%nat _ (hv_T5f c) (hv_lPC c) _ (v_runPC SC f l c OK) (v_chkPC SC f l c OK) (proj1 (v_nxT5f SC f l c OK)) (nx_le _ (v_nxT5f SC f l c OK)) J rho tp HJ).
  intros T M rho' HIN HK. destruct HIN as [Eq|[Eq|[]]]; injection Eq as <- <-; [exact (HC1 rho' HK) | exact (HC2 rho' HK)].
Qed.
Theorem seg_PD : ltac2:(tb__ "0|0|
S6S1SbS12Q40A1A1S9VQ;VX;R3A3S1S11S13S14A1R4R1A3S8VQ;VX;S5S7R6S23Vc;A1R2R4A5A3F_;Frho';S8VQ;VX;S5S7R5S1eVc;A1R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HJ HC.
  apply (tr_piece X 900%nat _ (hv_AM c) (hv_lPD c) _ (v_runPD SC f l c OK) (v_chkPD SC f l c OK) (proj1 (v_nxAM SC f l c OK)) (nx_le _ (v_nxAM SC f l c OK)) J rho tp HJ).
  intros T M rho' HIN HK. destruct HIN as [Eq|[]]. injection Eq as <- <-. exact (HC rho' HK).
Qed.
Theorem seg_PE : ltac2:(tb__ "0|0|
S6S1SbS12Q40A1A1S9VQ;VX;R3A3S1S11S13S14A1R4R1A3S8VQ;VX;S5S7R6S25Vc;A1R2R4A5A3F_;Frho';S8VQ;VX;S5S7R5S1fVc;A1R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HJ HC.
  apply (tr_piece X 900%nat _ (hv_AU c) (hv_lPE c) _ (v_runPE SC f l c OK) (v_chkPE SC f l c OK) (proj1 (v_nxAU SC f l c OK)) (nx_le _ (v_nxAU SC f l c OK)) J rho tp HJ).
  intros T M rho' HIN HK. destruct HIN as [Eq|[]]. injection Eq as <- <-. exact (HC rho' HK).
Qed.
Theorem seg_PT : ltac2:(tb__ "0|0|
S6S1SbS12Q40A1A1S9VQ;VX;R3A3S1S11S13S14A1R4R1A3S8VQ;VX;S5S7R6S28Vc;A1R2R4A5A3F_;Frho';S8VQ;VX;S5S7R5S26Vc;A1R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HJ HC.
  apply (tr_piece X FUELF _ (hv_PT c) (hv_lPT c) _ (v_runPT SC f l c OK) (v_chkPT SC f l c OK) (proj1 (v_nxPT SC f l c OK)) (nx_le _ (v_nxPT SC f l c OK)) J rho tp HJ).
  intros T M rho' HIN HK. destruct HIN as [Eq|[]]. injection Eq as <- <-. exact (HC rho' HK).
Qed.
End Var.
End TR.
