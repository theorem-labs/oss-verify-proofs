(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3 j5 i8.

(* [comment removed for export] *)
Module F0T_iLTBf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_lenient"; "ss_next"; "rw"; "SVar"; "ss_objs"; "sv_below"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iLTBf.ILTBf"; "contF"; "econtF"; "side_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "depot_onlyKf"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf"; "ED_LTBf"; "Ebg_LTBf"; "Edr_LTBf"; "LT_LTBf"; "P0_LTBf"; "S1c_LTBf"; "TD_LTBf"; "Xf_LTBf"; "l1_LTBf"; "EX_LTBf"; "LH0_LTBf"; "l2_LTBf"; "l3_LTBf"; "l4_LTBf"; "l1okb_LTBf"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "objs_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "pFR"; "LOOPH"; "atpc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma chk_split_LTBf : ltac2:(tb__ "0|9|
S0S0S2S1SeS13A1M0S3bS11S13A1M1A3A1S0S2S1G0S3eG1A3A1S0S2S1G0S3fG1A3A1S2S1G0S40G1A3A1A2A2A2S0S1ScS41S3bA1SdA3S0S1ScS4fS10S13S4aS49S3bA2A2U1A2SdA3S0S1ScS43S13S13S12S32S15R1A1M2S36A2S32G2S3cA2A2LL;S3eA3SdA3S0S1ScSbS14S4eS36S8S48A1M3A2A1A1SdA3S0S1ScSaS6S14S36A1M4A1M5G3A2SdA3S0S1ScS43S13S4dS36S3cS48A3S3fA3SdA3S0S1ScS43S13S13S32G2S38A2LL;S40A3SdA3S0S0S42S2cS6S14S37A1M6A1A2S0S42S2cS6S14S3dA1M7A1A2S0S42S2cG5A2S42S2cS6S14S3cA1M8A1A2A2A2A2S0S1ScS5G6A1SfA3S0S1ScS5G7A1SfA3S0S1ScS5G4A1SfA3S1ScS5G8A1SfA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chk_LTBf as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1ok_LTBf : ltac2:(tb__ "0|1|
S13S44S13R1S3bA3S3S1S16S15R2A1M0S3dA3S1ScS32G0S38A2SdA3A2F_;FL;").
Proof.
  destruct chk_split_LTBf as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_LTBf)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- LH0eq_LTBf. destruct (atpc LOOPH l1_LTBf) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ILTBf.
Let segs : list Segment := segsA.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S31U0S24Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S2aVsegs;Vok;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S29Vsegs;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Definition side_pure (A : AA) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S0S47Vrho1;S19Q40M0S7Vrho1;PaA2A2S9S14S37A1A1A3S0S1S17G0A1S7Vrho1;P99A2S18G0S22S21VA;A1M1A1M2A2A3S0S4bZ1G2A2S4bG2S4cS23G1A1A1A2A2A2A2").

Theorem spine_s1c_LTBf : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S2eU0S24RbRaR9R8R6S33S39R4AaS1dRcRbRaR9R7S34R5A7S1dRdRcRbRaR8S35R6A7S1dReRdRcRbR9S3aR7A7S4S2aVsegs;RfS1aVsegs;VJFi;SdReRdRbA4S38R1RaA5R9A4FrhoE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_LTBf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_LTBf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat UStopLe false Eps_LTBf C3_LTBf Ems_LTBf C4_LTBf TM0_LTBf run4_LTBf RM_LTBf D3_LTBf W3_LTBf EQ3_LTBf NX3b_LTBf RUN4_LTBf L4_LTBf D4_LTBf W4_LTBf EQ4_LTBf
             HeM_LTBf HchkM_LTBf HTM_LTBf FBM_LTBf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LTBf.
    apply (f0_s5 0%nat UStopLe q_LTBf false TM_LTBf Eq_LTBf EQ_LTBf TQ0_LTBf run5_LTBf RQ_LTBf NX5_LTBf RUN5_LTBf L5_LTBf AXQ_LTBf HeQ_LTBf HchkQ_LTBf HTQ_LTBf FBQ_LTBf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_LTBf.
    apply (f0_s6 0%nat UStopLe false TQ_LTBf Edr_LTBf Xf_LTBf run6_LTBf NX6_LTBf RUN6_LTBf L6_LTBf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s2 0%nat UStopLe true S1c_LTBf C2_LTBf EfD_LTBf ED_LTBf run2_LTBf D2_LTBf W2_LTBf NX2_LTBf EQ2_LTBf RUN2_LTBf L2_LTBf AXD_LTBf
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0%nat UStopLe false TD_LTBf TDr_LTBf CD_LTBf Eps_LTBf Ebg_LTBf run3_LTBf AXDr_LTBf ENTD_LTBf RUN3_LTBf L3_LTBf NX3_LTBf
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_LTBf : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S1fR9R6A2S2eU0S24RcRbRaR9R7S33S39R5AaS1dRdRcRbRaR8S34R6A7S1dReRdRcRbR9S35R7A7S1dRfReRdRcRaS3aR8A7S4S2aVsegs;R10S1aVsegs;S46RfReRcA3S37R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_LTBf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTBf LH0_LTBf LT_LTBf EX_LTBf S1c_LTBf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTBf l2_LTBf l3_LTBf l4_LTBf HNX HLEN
           (runT_some _ _ _ _ RUN1_LTBf NE1) L1ok_LTBf (runT_some _ _ _ _ RUN2f_LTBf NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_LTBf NE3) H3 (runT_some _ _ _ _ RUN4f_LTBf NE4) H4
           (hside_of A Kc rho1 P0_LTBf LT_LTBf tp SIDE_LTBf OBND_LTBf HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_s1c_LTBf keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF rhoE).
Qed.

Theorem espine_s1c_LTBf : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S2fU0S24R9R8R7R5S33S39R3A9S1eRaR9R8R6S34R4A6S1eRbRaR9R7S35R5A6S1eRcRbRaR8S3aR6A6S4S29Vsegs;S1aVsegs;VJFi;SdRdRcRaA4S38R1R9A5R8A3FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_LTBf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_LTBf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat UStopLe false Eps_LTBf C3_LTBf Ems_LTBf C4_LTBf TM0_LTBf run4_LTBf RM_LTBf D3_LTBf W3_LTBf EQ3_LTBf NX3b_LTBf RUN4_LTBf L4_LTBf D4_LTBf W4_LTBf EQ4_LTBf
             HeM_LTBf HchkM_LTBf HTM_LTBf FBM_LTBf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LTBf.
    apply (ef0_s5 0%nat UStopLe q_LTBf false TM_LTBf Eq_LTBf EQ_LTBf TQ0_LTBf run5_LTBf RQ_LTBf NX5_LTBf RUN5_LTBf L5_LTBf AXQ_LTBf HeQ_LTBf HchkQ_LTBf HTQ_LTBf FBQ_LTBf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_LTBf.
    apply (ef0_s6 0%nat UStopLe false TQ_LTBf Edr_LTBf Xf_LTBf run6_LTBf NX6_LTBf RUN6_LTBf L6_LTBf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s2 0%nat UStopLe true S1c_LTBf C2_LTBf EfD_LTBf ED_LTBf run2_LTBf D2_LTBf W2_LTBf NX2_LTBf EQ2_LTBf RUN2_LTBf L2_LTBf AXD_LTBf
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0%nat UStopLe false TD_LTBf TDr_LTBf CD_LTBf Eps_LTBf Ebg_LTBf run3_LTBf AXDr_LTBf ENTD_LTBf RUN3_LTBf L3_LTBf NX3_LTBf
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_LTBf : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S1fR8R5A2S2fU0S24RaR9R8R6S33S39R4A9S1eRbRaR9R7S34R5A6S1eRcRbRaR8S35R6A6S1eRdRcRbR9S3aR7A6S4S29Vsegs;S1aVsegs;S46ReRdRbA3S37R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_LTBf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTBf LH0_LTBf LT_LTBf EX_LTBf S1c_LTBf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTBf l2_LTBf l3_LTBf l4_LTBf HNX HLEN
           (runT_some _ _ _ _ RUN1_LTBf NE1) L1ok_LTBf (runT_some _ _ _ _ RUN2f_LTBf NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_LTBf NE3) H3 (runT_some _ _ _ _ RUN4f_LTBf NE4) H4
           (hside_of A Kc rho1 P0_LTBf LT_LTBf tp SIDE_LTBf OBND_LTBf HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_s1c_LTBf keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF rhoE).
Qed.
End ILTBf.
End F0T_iLTBf.

(* [comment removed for export] *)
Module F0T_iTA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_lenient"; "ss_next"; "rw"; "SVar"; "ss_objs"; "sv_below"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTA.ITA"; "contF"; "econtF"; "side_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "depot_onlyKf"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA"; "ED_TA"; "Ebg_TA"; "Edr_TA"; "LT_TA"; "P0_TA"; "S1c_TA"; "TD_TA"; "Xf_TA"; "l1_TA"; "EX_TA"; "LH0_TA"; "l2_TA"; "l3_TA"; "l4_TA"; "l1okb_TA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "objs_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "pFR"; "LOOPH"; "atpc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma chk_split_TA : ltac2:(tb__ "0|9|
S0S0S2S1SeS13A1M0S3bS11S13A1M1A3A1S0S2S1G0S3eG1A3A1S0S2S1G0S3fG1A3A1S2S1G0S40G1A3A1A2A2A2S0S1ScS41S3bA1SdA3S0S1ScS4fS10S13S4aS49S3bA2A2U1A2SdA3S0S1ScS43S13S13S12S32S15R1A1M2S36A2S32G2S3cA2A2LL;S3eA3SdA3S0S1ScSbS14S4eS36S8S48A1M3A2A1A1SdA3S0S1ScSaS6S14S36A1M4A1M5G3A2SdA3S0S1ScS43S13S4dS36S3cS48A3S3fA3SdA3S0S1ScS43S13S13S32G2S38A2LL;S40A3SdA3S0S0S42S2cS6S14S37A1M6A1A2S0S42S2cS6S14S3dA1M7A1A2S0S42S2cG5A2S42S2cS6S14S3cA1M8A1A2A2A2A2S0S1ScS5G6A1SfA3S0S1ScS5G7A1SfA3S0S1ScS5G4A1SfA3S1ScS5G8A1SfA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chk_TA as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1ok_TA : ltac2:(tb__ "0|1|
S13S44S13R1S3bA3S3S1S16S15R2A1M0S3dA3S1ScS32G0S38A2SdA3A2F_;FL;").
Proof.
  destruct chk_split_TA as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_TA)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- LH0eq_TA. destruct (atpc LOOPH l1_TA) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ITA.
Let segs : list Segment := segsA.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S31U0S24Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S2aVsegs;Vok;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S29Vsegs;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Definition side_pure (A : AA) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S0S47Vrho1;S19Q40M0S7Vrho1;PaA2A2S9S14S37A1A1A3S0S1S17G0A1S7Vrho1;P99A2S18G0S22S21VA;A1M1A1M2A2A3S0S4bZ1G2A2S4bG2S4cS23G1A1A1A2A2A2A2").

Theorem spine_s1c_TA : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S2eU0S24RbRaR9R8R6S33S39R4AaS1dRcRbRaR9R7S34R5A7S1dRdRcRbRaR8S35R6A7S1dReRdRcRbR9S3aR7A7S4S2aVsegs;RfS1aVsegs;VJFi;SdReRdRbA4S38R1RaA5R9A4FrhoE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_TA rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_TA rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat UStopLe false Eps_TA C3_TA Ems_TA C4_TA TM0_TA run4_TA RM_TA D3_TA W3_TA EQ3_TA NX3b_TA RUN4_TA L4_TA D4_TA W4_TA EQ4_TA
             HeM_TA HchkM_TA HTM_TA FBM_TA ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_TA.
    apply (f0_s5 0%nat UStopLe q_TA false TM_TA Eq_TA EQ_TA TQ0_TA run5_TA RQ_TA NX5_TA RUN5_TA L5_TA AXQ_TA HeQ_TA HchkQ_TA HTQ_TA FBQ_TA
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_TA.
    apply (f0_s6 0%nat UStopLe false TQ_TA Edr_TA Xf_TA run6_TA NX6_TA RUN6_TA L6_TA ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s2 0%nat UStopLe true S1c_TA C2_TA EfD_TA ED_TA run2_TA D2_TA W2_TA NX2_TA EQ2_TA RUN2_TA L2_TA AXD_TA
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0%nat UStopLe false TD_TA TDr_TA CD_TA Eps_TA Ebg_TA run3_TA AXDr_TA ENTD_TA RUN3_TA L3_TA NX3_TA
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_TA : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S1fR9R6A2S2eU0S24RcRbRaR9R7S33S39R5AaS1dRdRcRbRaR8S34R6A7S1dReRdRcRbR9S35R7A7S1dRfReRdRcRaS3aR8A7S4S2aVsegs;R10S1aVsegs;S46RfReRcA3S37R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_TA as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TA LH0_TA LT_TA EX_TA S1c_TA pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TA l2_TA l3_TA l4_TA HNX HLEN
           (runT_some _ _ _ _ RUN1_TA NE1) L1ok_TA (runT_some _ _ _ _ RUN2f_TA NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_TA NE3) H3 (runT_some _ _ _ _ RUN4f_TA NE4) H4
           (hside_of A Kc rho1 P0_TA LT_TA tp SIDE_TA OBND_TA HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_s1c_TA keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF rhoE).
Qed.

Theorem espine_s1c_TA : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S2fU0S24R9R8R7R5S33S39R3A9S1eRaR9R8R6S34R4A6S1eRbRaR9R7S35R5A6S1eRcRbRaR8S3aR6A6S4S29Vsegs;S1aVsegs;VJFi;SdRdRcRaA4S38R1R9A5R8A3FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_TA rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_TA rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat UStopLe false Eps_TA C3_TA Ems_TA C4_TA TM0_TA run4_TA RM_TA D3_TA W3_TA EQ3_TA NX3b_TA RUN4_TA L4_TA D4_TA W4_TA EQ4_TA
             HeM_TA HchkM_TA HTM_TA FBM_TA A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_TA.
    apply (ef0_s5 0%nat UStopLe q_TA false TM_TA Eq_TA EQ_TA TQ0_TA run5_TA RQ_TA NX5_TA RUN5_TA L5_TA AXQ_TA HeQ_TA HchkQ_TA HTQ_TA FBQ_TA
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_TA.
    apply (ef0_s6 0%nat UStopLe false TQ_TA Edr_TA Xf_TA run6_TA NX6_TA RUN6_TA L6_TA A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s2 0%nat UStopLe true S1c_TA C2_TA EfD_TA ED_TA run2_TA D2_TA W2_TA NX2_TA EQ2_TA RUN2_TA L2_TA AXD_TA
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0%nat UStopLe false TD_TA TDr_TA CD_TA Eps_TA Ebg_TA run3_TA AXDr_TA ENTD_TA RUN3_TA L3_TA NX3_TA
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_TA : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S1fR8R5A2S2fU0S24RaR9R8R6S33S39R4A9S1eRbRaR9R7S34R5A6S1eRcRbRaR8S35R6A6S1eRdRcRbR9S3aR7A6S4S29Vsegs;S1aVsegs;S46ReRdRbA3S37R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_TA as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TA LH0_TA LT_TA EX_TA S1c_TA pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TA l2_TA l3_TA l4_TA HNX HLEN
           (runT_some _ _ _ _ RUN1_TA NE1) L1ok_TA (runT_some _ _ _ _ RUN2f_TA NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_TA NE3) H3 (runT_some _ _ _ _ RUN4f_TA NE4) H4
           (hside_of A Kc rho1 P0_TA LT_TA tp SIDE_TA OBND_TA HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_s1c_TA keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF rhoE).
Qed.
End ITA.
End F0T_iTA.

(* [comment removed for export] *)
Module F0T_iTBe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_lenient"; "ss_next"; "rw"; "SVar"; "ss_objs"; "sv_below"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTBe.ITBe"; "contF"; "econtF"; "side_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "depot_onlyKf"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe"; "ED_TBe"; "Ebg_TBe"; "Edr_TBe"; "LT_TBe"; "P0_TBe"; "S1c_TBe"; "TD_TBe"; "Xf_TBe"; "l1_TBe"; "EX_TBe"; "LH0_TBe"; "l2_TBe"; "l3_TBe"; "l4_TBe"; "l1okb_TBe"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "objs_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "pFR"; "LOOPH"; "atpc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma chk_split_TBe : ltac2:(tb__ "0|9|
S0S0S2S1SeS13A1M0S3bS11S13A1M1A3A1S0S2S1G0S3eG1A3A1S0S2S1G0S3fG1A3A1S2S1G0S40G1A3A1A2A2A2S0S1ScS41S3bA1SdA3S0S1ScS4fS10S13S4aS49S3bA2A2U1A2SdA3S0S1ScS43S13S13S12S32S15R1A1M2S36A2S32G2S3cA2A2LL;S3eA3SdA3S0S1ScSbS14S4eS36S8S48A1M3A2A1A1SdA3S0S1ScSaS6S14S36A1M4A1M5G3A2SdA3S0S1ScS43S13S4dS36S3cS48A3S3fA3SdA3S0S1ScS43S13S13S32G2S38A2LL;S40A3SdA3S0S0S42S2cS6S14S37A1M6A1A2S0S42S2cS6S14S3dA1M7A1A2S0S42S2cG5A2S42S2cS6S14S3cA1M8A1A2A2A2A2S0S1ScS5G6A1SfA3S0S1ScS5G7A1SfA3S0S1ScS5G4A1SfA3S1ScS5G8A1SfA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chk_TBe as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1ok_TBe : ltac2:(tb__ "0|1|
S13S44S13R1S3bA3S3S1S16S15R2A1M0S3dA3S1ScS32G0S38A2SdA3A2F_;FL;").
Proof.
  destruct chk_split_TBe as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_TBe)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- LH0eq_TBe. destruct (atpc LOOPH l1_TBe) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ITBe.
Let segs : list Segment := segsA.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S31U0S24Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S2aVsegs;Vok;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S29Vsegs;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Definition side_pure (A : AA) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S0S47Vrho1;S19Q40M0S7Vrho1;PaA2A2S9S14S37A1A1A3S0S1S17G0A1S7Vrho1;P99A2S18G0S22S21VA;A1M1A1M2A2A3S0S4bZ1G2A2S4bG2S4cS23G1A1A1A2A2A2A2").

Theorem spine_s1c_TBe : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S2eU0S24RbRaR9R8R6S33S39R4AaS1dRcRbRaR9R7S34R5A7S1dRdRcRbRaR8S35R6A7S1dReRdRcRbR9S3aR7A7S4S2aVsegs;RfS1aVsegs;VJFi;SdReRdRbA4S38R1RaA5R9A4FrhoE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_TBe rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_TBe rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat UStopLe false Eps_TBe C3_TBe Ems_TBe C4_TBe TM0_TBe run4_TBe RM_TBe D3_TBe W3_TBe EQ3_TBe NX3b_TBe RUN4_TBe L4_TBe D4_TBe W4_TBe EQ4_TBe
             HeM_TBe HchkM_TBe HTM_TBe FBM_TBe ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_TBe.
    apply (f0_s5 0%nat UStopLe q_TBe false TM_TBe Eq_TBe EQ_TBe TQ0_TBe run5_TBe RQ_TBe NX5_TBe RUN5_TBe L5_TBe AXQ_TBe HeQ_TBe HchkQ_TBe HTQ_TBe FBQ_TBe
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_TBe.
    apply (f0_s6 0%nat UStopLe false TQ_TBe Edr_TBe Xf_TBe run6_TBe NX6_TBe RUN6_TBe L6_TBe ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s2 0%nat UStopLe true S1c_TBe C2_TBe EfD_TBe ED_TBe run2_TBe D2_TBe W2_TBe NX2_TBe EQ2_TBe RUN2_TBe L2_TBe AXD_TBe
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0%nat UStopLe false TD_TBe TDr_TBe CD_TBe Eps_TBe Ebg_TBe run3_TBe AXDr_TBe ENTD_TBe RUN3_TBe L3_TBe NX3_TBe
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_TBe : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S1fR9R6A2S2eU0S24RcRbRaR9R7S33S39R5AaS1dRdRcRbRaR8S34R6A7S1dReRdRcRbR9S35R7A7S1dRfReRdRcRaS3aR8A7S4S2aVsegs;R10S1aVsegs;S46RfReRcA3S37R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_TBe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TBe LH0_TBe LT_TBe EX_TBe S1c_TBe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TBe l2_TBe l3_TBe l4_TBe HNX HLEN
           (runT_some _ _ _ _ RUN1_TBe NE1) L1ok_TBe (runT_some _ _ _ _ RUN2f_TBe NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_TBe NE3) H3 (runT_some _ _ _ _ RUN4f_TBe NE4) H4
           (hside_of A Kc rho1 P0_TBe LT_TBe tp SIDE_TBe OBND_TBe HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_s1c_TBe keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF rhoE).
Qed.

Theorem espine_s1c_TBe : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S2fU0S24R9R8R7R5S33S39R3A9S1eRaR9R8R6S34R4A6S1eRbRaR9R7S35R5A6S1eRcRbRaR8S3aR6A6S4S29Vsegs;S1aVsegs;VJFi;SdRdRcRaA4S38R1R9A5R8A3FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_TBe rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_TBe rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat UStopLe false Eps_TBe C3_TBe Ems_TBe C4_TBe TM0_TBe run4_TBe RM_TBe D3_TBe W3_TBe EQ3_TBe NX3b_TBe RUN4_TBe L4_TBe D4_TBe W4_TBe EQ4_TBe
             HeM_TBe HchkM_TBe HTM_TBe FBM_TBe A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_TBe.
    apply (ef0_s5 0%nat UStopLe q_TBe false TM_TBe Eq_TBe EQ_TBe TQ0_TBe run5_TBe RQ_TBe NX5_TBe RUN5_TBe L5_TBe AXQ_TBe HeQ_TBe HchkQ_TBe HTQ_TBe FBQ_TBe
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_TBe.
    apply (ef0_s6 0%nat UStopLe false TQ_TBe Edr_TBe Xf_TBe run6_TBe NX6_TBe RUN6_TBe L6_TBe A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s2 0%nat UStopLe true S1c_TBe C2_TBe EfD_TBe ED_TBe run2_TBe D2_TBe W2_TBe NX2_TBe EQ2_TBe RUN2_TBe L2_TBe AXD_TBe
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0%nat UStopLe false TD_TBe TDr_TBe CD_TBe Eps_TBe Ebg_TBe run3_TBe AXDr_TBe ENTD_TBe RUN3_TBe L3_TBe NX3_TBe
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_TBe : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S1fR8R5A2S2fU0S24RaR9R8R6S33S39R4A9S1eRbRaR9R7S34R5A6S1eRcRbRaR8S35R6A6S1eRdRcRbR9S3aR7A6S4S29Vsegs;S1aVsegs;S46ReRdRbA3S37R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_TBe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TBe LH0_TBe LT_TBe EX_TBe S1c_TBe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TBe l2_TBe l3_TBe l4_TBe HNX HLEN
           (runT_some _ _ _ _ RUN1_TBe NE1) L1ok_TBe (runT_some _ _ _ _ RUN2f_TBe NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_TBe NE3) H3 (runT_some _ _ _ _ RUN4f_TBe NE4) H4
           (hside_of A Kc rho1 P0_TBe LT_TBe tp SIDE_TBe OBND_TBe HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_s1c_TBe keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF rhoE).
Qed.
End ITBe.
End F0T_iTBe.

(* [comment removed for export] *)
Module SpineMallocS5i.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "prod"; "list"; "pair"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "swf"; "SVar"; "ss_facts"; "SLit"; "ss_next"; "SPUle"; "SPBranch"; "SPNot"; "ss_objs"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E3p"; "E5s1"; "E5s2"; "C5b"; "C5c"; "E5f"; "C3"; "E5n"; "sreg1"; "sreg2"; "C6"; "V_CLS"; "C2p"; "C2r"; "C5"; "E3r"; "E4d"; "V_SIZE"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "E5s1'"; "E5s2'"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.SpineMallocS5i.INST"; "s1_0"; "s2_0"; "s3_0"; "s6n_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S28VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C2p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E3p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E3p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E3p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S22VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C3 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C3] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C3]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S29VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C2r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E3r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E3r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E3r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E4d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E4d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E4d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S23VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5n W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5n] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5n]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5f W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5f] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5f]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5s1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5s2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S1bSfSfS4SfS24VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (sreg1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [sreg1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [sreg1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S1bSfSfS4SfS25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (sreg2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [sreg2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [sreg2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S38U0Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s1' 0%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5s1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S39U0Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s2' 0%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [E5s2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma memo_17 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all | (cbv delta [C5c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP.MallocMemoSP_all) ]; reflexivity). Defined.
Lemma Cert3p_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z40e58S5S34Z3c614S8S34A1A3A3S36S5S0S28VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S1cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C2p W st tmax) memo_0. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SKY_0 : ltac2:(tb__ "0|1|
S4SaS9S9SfSfA2SfA2M0A1S4bS11G0S4fS1aS1S1cVW;Vst;Vtmax;A3A1A1A4S4bS11G0S4fScS11ScS11S5S11S56ScS11S5bVW;A1S57A3A3S55A3S5S11S2fS5S11S31S5S11S30S5S11S32S8S11A1A3A3A3A3A3A4A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YX_0 : ltac2:(tb__ "0|1|
S4SaS9SfSfA2M0A1S3S1cVW;Vst;Vtmax;A3A1S8G0A1A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YF_0 : ltac2:(tb__ "0|0|
S3eS10ScS10ScS10ScS10S5aVW;Vst;A2S59S58A1A3S54A3S2eA3S14S1S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YP_0 : ltac2:(tb__ "0|0|
S3dS10S17S15Z1A1S13S33A1A2S14S1S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY1_0 : ltac2:(tb__ "0|0|
S4S6S12S1S45S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY2_0 : ltac2:(tb__ "0|0|
S4S6S12S1S46S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY3_0 : ltac2:(tb__ "0|0|
S4S6S12S1S47S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY4_0 : ltac2:(tb__ "0|0|
S4S6S12S1S48S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY5_0 : ltac2:(tb__ "0|0|
S4S6S12S1S49S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY6_0 : ltac2:(tb__ "0|0|
S4S6S12S1S4aS1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY7_0 : ltac2:(tb__ "0|0|
S4S6S12S1S44S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s3_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S44S1cVW;Vst;Vtmax;A3A1A1S1S22VW;Vst;Vtmax;A3A1A3").
Lemma ENT3_0 : ltac2:(tb__ "0|0|
S4S6S2S44S1cVW;Vst;Vtmax;A3A1S22VW;Vst;Vtmax;A3S52A3S7A3").
Proof. unfold s3_0. memo_rw (E3p W st tmax) memo_1. memo_rw (C3 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID3_0 : ltac2:(tb__ "0|0|
S4S6S42S52S36A2S7A3").
Proof. unfold s3_0. memo_rw (C3 W st tmax) memo_2. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert3r_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z40e58S5S34Z3c614S8S34A1A3A3S36S5S0S29VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S2bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C2r W st tmax) memo_3. memo_rw (E3r W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert4_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z7e9e4S8S34A1A3S36S5S0S22VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S2cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C3 W st tmax) memo_2. memo_rw (E4d W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z3c774S5S34Z3c80cS8S34A1A3A3S36S5S0S2aVW;Vst;Vtmax;A3S8S0A1M0A3S5S0S23VW;Vst;Vtmax;A3S5S0S21VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. memo_rw (C5 W st tmax) memo_6. memo_rw (E5n W st tmax) memo_7. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s6n_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S23VW;Vst;Vtmax;A3A1S1S26VW;Vst;Vtmax;A3A1A3").
Lemma ENT6n_0 : ltac2:(tb__ "0|0|
S4S6S2S23VW;Vst;Vtmax;A3S26VW;Vst;Vtmax;A3S53A3S7A3").
Proof. unfold s6n_0. memo_rw (E5n W st tmax) memo_7. memo_rw (C6 W st tmax) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID6n_0 : ltac2:(tb__ "0|0|
S4S6S42S53S36A2S7A3").
Proof. unfold s6n_0. memo_rw (C6 W st tmax) memo_9. memo_rw (E5n W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W5b_0 : ltac2:(tb__ "0|0|
S4S6S12S1S1fVW;Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (C5b W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D5b_0 : ltac2:(tb__ "0|5|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S21VW;Vst;Vtmax;A3A1S1S1fVW;Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS3cS13S27A1M4A4S5G0SbSfSfS3bG4A4S8G0A1A3A3S8S10A1A4A2A3").
Proof. memo_rw (E5f W st tmax) memo_8. memo_rw (C5b W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX5b_0 : ltac2:(tb__ "0|0|
S4S35S16S1S1fVW;Vst;Vtmax;A3A1A1S16S1S21VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C5b W st tmax) memo_10. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F5f64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S21VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z3c7e0S8S34A1A3S36S5S0S1fVW;Vst;Vtmax;A3S8S0A1M0A3S5S0S1dVW;Vst;Vtmax;A3S5S0S1eVW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. memo_rw (C5b W st tmax) memo_10. memo_rw (E5s1 W st tmax) memo_11. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV1_0 : ltac2:(tb__ "0|0|
S4S6S4eP9eS24VW;Vst;Vtmax;A3A2S7A3").
Proof. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV2_0 : ltac2:(tb__ "0|0|
S4S6S4eP9eS25VW;Vst;Vtmax;A3A2S7A3").
Proof. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB1_0 : ltac2:(tb__ "0|0|
S4S6S3aP9eS24VW;Vst;Vtmax;A3S4dZ11UeA5S7A3").
Proof. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB2_0 : ltac2:(tb__ "0|0|
S4S6S3aP9eS25VW;Vst;Vtmax;A3S4dZ1U10A5S7A3").
Proof. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1'_0 : ltac2:(tb__ "0|0|
S4S6S12S1S38U0Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (E5s1' 0%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2'_0 : ltac2:(tb__ "0|0|
S4S6S12S1S39U0Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (E5s2' 0%nat st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D1'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S1dVW;Vst;Vtmax;A3A1S1S38U0Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS24VW;Vst;Vtmax;A3S13S2dA1A4S8G0A1A3S8S10A1A4A2A3").
Proof. memo_rw (E5s1 W st tmax) memo_11. memo_rw (E5s1' 0%nat st tmax) memo_15. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D2'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S1eVW;Vst;Vtmax;A3A1S1S39U0Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS25VW;Vst;Vtmax;A3S13S2dA1A4S8G0A1A3S8S10A1A4A2A3").
Proof. memo_rw (E5s2 W st tmax) memo_12. memo_rw (E5s2' 0%nat st tmax) memo_16. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1'_0 : ltac2:(tb__ "0|0|
S4S35S16S1S38U0Vst;Vtmax;A3A1A1S16S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E5s1' 0%nat st tmax) memo_15. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2'_0 : ltac2:(tb__ "0|0|
S4S35S16S1S39U0Vst;Vtmax;A3A1A1S16S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E5s2' 0%nat st tmax) memo_16. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1gt_0 : ltac2:(tb__ "0|0|
S3dS10S18S4cS15Z10A1S13S27A1A3S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2le_0 : ltac2:(tb__ "0|0|
S3dS10S19S18S4cS15Z10A1S13S27A1A3A1S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1_64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S38U0Vst;Vtmax;A3A1S1S20VW;Vst;Vtmax;A3A1A3").
Definition s2_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S39U0Vst;Vtmax;A3A1S1S20VW;Vst;Vtmax;A3A1A3").
Lemma ENT1_0 : ltac2:(tb__ "0|0|
S4S6S2S38U0Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S50A3S7A3").
Proof. unfold s1_0. memo_rw (E5s1' 0%nat st tmax) memo_15. memo_rw (C5c W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT2_0 : ltac2:(tb__ "0|0|
S4S6S2S39U0Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S51A3S7A3").
Proof. unfold s2_0. memo_rw (E5s2' 0%nat st tmax) memo_16. memo_rw (C5c W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID1_0 : ltac2:(tb__ "0|0|
S4S6S42S50S36A2S7A3").
Proof. unfold s1_0. memo_rw (C5c W st tmax) memo_17. memo_rw (E5s1' 0%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID2_0 : ltac2:(tb__ "0|0|
S4S6S42S51S36A2S7A3").
Proof. unfold s2_0. memo_rw (C5c W st tmax) memo_17. memo_rw (E5s2' 0%nat st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS5i.

(* [comment removed for export] *)
Module F0T_iTBf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_lenient"; "ss_next"; "rw"; "SVar"; "ss_objs"; "sv_below"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.F0T_iTBf.ITBf"; "contF"; "econtF"; "side_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "depot_onlyKf"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf"; "ED_TBf"; "Ebg_TBf"; "Edr_TBf"; "LT_TBf"; "P0_TBf"; "S1c_TBf"; "TD_TBf"; "Xf_TBf"; "l1_TBf"; "EX_TBf"; "LH0_TBf"; "l2_TBf"; "l3_TBf"; "l4_TBf"; "l1okb_TBf"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "objs_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "pFR"; "LOOPH"; "atpc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma chk_split_TBf : ltac2:(tb__ "0|9|
S0S0S2S1SeS13A1M0S3bS11S13A1M1A3A1S0S2S1G0S3eG1A3A1S0S2S1G0S3fG1A3A1S2S1G0S40G1A3A1A2A2A2S0S1ScS41S3bA1SdA3S0S1ScS4fS10S13S4aS49S3bA2A2U1A2SdA3S0S1ScS43S13S13S12S32S15R1A1M2S36A2S32G2S3cA2A2LL;S3eA3SdA3S0S1ScSbS14S4eS36S8S48A1M3A2A1A1SdA3S0S1ScSaS6S14S36A1M4A1M5G3A2SdA3S0S1ScS43S13S4dS36S3cS48A3S3fA3SdA3S0S1ScS43S13S13S32G2S38A2LL;S40A3SdA3S0S0S42S2cS6S14S37A1M6A1A2S0S42S2cS6S14S3dA1M7A1A2S0S42S2cG5A2S42S2cS6S14S3cA1M8A1A2A2A2A2S0S1ScS5G6A1SfA3S0S1ScS5G7A1SfA3S0S1ScS5G4A1SfA3S1ScS5G8A1SfA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chk_TBf as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1ok_TBf : ltac2:(tb__ "0|1|
S13S44S13R1S3bA3S3S1S16S15R2A1M0S3dA3S1ScS32G0S38A2SdA3A2F_;FL;").
Proof.
  destruct chk_split_TBf as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_TBf)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- LH0eq_TBf. destruct (atpc LOOPH l1_TBf) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ITBf.
Let segs : list Segment := segsA.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S31U0S24Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S2aVsegs;Vok;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S29Vsegs;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Definition side_pure (A : AA) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S0S47Vrho1;S19Q40M0S7Vrho1;PaA2A2S9S14S37A1A1A3S0S1S17G0A1S7Vrho1;P99A2S18G0S22S21VA;A1M1A1M2A2A3S0S4bZ1G2A2S4bG2S4cS23G1A1A1A2A2A2A2").

Theorem spine_s1c_TBf : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S2eU0S24RbRaR9R8R6S33S39R4AaS1dRcRbRaR9R7S34R5A7S1dRdRcRbRaR8S35R6A7S1dReRdRcRbR9S3aR7A7S4S2aVsegs;RfS1aVsegs;VJFi;SdReRdRbA4S38R1RaA5R9A4FrhoE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_TBf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_TBf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat UStopLe false Eps_TBf C3_TBf Ems_TBf C4_TBf TM0_TBf run4_TBf RM_TBf D3_TBf W3_TBf EQ3_TBf NX3b_TBf RUN4_TBf L4_TBf D4_TBf W4_TBf EQ4_TBf
             HeM_TBf HchkM_TBf HTM_TBf FBM_TBf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_TBf.
    apply (f0_s5 0%nat UStopLe q_TBf false TM_TBf Eq_TBf EQ_TBf TQ0_TBf run5_TBf RQ_TBf NX5_TBf RUN5_TBf L5_TBf AXQ_TBf HeQ_TBf HchkQ_TBf HTQ_TBf FBQ_TBf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_TBf.
    apply (f0_s6 0%nat UStopLe false TQ_TBf Edr_TBf Xf_TBf run6_TBf NX6_TBf RUN6_TBf L6_TBf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s2 0%nat UStopLe true S1c_TBf C2_TBf EfD_TBf ED_TBf run2_TBf D2_TBf W2_TBf NX2_TBf EQ2_TBf RUN2_TBf L2_TBf AXD_TBf
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0%nat UStopLe false TD_TBf TDr_TBf CD_TBf Eps_TBf Ebg_TBf run3_TBf AXDr_TBf ENTD_TBf RUN3_TBf L3_TBf NX3_TBf
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_TBf : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S1fR9R6A2S2eU0S24RcRbRaR9R7S33S39R5AaS1dRdRcRbRaR8S34R6A7S1dReRdRcRbR9S35R7A7S1dRfReRdRcRaS3aR8A7S4S2aVsegs;R10S1aVsegs;S46RfReRcA3S37R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_TBf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TBf LH0_TBf LT_TBf EX_TBf S1c_TBf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TBf l2_TBf l3_TBf l4_TBf HNX HLEN
           (runT_some _ _ _ _ RUN1_TBf NE1) L1ok_TBf (runT_some _ _ _ _ RUN2f_TBf NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_TBf NE3) H3 (runT_some _ _ _ _ RUN4f_TBf NE4) H4
           (hside_of A Kc rho1 P0_TBf LT_TBf tp SIDE_TBf OBND_TBf HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_s1c_TBf keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF rhoE).
Qed.

Theorem espine_s1c_TBf : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S2fU0S24R9R8R7R5S33S39R3A9S1eRaR9R8R6S34R4A6S1eRbRaR9R7S35R5A6S1eRcRbRaR8S3aR6A6S4S29Vsegs;S1aVsegs;VJFi;SdRdRcRaA4S38R1R9A5R8A3FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_TBf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_TBf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat UStopLe false Eps_TBf C3_TBf Ems_TBf C4_TBf TM0_TBf run4_TBf RM_TBf D3_TBf W3_TBf EQ3_TBf NX3b_TBf RUN4_TBf L4_TBf D4_TBf W4_TBf EQ4_TBf
             HeM_TBf HchkM_TBf HTM_TBf FBM_TBf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_TBf.
    apply (ef0_s5 0%nat UStopLe q_TBf false TM_TBf Eq_TBf EQ_TBf TQ0_TBf run5_TBf RQ_TBf NX5_TBf RUN5_TBf L5_TBf AXQ_TBf HeQ_TBf HchkQ_TBf HTQ_TBf FBQ_TBf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_TBf.
    apply (ef0_s6 0%nat UStopLe false TQ_TBf Edr_TBf Xf_TBf run6_TBf NX6_TBf RUN6_TBf L6_TBf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s2 0%nat UStopLe true S1c_TBf C2_TBf EfD_TBf ED_TBf run2_TBf D2_TBf W2_TBf NX2_TBf EQ2_TBf RUN2_TBf L2_TBf AXD_TBf
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0%nat UStopLe false TD_TBf TDr_TBf CD_TBf Eps_TBf Ebg_TBf run3_TBf AXDr_TBf ENTD_TBf RUN3_TBf L3_TBf NX3_TBf
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_TBf : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S1fR8R5A2S2fU0S24RaR9R8R6S33S39R4A9S1eRbRaR9R7S34R5A6S1eRcRbRaR8S35R6A6S1eRdRcRbR9S3aR7A6S4S29Vsegs;S1aVsegs;S46ReRdRbA3S37R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_TBf as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_TBf LH0_TBf LT_TBf EX_TBf S1c_TBf pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_TBf l2_TBf l3_TBf l4_TBf HNX HLEN
           (runT_some _ _ _ _ RUN1_TBf NE1) L1ok_TBf (runT_some _ _ _ _ RUN2f_TBf NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_TBf NE3) H3 (runT_some _ _ _ _ RUN4f_TBf NE4) H4
           (hside_of A Kc rho1 P0_TBf LT_TBf tp SIDE_TBf OBND_TBf HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_s1c_TBf keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF rhoE).
Qed.
End ITBf.
End F0T_iTBf.

(* [comment removed for export] *)
Module SpineMallocS5iW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "prod"; "list"; "pair"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "swf"; "SVar"; "ss_facts"; "SLit"; "ss_next"; "SPUle"; "SPBranch"; "SPNot"; "ss_objs"; "@Corelib.Init.Specif"; "sig"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E3p"; "E5s1"; "E5s2"; "C5b"; "C5c"; "E5f"; "C3"; "E5n"; "sreg1"; "sreg2"; "C6"; "V_CLS"; "C2p"; "C2r"; "C5"; "E3r"; "E4d"; "V_SIZE"; "F_gen"; "O_pcc"; "O_pck"; "O_pcs"; "O_st"; "V_CNT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "E5s1'"; "E5s2'"; "tab1_ok"; "clsp_e"; "clsp_e31"; "@Stdlib.Lists.List"; "In"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4"; "Y7"; "Y1"; "Y2"; "Y3"; "Y4"; "Y5"; "Y6"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j7.SpineMallocS5iW2.INST"; "s1_0"; "s2_0"; "s3_0"; "s6n_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3iW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineMallocS8.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S28VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C2p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E3p W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E3p] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E3p]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S22VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C3 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C3] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C3]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S29VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C2r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C2r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C2r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2bVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E3r W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E3r] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E3r]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2cVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E4d W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E4d] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E4d]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S2aVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S23VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5n W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5n] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5n]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_8 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S21VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5f W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5f] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5f]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S26VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C6 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C6] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C6]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1fVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5b W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5b] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5b]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1dVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5s1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S1eVW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5s2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_13 : ltac2:(tb__ "0|0|
S1bSfSfS4SfS24VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (sreg1 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [sreg1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [sreg1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_14 : ltac2:(tb__ "0|0|
S1bSfSfS4SfS25VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (sreg2 W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [sreg2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [sreg2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_15 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S38U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s1' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s1] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5s1]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_16 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S39U2Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (E5s2' 2%nat st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [E5s2] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [E5s2]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma memo_17 : ltac2:(tb__ "0|0|
S1bS0S0S4S0S20VW;Vst;Vtmax;A3R1A3Lx;A2"). Proof. let t0 := eval cbv delta [W st tmax] in (C5c W st tmax) in let w := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t0 in
  let w := match constr:(Set) with
           | _ => let _ := constr:(ltac:(constr_eq w t0; exact tt) : unit) in let t1 := eval cbv delta [C5c] in t0 in let t1 := eval cbv beta zeta in t1 in OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_subst t1
           | _ => w end in
  exists w; abstract (cbv delta [W st tmax]; first [ progress OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all | (cbv delta [C5c]; cbv beta zeta; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2.MallocMemoSPW2_all) ]; reflexivity). Defined.
Lemma Cert3p_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z40e58S5S34Z3c614S8S34A1A3A3S36S5S0S28VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S1cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C2p W st tmax) memo_0. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SKY_0 : ltac2:(tb__ "0|1|
S4SaS9S9SfSfA2SfA2M0A1S4bS11G0S4fS1aS1S1cVW;Vst;Vtmax;A3A1A1A4S4bS11G0S4fScS11ScS11S5S11S56ScS11S5bVW;A1S57A3A3S55A3S5S11S2fS5S11S31S5S11S30S5S11S32S8S11A1A3A3A3A3A3A4A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YX_0 : ltac2:(tb__ "0|1|
S4SaS9SfSfA2M0A1S3S1cVW;Vst;Vtmax;A3A1S8G0A1A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YF_0 : ltac2:(tb__ "0|0|
S3eS10ScS10ScS10ScS10S5aVW;Vst;A2S59S58A1A3S54A3S2eA3S14S1S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply inclb_incl. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma YP_0 : ltac2:(tb__ "0|0|
S3dS10S17S15Z1A1S13S33A1A2S14S1S1cVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY1_0 : ltac2:(tb__ "0|0|
S4S6S12S1S45S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY2_0 : ltac2:(tb__ "0|0|
S4S6S12S1S46S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY3_0 : ltac2:(tb__ "0|0|
S4S6S12S1S47S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY4_0 : ltac2:(tb__ "0|0|
S4S6S12S1S48S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY5_0 : ltac2:(tb__ "0|0|
S4S6S12S1S49S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY6_0 : ltac2:(tb__ "0|0|
S4S6S12S1S4aS1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WY7_0 : ltac2:(tb__ "0|0|
S4S6S12S1S44S1cVW;Vst;Vtmax;A3A1A1A1S7A3").
Proof. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s3_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S44S1cVW;Vst;Vtmax;A3A1A1S1S22VW;Vst;Vtmax;A3A1A3").
Lemma ENT3_0 : ltac2:(tb__ "0|0|
S4S6S2S44S1cVW;Vst;Vtmax;A3A1S22VW;Vst;Vtmax;A3S52A3S7A3").
Proof. unfold s3_0. memo_rw (E3p W st tmax) memo_1. memo_rw (C3 W st tmax) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID3_0 : ltac2:(tb__ "0|0|
S4S6S42S52S36A2S7A3").
Proof. unfold s3_0. memo_rw (C3 W st tmax) memo_2. memo_rw (E3p W st tmax) memo_1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert3r_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z40e58S5S34Z3c614S8S34A1A3A3S36S5S0S29VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S2bVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C2r W st tmax) memo_3. memo_rw (E3r W st tmax) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert4_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z7e9e4S8S34A1A3S36S5S0S22VW;Vst;Vtmax;A3S8S0A1M0A3S5S0S2cVW;Vst;Vtmax;A3G0A3A6S7A3").
Proof. memo_rw (C3 W st tmax) memo_2. memo_rw (E4d W st tmax) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z3c774S5S34Z3c80cS8S34A1A3A3S36S5S0S2aVW;Vst;Vtmax;A3S8S0A1M0A3S5S0S23VW;Vst;Vtmax;A3S5S0S21VW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. memo_rw (C5 W st tmax) memo_6. memo_rw (E5n W st tmax) memo_7. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s6n_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S23VW;Vst;Vtmax;A3A1S1S26VW;Vst;Vtmax;A3A1A3").
Lemma ENT6n_0 : ltac2:(tb__ "0|0|
S4S6S2S23VW;Vst;Vtmax;A3S26VW;Vst;Vtmax;A3S53A3S7A3").
Proof. unfold s6n_0. memo_rw (E5n W st tmax) memo_7. memo_rw (C6 W st tmax) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID6n_0 : ltac2:(tb__ "0|0|
S4S6S42S53S36A2S7A3").
Proof. unfold s6n_0. memo_rw (C6 W st tmax) memo_9. memo_rw (E5n W st tmax) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W5b_0 : ltac2:(tb__ "0|0|
S4S6S12S1S1fVW;Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (C5b W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D5b_0 : ltac2:(tb__ "0|5|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S21VW;Vst;Vtmax;A3A1S1S1fVW;Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS3cS13S27A1M4A4S5G0SbSfSfS3bG4A4S8G0A1A3A3S8S10A1A4A2A3").
Proof. memo_rw (E5f W st tmax) memo_8. memo_rw (C5b W st tmax) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX5b_0 : ltac2:(tb__ "0|0|
S4S35S16S1S1fVW;Vst;Vtmax;A3A1A1S16S1S21VW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (C5b W st tmax) memo_10. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F5f64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S21VW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5f W st tmax) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Cert5b_0 : ltac2:(tb__ "0|1|
S4S6S3fS37Ufa0S5S34Z3c7e0S8S34A1A3S36S5S0S1fVW;Vst;Vtmax;A3S8S0A1M0A3S5S0S1dVW;Vst;Vtmax;A3S5S0S1eVW;Vst;Vtmax;A3G0A3A3A6S7A3").
Proof. memo_rw (C5b W st tmax) memo_10. memo_rw (E5s1 W st tmax) memo_11. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV1_0 : ltac2:(tb__ "0|0|
S4S6S4eP9eS24VW;Vst;Vtmax;A3A2S7A3").
Proof. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OV2_0 : ltac2:(tb__ "0|0|
S4S6S4eP9eS25VW;Vst;Vtmax;A3A2S7A3").
Proof. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB1_0 : ltac2:(tb__ "0|0|
S4S6S3aP9eS24VW;Vst;Vtmax;A3S4dZ11UeA5S7A3").
Proof. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TAB2_0 : ltac2:(tb__ "0|0|
S4S6S3aP9eS25VW;Vst;Vtmax;A3S4dZ1U10A5S7A3").
Proof. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W1'_0 : ltac2:(tb__ "0|0|
S4S6S12S1S38U2Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (E5s1' 2%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma W2'_0 : ltac2:(tb__ "0|0|
S4S6S12S1S39U2Vst;Vtmax;A3A1A1S7A3").
Proof. memo_rw (E5s2' 2%nat st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D1'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S1dVW;Vst;Vtmax;A3A1S1S38U2Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS24VW;Vst;Vtmax;A3S13S2dA1A4S8G0A1A3S8S10A1A4A2A3").
Proof. memo_rw (E5s1 W st tmax) memo_11. memo_rw (E5s1' 2%nat st tmax) memo_15. memo_rw (sreg1 W st tmax) memo_13. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma D2'_0 : ltac2:(tb__ "0|4|
S4SeS9SaS9SfSfA2M0A1M1SaS10A1M2A2M3A1S43S1S1eVW;Vst;Vtmax;A3A1S1S39U2Vst;Vtmax;A3A1A2SdG3SbG1G2S5G0SbSfSfS25VW;Vst;Vtmax;A3S13S2dA1A4S8G0A1A3S8S10A1A4A2A3").
Proof. memo_rw (E5s2 W st tmax) memo_12. memo_rw (E5s2' 2%nat st tmax) memo_16. memo_rw (sreg2 W st tmax) memo_14. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1'_0 : ltac2:(tb__ "0|0|
S4S35S16S1S38U2Vst;Vtmax;A3A1A1S16S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E5s1' 2%nat st tmax) memo_15. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX2'_0 : ltac2:(tb__ "0|0|
S4S35S16S1S39U2Vst;Vtmax;A3A1A1S16S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. memo_rw (E5s2' 2%nat st tmax) memo_16. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1gt_0 : ltac2:(tb__ "0|0|
S3dS10S18S4cS15Z10A1S13S27A1A3S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2le_0 : ltac2:(tb__ "0|0|
S3dS10S19S18S4cS15Z10A1S13S27A1A3A1S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F1_64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S1dVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s1 W st tmax) memo_11. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_64_0 : ltac2:(tb__ "0|0|
S3dS10S17S13PcA1S15Zfc00A1A2S14S1S1eVW;Vst;Vtmax;A3A1A1A3").
Proof. apply In_of_inclb. memo_rw (E5s2 W st tmax) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s1_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S38U2Vst;Vtmax;A3A1S1S20VW;Vst;Vtmax;A3A1A3").
Definition s2_0 : ltac2:(tb__ "0|0|
S41") := ltac2:(tb__ "0|0|
S40S36S1S39U2Vst;Vtmax;A3A1S1S20VW;Vst;Vtmax;A3A1A3").
Lemma ENT1_0 : ltac2:(tb__ "0|0|
S4S6S2S38U2Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S50A3S7A3").
Proof. unfold s1_0. memo_rw (E5s1' 2%nat st tmax) memo_15. memo_rw (C5c W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENT2_0 : ltac2:(tb__ "0|0|
S4S6S2S39U2Vst;Vtmax;A3S20VW;Vst;Vtmax;A3S51A3S7A3").
Proof. unfold s2_0. memo_rw (E5s2' 2%nat st tmax) memo_16. memo_rw (C5c W st tmax) memo_17. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID1_0 : ltac2:(tb__ "0|0|
S4S6S42S50S36A2S7A3").
Proof. unfold s1_0. memo_rw (C5c W st tmax) memo_17. memo_rw (E5s1' 2%nat st tmax) memo_15. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SID2_0 : ltac2:(tb__ "0|0|
S4S6S42S51S36A2S7A3").
Proof. unfold s2_0. memo_rw (C5c W st tmax) memo_17. memo_rw (E5s2' 2%nat st tmax) memo_16. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End INST.
End SpineMallocS5iW2.

