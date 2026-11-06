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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im j2 j3.

(* [comment removed for export] *)
Module F0T_iLTA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_lenient"; "ss_next"; "rw"; "SVar"; "ss_objs"; "sv_below"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTA.ILTA"; "contF"; "econtF"; "side_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "depot_onlyKf"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA"; "ED_LTA"; "Ebg_LTA"; "Edr_LTA"; "LT_LTA"; "P0_LTA"; "S1c_LTA"; "TD_LTA"; "Xf_LTA"; "l1_LTA"; "EX_LTA"; "LH0_LTA"; "l2_LTA"; "l3_LTA"; "l4_LTA"; "l1okb_LTA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "objs_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "pFR"; "LOOPH"; "atpc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma chk_split_LTA : ltac2:(tb__ "0|9|
S0S0S2S1SeS13A1M0S3bS11S13A1M1A3A1S0S2S1G0S3eG1A3A1S0S2S1G0S3fG1A3A1S2S1G0S40G1A3A1A2A2A2S0S1ScS41S3bA1SdA3S0S1ScS4fS10S13S4aS49S3bA2A2U1A2SdA3S0S1ScS43S13S13S12S32S15R1A1M2S36A2S32G2S3cA2A2LL;S3eA3SdA3S0S1ScSbS14S4eS36S8S48A1M3A2A1A1SdA3S0S1ScSaS6S14S36A1M4A1M5G3A2SdA3S0S1ScS43S13S4dS36S3cS48A3S3fA3SdA3S0S1ScS43S13S13S32G2S38A2LL;S40A3SdA3S0S0S42S2cS6S14S37A1M6A1A2S0S42S2cS6S14S3dA1M7A1A2S0S42S2cG5A2S42S2cS6S14S3cA1M8A1A2A2A2A2S0S1ScS5G6A1SfA3S0S1ScS5G7A1SfA3S0S1ScS5G4A1SfA3S1ScS5G8A1SfA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chk_LTA as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1ok_LTA : ltac2:(tb__ "0|1|
S13S44S13R1S3bA3S3S1S16S15R2A1M0S3dA3S1ScS32G0S38A2SdA3A2F_;FL;").
Proof.
  destruct chk_split_LTA as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_LTA)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- LH0eq_LTA. destruct (atpc LOOPH l1_LTA) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ILTA.
Let segs : list Segment := segsA.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S31U0S24Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S2aVsegs;Vok;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S29Vsegs;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Definition side_pure (A : AA) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S0S47Vrho1;S19Q40M0S7Vrho1;PaA2A2S9S14S37A1A1A3S0S1S17G0A1S7Vrho1;P99A2S18G0S22S21VA;A1M1A1M2A2A3S0S4bZ1G2A2S4bG2S4cS23G1A1A1A2A2A2A2").

Theorem spine_s1c_LTA : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S2eU0S24RbRaR9R8R6S33S39R4AaS1dRcRbRaR9R7S34R5A7S1dRdRcRbRaR8S35R6A7S1dReRdRcRbR9S3aR7A7S4S2aVsegs;RfS1aVsegs;VJFi;SdReRdRbA4S38R1RaA5R9A4FrhoE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_LTA rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_LTA rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat UStopLe false Eps_LTA C3_LTA Ems_LTA C4_LTA TM0_LTA run4_LTA RM_LTA D3_LTA W3_LTA EQ3_LTA NX3b_LTA RUN4_LTA L4_LTA D4_LTA W4_LTA EQ4_LTA
             HeM_LTA HchkM_LTA HTM_LTA FBM_LTA ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LTA.
    apply (f0_s5 0%nat UStopLe q_LTA false TM_LTA Eq_LTA EQ_LTA TQ0_LTA run5_LTA RQ_LTA NX5_LTA RUN5_LTA L5_LTA AXQ_LTA HeQ_LTA HchkQ_LTA HTQ_LTA FBQ_LTA
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_LTA.
    apply (f0_s6 0%nat UStopLe false TQ_LTA Edr_LTA Xf_LTA run6_LTA NX6_LTA RUN6_LTA L6_LTA ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s2 0%nat UStopLe true S1c_LTA C2_LTA EfD_LTA ED_LTA run2_LTA D2_LTA W2_LTA NX2_LTA EQ2_LTA RUN2_LTA L2_LTA AXD_LTA
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0%nat UStopLe false TD_LTA TDr_LTA CD_LTA Eps_LTA Ebg_LTA run3_LTA AXDr_LTA ENTD_LTA RUN3_LTA L3_LTA NX3_LTA
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_LTA : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S1fR9R6A2S2eU0S24RcRbRaR9R7S33S39R5AaS1dRdRcRbRaR8S34R6A7S1dReRdRcRbR9S35R7A7S1dRfReRdRcRaS3aR8A7S4S2aVsegs;R10S1aVsegs;S46RfReRcA3S37R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_LTA as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTA LH0_LTA LT_LTA EX_LTA S1c_LTA pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTA l2_LTA l3_LTA l4_LTA HNX HLEN
           (runT_some _ _ _ _ RUN1_LTA NE1) L1ok_LTA (runT_some _ _ _ _ RUN2f_LTA NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_LTA NE3) H3 (runT_some _ _ _ _ RUN4f_LTA NE4) H4
           (hside_of A Kc rho1 P0_LTA LT_LTA tp SIDE_LTA OBND_LTA HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_s1c_LTA keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF rhoE).
Qed.

Theorem espine_s1c_LTA : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S2fU0S24R9R8R7R5S33S39R3A9S1eRaR9R8R6S34R4A6S1eRbRaR9R7S35R5A6S1eRcRbRaR8S3aR6A6S4S29Vsegs;S1aVsegs;VJFi;SdRdRcRaA4S38R1R9A5R8A3FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_LTA rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_LTA rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat UStopLe false Eps_LTA C3_LTA Ems_LTA C4_LTA TM0_LTA run4_LTA RM_LTA D3_LTA W3_LTA EQ3_LTA NX3b_LTA RUN4_LTA L4_LTA D4_LTA W4_LTA EQ4_LTA
             HeM_LTA HchkM_LTA HTM_LTA FBM_LTA A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LTA.
    apply (ef0_s5 0%nat UStopLe q_LTA false TM_LTA Eq_LTA EQ_LTA TQ0_LTA run5_LTA RQ_LTA NX5_LTA RUN5_LTA L5_LTA AXQ_LTA HeQ_LTA HchkQ_LTA HTQ_LTA FBQ_LTA
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_LTA.
    apply (ef0_s6 0%nat UStopLe false TQ_LTA Edr_LTA Xf_LTA run6_LTA NX6_LTA RUN6_LTA L6_LTA A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s2 0%nat UStopLe true S1c_LTA C2_LTA EfD_LTA ED_LTA run2_LTA D2_LTA W2_LTA NX2_LTA EQ2_LTA RUN2_LTA L2_LTA AXD_LTA
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0%nat UStopLe false TD_LTA TDr_LTA CD_LTA Eps_LTA Ebg_LTA run3_LTA AXDr_LTA ENTD_LTA RUN3_LTA L3_LTA NX3_LTA
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_LTA : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S1fR8R5A2S2fU0S24RaR9R8R6S33S39R4A9S1eRbRaR9R7S34R5A6S1eRcRbRaR8S35R6A6S1eRdRcRbR9S3aR7A6S4S29Vsegs;S1aVsegs;S46ReRdRbA3S37R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_LTA as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTA LH0_LTA LT_LTA EX_LTA S1c_LTA pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTA l2_LTA l3_LTA l4_LTA HNX HLEN
           (runT_some _ _ _ _ RUN1_LTA NE1) L1ok_LTA (runT_some _ _ _ _ RUN2f_LTA NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_LTA NE3) H3 (runT_some _ _ _ _ RUN4f_LTA NE4) H4
           (hside_of A Kc rho1 P0_LTA LT_LTA tp SIDE_LTA OBND_LTA HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_s1c_LTA keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF rhoE).
Qed.
End ILTA.
End F0T_iLTA.

(* [comment removed for export] *)
Module F0T_bLTBf.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf"; "Ebg_LTBf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_LTBf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0T_bLTBf.

(* [comment removed for export] *)
Module F0T_bTA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA"; "Ebg_TA"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_TA : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0T_bTA.

(* [comment removed for export] *)
Module F0T_bTBe.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe"; "Ebg_TBe"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_TBe : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0T_bTBe.

(* [comment removed for export] *)
Module F0T_iLTBe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_lenient"; "ss_next"; "rw"; "SVar"; "ss_objs"; "sv_below"; "swf"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "la_state"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j6.F0T_iLTBe.ILTBe"; "contF"; "econtF"; "side_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ag_stack_top"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "HDF"; "HDFE"; "depot_onlyKf"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe"; "ED_LTBe"; "Ebg_LTBe"; "Edr_LTBe"; "LT_LTBe"; "P0_LTBe"; "S1c_LTBe"; "TD_LTBe"; "Xf_LTBe"; "l1_LTBe"; "EX_LTBe"; "LH0_LTBe"; "l2_LTBe"; "l3_LTBe"; "l4_LTBe"; "l1okb_LTBe"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@Stdlib.Lists.List"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "JT"; "objs_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "pFR"; "LOOPH"; "atpc"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HBz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.UnwT_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j2.F0T_cLTBe.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma chk_split_LTBe : ltac2:(tb__ "0|9|
S0S0S2S1SeS13A1M0S3bS11S13A1M1A3A1S0S2S1G0S3eG1A3A1S0S2S1G0S3fG1A3A1S2S1G0S40G1A3A1A2A2A2S0S1ScS41S3bA1SdA3S0S1ScS4fS10S13S4aS49S3bA2A2U1A2SdA3S0S1ScS43S13S13S12S32S15R1A1M2S36A2S32G2S3cA2A2LL;S3eA3SdA3S0S1ScSbS14S4eS36S8S48A1M3A2A1A1SdA3S0S1ScSaS6S14S36A1M4A1M5G3A2SdA3S0S1ScS43S13S4dS36S3cS48A3S3fA3SdA3S0S1ScS43S13S13S32G2S38A2LL;S40A3SdA3S0S0S42S2cS6S14S37A1M6A1A2S0S42S2cS6S14S3dA1M7A1A2S0S42S2cG5A2S42S2cS6S14S3cA1M8A1A2A2A2A2S0S1ScS5G6A1SfA3S0S1ScS5G7A1SfA3S0S1ScS5G4A1SfA3S1ScS5G8A1SfA3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof chk_LTBe as H. repeat (apply andb_prop in H as [H ?X]).
  repeat match goal with X : negb _ = true |- _ => apply negb_true_iff in X end.
  repeat match goal with X : Pos.leb _ _ = true |- _ => apply Pos.leb_le in X end.
  assert (NE : forall l : list leafA, match l with [] => true | _ => false end = false -> l <> []) by (intros [|? ?] E; [discriminate | discriminate]).
  repeat split; try assumption; try (apply NE; assumption).
Qed.
Lemma L1ok_LTBe : ltac2:(tb__ "0|1|
S13S44S13R1S3bA3S3S1S16S15R2A1M0S3dA3S1ScS32G0S38A2SdA3A2F_;FL;").
Proof.
  destruct chk_split_LTBe as (_ & H1 & HN & _). intros L HinL.
  pose proof (proj1 (forallb_forall _ _) H1 L HinL) as HL. apply orb_prop in HL as [HP|HE]; [left | right; exact HE].
  assert (HinF : In L (atpc LOOPH l1_LTBe)).
  { unfold atpc. apply (proj2 (filter_In _ _ _)). split; [exact HinL | exact HP]. }
  rewrite <- LH0eq_LTBe. destruct (atpc LOOPH l1_LTBe) as [|L0 [|L1 r]]; try discriminate HN.
  destruct HinF as [<-|[]]. reflexivity.
Qed.

Section ILTBe.
Let segs : list Segment := segsA.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S31U0S24Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S2aVsegs;Vok;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
S20S4S4SeS17Q40A1A1S30VA;R4A2S45Vkeep;Vrho1;R4A3S29Vsegs;S1aVsegs;VJFi;SfR6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Definition side_pure (A : AA) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S0S47Vrho1;S19Q40M0S7Vrho1;PaA2A2S9S14S37A1A1A3S0S1S17G0A1S7Vrho1;P99A2S18G0S22S21VA;A1M1A1M2A2A3S0S4bZ1G2A2S4bG2S4cS23G1A1A1A2A2A2A2").

Theorem spine_s1c_LTBe : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S2eU0S24RbRaR9R8R6S33S39R4AaS1dRcRbRaR9R7S34R5A7S1dRdRcRbRaR8S35R6A7S1dReRdRcRbR9S3aR7A7S4S2aVsegs;RfS1aVsegs;VJFi;SdReRdRbA4S38R1RaA5R9A4FrhoE;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_LTBe rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_LTBe rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat UStopLe false Eps_LTBe C3_LTBe Ems_LTBe C4_LTBe TM0_LTBe run4_LTBe RM_LTBe D3_LTBe W3_LTBe EQ3_LTBe NX3b_LTBe RUN4_LTBe L4_LTBe D4_LTBe W4_LTBe EQ4_LTBe
             HeM_LTBe HchkM_LTBe HTM_LTBe FBM_LTBe ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_LTBe.
    apply (f0_s5 0%nat UStopLe q_LTBe false TM_LTBe Eq_LTBe EQ_LTBe TQ0_LTBe run5_LTBe RQ_LTBe NX5_LTBe RUN5_LTBe L5_LTBe AXQ_LTBe HeQ_LTBe HchkQ_LTBe HTQ_LTBe FBQ_LTBe
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_LTBe.
    apply (f0_s6 0%nat UStopLe false TQ_LTBe Edr_LTBe Xf_LTBe run6_LTBe NX6_LTBe RUN6_LTBe L6_LTBe ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s2 0%nat UStopLe true S1c_LTBe C2_LTBe EfD_LTBe ED_LTBe run2_LTBe D2_LTBe W2_LTBe NX2_LTBe EQ2_LTBe RUN2_LTBe L2_LTBe AXD_LTBe
           ok A Kc rho rho1 tp Q HUS HKc Hok HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (f0_s3 0%nat UStopLe false TD_LTBe TDr_LTBe CD_LTBe Eps_LTBe Ebg_LTBe run3_LTBe AXDr_LTBe ENTD_LTBe RUN3_LTBe L3_LTBe NX3_LTBe
           ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.
Theorem free_spine_LTBe : ltac2:(tb__ "0|0|
S27OF_;S28OF_;S20S25S4S4SeS17Q40A1A1S2bS26R5A1S1cVsegs;R8S1bR6A1A3S2dR6R5A2S1fR9R6A2S2eU0S24RcRbRaR9R7S33S39R5AaS1dRdRcRbRaR8S34R6A7S1dReRdRcRbR9S35R7A7S1dRfReRdRcRaS3aR8A7S4S2aVsegs;R10S1aVsegs;S46RfReRcA3S37R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_LTBe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (f0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTBe LH0_LTBe LT_LTBe EX_LTBe S1c_LTBe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTBe l2_LTBe l3_LTBe l4_LTBe HNX HLEN
           (runT_some _ _ _ _ RUN1_LTBe NE1) L1ok_LTBe (runT_some _ _ _ _ RUN2f_LTBe NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_LTBe NE3) H3 (runT_some _ _ _ _ RUN4f_LTBe NE4) H4
           (hside_of A Kc rho1 P0_LTBe LT_LTBe tp SIDE_LTBe OBND_LTBe HOB E153 HST) ok (JT_okf ok A Kc rho1 Hok) Q).
  intros rhoE. eapply triple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (spine_s1c_LTBe keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HBIG HQ3 HXF rhoE).
Qed.

Theorem espine_s1c_LTBe : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S2fU0S24R9R8R7R5S33S39R3A9S1eRaR9R8R6S34R4A6S1eRbRaR9R7S35R5A6S1eRcRbRaR8S3aR6A6S4S29Vsegs;S1aVsegs;VJFi;SdRdRcRaA4S38R1R9A5R8A3FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF.
  assert (HUS : stopJ_stable (Wcan 0) UStopLe) by apply stopJ_stable_le.
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_LTBe rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_LTBe rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat UStopLe false Eps_LTBe C3_LTBe Ems_LTBe C4_LTBe TM0_LTBe run4_LTBe RM_LTBe D3_LTBe W3_LTBe EQ3_LTBe NX3b_LTBe RUN4_LTBe L4_LTBe D4_LTBe W4_LTBe EQ4_LTBe
             HeM_LTBe HchkM_LTBe HTM_LTBe FBM_LTBe A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_LTBe.
    apply (ef0_s5 0%nat UStopLe q_LTBe false TM_LTBe Eq_LTBe EQ_LTBe TQ0_LTBe run5_LTBe RQ_LTBe NX5_LTBe RUN5_LTBe L5_LTBe AXQ_LTBe HeQ_LTBe HchkQ_LTBe HTQ_LTBe FBQ_LTBe
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_LTBe.
    apply (ef0_s6 0%nat UStopLe false TQ_LTBe Edr_LTBe Xf_LTBe run6_LTBe NX6_LTBe RUN6_LTBe L6_LTBe A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s2 0%nat UStopLe true S1c_LTBe C2_LTBe EfD_LTBe ED_LTBe run2_LTBe D2_LTBe W2_LTBe NX2_LTBe EQ2_LTBe RUN2_LTBe L2_LTBe AXD_LTBe
           A Kc rho rho1 tp Q HUS HKc HR).
  intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
  exact (ef0_s3 0%nat UStopLe false TD_LTBe TDr_LTBe CD_LTBe Eps_LTBe Ebg_LTBe run3_LTBe AXDr_LTBe ENTD_LTBe RUN3_LTBe L3_LTBe NX3_LTBe
           A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
Theorem efree_spine_LTBe : ltac2:(tb__ "0|0|
S27OF_;S20S25S4S4SeS17Q40A1A1S28OF_;S26R5A1S2dR5R4A2S1fR8R5A2S2fU0S24RaR9R8R6S33S39R4A9S1eRbRaR9R7S34R5A6S1eRcRbRaR8S35R6A6S1eRdRcRbR9S3aR7A6S4S29Vsegs;S1aVsegs;S46ReRdRbA3S37R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR (HOB & E153 & HST) HD1 HBIG HQ3 HXF rhoP.
  destruct chk_split_LTBe as ((NE1 & NE2 & NE3 & NE4) & _ & _ & H2 & HW & HB & H3 & H4 & HNX & HLEN).
  apply (ef0t_s1 segsA HTOP_B (JT A Kc rho1) (JT_stable A Kc rho1 HKc) P0_LTBe LH0_LTBe LT_LTBe EX_LTBe S1c_LTBe pFR tp FUELF [LOOPH; CASX] [LOOPH; LOOPX] [LOOPH; LOOPX] [CASX]
           l1_LTBe l2_LTBe l3_LTBe l4_LTBe HNX HLEN
           (runT_some _ _ _ _ RUN1_LTBe NE1) L1ok_LTBe (runT_some _ _ _ _ RUN2f_LTBe NE2) H2 HW HB (runT_some _ _ _ _ RUN3f_LTBe NE3) H3 (runT_some _ _ _ _ RUN4f_LTBe NE4) H4
           (hside_of A Kc rho1 P0_LTBe LT_LTBe tp SIDE_LTBe OBND_LTBe HOB E153 HST) Q).
  intros rhoE. eapply etriple_conseq; [intros w Hw; exact (SPA_JT_JF A Kc rho1 _ rhoE tp w Hw) | intros w Hw; exact Hw |].
  exact (espine_s1c_LTBe keep A Kc rho rho1 tp Q HKc HR HD1 HBIG HQ3 HXF rhoE).
Qed.
End ILTBe.
End F0T_iLTBe.

(* [comment removed for export] *)
Module F0T_bTBf.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf"; "Ebg_TBf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_TBf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0T_bTBf.

