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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel ag af RefillModel.

(* [comment removed for export] *)
Module F0A_i1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i1Bf.I1Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf"; "ED_1Bf_1"; "ED_1Bf_2"; "ED_1Bf_3"; "Ebg_1Bf"; "Edr_1Bf"; "P0_1Bf"; "TD_1Bf_1"; "TD_1Bf_2"; "TD_1Bf_3"; "Xf_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c1Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I1Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S12U1S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S10VA;R4A2S22Vkeep;Vrho1;R4A3S15Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S10VA;R4A2S22Vkeep;Vrho1;R4A3S14Vsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_1Bf : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SaS2S0S0S4SbQ40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3S11R6R5A2SeU1M0S1RbRaR9R8R6S18S1eR4AaSeG0S1RcRbRaR9R7S19S1fR5AaSeG0S1RdRcRbRaR8S1aS20R6AaScReRdRcRbR9S1bR7A7ScRfReRdRcRaS1cR8A7ScR10RfReRdRbS21R9A7S0S15Vsegs;R11S7Vsegs;VJFi;S6R10RfRdA4S1dR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_1Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_1Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_1Bf C3_1Bf Ems_1Bf C4_1Bf TM0_1Bf run4_1Bf RM_1Bf D3_1Bf W3_1Bf EQ3_1Bf NX3b_1Bf RUN4_1Bf L4_1Bf D4_1Bf W4_1Bf EQ4_1Bf
             HeM_1Bf HchkM_1Bf HTM_1Bf FBM_1Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_1Bf.
    apply (f0_s5 1%nat st q_1Bf false TM_1Bf Eq_1Bf EQ_1Bf TQ0_1Bf run5_1Bf RQ_1Bf NX5_1Bf RUN5_1Bf L5_1Bf AXQ_1Bf HeQ_1Bf HchkQ_1Bf HTQ_1Bf FBQ_1Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_1Bf.
    apply (f0_s6 1%nat st false TQ_1Bf Edr_1Bf Xf_1Bf run6_1Bf NX6_1Bf RUN6_1Bf L6_1Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 1%nat st q_1Bf true exits1_1Bf Cert1_1Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_1Bf in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_1Bf_1 C2_1Bf_1 EfD_1Bf_1 ED_1Bf_1 run2_1Bf_1 D2_1Bf_1 W2_1Bf_1 NX2_1Bf_1 EQ2_1Bf_1 RUN2_1Bf_1 L2_1Bf_1 AXD_1Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Bf_1 TDr_1Bf_1 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_1 ENTD_1Bf_1 RUN3_1Bf L3_1Bf NX3_1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1Bf_2 C2_1Bf_2 EfD_1Bf_2 ED_1Bf_2 run2_1Bf_2 D2_1Bf_2 W2_1Bf_2 NX2_1Bf_2 EQ2_1Bf_2 RUN2_1Bf_2 L2_1Bf_2 AXD_1Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Bf_2 TDr_1Bf_2 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_2 ENTD_1Bf_2 RUN3_1Bf L3_1Bf NX3_1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1Bf_3 C2_1Bf_3 EfD_1Bf_3 ED_1Bf_3 run2_1Bf_3 D2_1Bf_3 W2_1Bf_3 NX2_1Bf_3 EQ2_1Bf_3 RUN2_1Bf_3 L2_1Bf_3 AXD_1Bf_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Bf_3 TDr_1Bf_3 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_3 ENTD_1Bf_3 RUN3_1Bf L3_1Bf NX3_1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_1Bf : ltac2:(tb__ "0|1|
S13OF_;SaS2S0S0S4SbQ40A1A1S16OF_;S3R5A1S11R5R4A2SfU1M0S1R9R8R7R5S18S1eR3A9SfG0S1RaR9R8R6S19S1fR4A9SfG0S1RbRaR9R7S1aS20R5A9SdRcRbRaR8S1bR6A6SdRdRcRbR9S1cR7A6SdReRdRcRaS21R8A6S0S14Vsegs;S7Vsegs;VJFi;S6RfReRcA4S1dR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_1Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_1Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_1Bf C3_1Bf Ems_1Bf C4_1Bf TM0_1Bf run4_1Bf RM_1Bf D3_1Bf W3_1Bf EQ3_1Bf NX3b_1Bf RUN4_1Bf L4_1Bf D4_1Bf W4_1Bf EQ4_1Bf
             HeM_1Bf HchkM_1Bf HTM_1Bf FBM_1Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_1Bf.
    apply (ef0_s5 1%nat st q_1Bf false TM_1Bf Eq_1Bf EQ_1Bf TQ0_1Bf run5_1Bf RQ_1Bf NX5_1Bf RUN5_1Bf L5_1Bf AXQ_1Bf HeQ_1Bf HchkQ_1Bf HTQ_1Bf FBQ_1Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_1Bf.
    apply (ef0_s6 1%nat st false TQ_1Bf Edr_1Bf Xf_1Bf run6_1Bf NX6_1Bf RUN6_1Bf L6_1Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 1%nat st q_1Bf true exits1_1Bf ECert1_1Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_1Bf in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_1Bf_1 C2_1Bf_1 EfD_1Bf_1 ED_1Bf_1 run2_1Bf_1 D2_1Bf_1 W2_1Bf_1 NX2_1Bf_1 EQ2_1Bf_1 RUN2_1Bf_1 L2_1Bf_1 AXD_1Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Bf_1 TDr_1Bf_1 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_1 ENTD_1Bf_1 RUN3_1Bf L3_1Bf NX3_1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1Bf_2 C2_1Bf_2 EfD_1Bf_2 ED_1Bf_2 run2_1Bf_2 D2_1Bf_2 W2_1Bf_2 NX2_1Bf_2 EQ2_1Bf_2 RUN2_1Bf_2 L2_1Bf_2 AXD_1Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Bf_2 TDr_1Bf_2 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_2 ENTD_1Bf_2 RUN3_1Bf L3_1Bf NX3_1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1Bf_3 C2_1Bf_3 EfD_1Bf_3 ED_1Bf_3 run2_1Bf_3 D2_1Bf_3 W2_1Bf_3 NX2_1Bf_3 EQ2_1Bf_3 RUN2_1Bf_3 L2_1Bf_3 AXD_1Bf_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Bf_3 TDr_1Bf_3 CD_1Bf Eps_1Bf Ebg_1Bf run3_1Bf AXDr_1Bf_3 ENTD_1Bf_3 RUN3_1Bf L3_1Bf NX3_1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I1Bf.
End F0A_i1Bf.

(* [comment removed for export] *)
Module F0A_i2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i2A.I2A"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A"; "ED_2A_1"; "ED_2A_2"; "ED_2A_3"; "ED_2A_4"; "Ebg_2A"; "Edr_2A"; "P0_2A"; "TD_2A_1"; "TD_2A_2"; "TD_2A_3"; "TD_2A_4"; "Xf_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I2A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
SeU2S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SfS0S0S4S10Q40A1A1ScVA;R4A2S24Vkeep;Vrho1;R4A3S15Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SfS0S0S4S10Q40A1A1ScVA;R4A2S24Vkeep;Vrho1;R4A3S14Vsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_2A : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SfS2S0S0S4S10Q40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3SdR6R5A2SaU2M0S1RbRaR9R8R6S18S1fR4AaSaG0S1RcRbRaR9R7S19S20R5AaSaG0S1RdRcRbRaR8S1aS21R6AaSaG0S1ReRdRcRbR9S1bS22R7AaS11RfReRdRcRaS1cR8A7S11R10RfReRdRbS1dR9A7S11R11R10RfReRcS23RaA7S0S15Vsegs;R12S7Vsegs;VJFi;S6R11R10ReA4S1eR1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_2A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_2A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_2A C3_2A Ems_2A C4_2A TM0_2A run4_2A RM_2A D3_2A W3_2A EQ3_2A NX3b_2A RUN4_2A L4_2A D4_2A W4_2A EQ4_2A
             HeM_2A HchkM_2A HTM_2A FBM_2A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_2A.
    apply (f0_s5 2%nat st q_2A false TM_2A Eq_2A EQ_2A TQ0_2A run5_2A RQ_2A NX5_2A RUN5_2A L5_2A AXQ_2A HeQ_2A HchkQ_2A HTQ_2A FBQ_2A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_2A.
    apply (f0_s6 2%nat st false TQ_2A Edr_2A Xf_2A run6_2A NX6_2A RUN6_2A L6_2A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 2%nat st q_2A true exits1_2A Cert1_2A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_2A in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_2A_1 C2_2A_1 EfD_2A_1 ED_2A_1 run2_2A_1 D2_2A_1 W2_2A_1 NX2_2A_1 EQ2_2A_1 RUN2_2A_1 L2_2A_1 AXD_2A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2A_1 TDr_2A_1 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_1 ENTD_2A_1 RUN3_2A L3_2A NX3_2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2A_2 C2_2A_2 EfD_2A_2 ED_2A_2 run2_2A_2 D2_2A_2 W2_2A_2 NX2_2A_2 EQ2_2A_2 RUN2_2A_2 L2_2A_2 AXD_2A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2A_2 TDr_2A_2 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_2 ENTD_2A_2 RUN3_2A L3_2A NX3_2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2A_3 C2_2A_3 EfD_2A_3 ED_2A_3 run2_2A_3 D2_2A_3 W2_2A_3 NX2_2A_3 EQ2_2A_3 RUN2_2A_3 L2_2A_3 AXD_2A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2A_3 TDr_2A_3 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_3 ENTD_2A_3 RUN3_2A L3_2A NX3_2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2A_4 C2_2A_4 EfD_2A_4 ED_2A_4 run2_2A_4 D2_2A_4 W2_2A_4 NX2_2A_4 EQ2_2A_4 RUN2_2A_4 L2_2A_4 AXD_2A_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2A_4 TDr_2A_4 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_4 ENTD_2A_4 RUN3_2A L3_2A NX3_2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_2A : ltac2:(tb__ "0|1|
S13OF_;SfS2S0S0S4S10Q40A1A1S16OF_;S3R5A1SdR5R4A2SbU2M0S1R9R8R7R5S18S1fR3A9SbG0S1RaR9R8R6S19S20R4A9SbG0S1RbRaR9R7S1aS21R5A9SbG0S1RcRbRaR8S1bS22R6A9S12RdRcRbR9S1cR7A6S12ReRdRcRaS1dR8A6S12RfReRdRbS23R9A6S0S14Vsegs;S7Vsegs;VJFi;S6R10RfRdA4S1eR1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_2A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_2A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_2A C3_2A Ems_2A C4_2A TM0_2A run4_2A RM_2A D3_2A W3_2A EQ3_2A NX3b_2A RUN4_2A L4_2A D4_2A W4_2A EQ4_2A
             HeM_2A HchkM_2A HTM_2A FBM_2A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_2A.
    apply (ef0_s5 2%nat st q_2A false TM_2A Eq_2A EQ_2A TQ0_2A run5_2A RQ_2A NX5_2A RUN5_2A L5_2A AXQ_2A HeQ_2A HchkQ_2A HTQ_2A FBQ_2A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_2A.
    apply (ef0_s6 2%nat st false TQ_2A Edr_2A Xf_2A run6_2A NX6_2A RUN6_2A L6_2A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 2%nat st q_2A true exits1_2A ECert1_2A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_2A in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_2A_1 C2_2A_1 EfD_2A_1 ED_2A_1 run2_2A_1 D2_2A_1 W2_2A_1 NX2_2A_1 EQ2_2A_1 RUN2_2A_1 L2_2A_1 AXD_2A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2A_1 TDr_2A_1 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_1 ENTD_2A_1 RUN3_2A L3_2A NX3_2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2A_2 C2_2A_2 EfD_2A_2 ED_2A_2 run2_2A_2 D2_2A_2 W2_2A_2 NX2_2A_2 EQ2_2A_2 RUN2_2A_2 L2_2A_2 AXD_2A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2A_2 TDr_2A_2 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_2 ENTD_2A_2 RUN3_2A L3_2A NX3_2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2A_3 C2_2A_3 EfD_2A_3 ED_2A_3 run2_2A_3 D2_2A_3 W2_2A_3 NX2_2A_3 EQ2_2A_3 RUN2_2A_3 L2_2A_3 AXD_2A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2A_3 TDr_2A_3 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_3 ENTD_2A_3 RUN3_2A L3_2A NX3_2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2A_4 C2_2A_4 EfD_2A_4 ED_2A_4 run2_2A_4 D2_2A_4 W2_2A_4 NX2_2A_4 EQ2_2A_4 RUN2_2A_4 L2_2A_4 AXD_2A_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2A_4 TDr_2A_4 CD_2A Eps_2A Ebg_2A run3_2A AXDr_2A_4 ENTD_2A_4 RUN3_2A L3_2A NX3_2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I2A.
End F0A_i2A.

(* [comment removed for export] *)
Module F0A_i1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i1Be.I1Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be"; "ED_1Be_1"; "ED_1Be_2"; "ED_1Be_3"; "Ebg_1Be"; "Edr_1Be"; "P0_1Be"; "TD_1Be_1"; "TD_1Be_2"; "TD_1Be_3"; "Xf_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I1Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 1.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S12U1S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S10VA;R4A2S22Vkeep;Vrho1;R4A3S15Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S10VA;R4A2S22Vkeep;Vrho1;R4A3S14Vsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_1Be : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SaS2S0S0S4SbQ40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3S11R6R5A2SeU1M0S1RbRaR9R8R6S18S1eR4AaSeG0S1RcRbRaR9R7S19S1fR5AaSeG0S1RdRcRbRaR8S1aS20R6AaScReRdRcRbR9S1bR7A7ScRfReRdRcRaS1cR8A7ScR10RfReRdRbS21R9A7S0S15Vsegs;R11S7Vsegs;VJFi;S6R10RfRdA4S1dR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_1Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_1Be C3_1Be Ems_1Be C4_1Be TM0_1Be run4_1Be RM_1Be D3_1Be W3_1Be EQ3_1Be NX3b_1Be RUN4_1Be L4_1Be D4_1Be W4_1Be EQ4_1Be
             HeM_1Be HchkM_1Be HTM_1Be FBM_1Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_1Be.
    apply (f0_s5 1%nat st q_1Be false TM_1Be Eq_1Be EQ_1Be TQ0_1Be run5_1Be RQ_1Be NX5_1Be RUN5_1Be L5_1Be AXQ_1Be HeQ_1Be HchkQ_1Be HTQ_1Be FBQ_1Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_1Be.
    apply (f0_s6 1%nat st false TQ_1Be Edr_1Be Xf_1Be run6_1Be NX6_1Be RUN6_1Be L6_1Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 1%nat st q_1Be true exits1_1Be Cert1_1Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_1Be_1 C2_1Be_1 EfD_1Be_1 ED_1Be_1 run2_1Be_1 D2_1Be_1 W2_1Be_1 NX2_1Be_1 EQ2_1Be_1 RUN2_1Be_1 L2_1Be_1 AXD_1Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Be_1 TDr_1Be_1 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_1 ENTD_1Be_1 RUN3_1Be L3_1Be NX3_1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1Be_2 C2_1Be_2 EfD_1Be_2 ED_1Be_2 run2_1Be_2 D2_1Be_2 W2_1Be_2 NX2_1Be_2 EQ2_1Be_2 RUN2_1Be_2 L2_1Be_2 AXD_1Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Be_2 TDr_1Be_2 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_2 ENTD_1Be_2 RUN3_1Be L3_1Be NX3_1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1Be_3 C2_1Be_3 EfD_1Be_3 ED_1Be_3 run2_1Be_3 D2_1Be_3 W2_1Be_3 NX2_1Be_3 EQ2_1Be_3 RUN2_1Be_3 L2_1Be_3 AXD_1Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1Be_3 TDr_1Be_3 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_3 ENTD_1Be_3 RUN3_1Be L3_1Be NX3_1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_1Be : ltac2:(tb__ "0|1|
S13OF_;SaS2S0S0S4SbQ40A1A1S16OF_;S3R5A1S11R5R4A2SfU1M0S1R9R8R7R5S18S1eR3A9SfG0S1RaR9R8R6S19S1fR4A9SfG0S1RbRaR9R7S1aS20R5A9SdRcRbRaR8S1bR6A6SdRdRcRbR9S1cR7A6SdReRdRcRaS21R8A6S0S14Vsegs;S7Vsegs;VJFi;S6RfReRcA4S1dR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_1Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_1Be C3_1Be Ems_1Be C4_1Be TM0_1Be run4_1Be RM_1Be D3_1Be W3_1Be EQ3_1Be NX3b_1Be RUN4_1Be L4_1Be D4_1Be W4_1Be EQ4_1Be
             HeM_1Be HchkM_1Be HTM_1Be FBM_1Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_1Be.
    apply (ef0_s5 1%nat st q_1Be false TM_1Be Eq_1Be EQ_1Be TQ0_1Be run5_1Be RQ_1Be NX5_1Be RUN5_1Be L5_1Be AXQ_1Be HeQ_1Be HchkQ_1Be HTQ_1Be FBQ_1Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_1Be.
    apply (ef0_s6 1%nat st false TQ_1Be Edr_1Be Xf_1Be run6_1Be NX6_1Be RUN6_1Be L6_1Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 1%nat st q_1Be true exits1_1Be ECert1_1Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_1Be_1 C2_1Be_1 EfD_1Be_1 ED_1Be_1 run2_1Be_1 D2_1Be_1 W2_1Be_1 NX2_1Be_1 EQ2_1Be_1 RUN2_1Be_1 L2_1Be_1 AXD_1Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Be_1 TDr_1Be_1 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_1 ENTD_1Be_1 RUN3_1Be L3_1Be NX3_1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1Be_2 C2_1Be_2 EfD_1Be_2 ED_1Be_2 run2_1Be_2 D2_1Be_2 W2_1Be_2 NX2_1Be_2 EQ2_1Be_2 RUN2_1Be_2 L2_1Be_2 AXD_1Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Be_2 TDr_1Be_2 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_2 ENTD_1Be_2 RUN3_1Be L3_1Be NX3_1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1Be_3 C2_1Be_3 EfD_1Be_3 ED_1Be_3 run2_1Be_3 D2_1Be_3 W2_1Be_3 NX2_1Be_3 EQ2_1Be_3 RUN2_1Be_3 L2_1Be_3 AXD_1Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1Be_3 TDr_1Be_3 CD_1Be Eps_1Be Ebg_1Be run3_1Be AXDr_1Be_3 ENTD_1Be_3 RUN3_1Be L3_1Be NX3_1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I1Be.
End F0A_i1Be.

(* [comment removed for export] *)
Module F0A_skelC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Datatypes"; "list"; "false"; "bool"; "true"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma entF_SPA : ltac2:(tb__ "0|0|
S5S7S7S2S9SdQ40A1A1S10S13SbS15R5R4A2ScA3S6S0S1R7A3S4S0R8R7R5R4R3A6S19R6S18S1S8R8A1S8R7A1A3A2S2S14S4S0RaR8R1R6R5A6S3S1R7R1A3A2Trho';F_;F_;F_;Fw;Ftp;Frho;FT;FL;FJ;").
Proof.
  intros J L T rho tp w H HST HS rho'. unfold entsF in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [HE HI].
  split; [exact (SPA_entails segsA J GW L T _ rho tp w HE HI HST HS) | apply rho_sub_agree; exact HI].
Qed.
Lemma entF_cont : ltac2:(tb__ "0|0|
S5S10OF_;S7S7S2S9SdQ40A1A1S11S13SbS15R5R4A2ScA3S6S0S1R8A3S2S3S1R6R1A3SfS0RaS4S0RbR8R2R6A5R5A4F_;Frho';SfS0R9S4S0RaR8R6R5A5R4A4F_;F_;F_;FQ;Ftp;Frho;FT;FL;Fok;FJ;").
Proof.
  intros J ok L T rho tp Q H HST HC. eapply triple_conseq; [| intros w Hw; exact Hw | apply (HC (rho_sub rho (infer_sub GW (ax_S L) (ax_S T))))].
  - intros w Hw. exact (proj1 (entF_SPA J L T rho tp w H HST Hw)).
  - apply rho_sub_agree. unfold entsF in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ HI]. exact HI.
Qed.
Lemma entF_econt : ltac2:(tb__ "0|0|
S5S7S7S2S9SdQ40A1A1S10OF_;S13SbS15R5R4A2ScA3S6S0S1R7A3S2S3S1R6R1A3SeS0S4S0RaR8R2R6A5R5A3F_;Frho';SeS0S4S0R9R8R6R5A5R4A3F_;F_;F_;FQ;Ftp;Frho;FT;FL;FJ;").
Proof.
  intros J L T rho tp Q H HST HC. eapply etriple_conseq; [| intros w Hw; exact Hw | apply (HC (rho_sub rho (infer_sub GW (ax_S L) (ax_S T))))].
  - intros w Hw. exact (proj1 (entF_SPA J L T rho tp w H HST Hw)).
  - apply rho_sub_agree. unfold entsF in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ HI]. exact HI.
Qed.

Definition HRF (nW : nat) (st : ustop) (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (EC TR : axst) (Q : assn) : Prop := ltac2:(tb__ "0|1|
S2S9SdQ40A1A1M0S2S2G0S17Vkeep;Vrho1;R3A3SfS0Vok;S4S0S12VnW;Vst;SaS16VA;Z18A2VKc;R4A6VTR;R3R2A5VQ;A4F_;Ftp';FrhoX;Frho1';SfS0Vok;S4S0S12VnW;Vst;SaVA;VKc;Vrho1;A6VEC;R3R2A5VQ;A4F_;Ftp;FrhoE;").
Definition HRFE (nW : nat) (st : ustop) (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (EC TR : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|1|
S2S9SdQ40A1A1M0S2S2G0S17Vkeep;Vrho1;R3A3SeS0S4S0S12VnW;Vst;SaS16VA;Z18A2VKc;R4A6VTR;R3R2A5VQ;A3F_;Ftp';FrhoX;Frho1';SeS0S4S0S12VnW;Vst;SaVA;VKc;Vrho1;A6VEC;R3R2A5VQ;A3F_;Ftp;FrhoE;").
End F0A_skelC.

(* [comment removed for export] *)
Module F0A_i2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i2Be.I2Be"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be"; "ED_2Be_1"; "ED_2Be_2"; "ED_2Be_3"; "ED_2Be_4"; "Ebg_2Be"; "Edr_2Be"; "P0_2Be"; "TD_2Be_1"; "TD_2Be_2"; "TD_2Be_3"; "TD_2Be_4"; "Xf_2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I2Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
SeU2S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SfS0S0S4S10Q40A1A1ScVA;R4A2S24Vkeep;Vrho1;R4A3S15Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SfS0S0S4S10Q40A1A1ScVA;R4A2S24Vkeep;Vrho1;R4A3S14Vsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_2Be : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SfS2S0S0S4S10Q40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3SdR6R5A2SaU2M0S1RbRaR9R8R6S18S1fR4AaSaG0S1RcRbRaR9R7S19S20R5AaSaG0S1RdRcRbRaR8S1aS21R6AaSaG0S1ReRdRcRbR9S1bS22R7AaS11RfReRdRcRaS1cR8A7S11R10RfReRdRbS1dR9A7S11R11R10RfReRcS23RaA7S0S15Vsegs;R12S7Vsegs;VJFi;S6R11R10ReA4S1eR1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_2Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_2Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_2Be C3_2Be Ems_2Be C4_2Be TM0_2Be run4_2Be RM_2Be D3_2Be W3_2Be EQ3_2Be NX3b_2Be RUN4_2Be L4_2Be D4_2Be W4_2Be EQ4_2Be
             HeM_2Be HchkM_2Be HTM_2Be FBM_2Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_2Be.
    apply (f0_s5 2%nat st q_2Be false TM_2Be Eq_2Be EQ_2Be TQ0_2Be run5_2Be RQ_2Be NX5_2Be RUN5_2Be L5_2Be AXQ_2Be HeQ_2Be HchkQ_2Be HTQ_2Be FBQ_2Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_2Be.
    apply (f0_s6 2%nat st false TQ_2Be Edr_2Be Xf_2Be run6_2Be NX6_2Be RUN6_2Be L6_2Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 2%nat st q_2Be true exits1_2Be Cert1_2Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_2Be in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_2Be_1 C2_2Be_1 EfD_2Be_1 ED_2Be_1 run2_2Be_1 D2_2Be_1 W2_2Be_1 NX2_2Be_1 EQ2_2Be_1 RUN2_2Be_1 L2_2Be_1 AXD_2Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Be_1 TDr_2Be_1 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_1 ENTD_2Be_1 RUN3_2Be L3_2Be NX3_2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Be_2 C2_2Be_2 EfD_2Be_2 ED_2Be_2 run2_2Be_2 D2_2Be_2 W2_2Be_2 NX2_2Be_2 EQ2_2Be_2 RUN2_2Be_2 L2_2Be_2 AXD_2Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Be_2 TDr_2Be_2 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_2 ENTD_2Be_2 RUN3_2Be L3_2Be NX3_2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Be_3 C2_2Be_3 EfD_2Be_3 ED_2Be_3 run2_2Be_3 D2_2Be_3 W2_2Be_3 NX2_2Be_3 EQ2_2Be_3 RUN2_2Be_3 L2_2Be_3 AXD_2Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Be_3 TDr_2Be_3 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_3 ENTD_2Be_3 RUN3_2Be L3_2Be NX3_2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Be_4 C2_2Be_4 EfD_2Be_4 ED_2Be_4 run2_2Be_4 D2_2Be_4 W2_2Be_4 NX2_2Be_4 EQ2_2Be_4 RUN2_2Be_4 L2_2Be_4 AXD_2Be_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Be_4 TDr_2Be_4 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_4 ENTD_2Be_4 RUN3_2Be L3_2Be NX3_2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_2Be : ltac2:(tb__ "0|1|
S13OF_;SfS2S0S0S4S10Q40A1A1S16OF_;S3R5A1SdR5R4A2SbU2M0S1R9R8R7R5S18S1fR3A9SbG0S1RaR9R8R6S19S20R4A9SbG0S1RbRaR9R7S1aS21R5A9SbG0S1RcRbRaR8S1bS22R6A9S12RdRcRbR9S1cR7A6S12ReRdRcRaS1dR8A6S12RfReRdRbS23R9A6S0S14Vsegs;S7Vsegs;VJFi;S6R10RfRdA4S1eR1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_2Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_2Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_2Be C3_2Be Ems_2Be C4_2Be TM0_2Be run4_2Be RM_2Be D3_2Be W3_2Be EQ3_2Be NX3b_2Be RUN4_2Be L4_2Be D4_2Be W4_2Be EQ4_2Be
             HeM_2Be HchkM_2Be HTM_2Be FBM_2Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_2Be.
    apply (ef0_s5 2%nat st q_2Be false TM_2Be Eq_2Be EQ_2Be TQ0_2Be run5_2Be RQ_2Be NX5_2Be RUN5_2Be L5_2Be AXQ_2Be HeQ_2Be HchkQ_2Be HTQ_2Be FBQ_2Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_2Be.
    apply (ef0_s6 2%nat st false TQ_2Be Edr_2Be Xf_2Be run6_2Be NX6_2Be RUN6_2Be L6_2Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 2%nat st q_2Be true exits1_2Be ECert1_2Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_2Be in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_2Be_1 C2_2Be_1 EfD_2Be_1 ED_2Be_1 run2_2Be_1 D2_2Be_1 W2_2Be_1 NX2_2Be_1 EQ2_2Be_1 RUN2_2Be_1 L2_2Be_1 AXD_2Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Be_1 TDr_2Be_1 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_1 ENTD_2Be_1 RUN3_2Be L3_2Be NX3_2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Be_2 C2_2Be_2 EfD_2Be_2 ED_2Be_2 run2_2Be_2 D2_2Be_2 W2_2Be_2 NX2_2Be_2 EQ2_2Be_2 RUN2_2Be_2 L2_2Be_2 AXD_2Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Be_2 TDr_2Be_2 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_2 ENTD_2Be_2 RUN3_2Be L3_2Be NX3_2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Be_3 C2_2Be_3 EfD_2Be_3 ED_2Be_3 run2_2Be_3 D2_2Be_3 W2_2Be_3 NX2_2Be_3 EQ2_2Be_3 RUN2_2Be_3 L2_2Be_3 AXD_2Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Be_3 TDr_2Be_3 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_3 ENTD_2Be_3 RUN3_2Be L3_2Be NX3_2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Be_4 C2_2Be_4 EfD_2Be_4 ED_2Be_4 run2_2Be_4 D2_2Be_4 W2_2Be_4 NX2_2Be_4 EQ2_2Be_4 RUN2_2Be_4 L2_2Be_4 AXD_2Be_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Be_4 TDr_2Be_4 CD_2Be Eps_2Be Ebg_2Be run3_2Be AXDr_2Be_4 ENTD_2Be_4 RUN3_2Be L3_2Be NX3_2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I2Be.
End F0A_i2Be.

(* [comment removed for export] *)
Module F0A_i2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_i2Bf.I2Bf"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf"; "ED_2Bf_1"; "ED_2Bf_2"; "ED_2Bf_3"; "ED_2Bf_4"; "Ebg_2Bf"; "Edr_2Bf"; "P0_2Bf"; "TD_2Bf_1"; "TD_2Bf_2"; "TD_2Bf_3"; "TD_2Bf_4"; "Xf_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ag.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ag.F0A_c2Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I2Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 2.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
SeU2S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SfS0S0S4S10Q40A1A1ScVA;R4A2S24Vkeep;Vrho1;R4A3S15Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SfS0S0S4S10Q40A1A1ScVA;R4A2S24Vkeep;Vrho1;R4A3S14Vsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_2Bf : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SfS2S0S0S4S10Q40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3SdR6R5A2SaU2M0S1RbRaR9R8R6S18S1fR4AaSaG0S1RcRbRaR9R7S19S20R5AaSaG0S1RdRcRbRaR8S1aS21R6AaSaG0S1ReRdRcRbR9S1bS22R7AaS11RfReRdRcRaS1cR8A7S11R10RfReRdRbS1dR9A7S11R11R10RfReRcS23RaA7S0S15Vsegs;R12S7Vsegs;VJFi;S6R11R10ReA4S1eR1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_2Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_2Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_2Bf C3_2Bf Ems_2Bf C4_2Bf TM0_2Bf run4_2Bf RM_2Bf D3_2Bf W3_2Bf EQ3_2Bf NX3b_2Bf RUN4_2Bf L4_2Bf D4_2Bf W4_2Bf EQ4_2Bf
             HeM_2Bf HchkM_2Bf HTM_2Bf FBM_2Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_2Bf.
    apply (f0_s5 2%nat st q_2Bf false TM_2Bf Eq_2Bf EQ_2Bf TQ0_2Bf run5_2Bf RQ_2Bf NX5_2Bf RUN5_2Bf L5_2Bf AXQ_2Bf HeQ_2Bf HchkQ_2Bf HTQ_2Bf FBQ_2Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_2Bf.
    apply (f0_s6 2%nat st false TQ_2Bf Edr_2Bf Xf_2Bf run6_2Bf NX6_2Bf RUN6_2Bf L6_2Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 2%nat st q_2Bf true exits1_2Bf Cert1_2Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_2Bf in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_2Bf_1 C2_2Bf_1 EfD_2Bf_1 ED_2Bf_1 run2_2Bf_1 D2_2Bf_1 W2_2Bf_1 NX2_2Bf_1 EQ2_2Bf_1 RUN2_2Bf_1 L2_2Bf_1 AXD_2Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Bf_1 TDr_2Bf_1 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_1 ENTD_2Bf_1 RUN3_2Bf L3_2Bf NX3_2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Bf_2 C2_2Bf_2 EfD_2Bf_2 ED_2Bf_2 run2_2Bf_2 D2_2Bf_2 W2_2Bf_2 NX2_2Bf_2 EQ2_2Bf_2 RUN2_2Bf_2 L2_2Bf_2 AXD_2Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Bf_2 TDr_2Bf_2 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_2 ENTD_2Bf_2 RUN3_2Bf L3_2Bf NX3_2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Bf_3 C2_2Bf_3 EfD_2Bf_3 ED_2Bf_3 run2_2Bf_3 D2_2Bf_3 W2_2Bf_3 NX2_2Bf_3 EQ2_2Bf_3 RUN2_2Bf_3 L2_2Bf_3 AXD_2Bf_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Bf_3 TDr_2Bf_3 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_3 ENTD_2Bf_3 RUN3_2Bf L3_2Bf NX3_2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_2Bf_4 C2_2Bf_4 EfD_2Bf_4 ED_2Bf_4 run2_2Bf_4 D2_2Bf_4 W2_2Bf_4 NX2_2Bf_4 EQ2_2Bf_4 RUN2_2Bf_4 L2_2Bf_4 AXD_2Bf_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_2Bf_4 TDr_2Bf_4 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_4 ENTD_2Bf_4 RUN3_2Bf L3_2Bf NX3_2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_2Bf : ltac2:(tb__ "0|1|
S13OF_;SfS2S0S0S4S10Q40A1A1S16OF_;S3R5A1SdR5R4A2SbU2M0S1R9R8R7R5S18S1fR3A9SbG0S1RaR9R8R6S19S20R4A9SbG0S1RbRaR9R7S1aS21R5A9SbG0S1RcRbRaR8S1bS22R6A9S12RdRcRbR9S1cR7A6S12ReRdRcRaS1dR8A6S12RfReRdRbS23R9A6S0S14Vsegs;S7Vsegs;VJFi;S6R10RfRdA4S1eR1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_2Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_2Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_2Bf C3_2Bf Ems_2Bf C4_2Bf TM0_2Bf run4_2Bf RM_2Bf D3_2Bf W3_2Bf EQ3_2Bf NX3b_2Bf RUN4_2Bf L4_2Bf D4_2Bf W4_2Bf EQ4_2Bf
             HeM_2Bf HchkM_2Bf HTM_2Bf FBM_2Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_2Bf.
    apply (ef0_s5 2%nat st q_2Bf false TM_2Bf Eq_2Bf EQ_2Bf TQ0_2Bf run5_2Bf RQ_2Bf NX5_2Bf RUN5_2Bf L5_2Bf AXQ_2Bf HeQ_2Bf HchkQ_2Bf HTQ_2Bf FBQ_2Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_2Bf.
    apply (ef0_s6 2%nat st false TQ_2Bf Edr_2Bf Xf_2Bf run6_2Bf NX6_2Bf RUN6_2Bf L6_2Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 2%nat st q_2Bf true exits1_2Bf ECert1_2Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_2Bf in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_2Bf_1 C2_2Bf_1 EfD_2Bf_1 ED_2Bf_1 run2_2Bf_1 D2_2Bf_1 W2_2Bf_1 NX2_2Bf_1 EQ2_2Bf_1 RUN2_2Bf_1 L2_2Bf_1 AXD_2Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Bf_1 TDr_2Bf_1 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_1 ENTD_2Bf_1 RUN3_2Bf L3_2Bf NX3_2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Bf_2 C2_2Bf_2 EfD_2Bf_2 ED_2Bf_2 run2_2Bf_2 D2_2Bf_2 W2_2Bf_2 NX2_2Bf_2 EQ2_2Bf_2 RUN2_2Bf_2 L2_2Bf_2 AXD_2Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Bf_2 TDr_2Bf_2 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_2 ENTD_2Bf_2 RUN3_2Bf L3_2Bf NX3_2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Bf_3 C2_2Bf_3 EfD_2Bf_3 ED_2Bf_3 run2_2Bf_3 D2_2Bf_3 W2_2Bf_3 NX2_2Bf_3 EQ2_2Bf_3 RUN2_2Bf_3 L2_2Bf_3 AXD_2Bf_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Bf_3 TDr_2Bf_3 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_3 ENTD_2Bf_3 RUN3_2Bf L3_2Bf NX3_2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_2Bf_4 C2_2Bf_4 EfD_2Bf_4 ED_2Bf_4 run2_2Bf_4 D2_2Bf_4 W2_2Bf_4 NX2_2Bf_4 EQ2_2Bf_4 RUN2_2Bf_4 L2_2Bf_4 AXD_2Bf_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_2Bf_4 TDr_2Bf_4 CD_2Bf Eps_2Bf Ebg_2Bf run3_2Bf AXDr_2Bf_4 ENTD_2Bf_4 RUN3_2Bf L3_2Bf NX3_2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I2Bf.
End F0A_i2Bf.

