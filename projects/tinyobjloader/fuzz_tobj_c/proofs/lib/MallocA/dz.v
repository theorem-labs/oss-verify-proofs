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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar ae ah.

(* [comment removed for export] *)
Module F0A_iL0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0Be.IL0Be"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Be"; "ED_L0Be_1"; "ED_L0Be_2"; "Ebg_L0Be"; "Edr_L0Be"; "P0_L0Be"; "TD_L0Be_1"; "TD_L0Be_2"; "Xf_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL0Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S1fU0S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3S10Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3SfVsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_L0Be : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0Be C3_L0Be Ems_L0Be C4_L0Be TM0_L0Be run4_L0Be RM_L0Be D3_L0Be W3_L0Be EQ3_L0Be NX3b_L0Be RUN4_L0Be L4_L0Be D4_L0Be W4_L0Be EQ4_L0Be
             HeM_L0Be HchkM_L0Be HTM_L0Be FBM_L0Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0Be.
    apply (f0_s5 0%nat st q_L0Be false TM_L0Be Eq_L0Be EQ_L0Be TQ0_L0Be run5_L0Be RQ_L0Be NX5_L0Be RUN5_L0Be L5_L0Be AXQ_L0Be HeQ_L0Be HchkQ_L0Be HTQ_L0Be FBQ_L0Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0Be.
    apply (f0_s6 0%nat st false TQ_L0Be Edr_L0Be Xf_L0Be run6_L0Be NX6_L0Be RUN6_L0Be L6_L0Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true P0_L0Be exits1_L0Be Cert1_L0Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0Be_1 C2_L0Be_1 EfD_L0Be_1 ED_L0Be_1 run2_L0Be_1 D2_L0Be_1 W2_L0Be_1 NX2_L0Be_1 EQ2_L0Be_1 RUN2_L0Be_1 L2_L0Be_1 AXD_L0Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Be_1 TDr_L0Be_1 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_1 ENTD_L0Be_1 RUN3_L0Be L3_L0Be NX3_L0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0Be_2 C2_L0Be_2 EfD_L0Be_2 ED_L0Be_2 run2_L0Be_2 D2_L0Be_2 W2_L0Be_2 NX2_L0Be_2 EQ2_L0Be_2 RUN2_L0Be_2 L2_L0Be_2 AXD_L0Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Be_2 TDr_L0Be_2 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_2 ENTD_L0Be_2 RUN3_L0Be L3_L0Be NX3_L0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L0Be : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0Be C3_L0Be Ems_L0Be C4_L0Be TM0_L0Be run4_L0Be RM_L0Be D3_L0Be W3_L0Be EQ3_L0Be NX3b_L0Be RUN4_L0Be L4_L0Be D4_L0Be W4_L0Be EQ4_L0Be
             HeM_L0Be HchkM_L0Be HTM_L0Be FBM_L0Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0Be.
    apply (ef0_s5 0%nat st q_L0Be false TM_L0Be Eq_L0Be EQ_L0Be TQ0_L0Be run5_L0Be RQ_L0Be NX5_L0Be RUN5_L0Be L5_L0Be AXQ_L0Be HeQ_L0Be HchkQ_L0Be HTQ_L0Be FBQ_L0Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0Be.
    apply (ef0_s6 0%nat st false TQ_L0Be Edr_L0Be Xf_L0Be run6_L0Be NX6_L0Be RUN6_L0Be L6_L0Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true P0_L0Be exits1_L0Be (eq_refl : (GW <=? ss_next (ax_S P0_L0Be))%positive = true) ECert1_L0Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0Be_1 C2_L0Be_1 EfD_L0Be_1 ED_L0Be_1 run2_L0Be_1 D2_L0Be_1 W2_L0Be_1 NX2_L0Be_1 EQ2_L0Be_1 RUN2_L0Be_1 L2_L0Be_1 AXD_L0Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Be_1 TDr_L0Be_1 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_1 ENTD_L0Be_1 RUN3_L0Be L3_L0Be NX3_L0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0Be_2 C2_L0Be_2 EfD_L0Be_2 ED_L0Be_2 run2_L0Be_2 D2_L0Be_2 W2_L0Be_2 NX2_L0Be_2 EQ2_L0Be_2 RUN2_L0Be_2 L2_L0Be_2 AXD_L0Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Be_2 TDr_L0Be_2 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_2 ENTD_L0Be_2 RUN3_L0Be L3_L0Be NX3_L0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL0Be.
End F0A_iL0Be.

(* [comment removed for export] *)
Module F0A_iL0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0A.IL0A"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0A"; "ED_L0A_1"; "ED_L0A_2"; "Ebg_L0A"; "Edr_L0A"; "P0_L0A"; "TD_L0A_1"; "TD_L0A_2"; "Xf_L0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL0A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S1fU0S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3S10Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3SfVsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_L0A : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0A C3_L0A Ems_L0A C4_L0A TM0_L0A run4_L0A RM_L0A D3_L0A W3_L0A EQ3_L0A NX3b_L0A RUN4_L0A L4_L0A D4_L0A W4_L0A EQ4_L0A
             HeM_L0A HchkM_L0A HTM_L0A FBM_L0A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0A.
    apply (f0_s5 0%nat st q_L0A false TM_L0A Eq_L0A EQ_L0A TQ0_L0A run5_L0A RQ_L0A NX5_L0A RUN5_L0A L5_L0A AXQ_L0A HeQ_L0A HchkQ_L0A HTQ_L0A FBQ_L0A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0A.
    apply (f0_s6 0%nat st false TQ_L0A Edr_L0A Xf_L0A run6_L0A NX6_L0A RUN6_L0A L6_L0A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true P0_L0A exits1_L0A Cert1_L0A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0A_1 C2_L0A_1 EfD_L0A_1 ED_L0A_1 run2_L0A_1 D2_L0A_1 W2_L0A_1 NX2_L0A_1 EQ2_L0A_1 RUN2_L0A_1 L2_L0A_1 AXD_L0A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0A_1 TDr_L0A_1 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_1 ENTD_L0A_1 RUN3_L0A L3_L0A NX3_L0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0A_2 C2_L0A_2 EfD_L0A_2 ED_L0A_2 run2_L0A_2 D2_L0A_2 W2_L0A_2 NX2_L0A_2 EQ2_L0A_2 RUN2_L0A_2 L2_L0A_2 AXD_L0A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0A_2 TDr_L0A_2 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_2 ENTD_L0A_2 RUN3_L0A L3_L0A NX3_L0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L0A : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0A C3_L0A Ems_L0A C4_L0A TM0_L0A run4_L0A RM_L0A D3_L0A W3_L0A EQ3_L0A NX3b_L0A RUN4_L0A L4_L0A D4_L0A W4_L0A EQ4_L0A
             HeM_L0A HchkM_L0A HTM_L0A FBM_L0A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0A.
    apply (ef0_s5 0%nat st q_L0A false TM_L0A Eq_L0A EQ_L0A TQ0_L0A run5_L0A RQ_L0A NX5_L0A RUN5_L0A L5_L0A AXQ_L0A HeQ_L0A HchkQ_L0A HTQ_L0A FBQ_L0A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0A.
    apply (ef0_s6 0%nat st false TQ_L0A Edr_L0A Xf_L0A run6_L0A NX6_L0A RUN6_L0A L6_L0A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true P0_L0A exits1_L0A (eq_refl : (GW <=? ss_next (ax_S P0_L0A))%positive = true) ECert1_L0A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0A_1 C2_L0A_1 EfD_L0A_1 ED_L0A_1 run2_L0A_1 D2_L0A_1 W2_L0A_1 NX2_L0A_1 EQ2_L0A_1 RUN2_L0A_1 L2_L0A_1 AXD_L0A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0A_1 TDr_L0A_1 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_1 ENTD_L0A_1 RUN3_L0A L3_L0A NX3_L0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0A_2 C2_L0A_2 EfD_L0A_2 ED_L0A_2 run2_L0A_2 D2_L0A_2 W2_L0A_2 NX2_L0A_2 EQ2_L0A_2 RUN2_L0A_2 L2_L0A_2 AXD_L0A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0A_2 TDr_L0A_2 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_2 ENTD_L0A_2 RUN3_L0A L3_L0A NX3_L0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL0A.
End F0A_iL0A.

(* [comment removed for export] *)
Module F0A_iL1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL1Be.IL1Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be"; "ED_L1Be_1"; "ED_L1Be_2"; "ED_L1Be_3"; "Ebg_L1Be"; "Edr_L1Be"; "P0_L1Be"; "TD_L1Be_1"; "TD_L1Be_2"; "TD_L1Be_3"; "Xf_L1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL1Be.
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

Theorem free_spine_L1Be : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SaS2S0S0S4SbQ40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3S11R6R5A2SeU1M0S1RbRaR9R8R6S18S1eR4AaSeG0S1RcRbRaR9R7S19S1fR5AaSeG0S1RdRcRbRaR8S1aS20R6AaScReRdRcRbR9S1bR7A7ScRfReRdRcRaS1cR8A7ScR10RfReRdRbS21R9A7S0S15Vsegs;R11S7Vsegs;VJFi;S6R10RfRdA4S1dR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L1Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_L1Be C3_L1Be Ems_L1Be C4_L1Be TM0_L1Be run4_L1Be RM_L1Be D3_L1Be W3_L1Be EQ3_L1Be NX3b_L1Be RUN4_L1Be L4_L1Be D4_L1Be W4_L1Be EQ4_L1Be
             HeM_L1Be HchkM_L1Be HTM_L1Be FBM_L1Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L1Be.
    apply (f0_s5 1%nat st q_L1Be false TM_L1Be Eq_L1Be EQ_L1Be TQ0_L1Be run5_L1Be RQ_L1Be NX5_L1Be RUN5_L1Be L5_L1Be AXQ_L1Be HeQ_L1Be HchkQ_L1Be HTQ_L1Be FBQ_L1Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L1Be.
    apply (f0_s6 1%nat st false TQ_L1Be Edr_L1Be Xf_L1Be run6_L1Be NX6_L1Be RUN6_L1Be L6_L1Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true P0_L1Be exits1_L1Be Cert1_L1Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_L1Be_1 C2_L1Be_1 EfD_L1Be_1 ED_L1Be_1 run2_L1Be_1 D2_L1Be_1 W2_L1Be_1 NX2_L1Be_1 EQ2_L1Be_1 RUN2_L1Be_1 L2_L1Be_1 AXD_L1Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_1 TDr_L1Be_1 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_1 ENTD_L1Be_1 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Be_2 C2_L1Be_2 EfD_L1Be_2 ED_L1Be_2 run2_L1Be_2 D2_L1Be_2 W2_L1Be_2 NX2_L1Be_2 EQ2_L1Be_2 RUN2_L1Be_2 L2_L1Be_2 AXD_L1Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_2 TDr_L1Be_2 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_2 ENTD_L1Be_2 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Be_3 C2_L1Be_3 EfD_L1Be_3 ED_L1Be_3 run2_L1Be_3 D2_L1Be_3 W2_L1Be_3 NX2_L1Be_3 EQ2_L1Be_3 RUN2_L1Be_3 L2_L1Be_3 AXD_L1Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Be_3 TDr_L1Be_3 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_3 ENTD_L1Be_3 RUN3_L1Be L3_L1Be NX3_L1Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L1Be : ltac2:(tb__ "0|1|
S13OF_;SaS2S0S0S4SbQ40A1A1S16OF_;S3R5A1S11R5R4A2SfU1M0S1R9R8R7R5S18S1eR3A9SfG0S1RaR9R8R6S19S1fR4A9SfG0S1RbRaR9R7S1aS20R5A9SdRcRbRaR8S1bR6A6SdRdRcRbR9S1cR7A6SdReRdRcRaS21R8A6S0S14Vsegs;S7Vsegs;VJFi;S6RfReRcA4S1dR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L1Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L1Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_L1Be C3_L1Be Ems_L1Be C4_L1Be TM0_L1Be run4_L1Be RM_L1Be D3_L1Be W3_L1Be EQ3_L1Be NX3b_L1Be RUN4_L1Be L4_L1Be D4_L1Be W4_L1Be EQ4_L1Be
             HeM_L1Be HchkM_L1Be HTM_L1Be FBM_L1Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L1Be.
    apply (ef0_s5 1%nat st q_L1Be false TM_L1Be Eq_L1Be EQ_L1Be TQ0_L1Be run5_L1Be RQ_L1Be NX5_L1Be RUN5_L1Be L5_L1Be AXQ_L1Be HeQ_L1Be HchkQ_L1Be HTQ_L1Be FBQ_L1Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L1Be.
    apply (ef0_s6 1%nat st false TQ_L1Be Edr_L1Be Xf_L1Be run6_L1Be NX6_L1Be RUN6_L1Be L6_L1Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true P0_L1Be exits1_L1Be (eq_refl : (GW <=? ss_next (ax_S P0_L1Be))%positive = true) ECert1_L1Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L1Be in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_L1Be_1 C2_L1Be_1 EfD_L1Be_1 ED_L1Be_1 run2_L1Be_1 D2_L1Be_1 W2_L1Be_1 NX2_L1Be_1 EQ2_L1Be_1 RUN2_L1Be_1 L2_L1Be_1 AXD_L1Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_1 TDr_L1Be_1 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_1 ENTD_L1Be_1 RUN3_L1Be L3_L1Be NX3_L1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Be_2 C2_L1Be_2 EfD_L1Be_2 ED_L1Be_2 run2_L1Be_2 D2_L1Be_2 W2_L1Be_2 NX2_L1Be_2 EQ2_L1Be_2 RUN2_L1Be_2 L2_L1Be_2 AXD_L1Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_2 TDr_L1Be_2 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_2 ENTD_L1Be_2 RUN3_L1Be L3_L1Be NX3_L1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Be_3 C2_L1Be_3 EfD_L1Be_3 ED_L1Be_3 run2_L1Be_3 D2_L1Be_3 W2_L1Be_3 NX2_L1Be_3 EQ2_L1Be_3 RUN2_L1Be_3 L2_L1Be_3 AXD_L1Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Be_3 TDr_L1Be_3 CD_L1Be Eps_L1Be Ebg_L1Be run3_L1Be AXDr_L1Be_3 ENTD_L1Be_3 RUN3_L1Be L3_L1Be NX3_L1Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL1Be.
End F0A_iL1Be.

(* [comment removed for export] *)
Module F0A_iL0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0Bf.IL0Bf"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Bf"; "ED_L0Bf_1"; "ED_L0Bf_2"; "Ebg_L0Bf"; "Edr_L0Bf"; "P0_L0Bf"; "TD_L0Bf_1"; "TD_L0Bf_2"; "Xf_L0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL0Bf.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S1fU0S1Vb;VA;VKc;Vrho1;A6").

Definition contF (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : assn) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3S10Vsegs;Vok;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A4F_;F_;FtpE;FrhoE;Frho1';FA';").
Definition econtF (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (E : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|0|
SaS0S0S4SbQ40A1A1S1dVA;R4A2S20Vkeep;Vrho1;R4A3SfVsegs;S7Vsegs;VJFi;S5R6VKc;R5A4VE;R4R3A5VQ;A3F_;F_;FtpE;FrhoE;Frho1';FA';").

Theorem free_spine_L0Bf : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0Bf C3_L0Bf Ems_L0Bf C4_L0Bf TM0_L0Bf run4_L0Bf RM_L0Bf D3_L0Bf W3_L0Bf EQ3_L0Bf NX3b_L0Bf RUN4_L0Bf L4_L0Bf D4_L0Bf W4_L0Bf EQ4_L0Bf
             HeM_L0Bf HchkM_L0Bf HTM_L0Bf FBM_L0Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0Bf.
    apply (f0_s5 0%nat st q_L0Bf false TM_L0Bf Eq_L0Bf EQ_L0Bf TQ0_L0Bf run5_L0Bf RQ_L0Bf NX5_L0Bf RUN5_L0Bf L5_L0Bf AXQ_L0Bf HeQ_L0Bf HchkQ_L0Bf HTQ_L0Bf FBQ_L0Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0Bf.
    apply (f0_s6 0%nat st false TQ_L0Bf Edr_L0Bf Xf_L0Bf run6_L0Bf NX6_L0Bf RUN6_L0Bf L6_L0Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true P0_L0Bf exits1_L0Bf Cert1_L0Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0Bf in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0Bf_1 C2_L0Bf_1 EfD_L0Bf_1 ED_L0Bf_1 run2_L0Bf_1 D2_L0Bf_1 W2_L0Bf_1 NX2_L0Bf_1 EQ2_L0Bf_1 RUN2_L0Bf_1 L2_L0Bf_1 AXD_L0Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Bf_1 TDr_L0Bf_1 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_1 ENTD_L0Bf_1 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0Bf_2 C2_L0Bf_2 EfD_L0Bf_2 ED_L0Bf_2 run2_L0Bf_2 D2_L0Bf_2 W2_L0Bf_2 NX2_L0Bf_2 EQ2_L0Bf_2 RUN2_L0Bf_2 L2_L0Bf_2 AXD_L0Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Bf_2 TDr_L0Bf_2 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_2 ENTD_L0Bf_2 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L0Bf : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0Bf C3_L0Bf Ems_L0Bf C4_L0Bf TM0_L0Bf run4_L0Bf RM_L0Bf D3_L0Bf W3_L0Bf EQ3_L0Bf NX3b_L0Bf RUN4_L0Bf L4_L0Bf D4_L0Bf W4_L0Bf EQ4_L0Bf
             HeM_L0Bf HchkM_L0Bf HTM_L0Bf FBM_L0Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0Bf.
    apply (ef0_s5 0%nat st q_L0Bf false TM_L0Bf Eq_L0Bf EQ_L0Bf TQ0_L0Bf run5_L0Bf RQ_L0Bf NX5_L0Bf RUN5_L0Bf L5_L0Bf AXQ_L0Bf HeQ_L0Bf HchkQ_L0Bf HTQ_L0Bf FBQ_L0Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0Bf.
    apply (ef0_s6 0%nat st false TQ_L0Bf Edr_L0Bf Xf_L0Bf run6_L0Bf NX6_L0Bf RUN6_L0Bf L6_L0Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true P0_L0Bf exits1_L0Bf (eq_refl : (GW <=? ss_next (ax_S P0_L0Bf))%positive = true) ECert1_L0Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0Bf in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0Bf_1 C2_L0Bf_1 EfD_L0Bf_1 ED_L0Bf_1 run2_L0Bf_1 D2_L0Bf_1 W2_L0Bf_1 NX2_L0Bf_1 EQ2_L0Bf_1 RUN2_L0Bf_1 L2_L0Bf_1 AXD_L0Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Bf_1 TDr_L0Bf_1 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_1 ENTD_L0Bf_1 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0Bf_2 C2_L0Bf_2 EfD_L0Bf_2 ED_L0Bf_2 run2_L0Bf_2 D2_L0Bf_2 W2_L0Bf_2 NX2_L0Bf_2 EQ2_L0Bf_2 RUN2_L0Bf_2 L2_L0Bf_2 AXD_L0Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Bf_2 TDr_L0Bf_2 CD_L0Bf Eps_L0Bf Ebg_L0Bf run3_L0Bf AXDr_L0Bf_2 ENTD_L0Bf_2 RUN3_L0Bf L3_L0Bf NX3_L0Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL0Bf.
End F0A_iL0Bf.

(* [comment removed for export] *)
Module F0A_iL1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL1A.IL1A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL1A"; "ED_L1A_1"; "ED_L1A_2"; "ED_L1A_3"; "Ebg_L1A"; "Edr_L1A"; "P0_L1A"; "TD_L1A_1"; "TD_L1A_2"; "TD_L1A_3"; "Xf_L1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL1A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL1A.
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

Theorem free_spine_L1A : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SaS2S0S0S4SbQ40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3S11R6R5A2SeU1M0S1RbRaR9R8R6S18S1eR4AaSeG0S1RcRbRaR9R7S19S1fR5AaSeG0S1RdRcRbRaR8S1aS20R6AaScReRdRcRbR9S1bR7A7ScRfReRdRcRaS1cR8A7ScR10RfReRdRbS21R9A7S0S15Vsegs;R11S7Vsegs;VJFi;S6R10RfRdA4S1dR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L1A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_L1A C3_L1A Ems_L1A C4_L1A TM0_L1A run4_L1A RM_L1A D3_L1A W3_L1A EQ3_L1A NX3b_L1A RUN4_L1A L4_L1A D4_L1A W4_L1A EQ4_L1A
             HeM_L1A HchkM_L1A HTM_L1A FBM_L1A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L1A.
    apply (f0_s5 1%nat st q_L1A false TM_L1A Eq_L1A EQ_L1A TQ0_L1A run5_L1A RQ_L1A NX5_L1A RUN5_L1A L5_L1A AXQ_L1A HeQ_L1A HchkQ_L1A HTQ_L1A FBQ_L1A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L1A.
    apply (f0_s6 1%nat st false TQ_L1A Edr_L1A Xf_L1A run6_L1A NX6_L1A RUN6_L1A L6_L1A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true P0_L1A exits1_L1A Cert1_L1A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_L1A_1 C2_L1A_1 EfD_L1A_1 ED_L1A_1 run2_L1A_1 D2_L1A_1 W2_L1A_1 NX2_L1A_1 EQ2_L1A_1 RUN2_L1A_1 L2_L1A_1 AXD_L1A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_1 TDr_L1A_1 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_1 ENTD_L1A_1 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1A_2 C2_L1A_2 EfD_L1A_2 ED_L1A_2 run2_L1A_2 D2_L1A_2 W2_L1A_2 NX2_L1A_2 EQ2_L1A_2 RUN2_L1A_2 L2_L1A_2 AXD_L1A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_2 TDr_L1A_2 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_2 ENTD_L1A_2 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1A_3 C2_L1A_3 EfD_L1A_3 ED_L1A_3 run2_L1A_3 D2_L1A_3 W2_L1A_3 NX2_L1A_3 EQ2_L1A_3 RUN2_L1A_3 L2_L1A_3 AXD_L1A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1A_3 TDr_L1A_3 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_3 ENTD_L1A_3 RUN3_L1A L3_L1A NX3_L1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L1A : ltac2:(tb__ "0|1|
S13OF_;SaS2S0S0S4SbQ40A1A1S16OF_;S3R5A1S11R5R4A2SfU1M0S1R9R8R7R5S18S1eR3A9SfG0S1RaR9R8R6S19S1fR4A9SfG0S1RbRaR9R7S1aS20R5A9SdRcRbRaR8S1bR6A6SdRdRcRbR9S1cR7A6SdReRdRcRaS21R8A6S0S14Vsegs;S7Vsegs;VJFi;S6RfReRcA4S1dR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L1A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_L1A C3_L1A Ems_L1A C4_L1A TM0_L1A run4_L1A RM_L1A D3_L1A W3_L1A EQ3_L1A NX3b_L1A RUN4_L1A L4_L1A D4_L1A W4_L1A EQ4_L1A
             HeM_L1A HchkM_L1A HTM_L1A FBM_L1A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L1A.
    apply (ef0_s5 1%nat st q_L1A false TM_L1A Eq_L1A EQ_L1A TQ0_L1A run5_L1A RQ_L1A NX5_L1A RUN5_L1A L5_L1A AXQ_L1A HeQ_L1A HchkQ_L1A HTQ_L1A FBQ_L1A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L1A.
    apply (ef0_s6 1%nat st false TQ_L1A Edr_L1A Xf_L1A run6_L1A NX6_L1A RUN6_L1A L6_L1A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true P0_L1A exits1_L1A (eq_refl : (GW <=? ss_next (ax_S P0_L1A))%positive = true) ECert1_L1A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_L1A_1 C2_L1A_1 EfD_L1A_1 ED_L1A_1 run2_L1A_1 D2_L1A_1 W2_L1A_1 NX2_L1A_1 EQ2_L1A_1 RUN2_L1A_1 L2_L1A_1 AXD_L1A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_1 TDr_L1A_1 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_1 ENTD_L1A_1 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1A_2 C2_L1A_2 EfD_L1A_2 ED_L1A_2 run2_L1A_2 D2_L1A_2 W2_L1A_2 NX2_L1A_2 EQ2_L1A_2 RUN2_L1A_2 L2_L1A_2 AXD_L1A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_2 TDr_L1A_2 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_2 ENTD_L1A_2 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1A_3 C2_L1A_3 EfD_L1A_3 ED_L1A_3 run2_L1A_3 D2_L1A_3 W2_L1A_3 NX2_L1A_3 EQ2_L1A_3 RUN2_L1A_3 L2_L1A_3 AXD_L1A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1A_3 TDr_L1A_3 CD_L1A Eps_L1A Ebg_L1A run3_L1A AXDr_L1A_3 ENTD_L1A_3 RUN3_L1A L3_L1A NX3_L1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL1A.
End F0A_iL1A.

(* [comment removed for export] *)
Module F0A_iL1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL1Bf.IL1Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf"; "ED_L1Bf_1"; "ED_L1Bf_2"; "ED_L1Bf_3"; "Ebg_L1Bf"; "Edr_L1Bf"; "P0_L1Bf"; "TD_L1Bf_1"; "TD_L1Bf_2"; "TD_L1Bf_3"; "Xf_L1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ah.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL1Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL1Bf.
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

Theorem free_spine_L1Bf : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SaS2S0S0S4SbQ40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3S11R6R5A2SeU1M0S1RbRaR9R8R6S18S1eR4AaSeG0S1RcRbRaR9R7S19S1fR5AaSeG0S1RdRcRbRaR8S1aS20R6AaScReRdRcRbR9S1bR7A7ScRfReRdRcRaS1cR8A7ScR10RfReRdRbS21R9A7S0S15Vsegs;R11S7Vsegs;VJFi;S6R10RfRdA4S1dR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L1Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L1Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_L1Bf C3_L1Bf Ems_L1Bf C4_L1Bf TM0_L1Bf run4_L1Bf RM_L1Bf D3_L1Bf W3_L1Bf EQ3_L1Bf NX3b_L1Bf RUN4_L1Bf L4_L1Bf D4_L1Bf W4_L1Bf EQ4_L1Bf
             HeM_L1Bf HchkM_L1Bf HTM_L1Bf FBM_L1Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L1Bf.
    apply (f0_s5 1%nat st q_L1Bf false TM_L1Bf Eq_L1Bf EQ_L1Bf TQ0_L1Bf run5_L1Bf RQ_L1Bf NX5_L1Bf RUN5_L1Bf L5_L1Bf AXQ_L1Bf HeQ_L1Bf HchkQ_L1Bf HTQ_L1Bf FBQ_L1Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L1Bf.
    apply (f0_s6 1%nat st false TQ_L1Bf Edr_L1Bf Xf_L1Bf run6_L1Bf NX6_L1Bf RUN6_L1Bf L6_L1Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 1%nat st true P0_L1Bf exits1_L1Bf Cert1_L1Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L1Bf in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_L1Bf_1 C2_L1Bf_1 EfD_L1Bf_1 ED_L1Bf_1 run2_L1Bf_1 D2_L1Bf_1 W2_L1Bf_1 NX2_L1Bf_1 EQ2_L1Bf_1 RUN2_L1Bf_1 L2_L1Bf_1 AXD_L1Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Bf_1 TDr_L1Bf_1 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_1 ENTD_L1Bf_1 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Bf_2 C2_L1Bf_2 EfD_L1Bf_2 ED_L1Bf_2 run2_L1Bf_2 D2_L1Bf_2 W2_L1Bf_2 NX2_L1Bf_2 EQ2_L1Bf_2 RUN2_L1Bf_2 L2_L1Bf_2 AXD_L1Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Bf_2 TDr_L1Bf_2 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_2 ENTD_L1Bf_2 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_L1Bf_3 C2_L1Bf_3 EfD_L1Bf_3 ED_L1Bf_3 run2_L1Bf_3 D2_L1Bf_3 W2_L1Bf_3 NX2_L1Bf_3 EQ2_L1Bf_3 RUN2_L1Bf_3 L2_L1Bf_3 AXD_L1Bf_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_L1Bf_3 TDr_L1Bf_3 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_3 ENTD_L1Bf_3 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L1Bf : ltac2:(tb__ "0|1|
S13OF_;SaS2S0S0S4SbQ40A1A1S16OF_;S3R5A1S11R5R4A2SfU1M0S1R9R8R7R5S18S1eR3A9SfG0S1RaR9R8R6S19S1fR4A9SfG0S1RbRaR9R7S1aS20R5A9SdRcRbRaR8S1bR6A6SdRdRcRbR9S1cR7A6SdReRdRcRaS21R8A6S0S14Vsegs;S7Vsegs;VJFi;S6RfReRcA4S1dR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L1Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L1Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_L1Bf C3_L1Bf Ems_L1Bf C4_L1Bf TM0_L1Bf run4_L1Bf RM_L1Bf D3_L1Bf W3_L1Bf EQ3_L1Bf NX3b_L1Bf RUN4_L1Bf L4_L1Bf D4_L1Bf W4_L1Bf EQ4_L1Bf
             HeM_L1Bf HchkM_L1Bf HTM_L1Bf FBM_L1Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L1Bf.
    apply (ef0_s5 1%nat st q_L1Bf false TM_L1Bf Eq_L1Bf EQ_L1Bf TQ0_L1Bf run5_L1Bf RQ_L1Bf NX5_L1Bf RUN5_L1Bf L5_L1Bf AXQ_L1Bf HeQ_L1Bf HchkQ_L1Bf HTQ_L1Bf FBQ_L1Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L1Bf.
    apply (ef0_s6 1%nat st false TQ_L1Bf Edr_L1Bf Xf_L1Bf run6_L1Bf NX6_L1Bf RUN6_L1Bf L6_L1Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 1%nat st true P0_L1Bf exits1_L1Bf (eq_refl : (GW <=? ss_next (ax_S P0_L1Bf))%positive = true) ECert1_L1Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L1Bf in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_L1Bf_1 C2_L1Bf_1 EfD_L1Bf_1 ED_L1Bf_1 run2_L1Bf_1 D2_L1Bf_1 W2_L1Bf_1 NX2_L1Bf_1 EQ2_L1Bf_1 RUN2_L1Bf_1 L2_L1Bf_1 AXD_L1Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Bf_1 TDr_L1Bf_1 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_1 ENTD_L1Bf_1 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Bf_2 C2_L1Bf_2 EfD_L1Bf_2 ED_L1Bf_2 run2_L1Bf_2 D2_L1Bf_2 W2_L1Bf_2 NX2_L1Bf_2 EQ2_L1Bf_2 RUN2_L1Bf_2 L2_L1Bf_2 AXD_L1Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Bf_2 TDr_L1Bf_2 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_2 ENTD_L1Bf_2 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_L1Bf_3 C2_L1Bf_3 EfD_L1Bf_3 ED_L1Bf_3 run2_L1Bf_3 D2_L1Bf_3 W2_L1Bf_3 NX2_L1Bf_3 EQ2_L1Bf_3 RUN2_L1Bf_3 L2_L1Bf_3 AXD_L1Bf_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_L1Bf_3 TDr_L1Bf_3 CD_L1Bf Eps_L1Bf Ebg_L1Bf run3_L1Bf AXDr_L1Bf_3 ENTD_L1Bf_3 RUN3_L1Bf L3_L1Bf NX3_L1Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL1Bf.
End F0A_iL1Bf.

