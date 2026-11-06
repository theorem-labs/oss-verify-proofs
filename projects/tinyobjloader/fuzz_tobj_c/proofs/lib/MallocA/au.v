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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar ah.

(* [comment removed for export] *)
Module F0A_iL2A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2A.IL2A"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A"; "ED_L2A_1"; "ED_L2A_2"; "ED_L2A_3"; "ED_L2A_4"; "Ebg_L2A"; "Edr_L2A"; "P0_L2A"; "TD_L2A_1"; "TD_L2A_2"; "TD_L2A_3"; "TD_L2A_4"; "Xf_L2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL2A.
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

Theorem free_spine_L2A : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SfS2S0S0S4S10Q40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3SdR6R5A2SaU2M0S1RbRaR9R8R6S18S1fR4AaSaG0S1RcRbRaR9R7S19S20R5AaSaG0S1RdRcRbRaR8S1aS21R6AaSaG0S1ReRdRcRbR9S1bS22R7AaS11RfReRdRcRaS1cR8A7S11R10RfReRdRbS1dR9A7S11R11R10RfReRcS23RaA7S0S15Vsegs;R12S7Vsegs;VJFi;S6R11R10ReA4S1eR1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L2A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L2A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_L2A C3_L2A Ems_L2A C4_L2A TM0_L2A run4_L2A RM_L2A D3_L2A W3_L2A EQ3_L2A NX3b_L2A RUN4_L2A L4_L2A D4_L2A W4_L2A EQ4_L2A
             HeM_L2A HchkM_L2A HTM_L2A FBM_L2A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L2A.
    apply (f0_s5 2%nat st q_L2A false TM_L2A Eq_L2A EQ_L2A TQ0_L2A run5_L2A RQ_L2A NX5_L2A RUN5_L2A L5_L2A AXQ_L2A HeQ_L2A HchkQ_L2A HTQ_L2A FBQ_L2A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L2A.
    apply (f0_s6 2%nat st false TQ_L2A Edr_L2A Xf_L2A run6_L2A NX6_L2A RUN6_L2A L6_L2A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true P0_L2A exits1_L2A Cert1_L2A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L2A in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_L2A_1 C2_L2A_1 EfD_L2A_1 ED_L2A_1 run2_L2A_1 D2_L2A_1 W2_L2A_1 NX2_L2A_1 EQ2_L2A_1 RUN2_L2A_1 L2_L2A_1 AXD_L2A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2A_1 TDr_L2A_1 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_1 ENTD_L2A_1 RUN3_L2A L3_L2A NX3_L2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2A_2 C2_L2A_2 EfD_L2A_2 ED_L2A_2 run2_L2A_2 D2_L2A_2 W2_L2A_2 NX2_L2A_2 EQ2_L2A_2 RUN2_L2A_2 L2_L2A_2 AXD_L2A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2A_2 TDr_L2A_2 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_2 ENTD_L2A_2 RUN3_L2A L3_L2A NX3_L2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2A_3 C2_L2A_3 EfD_L2A_3 ED_L2A_3 run2_L2A_3 D2_L2A_3 W2_L2A_3 NX2_L2A_3 EQ2_L2A_3 RUN2_L2A_3 L2_L2A_3 AXD_L2A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2A_3 TDr_L2A_3 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_3 ENTD_L2A_3 RUN3_L2A L3_L2A NX3_L2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2A_4 C2_L2A_4 EfD_L2A_4 ED_L2A_4 run2_L2A_4 D2_L2A_4 W2_L2A_4 NX2_L2A_4 EQ2_L2A_4 RUN2_L2A_4 L2_L2A_4 AXD_L2A_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2A_4 TDr_L2A_4 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_4 ENTD_L2A_4 RUN3_L2A L3_L2A NX3_L2A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L2A : ltac2:(tb__ "0|1|
S13OF_;SfS2S0S0S4S10Q40A1A1S16OF_;S3R5A1SdR5R4A2SbU2M0S1R9R8R7R5S18S1fR3A9SbG0S1RaR9R8R6S19S20R4A9SbG0S1RbRaR9R7S1aS21R5A9SbG0S1RcRbRaR8S1bS22R6A9S12RdRcRbR9S1cR7A6S12ReRdRcRaS1dR8A6S12RfReRdRbS23R9A6S0S14Vsegs;S7Vsegs;VJFi;S6R10RfRdA4S1eR1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L2A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L2A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_L2A C3_L2A Ems_L2A C4_L2A TM0_L2A run4_L2A RM_L2A D3_L2A W3_L2A EQ3_L2A NX3b_L2A RUN4_L2A L4_L2A D4_L2A W4_L2A EQ4_L2A
             HeM_L2A HchkM_L2A HTM_L2A FBM_L2A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L2A.
    apply (ef0_s5 2%nat st q_L2A false TM_L2A Eq_L2A EQ_L2A TQ0_L2A run5_L2A RQ_L2A NX5_L2A RUN5_L2A L5_L2A AXQ_L2A HeQ_L2A HchkQ_L2A HTQ_L2A FBQ_L2A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L2A.
    apply (ef0_s6 2%nat st false TQ_L2A Edr_L2A Xf_L2A run6_L2A NX6_L2A RUN6_L2A L6_L2A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true P0_L2A exits1_L2A (eq_refl : (GW <=? ss_next (ax_S P0_L2A))%positive = true) ECert1_L2A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L2A in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_L2A_1 C2_L2A_1 EfD_L2A_1 ED_L2A_1 run2_L2A_1 D2_L2A_1 W2_L2A_1 NX2_L2A_1 EQ2_L2A_1 RUN2_L2A_1 L2_L2A_1 AXD_L2A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2A_1 TDr_L2A_1 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_1 ENTD_L2A_1 RUN3_L2A L3_L2A NX3_L2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2A_2 C2_L2A_2 EfD_L2A_2 ED_L2A_2 run2_L2A_2 D2_L2A_2 W2_L2A_2 NX2_L2A_2 EQ2_L2A_2 RUN2_L2A_2 L2_L2A_2 AXD_L2A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2A_2 TDr_L2A_2 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_2 ENTD_L2A_2 RUN3_L2A L3_L2A NX3_L2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2A_3 C2_L2A_3 EfD_L2A_3 ED_L2A_3 run2_L2A_3 D2_L2A_3 W2_L2A_3 NX2_L2A_3 EQ2_L2A_3 RUN2_L2A_3 L2_L2A_3 AXD_L2A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2A_3 TDr_L2A_3 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_3 ENTD_L2A_3 RUN3_L2A L3_L2A NX3_L2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2A_4 C2_L2A_4 EfD_L2A_4 ED_L2A_4 run2_L2A_4 D2_L2A_4 W2_L2A_4 NX2_L2A_4 EQ2_L2A_4 RUN2_L2A_4 L2_L2A_4 AXD_L2A_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2A_4 TDr_L2A_4 CD_L2A Eps_L2A Ebg_L2A run3_L2A AXDr_L2A_4 ENTD_L2A_4 RUN3_L2A L3_L2A NX3_L2A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL2A.
End F0A_iL2A.

(* [comment removed for export] *)
Module F0A_iL2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2Bf.IL2Bf"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Bf"; "ED_L2Bf_1"; "ED_L2Bf_2"; "ED_L2Bf_3"; "ED_L2Bf_4"; "Ebg_L2Bf"; "Edr_L2Bf"; "P0_L2Bf"; "TD_L2Bf_1"; "TD_L2Bf_2"; "TD_L2Bf_3"; "TD_L2Bf_4"; "Xf_L2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL2Bf.
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

Theorem free_spine_L2Bf : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SfS2S0S0S4S10Q40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3SdR6R5A2SaU2M0S1RbRaR9R8R6S18S1fR4AaSaG0S1RcRbRaR9R7S19S20R5AaSaG0S1RdRcRbRaR8S1aS21R6AaSaG0S1ReRdRcRbR9S1bS22R7AaS11RfReRdRcRaS1cR8A7S11R10RfReRdRbS1dR9A7S11R11R10RfReRcS23RaA7S0S15Vsegs;R12S7Vsegs;VJFi;S6R11R10ReA4S1eR1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L2Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L2Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_L2Bf C3_L2Bf Ems_L2Bf C4_L2Bf TM0_L2Bf run4_L2Bf RM_L2Bf D3_L2Bf W3_L2Bf EQ3_L2Bf NX3b_L2Bf RUN4_L2Bf L4_L2Bf D4_L2Bf W4_L2Bf EQ4_L2Bf
             HeM_L2Bf HchkM_L2Bf HTM_L2Bf FBM_L2Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L2Bf.
    apply (f0_s5 2%nat st q_L2Bf false TM_L2Bf Eq_L2Bf EQ_L2Bf TQ0_L2Bf run5_L2Bf RQ_L2Bf NX5_L2Bf RUN5_L2Bf L5_L2Bf AXQ_L2Bf HeQ_L2Bf HchkQ_L2Bf HTQ_L2Bf FBQ_L2Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L2Bf.
    apply (f0_s6 2%nat st false TQ_L2Bf Edr_L2Bf Xf_L2Bf run6_L2Bf NX6_L2Bf RUN6_L2Bf L6_L2Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true P0_L2Bf exits1_L2Bf Cert1_L2Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L2Bf in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_L2Bf_1 C2_L2Bf_1 EfD_L2Bf_1 ED_L2Bf_1 run2_L2Bf_1 D2_L2Bf_1 W2_L2Bf_1 NX2_L2Bf_1 EQ2_L2Bf_1 RUN2_L2Bf_1 L2_L2Bf_1 AXD_L2Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Bf_1 TDr_L2Bf_1 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_1 ENTD_L2Bf_1 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Bf_2 C2_L2Bf_2 EfD_L2Bf_2 ED_L2Bf_2 run2_L2Bf_2 D2_L2Bf_2 W2_L2Bf_2 NX2_L2Bf_2 EQ2_L2Bf_2 RUN2_L2Bf_2 L2_L2Bf_2 AXD_L2Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Bf_2 TDr_L2Bf_2 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_2 ENTD_L2Bf_2 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Bf_3 C2_L2Bf_3 EfD_L2Bf_3 ED_L2Bf_3 run2_L2Bf_3 D2_L2Bf_3 W2_L2Bf_3 NX2_L2Bf_3 EQ2_L2Bf_3 RUN2_L2Bf_3 L2_L2Bf_3 AXD_L2Bf_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Bf_3 TDr_L2Bf_3 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_3 ENTD_L2Bf_3 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Bf_4 C2_L2Bf_4 EfD_L2Bf_4 ED_L2Bf_4 run2_L2Bf_4 D2_L2Bf_4 W2_L2Bf_4 NX2_L2Bf_4 EQ2_L2Bf_4 RUN2_L2Bf_4 L2_L2Bf_4 AXD_L2Bf_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Bf_4 TDr_L2Bf_4 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_4 ENTD_L2Bf_4 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L2Bf : ltac2:(tb__ "0|1|
S13OF_;SfS2S0S0S4S10Q40A1A1S16OF_;S3R5A1SdR5R4A2SbU2M0S1R9R8R7R5S18S1fR3A9SbG0S1RaR9R8R6S19S20R4A9SbG0S1RbRaR9R7S1aS21R5A9SbG0S1RcRbRaR8S1bS22R6A9S12RdRcRbR9S1cR7A6S12ReRdRcRaS1dR8A6S12RfReRdRbS23R9A6S0S14Vsegs;S7Vsegs;VJFi;S6R10RfRdA4S1eR1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L2Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L2Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_L2Bf C3_L2Bf Ems_L2Bf C4_L2Bf TM0_L2Bf run4_L2Bf RM_L2Bf D3_L2Bf W3_L2Bf EQ3_L2Bf NX3b_L2Bf RUN4_L2Bf L4_L2Bf D4_L2Bf W4_L2Bf EQ4_L2Bf
             HeM_L2Bf HchkM_L2Bf HTM_L2Bf FBM_L2Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L2Bf.
    apply (ef0_s5 2%nat st q_L2Bf false TM_L2Bf Eq_L2Bf EQ_L2Bf TQ0_L2Bf run5_L2Bf RQ_L2Bf NX5_L2Bf RUN5_L2Bf L5_L2Bf AXQ_L2Bf HeQ_L2Bf HchkQ_L2Bf HTQ_L2Bf FBQ_L2Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L2Bf.
    apply (ef0_s6 2%nat st false TQ_L2Bf Edr_L2Bf Xf_L2Bf run6_L2Bf NX6_L2Bf RUN6_L2Bf L6_L2Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true P0_L2Bf exits1_L2Bf (eq_refl : (GW <=? ss_next (ax_S P0_L2Bf))%positive = true) ECert1_L2Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L2Bf in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_L2Bf_1 C2_L2Bf_1 EfD_L2Bf_1 ED_L2Bf_1 run2_L2Bf_1 D2_L2Bf_1 W2_L2Bf_1 NX2_L2Bf_1 EQ2_L2Bf_1 RUN2_L2Bf_1 L2_L2Bf_1 AXD_L2Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Bf_1 TDr_L2Bf_1 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_1 ENTD_L2Bf_1 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Bf_2 C2_L2Bf_2 EfD_L2Bf_2 ED_L2Bf_2 run2_L2Bf_2 D2_L2Bf_2 W2_L2Bf_2 NX2_L2Bf_2 EQ2_L2Bf_2 RUN2_L2Bf_2 L2_L2Bf_2 AXD_L2Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Bf_2 TDr_L2Bf_2 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_2 ENTD_L2Bf_2 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Bf_3 C2_L2Bf_3 EfD_L2Bf_3 ED_L2Bf_3 run2_L2Bf_3 D2_L2Bf_3 W2_L2Bf_3 NX2_L2Bf_3 EQ2_L2Bf_3 RUN2_L2Bf_3 L2_L2Bf_3 AXD_L2Bf_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Bf_3 TDr_L2Bf_3 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_3 ENTD_L2Bf_3 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Bf_4 C2_L2Bf_4 EfD_L2Bf_4 ED_L2Bf_4 run2_L2Bf_4 D2_L2Bf_4 W2_L2Bf_4 NX2_L2Bf_4 EQ2_L2Bf_4 RUN2_L2Bf_4 L2_L2Bf_4 AXD_L2Bf_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Bf_4 TDr_L2Bf_4 CD_L2Bf Eps_L2Bf Ebg_L2Bf run3_L2Bf AXDr_L2Bf_4 ENTD_L2Bf_4 RUN3_L2Bf L3_L2Bf NX3_L2Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL2Bf.
End F0A_iL2Bf.

(* [comment removed for export] *)
Module F0A_iL2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.au.F0A_iL2Be.IL2Be"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be"; "ED_L2Be_1"; "ED_L2Be_2"; "ED_L2Be_3"; "ED_L2Be_4"; "Ebg_L2Be"; "Edr_L2Be"; "P0_L2Be"; "TD_L2Be_1"; "TD_L2Be_2"; "TD_L2Be_3"; "TD_L2Be_4"; "Xf_L2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ah.F0A_cL2Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section IL2Be.
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

Theorem free_spine_L2Be : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SfS2S0S0S4S10Q40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3SdR6R5A2SaU2M0S1RbRaR9R8R6S18S1fR4AaSaG0S1RcRbRaR9R7S19S20R5AaSaG0S1RdRcRbRaR8S1aS21R6AaSaG0S1ReRdRcRbR9S1bS22R7AaS11RfReRdRcRaS1cR8A7S11R10RfReRdRbS1dR9A7S11R11R10RfReRcS23RaA7S0S15Vsegs;R12S7Vsegs;VJFi;S6R11R10ReA4S1eR1RdA5RcA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L2Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L2Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 2%nat st false Eps_L2Be C3_L2Be Ems_L2Be C4_L2Be TM0_L2Be run4_L2Be RM_L2Be D3_L2Be W3_L2Be EQ3_L2Be NX3b_L2Be RUN4_L2Be L4_L2Be D4_L2Be W4_L2Be EQ4_L2Be
             HeM_L2Be HchkM_L2Be HTM_L2Be FBM_L2Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L2Be.
    apply (f0_s5 2%nat st q_L2Be false TM_L2Be Eq_L2Be EQ_L2Be TQ0_L2Be run5_L2Be RQ_L2Be NX5_L2Be RUN5_L2Be L5_L2Be AXQ_L2Be HeQ_L2Be HchkQ_L2Be HTQ_L2Be FBQ_L2Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L2Be.
    apply (f0_s6 2%nat st false TQ_L2Be Edr_L2Be Xf_L2Be run6_L2Be NX6_L2Be RUN6_L2Be L6_L2Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 2%nat st true P0_L2Be exits1_L2Be Cert1_L2Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L2Be in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (f0_s2 2%nat st true S1c_L2Be_1 C2_L2Be_1 EfD_L2Be_1 ED_L2Be_1 run2_L2Be_1 D2_L2Be_1 W2_L2Be_1 NX2_L2Be_1 EQ2_L2Be_1 RUN2_L2Be_1 L2_L2Be_1 AXD_L2Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Be_1 TDr_L2Be_1 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_1 ENTD_L2Be_1 RUN3_L2Be L3_L2Be NX3_L2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Be_2 C2_L2Be_2 EfD_L2Be_2 ED_L2Be_2 run2_L2Be_2 D2_L2Be_2 W2_L2Be_2 NX2_L2Be_2 EQ2_L2Be_2 RUN2_L2Be_2 L2_L2Be_2 AXD_L2Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Be_2 TDr_L2Be_2 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_2 ENTD_L2Be_2 RUN3_L2Be L3_L2Be NX3_L2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Be_3 C2_L2Be_3 EfD_L2Be_3 ED_L2Be_3 run2_L2Be_3 D2_L2Be_3 W2_L2Be_3 NX2_L2Be_3 EQ2_L2Be_3 RUN2_L2Be_3 L2_L2Be_3 AXD_L2Be_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Be_3 TDr_L2Be_3 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_3 ENTD_L2Be_3 RUN3_L2Be L3_L2Be NX3_L2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 2%nat st true S1c_L2Be_4 C2_L2Be_4 EfD_L2Be_4 ED_L2Be_4 run2_L2Be_4 D2_L2Be_4 W2_L2Be_4 NX2_L2Be_4 EQ2_L2Be_4 RUN2_L2Be_4 L2_L2Be_4 AXD_L2Be_4
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 2%nat st false TD_L2Be_4 TDr_L2Be_4 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_4 ENTD_L2Be_4 RUN3_L2Be L3_L2Be NX3_L2Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_L2Be : ltac2:(tb__ "0|1|
S13OF_;SfS2S0S0S4S10Q40A1A1S16OF_;S3R5A1SdR5R4A2SbU2M0S1R9R8R7R5S18S1fR3A9SbG0S1RaR9R8R6S19S20R4A9SbG0S1RbRaR9R7S1aS21R5A9SbG0S1RcRbRaR8S1bS22R6A9S12RdRcRbR9S1cR7A6S12ReRdRcRaS1dR8A6S12RfReRdRbS23R9A6S0S14Vsegs;S7Vsegs;VJFi;S6R10RfRdA4S1eR1RcA5RbA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HD4 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L2Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L2Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 2%nat st false Eps_L2Be C3_L2Be Ems_L2Be C4_L2Be TM0_L2Be run4_L2Be RM_L2Be D3_L2Be W3_L2Be EQ3_L2Be NX3b_L2Be RUN4_L2Be L4_L2Be D4_L2Be W4_L2Be EQ4_L2Be
             HeM_L2Be HchkM_L2Be HTM_L2Be FBM_L2Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L2Be.
    apply (ef0_s5 2%nat st q_L2Be false TM_L2Be Eq_L2Be EQ_L2Be TQ0_L2Be run5_L2Be RQ_L2Be NX5_L2Be RUN5_L2Be L5_L2Be AXQ_L2Be HeQ_L2Be HchkQ_L2Be HTQ_L2Be FBQ_L2Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L2Be.
    apply (ef0_s6 2%nat st false TQ_L2Be Edr_L2Be Xf_L2Be run6_L2Be NX6_L2Be RUN6_L2Be L6_L2Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 2%nat st true P0_L2Be exits1_L2Be (eq_refl : (GW <=? ss_next (ax_S P0_L2Be))%positive = true) ECert1_L2Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L2Be in HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (ef0_s2 2%nat st true S1c_L2Be_1 C2_L2Be_1 EfD_L2Be_1 ED_L2Be_1 run2_L2Be_1 D2_L2Be_1 W2_L2Be_1 NX2_L2Be_1 EQ2_L2Be_1 RUN2_L2Be_1 L2_L2Be_1 AXD_L2Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Be_1 TDr_L2Be_1 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_1 ENTD_L2Be_1 RUN3_L2Be L3_L2Be NX3_L2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Be_2 C2_L2Be_2 EfD_L2Be_2 ED_L2Be_2 run2_L2Be_2 D2_L2Be_2 W2_L2Be_2 NX2_L2Be_2 EQ2_L2Be_2 RUN2_L2Be_2 L2_L2Be_2 AXD_L2Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Be_2 TDr_L2Be_2 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_2 ENTD_L2Be_2 RUN3_L2Be L3_L2Be NX3_L2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Be_3 C2_L2Be_3 EfD_L2Be_3 ED_L2Be_3 run2_L2Be_3 D2_L2Be_3 W2_L2Be_3 NX2_L2Be_3 EQ2_L2Be_3 RUN2_L2Be_3 L2_L2Be_3 AXD_L2Be_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Be_3 TDr_L2Be_3 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_3 ENTD_L2Be_3 RUN3_L2Be L3_L2Be NX3_L2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 2%nat st true S1c_L2Be_4 C2_L2Be_4 EfD_L2Be_4 ED_L2Be_4 run2_L2Be_4 D2_L2Be_4 W2_L2Be_4 NX2_L2Be_4 EQ2_L2Be_4 RUN2_L2Be_4 L2_L2Be_4 AXD_L2Be_4
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD4. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 2%nat st false TD_L2Be_4 TDr_L2Be_4 CD_L2Be Eps_L2Be Ebg_L2Be run3_L2Be AXDr_L2Be_4 ENTD_L2Be_4 RUN3_L2Be L3_L2Be NX3_L2Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End IL2Be.
End F0A_iL2Be.

(* [comment removed for export] *)
Module F0A_b0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A"; "Ebg_0A"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_0A : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_b0A.

(* [comment removed for export] *)
Module F0A_b0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be"; "Ebg_0Be"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_0Be : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_b0Be.

(* [comment removed for export] *)
Module F0A_b0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sprop_eqb"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Bf"; "Ebg_0Bf"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Bf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno.
Import ListNotations.
Open Scope Z_scope.

Lemma big_fact_0Bf : ltac2:(tb__ "0|0|
S2S0S9S3S4S7A1S5S6S8A1A1A3S1A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End F0A_b0Bf.

