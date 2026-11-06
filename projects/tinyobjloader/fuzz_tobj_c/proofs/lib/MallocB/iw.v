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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel ib.

(* [comment removed for export] *)
Module F0A_i0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i0Bf.I0Bf"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf"; "ED_0Bf_1"; "ED_0Bf_2"; "Ebg_0Bf"; "Edr_0Bf"; "P0_0Bf"; "TD_0Bf_1"; "TD_0Bf_2"; "Xf_0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.F0A_c0Bf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I0Bf.
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

Theorem free_spine_0Bf : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_0Bf rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_0Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_0Bf C3_0Bf Ems_0Bf C4_0Bf TM0_0Bf run4_0Bf RM_0Bf D3_0Bf W3_0Bf EQ3_0Bf NX3b_0Bf RUN4_0Bf L4_0Bf D4_0Bf W4_0Bf EQ4_0Bf
             HeM_0Bf HchkM_0Bf HTM_0Bf FBM_0Bf ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_0Bf.
    apply (f0_s5 0%nat st q_0Bf false TM_0Bf Eq_0Bf EQ_0Bf TQ0_0Bf run5_0Bf RQ_0Bf NX5_0Bf RUN5_0Bf L5_0Bf AXQ_0Bf HeQ_0Bf HchkQ_0Bf HTQ_0Bf FBQ_0Bf
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_0Bf.
    apply (f0_s6 0%nat st false TQ_0Bf Edr_0Bf Xf_0Bf run6_0Bf NX6_0Bf RUN6_0Bf L6_0Bf ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 0%nat st q_0Bf true exits1_0Bf Cert1_0Bf ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_0Bf in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_0Bf_1 C2_0Bf_1 EfD_0Bf_1 ED_0Bf_1 run2_0Bf_1 D2_0Bf_1 W2_0Bf_1 NX2_0Bf_1 EQ2_0Bf_1 RUN2_0Bf_1 L2_0Bf_1 AXD_0Bf_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0Bf_1 TDr_0Bf_1 CD_0Bf Eps_0Bf Ebg_0Bf run3_0Bf AXDr_0Bf_1 ENTD_0Bf_1 RUN3_0Bf L3_0Bf NX3_0Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_0Bf_2 C2_0Bf_2 EfD_0Bf_2 ED_0Bf_2 run2_0Bf_2 D2_0Bf_2 W2_0Bf_2 NX2_0Bf_2 EQ2_0Bf_2 RUN2_0Bf_2 L2_0Bf_2 AXD_0Bf_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0Bf_2 TDr_0Bf_2 CD_0Bf Eps_0Bf Ebg_0Bf run3_0Bf AXDr_0Bf_2 ENTD_0Bf_2 RUN3_0Bf L3_0Bf NX3_0Bf
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_0Bf : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_0Bf rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_0Bf rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_0Bf C3_0Bf Ems_0Bf C4_0Bf TM0_0Bf run4_0Bf RM_0Bf D3_0Bf W3_0Bf EQ3_0Bf NX3b_0Bf RUN4_0Bf L4_0Bf D4_0Bf W4_0Bf EQ4_0Bf
             HeM_0Bf HchkM_0Bf HTM_0Bf FBM_0Bf A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_0Bf.
    apply (ef0_s5 0%nat st q_0Bf false TM_0Bf Eq_0Bf EQ_0Bf TQ0_0Bf run5_0Bf RQ_0Bf NX5_0Bf RUN5_0Bf L5_0Bf AXQ_0Bf HeQ_0Bf HchkQ_0Bf HTQ_0Bf FBQ_0Bf
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_0Bf.
    apply (ef0_s6 0%nat st false TQ_0Bf Edr_0Bf Xf_0Bf run6_0Bf NX6_0Bf RUN6_0Bf L6_0Bf A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 0%nat st q_0Bf true exits1_0Bf ECert1_0Bf A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_0Bf in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_0Bf_1 C2_0Bf_1 EfD_0Bf_1 ED_0Bf_1 run2_0Bf_1 D2_0Bf_1 W2_0Bf_1 NX2_0Bf_1 EQ2_0Bf_1 RUN2_0Bf_1 L2_0Bf_1 AXD_0Bf_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0Bf_1 TDr_0Bf_1 CD_0Bf Eps_0Bf Ebg_0Bf run3_0Bf AXDr_0Bf_1 ENTD_0Bf_1 RUN3_0Bf L3_0Bf NX3_0Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_0Bf_2 C2_0Bf_2 EfD_0Bf_2 ED_0Bf_2 run2_0Bf_2 D2_0Bf_2 W2_0Bf_2 NX2_0Bf_2 EQ2_0Bf_2 RUN2_0Bf_2 L2_0Bf_2 AXD_0Bf_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0Bf_2 TDr_0Bf_2 CD_0Bf Eps_0Bf Ebg_0Bf run3_0Bf AXDr_0Bf_2 ENTD_0Bf_2 RUN3_0Bf L3_0Bf NX3_0Bf
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I0Bf.
End F0A_i0Bf.

(* [comment removed for export] *)
Module F0A_i1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1A.I1A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1A"; "ED_1A_1"; "ED_1A_2"; "ED_1A_3"; "Ebg_1A"; "Edr_1A"; "P0_1A"; "TD_1A_1"; "TD_1A_2"; "TD_1A_3"; "Xf_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I1A.
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

Theorem free_spine_1A : ltac2:(tb__ "0|1|
S13OF_;S16OF_;SaS2S0S0S4SbQ40A1A1S17S3R5A1S9Vsegs;R8S8R6A1A3S11R6R5A2SeU1M0S1RbRaR9R8R6S18S1eR4AaSeG0S1RcRbRaR9R7S19S1fR5AaSeG0S1RdRcRbRaR8S1aS20R6AaScReRdRcRbR9S1bR7A7ScRfReRdRcRaS1cR8A7ScR10RfReRdRbS21R9A7S0S15Vsegs;R11S7Vsegs;VJFi;S6R10RfRdA4S1dR1RcA5RbA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_1A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 1%nat st false Eps_1A C3_1A Ems_1A C4_1A TM0_1A run4_1A RM_1A D3_1A W3_1A EQ3_1A NX3b_1A RUN4_1A L4_1A D4_1A W4_1A EQ4_1A
             HeM_1A HchkM_1A HTM_1A FBM_1A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_1A.
    apply (f0_s5 1%nat st q_1A false TM_1A Eq_1A EQ_1A TQ0_1A run5_1A RQ_1A NX5_1A RUN5_1A L5_1A AXQ_1A HeQ_1A HchkQ_1A HTQ_1A FBQ_1A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_1A.
    apply (f0_s6 1%nat st false TQ_1A Edr_1A Xf_1A run6_1A NX6_1A RUN6_1A L6_1A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 1%nat st q_1A true exits1_1A Cert1_1A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (f0_s2 1%nat st true S1c_1A_1 C2_1A_1 EfD_1A_1 ED_1A_1 run2_1A_1 D2_1A_1 W2_1A_1 NX2_1A_1 EQ2_1A_1 RUN2_1A_1 L2_1A_1 AXD_1A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1A_1 TDr_1A_1 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_1 ENTD_1A_1 RUN3_1A L3_1A NX3_1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1A_2 C2_1A_2 EfD_1A_2 ED_1A_2 run2_1A_2 D2_1A_2 W2_1A_2 NX2_1A_2 EQ2_1A_2 RUN2_1A_2 L2_1A_2 AXD_1A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1A_2 TDr_1A_2 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_2 ENTD_1A_2 RUN3_1A L3_1A NX3_1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 1%nat st true S1c_1A_3 C2_1A_3 EfD_1A_3 ED_1A_3 run2_1A_3 D2_1A_3 W2_1A_3 NX2_1A_3 EQ2_1A_3 RUN2_1A_3 L2_1A_3 AXD_1A_3
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 1%nat st false TD_1A_3 TDr_1A_3 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_3 ENTD_1A_3 RUN3_1A L3_1A NX3_1A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_1A : ltac2:(tb__ "0|1|
S13OF_;SaS2S0S0S4SbQ40A1A1S16OF_;S3R5A1S11R5R4A2SfU1M0S1R9R8R7R5S18S1eR3A9SfG0S1RaR9R8R6S19S1fR4A9SfG0S1RbRaR9R7S1aS20R5A9SdRcRbRaR8S1bR6A6SdRdRcRbR9S1cR7A6SdReRdRcRaS21R8A6S0S14Vsegs;S7Vsegs;VJFi;S6RfReRcA4S1dR1RbA5RaA3FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HD3 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_1A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_1A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 1%nat st false Eps_1A C3_1A Ems_1A C4_1A TM0_1A run4_1A RM_1A D3_1A W3_1A EQ3_1A NX3b_1A RUN4_1A L4_1A D4_1A W4_1A EQ4_1A
             HeM_1A HchkM_1A HTM_1A FBM_1A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_1A.
    apply (ef0_s5 1%nat st q_1A false TM_1A Eq_1A EQ_1A TQ0_1A run5_1A RQ_1A NX5_1A RUN5_1A L5_1A AXQ_1A HeQ_1A HchkQ_1A HTQ_1A FBQ_1A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_1A.
    apply (ef0_s6 1%nat st false TQ_1A Edr_1A Xf_1A run6_1A NX6_1A RUN6_1A L6_1A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 1%nat st q_1A true exits1_1A ECert1_1A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_1A in HinE. destruct HinE as [<-|[<-|[<-|[]]]].
  - apply (ef0_s2 1%nat st true S1c_1A_1 C2_1A_1 EfD_1A_1 ED_1A_1 run2_1A_1 D2_1A_1 W2_1A_1 NX2_1A_1 EQ2_1A_1 RUN2_1A_1 L2_1A_1 AXD_1A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1A_1 TDr_1A_1 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_1 ENTD_1A_1 RUN3_1A L3_1A NX3_1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1A_2 C2_1A_2 EfD_1A_2 ED_1A_2 run2_1A_2 D2_1A_2 W2_1A_2 NX2_1A_2 EQ2_1A_2 RUN2_1A_2 L2_1A_2 AXD_1A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1A_2 TDr_1A_2 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_2 ENTD_1A_2 RUN3_1A L3_1A NX3_1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 1%nat st true S1c_1A_3 C2_1A_3 EfD_1A_3 ED_1A_3 run2_1A_3 D2_1A_3 W2_1A_3 NX2_1A_3 EQ2_1A_3 RUN2_1A_3 L2_1A_3 AXD_1A_3
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD3. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 1%nat st false TD_1A_3 TDr_1A_3 CD_1A Eps_1A Ebg_1A run3_1A AXDr_1A_3 ENTD_1A_3 RUN3_1A L3_1A NX3_1A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I1A.
End F0A_i1A.

(* [comment removed for export] *)
Module F0A_i1Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Be.I1Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be"; "ED_1Be_1"; "ED_1Be_2"; "ED_1Be_3"; "Ebg_1Be"; "Edr_1Be"; "P0_1Be"; "TD_1Be_1"; "TD_1Be_2"; "TD_1Be_3"; "Xf_1Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Be.
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
Module F0A_i1Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i1Bf.I1Bf"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf"; "ED_1Bf_1"; "ED_1Bf_2"; "ED_1Bf_3"; "Ebg_1Bf"; "Edr_1Bf"; "P0_1Bf"; "TD_1Bf_1"; "TD_1Bf_2"; "TD_1Bf_3"; "Xf_1Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c1Bf.
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
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2A.I2A"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A"; "ED_2A_1"; "ED_2A_2"; "ED_2A_3"; "ED_2A_4"; "Ebg_2A"; "Edr_2A"; "P0_2A"; "TD_2A_1"; "TD_2A_2"; "TD_2A_3"; "TD_2A_4"; "Xf_2A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.F0A_c2A.
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
Module F0A_i2Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iw.F0A_i2Be.I2Be"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be"; "ED_2Be_1"; "ED_2Be_2"; "ED_2Be_3"; "ED_2Be_4"; "Ebg_2Be"; "Edr_2Be"; "P0_2Be"; "TD_2Be_1"; "TD_2Be_2"; "TD_2Be_3"; "TD_2Be_4"; "Xf_2Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymEntail SymFrame SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Be.
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

