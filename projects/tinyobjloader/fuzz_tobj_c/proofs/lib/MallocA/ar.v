(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel af.

(* [comment removed for export] *)
Module F0A_i1A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i1A.I1A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A"; "ED_1A_1"; "ED_1A_2"; "ED_1A_3"; "Ebg_1A"; "Edr_1A"; "P0_1A"; "TD_1A_1"; "TD_1A_2"; "TD_1A_3"; "Xf_1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c1A.
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
Module F0A_i0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i0Be.I0Be"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be"; "ED_0Be_1"; "ED_0Be_2"; "Ebg_0Be"; "Edr_0Be"; "P0_0Be"; "TD_0Be_1"; "TD_0Be_2"; "Xf_0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I0Be.
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

Theorem free_spine_0Be : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_0Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_0Be C3_0Be Ems_0Be C4_0Be TM0_0Be run4_0Be RM_0Be D3_0Be W3_0Be EQ3_0Be NX3b_0Be RUN4_0Be L4_0Be D4_0Be W4_0Be EQ4_0Be
             HeM_0Be HchkM_0Be HTM_0Be FBM_0Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_0Be.
    apply (f0_s5 0%nat st q_0Be false TM_0Be Eq_0Be EQ_0Be TQ0_0Be run5_0Be RQ_0Be NX5_0Be RUN5_0Be L5_0Be AXQ_0Be HeQ_0Be HchkQ_0Be HTQ_0Be FBQ_0Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_0Be.
    apply (f0_s6 0%nat st false TQ_0Be Edr_0Be Xf_0Be run6_0Be NX6_0Be RUN6_0Be L6_0Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 0%nat st q_0Be true exits1_0Be Cert1_0Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_0Be_1 C2_0Be_1 EfD_0Be_1 ED_0Be_1 run2_0Be_1 D2_0Be_1 W2_0Be_1 NX2_0Be_1 EQ2_0Be_1 RUN2_0Be_1 L2_0Be_1 AXD_0Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0Be_1 TDr_0Be_1 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_1 ENTD_0Be_1 RUN3_0Be L3_0Be NX3_0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_0Be_2 C2_0Be_2 EfD_0Be_2 ED_0Be_2 run2_0Be_2 D2_0Be_2 W2_0Be_2 NX2_0Be_2 EQ2_0Be_2 RUN2_0Be_2 L2_0Be_2 AXD_0Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0Be_2 TDr_0Be_2 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_2 ENTD_0Be_2 RUN3_0Be L3_0Be NX3_0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_0Be : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_0Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_0Be C3_0Be Ems_0Be C4_0Be TM0_0Be run4_0Be RM_0Be D3_0Be W3_0Be EQ3_0Be NX3b_0Be RUN4_0Be L4_0Be D4_0Be W4_0Be EQ4_0Be
             HeM_0Be HchkM_0Be HTM_0Be FBM_0Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_0Be.
    apply (ef0_s5 0%nat st q_0Be false TM_0Be Eq_0Be EQ_0Be TQ0_0Be run5_0Be RQ_0Be NX5_0Be RUN5_0Be L5_0Be AXQ_0Be HeQ_0Be HchkQ_0Be HTQ_0Be FBQ_0Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_0Be.
    apply (ef0_s6 0%nat st false TQ_0Be Edr_0Be Xf_0Be run6_0Be NX6_0Be RUN6_0Be L6_0Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 0%nat st q_0Be true exits1_0Be ECert1_0Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_0Be_1 C2_0Be_1 EfD_0Be_1 ED_0Be_1 run2_0Be_1 D2_0Be_1 W2_0Be_1 NX2_0Be_1 EQ2_0Be_1 RUN2_0Be_1 L2_0Be_1 AXD_0Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0Be_1 TDr_0Be_1 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_1 ENTD_0Be_1 RUN3_0Be L3_0Be NX3_0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_0Be_2 C2_0Be_2 EfD_0Be_2 ED_0Be_2 run2_0Be_2 D2_0Be_2 W2_0Be_2 NX2_0Be_2 EQ2_0Be_2 RUN2_0Be_2 L2_0Be_2 AXD_0Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0Be_2 TDr_0Be_2 CD_0Be Eps_0Be Ebg_0Be run3_0Be AXDr_0Be_2 ENTD_0Be_2 RUN3_0Be L3_0Be NX3_0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I0Be.
End F0A_i0Be.

(* [comment removed for export] *)
Module F0A_i0Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i0Bf.I0Bf"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Bf"; "ED_0Bf_1"; "ED_0Bf_2"; "Ebg_0Bf"; "Edr_0Bf"; "P0_0Bf"; "TD_0Bf_1"; "TD_0Bf_2"; "Xf_0Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0Bf.
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
Module F0A_skelc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "list"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section S1c.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop. Variable bud : bool.
Variable P0 : axst.
Variable exits1 : list axst.
Hypothesis NX0 : ltac2:(tb__ "0|0|
SfS7S24S14S4S1VP0;A1A1A2S8A3").
Hypothesis Cert1 : ltac2:(tb__ "0|0|
SfS7S12S15S1bS5SaS1aS6SaA1A3S14S5S0VP0;S6S0A1A3Vexits1;A6S8A3").
Hypothesis ECert1 : ltac2:(tb__ "0|2|
SfS7S13S15S1bS5SaS1aS6SaA1A3S14S5S10S11VP0;Z1S3Z0M0A1M1A3S6S10A1A3S23S0S10S0S11R1G0G1A3LE;Vexits1;A4A6S8A3").

Theorem f0_s1c : ltac2:(tb__ "0|0|
S18OF_;S1fS1cS2S9S22Q40A1A1S19S20S1eVnW;A1Vst;A2S1dR5A1SdVsegs;R8ScR6A1A3S0S2S21S0R2Vexits1;A3S17Vsegs;RcSbVsegs;SeVnW;Vst;Vbud;RbRaR9A6R3R2R8A5R7A4F_;FrhoE;FE;S2S17Vsegs;RbSbVsegs;SeVnW;Vst;Vbud;RaR9R8A6VP0;R1R7A5R6A4FrhoP;F_;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho1 tp Q HUS HKc Hok HE rhoP.
  apply (cfg_soundA segs FUELF [CASX] GW [P0] exits1 (JF nW st bud A Kc rho1) ok Q tp).
  - apply JF_okf. exact Hok.
  - apply JF_stable; assumption.
  - exact Cert1.
  - intros E rhoE HinE. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE E rhoE HinE)].
  - left. reflexivity.
Qed.
Theorem ef0_s1c : ltac2:(tb__ "0|0|
S1fS1cS2S9S22Q40A1A1S18OF_;S20S1eVnW;A1Vst;A2S1dR5A1S0S2S21S0R2Vexits1;A3S16Vsegs;SbVsegs;SeVnW;Vst;Vbud;RaR9R8A6R3R2R7A5R6A3F_;FrhoE;FE;S2S16Vsegs;SbVsegs;SeVnW;Vst;Vbud;R9R8R7A6VP0;R1R6A5R5A3FrhoP;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 tp Q HUS HKc HE rhoP.
  change P0 with (vna_state (mkVNA P0 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELF [CASX] GW [mkVNA P0 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1) (JF nW st bud A Kc rho1) Q tp).
  - apply JF_stable; assumption.
  - intros n [<-|[]]. cbn [vna_state]. apply Pos.leb_le. exact NX0.
  - exact ECert1.
  - intros E rhoE HinE. apply in_map_iff in HinE as (E0 & <- & HinE0). cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE E0 rhoE HinE0)].
  - left. reflexivity.
Qed.
End S1c.
End F0A_skelc.

(* [comment removed for export] *)
Module F0A_i0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_i0A.I0A"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A"; "ED_0A_1"; "ED_0A_2"; "Ebg_0A"; "Edr_0A"; "P0_0A"; "TD_0A_1"; "TD_0A_2"; "Xf_0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_c0A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section I0A.
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

Theorem free_spine_0A : ltac2:(tb__ "0|1|
SeOF_;S11OF_;SaS2S0S0S4SbQ40A1A1S12S3R5A1S9Vsegs;R8S8R6A1A3S1eR6R5A2S1bU0M0S1RbRaR9R8R6S13S18R4AaS1bG0S1RcRbRaR9R7S14S19R5AaScRdRcRbRaR8S15R6A7ScReRdRcRbR9S16R7A7ScRfReRdRcRaS1aR8A7S0S10Vsegs;R10S7Vsegs;VJFi;S6RfReRcA4S17R1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_0A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_0A C3_0A Ems_0A C4_0A TM0_0A run4_0A RM_0A D3_0A W3_0A EQ3_0A NX3b_0A RUN4_0A L4_0A D4_0A W4_0A EQ4_0A
             HeM_0A HchkM_0A HTM_0A FBM_0A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_0A.
    apply (f0_s5 0%nat st q_0A false TM_0A Eq_0A EQ_0A TQ0_0A run5_0A RQ_0A NX5_0A RUN5_0A L5_0A AXQ_0A HeQ_0A HchkQ_0A HTQ_0A FBQ_0A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_0A.
    apply (f0_s6 0%nat st false TQ_0A Edr_0A Xf_0A run6_0A NX6_0A RUN6_0A L6_0A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1 0%nat st q_0A true exits1_0A Cert1_0A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_0A_1 C2_0A_1 EfD_0A_1 ED_0A_1 run2_0A_1 D2_0A_1 W2_0A_1 NX2_0A_1 EQ2_0A_1 RUN2_0A_1 L2_0A_1 AXD_0A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0A_1 TDr_0A_1 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_1 ENTD_0A_1 RUN3_0A L3_0A NX3_0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_0A_2 C2_0A_2 EfD_0A_2 ED_0A_2 run2_0A_2 D2_0A_2 W2_0A_2 NX2_0A_2 EQ2_0A_2 RUN2_0A_2 L2_0A_2 AXD_0A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_0A_2 TDr_0A_2 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_2 ENTD_0A_2 RUN3_0A L3_0A NX3_0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_0A : ltac2:(tb__ "0|1|
SeOF_;SaS2S0S0S4SbQ40A1A1S11OF_;S3R5A1S1eR5R4A2S1cU0M0S1R9R8R7R5S13S18R3A9S1cG0S1RaR9R8R6S14S19R4A9SdRbRaR9R7S15R5A6SdRcRbRaR8S16R6A6SdRdRcRbR9S1aR7A6S0SfVsegs;S7Vsegs;VJFi;S6ReRdRbA4S17R1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_0A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_0A C3_0A Ems_0A C4_0A TM0_0A run4_0A RM_0A D3_0A W3_0A EQ3_0A NX3b_0A RUN4_0A L4_0A D4_0A W4_0A EQ4_0A
             HeM_0A HchkM_0A HTM_0A FBM_0A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_0A.
    apply (ef0_s5 0%nat st q_0A false TM_0A Eq_0A EQ_0A TQ0_0A run5_0A RQ_0A NX5_0A RUN5_0A L5_0A AXQ_0A HeQ_0A HchkQ_0A HTQ_0A FBQ_0A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_0A.
    apply (ef0_s6 0%nat st false TQ_0A Edr_0A Xf_0A run6_0A NX6_0A RUN6_0A L6_0A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1 0%nat st q_0A true exits1_0A ECert1_0A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_0A_1 C2_0A_1 EfD_0A_1 ED_0A_1 run2_0A_1 D2_0A_1 W2_0A_1 NX2_0A_1 EQ2_0A_1 RUN2_0A_1 L2_0A_1 AXD_0A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0A_1 TDr_0A_1 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_1 ENTD_0A_1 RUN3_0A L3_0A NX3_0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_0A_2 C2_0A_2 EfD_0A_2 ED_0A_2 run2_0A_2 D2_0A_2 W2_0A_2 NX2_0A_2 EQ2_0A_2 RUN2_0A_2 L2_0A_2 AXD_0A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_0A_2 TDr_0A_2 CD_0A Eps_0A Ebg_0A run3_0A AXDr_0A_2 ENTD_0A_2 RUN3_0A L3_0A NX3_0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.
End I0A.
End F0A_i0A.

(* [comment removed for export] *)
Module F0A_bigno.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "SAlu"; "SLit"; "sprop"; "sprop_eqb"; "ss_facts"; "SVar"; "SExt"; "SPBranch"; "SPNot"; "eval"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "div"; "lt"; "modulo"; "pow"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_bigno"; "big_fact"; "big_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "@Stdlib.Lists.List"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "hd_link"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_OR"; "ALU_SLL"; "ALU_SRL"; "BC_GEU"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition big_size : sv := ltac2:(tb__ "0|0|
S2S2fS2S30S2S31S7P6bA1S3Z10A1A3S3Z20A1A3S8S1eQ20S7P67A1A3A3").
Definition big_fact : sprop := ltac2:(tb__ "0|0|
SaS9S32S3Z10000000A1S27A3A1").

Lemma big_size_small : ltac2:(tb__ "0|5|
S0ScScSeS10Z0M0R1A2S14R1Z100M1A2A2SeS10G0R3A2S10R3Z10000000A2A2SdScS17Q40M2S1R5P67A2A2S15R4S16Z2M3Z20A2M4A2A3SdScS17G2S1R6P6bA2A2S11S11S11G3S12G1R4A2A2S12Z10000S13R5G4A2A2A2Z1A2A3SdScS17G2SbR7S27A2A2R6A3F_;F_;F_;F_;Ft;Fn;Frho;").
Proof.
  intros rho n t Ht Hn E103 E107.
  assert (Hh : n / 2 ^ 32 = 0) by (apply Z.div_small; lia).
  assert (Hl : n mod 2 ^ 32 = n) by (apply Z.mod_small; lia).
  rewrite Hh in E107. rewrite Hl in E103.
  unfold big_size. rewrite U_or2, CursorGlue.U_sll_lit, CursorGlue.U_srl_lit, U_zext_e by lia. cbn [eval]. rewrite E103, E107.
  change (16 mod 64) with 16. change (32 mod 64) with 32.
  replace ((2 + 256 * t + 65536 * 0 + 1) / 2 ^ 16) with 0 by (symmetry; apply Z.div_small; lia).
  rewrite Z.mul_0_l, Z.mod_0_l by (unfold M64v; lia). rewrite Z.lor_0_l. apply Z.mod_small. lia.
Qed.

Section BigNo.
Variables (nW : nat) (st : ustop) (bud : bool).

Lemma big_leaf_absurd : ltac2:(tb__ "0|1|
S1aS2cS0S0S25S0S1cS18Q40M0A1A1S1fSdS1bS2dS4S5S26A1S6S24R4A1A1A3S1dA3S29R7R6A2S10S17G0S1R7PdA2A2S2bA2S23S19S28VnW;Vst;Vbud;RbRaR8A6R7R6R5R4A6SfF_;F_;F_;F_;Fw;FtpE;FrhoE;FE;Frho1';Frho;FKc;FA';").
Proof.
  intros A' Kc rho rho1' E rhoE tpE w HB R Hn [Hsm HJ].
  pose proof (smatchA_facts segsA rhoE tpE E w Hsm) as HF.
  apply existsb_exists in HB as (f & Hf & Ef). apply sprop_eqb_sound in Ef. subst f.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as HBF.
  destruct w as [tr [ms md]]. destruct HJ as [Hag _].
  destruct R as [_ (t & Ht & _ & E104) _ _ N1 _ E103 E107 _ _].
  assert (A103 : rw rhoE 103%positive = rw rho1' 103%positive) by (symmetry; apply (proj1 Hag); reflexivity).
  assert (A107 : rw rhoE 107%positive = rw rho1' 107%positive) by (symmetry; apply (proj1 Hag); reflexivity).
  unfold kQuarantineMax in Hn.
  pose proof (big_size_small rhoE (bv_unsigned (rw rho1' 13%positive)) t Ht ltac:(lia) ltac:(rewrite A103; exact E103) ltac:(rewrite A107, E107, E104; reflexivity)) as EV.
  unfold big_fact in HBF. apply (proj1 (holds_nbgeu _ _ _)) in HBF. rewrite EV in HBF.
  rewrite CursorGlue.U_lit in HBF. unfold M64v in HBF. rewrite Z.mod_small in HBF by lia. lia.
Qed.

Lemma contF_small : ltac2:(tb__ "0|1|
ScOF_;S1fOF_;S1aS2cS0S0S25S20SdS1bS2dS4S5S26A1S6S24R2A1A1A3S1dA3S29R5R4A2S10S17Q40M0S1R6PdA2A2S2bA2S1aS0S0S1cS18G0A1A1S2aRdR4A2S2eR10RbR4A3S22S19R10S23S19S28VnW;Vst;Vbud;R6ReR5A6RbR4R3A5RaA4F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;FQ;FE;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 E Q HB R Hn A' rho1' rhoE tpE _ HL n Hg w Hw. exfalso.
  pose proof (rigF_hd keep rho rho1 rho1' R HL) as R'.
  apply (big_leaf_absurd A' Kc rho rho1' E rhoE tpE w HB R'); [|exact Hw].
  rewrite <- (proj1 (rg_agree _ _ R') 13%positive eq_refl). exact Hn.
Qed.
Lemma econtF_small : ltac2:(tb__ "0|1|
ScOF_;S1aS2cS0S0S25S1fOF_;SdS1bS2dS4S5S26A1S6S24R2A1A1A3S1dA3S29R5R4A2S10S17Q40M0S1R6PdA2A2S2bA2S1aS0S0S1cS18G0A1A1S2aRdR4A2S2eRfRbR4A3S21S19S23S19S28VnW;Vst;Vbud;R6ReR5A6RbR4R3A5RaA3F_;F_;FtpE;FrhoE;Frho1';FA';F_;F_;F_;FQ;FE;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 E Q HB R Hn A' rho1' rhoE tpE _ HL w Hw. exfalso.
  pose proof (rigF_hd keep rho rho1 rho1' R HL) as R'.
  apply (big_leaf_absurd A' Kc rho rho1' E rhoE tpE w HB R'); [|exact Hw].
  rewrite <- (proj1 (rg_agree _ _ R') 13%positive eq_refl). exact Hn.
Qed.
End BigNo.
End F0A_bigno.

