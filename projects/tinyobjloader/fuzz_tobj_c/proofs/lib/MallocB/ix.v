(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel ii.
From Stdlib Require FunctionalExtensionality.

(* [comment removed for export] *)
Module F0A_i2Bf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "@Corelib.Init.Datatypes"; "list"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "HDF"; "HDFE"; "depot_onlyKf"; "rigF"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_i2Bf.I2Bf"; "contF"; "econtF"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf"; "ED_2Bf_1"; "ED_2Bf_2"; "ED_2Bf_3"; "ED_2Bf_4"; "Ebg_2Bf"; "Edr_2Bf"; "P0_2Bf"; "TD_2Bf_1"; "TD_2Bf_2"; "TD_2Bf_3"; "TD_2Bf_4"; "Xf_2Bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_c2Bf.
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

(* [comment removed for export] *)
Module F0A_bigno.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "SAlu"; "SLit"; "sprop"; "sprop_eqb"; "ss_facts"; "SVar"; "SExt"; "SPBranch"; "SPNot"; "eval"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "div"; "lt"; "modulo"; "pow"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "big_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "rigF"; "depot_onlyKf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "@Stdlib.Lists.List"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_OR"; "ALU_SLL"; "ALU_SRL"; "BC_GEU"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side.
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

(* [comment removed for export] *)
Module F0A_skelC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Datatypes"; "list"; "false"; "bool"; "true"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
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
Module F0A_skelc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "ss_next"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "bool"; "true"; "list"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@Stdlib.Lists.List"; "In"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
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
Module UnwT_side.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "obj_range"; "rm"; "ss_objs"; "valuation"; "@Corelib.Init.Datatypes"; "list"; "nil"; "prod"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "PRES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop"; "side"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma side_of : ltac2:(tb__ "0|1|
SaS11A1S14S4S9S3S3SfSaScS4S4A2M0A1S13R5A1SbG0A1A3S10S5S5S0SdS3S3S6R5R1A2A3R4A2Lo;S8S12R6A1A1A3S0S15R4A2S0S1R5Z10A2SeR6R7A2A2S0SeR7R8A2R5A2S0R6S2Z2Z3eA2A2S16RcS7R9A1R8R7A4S17RdRcRbRaA4F_;F_;F_;F_;F_;F_;F_;Fhb;Fspu;Frho;Fb;FLT;Fsegs;").
Proof.
  intros segs LT b rho spu hb HX HO H1 H2 H3 H4 HP. unfold side. cbv zeta.
  split; [lia|]. split; [lia|]. split; [|split].
  - eapply Forall_impl; [|exact HO]. intros o Ho. cbv beta in Ho. unfold ranges_disjoint. cbn [fst snd]. right. right. left. lia.
  - apply (PRES_sub segs (rm rho) spu hb); [lia | lia | exact HP].
  - destruct LT as [S X bs]. cbn in HX. subst X. apply xwords_clear_nil.
Qed.
End UnwT_side.

(* [comment removed for export] *)
Module UnwT_node.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sobj"; "sprop"; "SLit"; "obj_range"; "SVar"; "rm"; "rw"; "ss_objs"; "SAlu"; "SPUle"; "agree_below"; "sv_below"; "SPBranch"; "ob_base"; "ob_hi"; "ob_lo"; "SPNot"; "sprop_eqb"; "ss_facts"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "true"; "andb"; "bool"; "nil"; "pair"; "false"; "option"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "pow"; "div"; "lt"; "sub"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "ag_stack_top"; "aa_Kf"; "aa_Km"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node.Node"; "obnd"; "JT"; "J_free_tol_preT"; "objs_le"; "obnd_below"; "side_chkb"; "side_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "liftKA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "UStopLe"; "J_free_preT"; "Kc_ok"; "ulink"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "HBz"; "PRES"; "STK_SPAN"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "BC_GEU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "pFR"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "KMAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop"; "side"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_glue2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.UnwT_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_side.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma HTOP_B : InitState.segs_top segsA <= IMG_HI.
Proof. vm_compute. discriminate. Qed.

Lemma HBz_bounds : ltac2:(tb__ "0|1|
S20S23S25Z0R1A2S25R1Z7fffff800000A2A2S23S25S26R2S4fA2S4dR2A1M0A2S25G0Z1000000000000A2A2F_;Ft;").
Proof.
  intros t Ht. unfold HBz, STK_SPAN, page_round_up_Z, page_size.
  pose proof (Z.div_mod (t + 8388448 + 4096 - 1) 4096 ltac:(lia)) as E. pose proof (Z.mod_pos_bound (t + 8388448 + 4096 - 1) 4096 ltac:(lia)) as B.
  set (q := (t + 8388448 + 4096 - 1) / 4096) in *. set (r := (t + 8388448 + 4096 - 1) mod 4096) in *. lia.
Qed.

Lemma sub16_mod : ltac2:(tb__ "0|2|
S20S23S25Z10M0R1A2S2aR1Z10000000000000000M1A2A2S22S20S27S26R2Zfffffffffffffff0A2G1A2S2bR2G0A2A3F_;Fx;").
Proof.
  intros x Hx. replace (x + 18446744073709551600) with ((x - 16) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma srl12_ge : ltac2:(tb__ "0|1|
S20S25Z0M0R1A2S24S22S20S29R2S28Z2S27ZcZ40A2A2A2S27G0Z10000000000000000A2A3A1S25Z1000R3A2F_;F_;Fx;").
Proof.
  intros x Hx H. change (2 ^ (12 mod 64)) with 4096 in H. change (0 mod 18446744073709551616) with 0 in H.
  destruct (Z_lt_ge_dec x 4096) as [L|G]; [exfalso; apply H; apply Z.div_small; lia | lia].
Qed.

Section Node.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition J_free_tol_preT (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S0S15S2cQ40M0A1A1S15S48A1S47S23S42VAInv;S1bS44A1S41VA;VKc;R4R3R2R1A9S23S25S26S34VA;A1S33VA;A1A2S5aA2S4eVsegs;S7R4A1S2dG0S8R4PaA2A2S4dS31S30VA;A1A1A1A4A2A2Lmd;Ltr;Ltp;Lrho;").

Definition JT (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|1|
S0S15S2cQ40M0A1A1S15S48A1S47S23S55U0S41S18VA;VKc;Vrho1;R4R3R2R1AaS4eVsegs;S7R4A1S2dG0S8R4PaA2A2S4dS31S30VA;A1A1A1A4A2Lmd;Ltr;Ltp;Lrho;").

Lemma rm_agree : ltac2:(tb__ "0|0|
S21S0S0ScR3R2R1A3S22S2cQ40A1S1eS2cQ8A1A1F_;S7R2A1S7R3A1A3F_;Frho';Frho;Fn;").
Proof. intros n rho rho' (_ & _ & Hm). apply functional_extensionality. intros a. symmetry. apply Hm. Qed.

Lemma JTr_agree : ltac2:(tb__ "0|0|
S2fS40S0S0S15S2cQ40A1A1S15S48A1S47ScS59R5R4A3S37R8R7R6R4R3R2A6S37R9R8R6R5R4R3A6F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FKc;FA;").
Proof.
  intros A Kc rho rho' tp tr md Hag (HJ & HK & HP). split; [|split; [exact HK|]].
  - exact (JFr_agree 0%nat UStopLe true A Kc rho rho' tp tr md (stopJ_stable_le _) Hag HJ).
  - rewrite (rm_agree _ _ _ Hag). rewrite <- (proj1 Hag 10%positive) by (unfold NF; lia). exact HP.
Qed.
Lemma JT_stable : ltac2:(tb__ "0|0|
S2fS40S0S43R2A1S3fVsegs;S54S36R4R3R2A3A3F_;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 HKc rho rho' tp tr md md' Hag Hme (HJ & HP). split.
  - exact (JF_stable 0%nat UStopLe true A Kc rho1 (stopJ_stable_le _) HKc rho rho' tp tr md md' Hag Hme HJ).
  - rewrite (rm_agree _ _ _ Hag). rewrite <- (proj1 Hag 10%positive) by (unfold GW; lia). exact HP.
Qed.
Lemma JT_okf : ltac2:(tb__ "0|0|
S49OF_;S2fS15S48A1S47OF_;F_;S0S3dVsegs;R4S3eR2A1A3S3dVsegs;R5S36R4R3R2A3A3F_;Frho1;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho1 H r t tr ms md msv' [HJ _]. exact (JF_okf 0%nat UStopLe true ok A Kc rho1 H r t tr ms md msv' HJ).
Qed.
Lemma SPA_JT_JF : ltac2:(tb__ "0|0|
S2fS40S0S4bS0S15S2cQ40A1A1S49S3cVsegs;S36R7R6R5A3R4R3R2R1A6S3cVsegs;S55U0S41S18R8R7R6A6R5R4R3R2A6F_;Fw;Ftp;Frho;FS;Frho1;FKc;FA;").
Proof. intros A Kc rho1 S rho tp w [Hsm [HJ _]]. split; assumption. Qed.

Lemma SPA_JT_intro : ltac2:(tb__ "0|0|
S2fS40S4bS0S15S2cQ40A1A1S49S3cVsegs;S37R6R5A2R4R3R2R1A6S3cVsegs;S36R7R6R4A3R5R4R3R2A6F_;Fw;Ftp;Frho1;FS;FKc;FA;").
Proof.
  intros A Kc S rho1 tp w [Hsm (HJ & _ & HP)]. split; [exact Hsm|]. split; [|exact HP].
  split; [apply agree_below_refl | exact HJ].
Qed.

Definition obnd (o : sobj) : sv * sv * sv := ltac2:(tb__ "0|0|
S1cS16S1S1A2S1S1cS1S1SfVo;A1S11Vo;A1A4S10Vo;A1A4").
Definition objs_le (rho : valuation) (spu : Z) (objs : list sobj) : Prop := ltac2:(tb__ "0|0|
S46S2S2S25S1fS20S20S5Vrho;R1A2A3Vspu;A2Lo;Vobjs;A3").
Lemma obj_range_bnd : ltac2:(tb__ "0|0|
S0S2S2S22S16S16S1S1A2S1A2S35R2A1S35R1A1A3S22S16S20S20A2S5R4R3A2S5R4R2A2A3F_;Fo';Fo;Frho;").
Proof. intros rho [b l h c d] [b' l' h' c' d'] E. unfold obnd in E. cbn in E. injection E as -> -> ->. reflexivity. Qed.
Lemma objs_le_bnds : ltac2:(tb__ "0|2|
S0S20S15S2A1M0G0S22S15S16S16S1S1A2S1A2M1A1S45S2G1S35R2A4S45S2G1S35R1A4A3S38R5R4R2A3S38R6R5R4A3F_;F_;Fl';Fl;Fspu;Frho;").
Proof.
  intros rho spu l. induction l as [|o l IH]; intros [|o' l'] E H; try discriminate E; [constructor|].
  cbn [map] in E. pose proof (f_equal (hd (obnd o)) E) as E1. pose proof (f_equal (@tl _) E) as E2. cbn [hd tl] in E1, E2. apply Forall_cons.
  - rewrite (obj_range_bnd rho o o' E1). exact (Forall_inv H).
  - exact (IH l' E2 (Forall_inv_tail H)).
Qed.
Definition obnd_below (n : positive) (o : sobj) : bool := ltac2:(tb__ "0|0|
S19S19SdVn;SfVo;A1A2SdVn;S11Vo;A1A2A2SdVn;S10Vo;A1A2A2").
Lemma obj_range_agreeb : ltac2:(tb__ "0|0|
S21S0S0S2ScR4R3R2A3S22S1aS39R5R2A2S18A3S22S16S20S20A2S5R4R3A2S5R5R3A2A3F_;F_;Fo;Frho';Frho;Fn;").
Proof.
  intros n rho rho' o Hag Hb. unfold obnd_below in Hb. apply andb_prop in Hb as [Hb Hh]. apply andb_prop in Hb as [Hb Hl].
  unfold obj_range, obj_lo_of, obj_hi_of.
  rewrite <- (eval_agree n rho rho' _ Hag Hb), (soff_agree n rho rho' _ Hag Hl), (soff_agree n rho rho' _ Hag Hh). reflexivity.
Qed.

Definition side_facts : list sprop := ltac2:(tb__ "0|3|
S17S3SbS6PaA1M0S4S28Z2Z2fA2A1A2S17S3SbS4S26Z7fff7f800000Z1000A2A1G0A2S17S3SbSaS50G0S4Z10A1A3S6S56A1M1A2S17S3S12SeS52G1SaS50S6P99A1M2S4N10A1A3A3A1S17S3SeS53SaS51G2S4ZcA1A3S4Z0A1A3S1bS3A1A3A3A3A3A3").

Definition side_chkb (P0 LT : axst) : bool := ltac2:(tb__ "0|3|
S19S19S57S2S39S54A1S9S4aVLT;A1M0A1A3S15S16S1S1A2M1A1M2S1aLx;S4cVLT;A1S18G1G2S1dLl;Lp;X15x2A2S57S3S3S58S3S13R1A1S14G0A1A3Lf;S3bA3A2").

Lemma hside_of : ltac2:(tb__ "0|5|
S2fS40S0S4bS4bS15S2cQ40M0A1M1A1S22S1aS3aR3R2A2S18A3S22S15S16S16S1S1A2S1A2M2A1S45S2G2S35S9S4aR3A1A1A4S45S2G2S35S9S4aR4A1A1A4A3S38R6S2dG0S8R6PaA2A2S9S4aR5A1A1A3S22G1S8R7P99A2S2eG0S32S30R9A1A1A2A3S23S25Z1S32S30RaA1M3A1M4A2S25G4S4dS31G3A1A1A2A2S0S49S3cVsegs;S36RdRcRbA3R9R2R8R1A6S5bVsegs;RaS6S56A1R3A4F_;Fw;Frho;F_;F_;F_;F_;F_;Ftp;FLT;FP0;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 P0 LT tp HC HB HO E153 HST rho w HS.
  unfold side_chkb in HC. apply andb_prop in HC as [HC HF]. apply andb_prop in HC as [HW HX].
  pose proof (SPA_facts_hold segs _ _ _ _ _ HS) as HFa.
  destruct HS as [_ [[Hag _] HP]].
  assert (FA : forall f, In f side_facts -> holds rho f).
  { intros f Hf. pose proof (proj1 (forallb_forall _ _) HF f Hf) as X. apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
    exact (proj1 (Forall_forall _ _) HFa f Hg). }
  pose proof (FA _ (or_introl eq_refl)) as F1. pose proof (FA _ (or_intror (or_introl eq_refl))) as F2.
  pose proof (FA _ (or_intror (or_intror (or_introl eq_refl)))) as F3. pose proof (FA _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as F4.
  pose proof (FA _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as F5.
  clear FA HF HFa.
  apply (proj1 (holds_ule _ _ _)) in F1, F2, F3. apply (proj1 (holds_nbgeu _ _ _)) in F4.
  rewrite U_lit in F1, F2. rewrite U_add, U_lit in F3. rewrite U_add, U_lit in F4. cbn [eval] in F1, F2, F3, F4.
  assert (E153' : rw rho 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))) by (rewrite <- (proj1 Hag 153%positive) by (unfold GW; lia); exact E153).
  rewrite E153' in F4. pose proof (topG_range (aa_geom A)) as TR.
  pose proof (proj2 (HBz_bounds (topG (aa_geom A)) ltac:(lia))) as HBhi.
  rewrite u64_lit in F4 by lia.
  apply (proj1 (holds_bne _ _ _)) in F5. rewrite U_srl_lit, U_lit in F5. cbn [eval] in F5. rewrite E153' in F5. rewrite u64_lit in F5 by lia.
  assert (HT4096 : 4096 <= ag_stack_top (aa_geom A)) by (apply srl12_ge; [clear - HST; lia | exact F5]).
  unfold M64v in *. change (2 ^ 47 mod 18446744073709551616) with (2 ^ 47) in F1.
  change ((140735332483072 + 4096) mod 18446744073709551616) with 140735332487168 in F2.
  change (16 mod 18446744073709551616) with 16 in F3. change (-16 mod 18446744073709551616) with 18446744073709551600 in F4.
  pose proof (urange (rw rho 10%positive)) as U10.
  rewrite Z.mod_small in F3 by lia.
  rewrite sub16_mod in F4 by lia.
  apply (side_of segs LT (SVar pFR) rho (bv_unsigned (rw rho 10%positive)) (HBz (topG (aa_geom A)))).
  - destruct (ax_X LT); [reflexivity | discriminate HX].
  - assert (E10 : bv_unsigned (rw rho 10%positive) = bv_unsigned (rw rho1 10%positive)) by (rewrite <- (proj1 Hag 10%positive) by (unfold GW; lia); reflexivity).
    rewrite E10.
    pose proof (objs_le_bnds rho1 _ _ _ HB HO) as HO1. unfold objs_le in *.
    apply Forall_forall. intros o Ho. rewrite (obj_range_agreeb GW rho1 rho o Hag (proj1 (forallb_forall _ _) HW o Ho)).
    exact (proj1 (Forall_forall _ _) HO1 o Ho).
  - unfold IMG_HI. lia.
  - unfold uval. cbn [eval]. lia.
  - unfold uval. cbn [eval]. lia.
  - lia.
  - exact HP.
Qed.
End Node.
End UnwT_node.

