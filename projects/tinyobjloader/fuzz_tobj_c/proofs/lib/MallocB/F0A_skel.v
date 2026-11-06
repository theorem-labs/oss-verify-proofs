(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sprop"; "agree_below"; "sv"; "ss_lenient"; "ss_facts"; "sprop_below"; "swf"; "rw"; "sobj"; "SLit"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "prod"; "Some"; "false"; "option"; "pair"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "jpredA"; "liftKA"; "LQA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "mkLeafA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.F0"; "JF"; "rigF"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "ageom"; "budget_ok_free"; "class_state"; "qbatch"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "top_high"; "tp_ok"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "leaf"; "runA"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "PreQ1"; "leaves_at"; "FUELF"; "PostQ1"; "P0_f"; "sM_of"; "sQ_of"; "BIGX"; "CASX"; "DEPE"; "DRNE"; "ENQE"; "MSE"; "PSE"; "RETF"; "F_typ"; "PostMS"; "XD"; "XDr"; "XQ"; "casx"; "d3F"; "d4F"; "vH3"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "depot_onlyKf"; "@Stdlib.Lists.List"; "forallb"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1"; "JQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5"; "hd_link"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem"; "semF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "one_at"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma leaves_at1 : ltac2:(tb__ "0|0|
S10S25A1S1aS0S11S51R2S12S1aR1S14S1aA1A3A2S13A3S0S11S85R3R2A2S13A3F_;Fpc;Fl;").
Proof.
  intros l pc H. unfold leaves_at in H. apply andb_prop in H as [Hl Hf]. destruct l as [|L [|L' l']]; try discriminate Hl.
  cbn in Hf. rewrite Bool.andb_true_r in Hf. unfold one_at. exact Hf.
Qed.
Lemma leaves_at2 : ltac2:(tb__ "0|1|
S10S25A1M0S1aS1aS0S11S51R3S12S1aR2S12S1aR1S14S1aA1A3A3A2S13A3S2S25S25S2S25S25S0G0R6S12S25R2S12S25R1S14S25A1A3A3A3LL2;A2LL1;A2F_;Fpc2;Fpc1;Fl;").
Proof.
  intros l pc1 pc2 H. unfold leaves_at in H. apply andb_prop in H as [Hl _]. destruct l as [|L1 [|L2 [|L3 l']]]; try discriminate Hl.
  exists L1, L2. reflexivity.
Qed.

Lemma JQ_LQA : ltac2:(tb__ "0|1|
S1fS1bS4S10S2cQ40A1A1S23S2eS6aS22R5R4R3S12S15S23S69A2M0S19S23S69R2S7fR6A1A4S14G0A1A3R1A6S21S22R7R6R5R4S12S25S28R3S78A2S14S25A1A3R2A7F_;Fw;FPost;Ftp;Frho;Fn;FJ;").
Proof.
  intros J n rho tp Post w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  destruct Hin as [E|[]]. injection E as <- <-. destruct HJL as (HJ & -> & Hrm & Hrl). destruct Hag as [Hw Hl].
  exists (mkLeafA Post RsSymJump), rho'. split; [left; reflexivity|]. split; [|split; [exact Hsm | exact HJ]].
  split; [exact Hw|]. split; [exact Hl|]. intros a. symmetry. apply Hrm.
Qed.

Section Run2p.
Variables (fuel : nat) (cuts : list Z) (Pre : axst) (l : list leafA) (n : positive) (EA EB : axst) (pc1 pc2 : Z).
Hypothesis HLEN : ltac2:(tb__ "0|0|
S0S11S9S24VPre;A1A1S17A3").
Hypothesis RUNL : ltac2:(tb__ "0|0|
S0S10S25A1S4eVfuel;Vcuts;VPre;A3Vl;A3").
Hypothesis HL : ltac2:(tb__ "0|0|
S1S0S11S51Vl;S12S1aVpc1;S12S1aVpc2;S14S1aA1A3A3A2S13A3S1S0S23S4dU0Vl;A2VEA;A3S0S23S4dU1Vl;A2VEB;A3A2A2").
Lemma run2p_shape : ltac2:(tb__ "0|1|
S2S25S25S2S25S25S1S0S10S25A1M0Vl;S12S25R2S12S25R1S14S25A1A3A3A3S1S0S23S27R2A1VEA;A3S1S0S23S27R1A1VEB;A3S0S18G0A1S29S22Vfuel;Vcuts;VPre;S13A5S16G0Vl;A2A3A2A2A2LLB;A2LLA;A2").
Proof using RUNL HL.
  destruct HL as (La & Lb & Lc). destruct (leaves_at2 _ _ _ La) as (LA & LB & El). exists LA, LB. split; [exact El|].
  rewrite El in Lb, Lc. cbn in Lb, Lc. split; [exact Lb|]. split; [exact Lc|].
  apply (run_some fuel cuts Pre l RUNL). rewrite El. discriminate.
Qed.
Theorem run_cont2p : ltac2:(tb__ "0|1|
S1fS2eOF_;S4S10S2cQ40A1A1S31S1dS22R4R5A3S1eS22S5S24VPre;A1A1M0R6A3S4S7G0R6R1A3S30S22R8S1cS22R9VEA;R2R6A5R5A4F_;FrhoE;S4S7G0R7R1A3S30S22R9S1cS22RaVEB;R2R7A5R6A4F_;FrhoE;S30S22R8S1cS22R9VPre;R7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;Fok;FJ;").
Proof using HLEN RUNL HL.
  intros J ok rho tp Q HOK HST HCA HCB. destruct run2p_shape as (LA & LB & El & Ea & Eb & RUN). eapply triple_seq.
  - apply triple1_triple. exact (sym_run_soundA segsA fuel cuts Pre l ok J rho tp RUN HOK HLEN HST).
  - apply triple_LQA_of_leaves. intros L0 rhoE Hin Hag. rewrite El in Hin.
    destruct Hin as [<-|[<-|[]]]; [rewrite Ea; exact (HCA rhoE Hag) | rewrite Eb; exact (HCB rhoE Hag)].
Qed.
Theorem run_econt2p : ltac2:(tb__ "0|1|
S1fS4S10S2cQ40A1A1S2eOF_;S1eS22S5S24VPre;A1A1M0R4A3S4S7G0R5R1A3S2fS22S1cS22R7VEA;R2R5A5R4A3F_;FrhoE;S4S7G0R6R1A3S2fS22S1cS22R8VEB;R2R6A5R5A3F_;FrhoE;S2fS22S1cS22R7VPre;R6R5A5R4A3F_;F_;F_;FQ;Ftp;Frho;FJ;").
Proof using HLEN RUNL HL.
  intros J rho tp Q HST HCA HCB. destruct run2p_shape as (LA & LB & El & Ea & Eb & RUN). eapply etriple_seq.
  - exact (sym_run_etripleA segsA fuel cuts Pre l J rho tp HLEN HST RUN).
  - apply etriple_LQA_of_leaves. intros L0 rhoE Hin Hag. rewrite El in Hin.
    destruct Hin as [<-|[<-|[]]]; [rewrite Ea; exact (HCA rhoE Hag) | rewrite Eb; exact (HCB rhoE Hag)].
Qed.
End Run2p.

Section F0.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop. Variable q : qvar.

Variable bud : bool.
Let W : list ulink := Wcan nW.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition Jb (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|1|
S4S10S2cQ40M0A1A1S10S74A1S73S1VAInv;VA;R4R3R1A4S1S4aVW;Vst;R4A3S1S72S15S1aS1aA2S19S1aS1aS2dG0SdR4PcA2A2S2dG0SdR4PdA2A2A4S33VA;A1A3S1VKc;R2R1A2S1S49VA;R4A2S1S11OLbud;Vbud;S42VA;A1S3X11x2S48VA;R4A2A2A2A2A2A2A2Lmd;Ltr;Ltp;Lrho;").
Let J (A : AA) (Kc : KcA) : jpredA := Jb A Kc.

Definition depot_onlyKf (A A' : AA) : Prop := ltac2:(tb__ "0|2|
S1S0S41S3bVA';A1S3bVA;A1A3S1S0S10S43A1S38VA';A1S38VA;A1A3S1S0S11S37VA';A1S37VA;A1A3S1S0S10S45A1S40VA';A1S40VA;A1A3S1S0S1aS3dVA';A1S3dVA;A1A3S1S0S10S15S1aS1aA2A1M0S33VA';A1S33VA;A1A3S1S0S10S44A1M1S3fVA';A1S3fVA;A1A3S1S0G1S3eVA';A1S3eVA;A1A3S1S0S11S3cVA';A1S3cVA;A1A3S1S0S10G0A1S39VA';A1S39VA;A1A3S1S0S10S1aA1S3aVA';A1S3aVA;A1A3S1S0S1aS36VA';A1S36VA;A1A3S1S0S1aS35VA';A1S35VA;A1A3S0S1aS34VA';A1S86S34VA;A1Z1A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2").

Definition JF (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S7dS4S7S4cVrho1;R1A3Lr;VJ;VA;VKc;A2A2").

Lemma JFr_agree : ltac2:(tb__ "0|0|
S32S46S4S4S10S2cQ40A1A1S10S74A1S73S4bVW;Vst;A2S7S82R6R5A3VJ;R9R8R7R5R4R3A6VJ;RaR9R7R6R5R4A6F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FKc;FA;").
Proof.
  intros A Kc rho rho' tp tr md HUS Hag (HA & HU & HL & HK & Htp & HB & Htop). pose proof Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  split; [unfold AInv, AInvA in *; rewrite Erm; exact HA|]. split; [exact (HUS rho rho' Hag HU)|].
  split; [rewrite <- (Hw 12%positive), <- (Hw 13%positive) by (unfold NF; lia); exact HL|].
  split; [exact HK|]. split; [unfold tp_ok in *; rewrite <- (Hw 24%positive) by (unfold NF; lia); exact Htp |].
  split; [exact HB|]. unfold top_high in *. rewrite <- (Hw 10%positive), <- (Hw V_DEPTH) by (unfold NF, V_DEPTH; lia). exact Htop.
Qed.
Lemma J_stableA : ltac2:(tb__ "0|0|
S32S46S4bVW;Vst;A2S47R2A1S1eVsegs;S4cVJ;R4R3A2A3F_;F_;FKc;FA;").
Proof.
  intros A Kc HUS HKc rho rho' tp tr md md' Hag Hme HJ.
  pose proof (JFr_agree A Kc rho rho' tp tr md HUS ltac:(eapply agree_below_le; [|exact Hag]; cbv; discriminate) HJ) as (HA & HU & HL & HK & Htp & HB & Htop).
  split; [apply (AInvA_mat segs A rho' tp md md'); [exact HA | exact Hme]|].
  split; [exact HU|]. split; [exact HL|].
  split; [destruct Hme as ((mat' & ->) & _); rewrite with_vm_backing_with_vm; apply HKc; exact HK|].
  split; [exact Htp |]. split; [exact HB | exact Htop].
Qed.
Lemma JF_stable : ltac2:(tb__ "0|0|
S32S46S4S4bVW;Vst;A2S47R3A1S1eVsegs;S4cS2aR5R4R3A3A3F_;F_;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 HUS HKc. unfold JF. apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply J_stableA; assumption].
Qed.
Lemma JF_okf : ltac2:(tb__ "0|0|
S2eOF_;S32S10S74A1S73OF_;F_;S4S1dVsegs;R4S20R2A1A3S1dVsegs;R5S2aR4R3R2A3A3F_;Frho1;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho1 H r t tr ms md msv' [_ HJ]. apply (H r t tr ms md msv'). destruct HJ as (_ & _ & _ & HK & _). exact HK.
Qed.

Record rigF (rho rho1 : valuation) : Prop := mkRigF {
  rg_agree : agree_vals NF rho rho1;
  rg_t : exists t, 0 <= t < 256 /\ t mod 4 = 1 /\ bv_unsigned (rw rho1 104%positive) = 2 + 256 * t + 65536 * (bv_unsigned (rw rho1 13%positive) / 2 ^ 32);
  rg_p16 : bv_unsigned (rw rho1 12%positive) mod 16 = 0;
  rg_plo : 16 <= bv_unsigned (rw rho1 12%positive);
  rg_n : 1 <= bv_unsigned (rw rho1 13%positive);
  rg_pn : bv_unsigned (rw rho1 12%positive) + bv_unsigned (rw rho1 105%positive) <= aceilF;
  rg_103 : bv_unsigned (rw rho1 103%positive) = bv_unsigned (rw rho1 13%positive) mod 2 ^ 32;
  rg_107 : bv_unsigned (rw rho1 107%positive) = bv_unsigned (rw rho1 104%positive) + 1;
  rg_105 : bv_unsigned (rw rho1 105%positive) = (bv_unsigned (rw rho1 13%positive) + 7) / 8 * 8;
  rg_106 : bv_unsigned (rw rho1 106%positive) = bv_unsigned (rw rho1 105%positive) / 8 }.

Lemma rigF_hd : ltac2:(tb__ "0|0|
S1aOF_;S4S4S4S2bR3R2A2S80R5R3R2A3S2bR5R3A2F_;F_;Frho1';Frho1;Frho;Fkeep;").
Proof.
  intros keep rho rho1 rho1' R (Hw & Hl & Hm & Hd). destruct R as [[A1 A2] Ht P16 PL N PN E103 E107 E105 E106].
  constructor; rewrite ?Hw; try assumption.
  split; [intros i Hi; rewrite Hw; apply A1; exact Hi | intros l0; rewrite Hl; apply A2].
Qed.

Lemma rig_at : ltac2:(tb__ "0|0|
S4S4S4S2bR3R2A2S7S4cR3R2A3S2S1aS1aS83R4R1A2Lt;A2F_;F_;FrhoE;Frho1;Frho;").
Proof.
  intros rho rho1 rhoE [Hag (t & Ht1 & Ht2 & Ht3) P16 PL N PN E103 E107 E105 E106] (Hw & _ & _).
  exists t. unfold semF. rewrite <- !(Hw 12%positive), <- !(Hw 13%positive), <- !(Hw 103%positive), <- !(Hw 104%positive), <- !(Hw 105%positive),
    <- !(Hw 106%positive), <- !(Hw 107%positive) by (unfold GW; lia).
  destruct Ht1. repeat split; assumption.
Qed.

Lemma JF_agreeG : ltac2:(tb__ "0|0|
S32S46S4S23S4S10S2cQ40A1A1S2eS1cVsegs;S2aR7R6R5A3R4R3R2R1A6S7S4cR6R4A3F_;Fw;Ftp;FrhoE;FE;Frho1;FKc;FA;").
Proof. intros A Kc rho1 E rhoE tp w [_ [Hag _]]. exact Hag. Qed.

Section S1.
Variable exits1 : list axst.
Hypothesis Cert1 : ltac2:(tb__ "0|0|
S0S11S7bS22S52S12S1aS58S14S1aA1A3S4cS12S23S54VW;Vst;Vq;A3S14S23A1A3Vexits1;A6S13A3").
Hypothesis ECert1 : ltac2:(tb__ "0|2|
S0S11S7cS22S52S12S1aS58S14S1aA1A3S4cS12S79S7aS54VW;Vst;Vq;A3Z1SfZ0M0A1M1A3S14S79A1A3S81S23S79S23S7aR1G0G1A3LE;Vexits1;A4A6S13A3").

Theorem f0_s1 : ltac2:(tb__ "0|0|
S2eOF_;S32S46S4S10S2cQ40A1A1S31S4bVW;Vst;A2S47R5A1S1dVsegs;R8S20R6A1A3S23S4S72S23R2Vexits1;A3S30Vsegs;RcS1cVsegs;S2aRbRaR9A3R3R2R8A5R7A4F_;FrhoE;FE;S4S30Vsegs;RbS1cVsegs;S2aRaR9R8A3S54VW;Vst;Vq;A3R1R7A5R6A4FrhoP;F_;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho1 tp Q HUS HKc Hok HE rhoP.
  apply (cfg_soundA segs FUELF [CASX] GW [P0_f W st q] exits1 (JF A Kc rho1) ok Q tp).
  - apply JF_okf. exact Hok.
  - apply JF_stable; assumption.
  - exact Cert1.
  - intros E rhoE HinE. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE E rhoE HinE)].
  - left. reflexivity.
Qed.
Theorem ef0_s1 : ltac2:(tb__ "0|0|
S32S46S4S10S2cQ40A1A1S2eOF_;S4bVW;Vst;A2S47R5A1S23S4S72S23R2Vexits1;A3S2fVsegs;S1cVsegs;S2aRaR9R8A3R3R2R7A5R6A3F_;FrhoE;FE;S4S2fVsegs;S1cVsegs;S2aR9R8R7A3S54VW;Vst;Vq;A3R1R6A5R5A3FrhoP;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 tp Q HUS HKc HE rhoP.
  change (P0_f W st q) with (vna_state (mkVNA (P0_f W st q) 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELF [CASX] GW [mkVNA (P0_f W st q) 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1) (JF A Kc rho1) Q tp).
  - apply JF_stable; assumption.
  - intros n [<-|[]]. cbv. discriminate.
  - exact ECert1.
  - intros E rhoE HinE. apply in_map_iff in HinE as (E0 & <- & HinE0). cbn [vna_state].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (HE E0 rhoE HinE0)].
  - left. reflexivity.
Qed.
End S1.

Section S2.
Variables (S1 C2 EfD ED : axst) (l2 : list leafA).
Hypothesis D2 : ltac2:(tb__ "0|4|
S0S18S15S10S15S8S8A2M0A1M1S10S6A1M2A2M3A1S77S24VS1;A1S24VC2;A1A2S16G3S19G1G2S12G0S19S8S8S64S67A4S14G0A1A3S5fA4A2A3").
Hypothesis W2 : ltac2:(tb__ "0|1|
S1S0S11ScS24VC2;A1M0A1S13A3S1S0S1bS5G0A1S5S24VS1;A1A1A3S0S11S9G0A1S17A3A2A2").
Hypothesis NX2 : ltac2:(tb__ "0|0|
S0S11S68S4cS5S24VC2;A1A1A2S13A3").
Hypothesis EQ2 : ltac2:(tb__ "0|0|
S0S23S26VS1;S24VC2;A1A2VC2;A3").
Hypothesis RUN2 : ltac2:(tb__ "0|0|
S0S10S25A1S4eS52S12S1aS59S14S1aA1A3VC2;A3Vl2;A3").
Hypothesis L2 : ltac2:(tb__ "0|0|
S1S0S11S51Vl2;S12S1aS59S14S1aA1A3A2S13A3S0S23S4dU0Vl2;A2VEfD;A3A2").
Hypothesis AXD : ltac2:(tb__ "0|0|
S0S18S23A1S7eVEfD;S61A2S16S23VED;A2A3").

Lemma g1 : ltac2:(tb__ "0|0|
S32S46S4S4S4S10S2cQ40A1A1S2eS2bR5R4A2S1cVsegs;S2aR8R7R5A3VS1;R4R3R2A6S1cVsegs;S2aR9R8R6A3VC2;R5R4R3A6F_;F_;Fw;Ftp;FrhoE;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 rhoE tp w HR Hw. destruct W2 as (Wa & Wb & _).
  destruct (rig_at rho rho1 rhoE HR (JF_agreeG _ _ _ _ _ _ _ Hw)) as (t & HH).
  rewrite <- EQ2. eapply SPA_restate; [exact Wa | exact D2 | exact Wb | | | exact Hw].
  - unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (sem_casx rhoE t HH).
  - exact (sem_typ rhoE t HH).
Qed.

Theorem f0_s2 : ltac2:(tb__ "0|0|
S2eOF_;S32S46S4S4S10S2cQ40A1A1S31S4bVW;Vst;A2S47R6A1S1dVsegs;R9S20R7A1A3S2bR7R6A2S4S30Vsegs;RcS1cVsegs;S2aRbRaR8A3VED;R1R7A5R6A4FrhoE;S4S30Vsegs;RdS1cVsegs;S2aRcRbR9A3VS1;R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho rho1 tp Q HUS HKc Hok HR HC rhoE. destruct W2 as (Wa & Wb & Wc). destruct L2 as [La Lb].
  eapply triple_conseq; [intros w Hw; exact (g1 A Kc rho rho1 rhoE tp w HR Hw) | intros w Hw; exact Hw |].
  apply (run_cont1 FUELF [DEPE] C2 l2 (ss_next (ax_S C2)) EfD Wc eq_refl RUN2 Lb DEPE (JF A Kc rho1) ok rhoE tp Q (leaves_at1 _ _ La)).
  - apply JF_okf. exact Hok.
  - eapply stableA_mono; [|apply JF_stable; assumption]. apply Pos.leb_le. exact NX2.
  - intros rhoX Hag. eapply triple_conseq; [intros w Hw; exact (SPA_axforms segs _ XD rhoX EfD ED tp w AXD Hw) | intros w Hw; exact Hw | apply HC].
Qed.
Theorem ef0_s2 : ltac2:(tb__ "0|0|
S32S46S4S4S10S2cQ40A1A1S2eOF_;S4bVW;Vst;A2S47R6A1S2bR6R5A2S4S2fVsegs;S1cVsegs;S2aRaR9R7A3VED;R1R6A5R5A3FrhoE;S4S2fVsegs;S1cVsegs;S2aRbRaR8A3VS1;R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 tp Q HUS HKc HR HC rhoE. destruct W2 as (Wa & Wb & Wc). destruct L2 as [La Lb].
  eapply etriple_conseq; [intros w Hw; exact (g1 A Kc rho rho1 rhoE tp w HR Hw) | intros w Hw; exact Hw |].
  apply (run_econt1 FUELF [DEPE] C2 l2 (ss_next (ax_S C2)) EfD Wc eq_refl RUN2 Lb DEPE (JF A Kc rho1) rhoE tp Q (leaves_at1 _ _ La)).
  - eapply stableA_mono; [|apply JF_stable; assumption]. apply Pos.leb_le. exact NX2.
  - intros rhoX Hag. eapply etriple_conseq; [intros w Hw; exact (SPA_axforms segs _ XD rhoX EfD ED tp w AXD Hw) | intros w Hw; exact Hw | apply HC].
Qed.
End S2.

Section S3.
Variables (TD TDr CD Eps Ebg : axst) (l3 : list leafA).
Hypothesis AXDr : ltac2:(tb__ "0|0|
S0S18S23A1S7eVTD;S62A2S16S23VTDr;A2A3").
Hypothesis ENTD : ltac2:(tb__ "0|0|
S0S11S84VTDr;VCD;A2S13A3").
Hypothesis RUN3 : ltac2:(tb__ "0|0|
S0S10S25A1S4eS52S12S1aS5dS12S1aS57S14S1aA1A3A3VCD;A3Vl3;A3").
Hypothesis L3 : ltac2:(tb__ "0|0|
S1S0S11S51Vl3;S12S1aS5dS12S1aS57S14S1aA1A3A3A2S13A3S1S0S23S4dU0Vl3;A2VEps;A3S0S23S4dU1Vl3;A2VEbg;A3A2A2").
Hypothesis NX3 : ltac2:(tb__ "0|1|
S1S0S11S68S4cS5S24VCD;A1M0A1A2S13A3S0S11S9G0A1S17A3A2").

Theorem f0_s3 : ltac2:(tb__ "0|0|
S2eOF_;S32S46S4S10S2cQ40A1A1S31S4bVW;Vst;A2S47R5A1S1dVsegs;R8S20R6A1A3S4S30Vsegs;RaS1cVsegs;S2aR9R8R7A3VEps;R1R6A5R5A4FrhoE;S4S30Vsegs;RbS1cVsegs;S2aRaR9R8A3VEbg;R1R7A5R6A4FrhoE;S4S30Vsegs;RcS1cVsegs;S2aRbRaR9A3VTD;R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho1 tp Q HUS HKc Hok HP HB rhoE. destruct L3 as (La & Lb & Lc). destruct NX3 as [Na Nb].
  pose proof (JF_stable A Kc rho1 HUS HKc) as HST.
  eapply triple_conseq; [intros w Hw; exact (SPA_axforms segs _ XDr rhoE TD TDr tp w AXDr Hw) | intros w Hw; exact Hw |].
  apply (ent_cont (JF A Kc rho1) ok TDr CD rhoE tp Q ENTD HST). intros rhoC HagC.
  apply (run_cont2p FUELF [PSE; BIGX] CD l3 Eps Ebg PSE BIGX Nb RUN3 (conj La (conj Lb Lc)) (JF A Kc rho1) ok rhoC tp Q).
  - apply JF_okf. exact Hok.
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoX _. apply HP.
  - intros rhoX _. apply HB.
Qed.
Theorem ef0_s3 : ltac2:(tb__ "0|0|
S32S46S4S10S2cQ40A1A1S2eOF_;S4bVW;Vst;A2S47R5A1S4S2fVsegs;S1cVsegs;S2aR8R7R6A3VEps;R1R5A5R4A3FrhoE;S4S2fVsegs;S1cVsegs;S2aR9R8R7A3VEbg;R1R6A5R5A3FrhoE;S4S2fVsegs;S1cVsegs;S2aRaR9R8A3VTD;R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 tp Q HUS HKc HP HB rhoE. destruct L3 as (La & Lb & Lc). destruct NX3 as [Na Nb].
  pose proof (JF_stable A Kc rho1 HUS HKc) as HST.
  eapply etriple_conseq; [intros w Hw; exact (SPA_axforms segs _ XDr rhoE TD TDr tp w AXDr Hw) | intros w Hw; exact Hw |].
  apply (ent_econt (JF A Kc rho1) TDr CD rhoE tp Q ENTD HST). intros rhoC HagC.
  apply (run_econt2p FUELF [PSE; BIGX] CD l3 Eps Ebg PSE BIGX Nb RUN3 (conj La (conj Lb Lc)) (JF A Kc rho1) rhoC tp Q).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoX _. apply HP.
  - intros rhoX _. apply HB.
Qed.
End S3.

Section S4.
Variables (Eps C3 Ems C4 TM0 : axst) (l4 : list leafA) (RM : list sobj).
Hypothesis D3 : ltac2:(tb__ "0|3|
S0S18S15S10S15S8S8A2A1M0S10S6A1M1A2M2A1S77S24VEps;A1S24VC3;A1A2S16G2S19G0G1S65S14S6A1A4A2A3").
Hypothesis W3 : ltac2:(tb__ "0|1|
S1S0S11ScS24VC3;A1M0A1S13A3S1S0S1bS5G0A1S5S24VEps;A1A1A3S0S11S9G0A1S17A3A2A2").
Hypothesis EQ3 : ltac2:(tb__ "0|0|
S0S23S26VEps;S24VC3;A1A2VC3;A3").
Hypothesis NX3' : ltac2:(tb__ "0|0|
S0S11S68S4cS5S24VC3;A1A1A2S13A3").
Hypothesis RUN4 : ltac2:(tb__ "0|0|
S0S10S25A1S4eS52S12S1aS5cS14S1aA1A3VC3;A3Vl4;A3").
Hypothesis L4 : ltac2:(tb__ "0|0|
S1S0S11S51Vl4;S12S1aS5cS14S1aA1A3A2S13A3S0S23S4dU0Vl4;A2VEms;A3A2").
Hypothesis D4 : ltac2:(tb__ "0|3|
S0S18S15S10S15S8S8A2A1M0S10S6A1M1A2M2A1S77S24VEms;A1S24VC4;A1A2S16G2S19G0G1S66S14S6A1A4A2A3").
Hypothesis W4 : ltac2:(tb__ "0|1|
S1S0S11ScS24VC4;A1M0A1S13A3S1S0S1bS5G0A1S5S24VEms;A1A1A3S0S11S9G0A1S17A3A2A2").
Hypothesis EQ4 : ltac2:(tb__ "0|0|
S0S23S26VEms;S24VC4;A1A2VC4;A3").
Hypothesis HeM : ltac2:(tb__ "0|1|
S0S18S10SeA1M0A1S6cVC4;S75S55VC4;A1A3S16G0VRM;A2A3").
Hypothesis HchkM : ltac2:(tb__ "0|0|
S0S11S6bVC4;S75S55VC4;A1VRM;S81S25S23S27S76A4A5S13A3").
Hypothesis HTM : ltac2:(tb__ "0|0|
S0S23S6dS55VC4;A1S75S60VC4;VRM;A5VTM0;A3").
Hypothesis FBM : ltac2:(tb__ "0|3|
S1S0S11S71S6SbS5S24VC4;A1M0A1M1A1SaG0A1M2A3S13A3S1S0S11S71S6SbS5S24VTM0;A1A1A1G2A3S13A3S0S11S68S4cG1A2S13A3A2A2").

Lemma g3 : ltac2:(tb__ "0|0|
S32S46S4S4S4S10S2cQ40A1A1S2eS2bR5R4A2S1cVsegs;S2aR8R7R5A3VEps;R4R3R2A6S1cVsegs;S2aR9R8R6A3VC3;R5R4R3A6F_;F_;Fw;Ftp;FrhoE;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 rhoE tp w HR Hw. destruct W3 as (Wa & Wb & _).
  destruct (rig_at rho rho1 rhoE HR (JF_agreeG _ _ _ _ _ _ _ Hw)) as (t & HH).
  rewrite <- EQ3. eapply SPA_restate; [exact Wa | exact D3 | exact Wb | | constructor | exact Hw].
  exact (sem_d3 rhoE t HH).
Qed.
Lemma g4 : ltac2:(tb__ "0|0|
S32S46S4S4S4S10S2cQ40A1A1S2eS2bR5R4A2S1cVsegs;S2aR8R7R5A3VEms;R4R3R2A6S1cVsegs;S2aR9R8R6A3VC4;R5R4R3A6F_;F_;Fw;Ftp;FrhoE;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 rhoE tp w HR Hw. destruct W4 as (Wa & Wb & _).
  destruct (rig_at rho rho1 rhoE HR (JF_agreeG _ _ _ _ _ _ _ Hw)) as (t & HH).
  rewrite <- EQ4. eapply SPA_restate; [exact Wa | exact D4 | exact Wb | | constructor | exact Hw].
  exact (sem_d4 rhoE t HH).
Qed.

Theorem f0_s4 : ltac2:(tb__ "0|2|
S2eOF_;S32S46S4S4S10S2cQ40A1A1M0S31S4bVW;Vst;A2S47R6A1S1dVsegs;R9S20R7A1A3S2bR7R6A2S4G0S30Vsegs;RdS1cVsegs;S2aRcRbR9A3M1S6eVTM0;SaS24VC4;A1A1A2R2R1A5R7A4FtpE;FrhoE;S4S30Vsegs;RdS1cVsegs;G1VEps;R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho rho1 tp Q HUS HKc Hok HR HC rhoE. destruct W3 as (W3a & W3b & W3c). destruct L4 as [La Lb]. destruct FBM as (Fa & Fb & Fc).
  pose proof (JF_stable A Kc rho1 HUS HKc) as HST. pose proof (JF_okf ok A Kc rho1 Hok) as HOK.
  eapply triple_conseq; [intros w Hw; exact (g3 A Kc rho rho1 rhoE tp w HR Hw) | intros w Hw; exact Hw |].
  apply (run_cont1 FUELF [MSE] C3 l4 (ss_next (ax_S C3)) Ems W3c eq_refl RUN4 Lb MSE (JF A Kc rho1) ok rhoE tp Q (leaves_at1 _ _ La) HOK).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact NX3'.
  - intros rhoM HagM.
    eapply triple_conseq; [intros w Hw; exact (g4 A Kc rho rho1 rhoM tp w HR Hw) | intros w Hw; exact Hw |].
    apply (call_cont C4 Pre_memsetA Posts_memsetA (sM_of C4) RM TM0 GW
             (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs)
             HeM HchkM ltac:(intros P [<-|[]]; exact HTM) Fa Fb ltac:(apply Pos.leb_le; exact Fc) (JF A Kc rho1) ok rhoM tp Q HOK HST).
    intros rho' Hag'. apply HC.
Qed.
Theorem ef0_s4 : ltac2:(tb__ "0|2|
S32S46S4S4S10S2cQ40A1A1M0S2eOF_;S4bVW;Vst;A2S47R6A1S2bR6R5A2S4G0S2fVsegs;S1cVsegs;S2aRbRaR8A3M1S6eVTM0;SaS24VC4;A1A1A2R2R1A5R6A3FtpE;FrhoE;S4S2fVsegs;S1cVsegs;G1VEps;R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;").
Proof.
  intros A Kc rho rho1 tp Q HUS HKc HR HC rhoE. destruct W3 as (W3a & W3b & W3c). destruct L4 as [La Lb]. destruct FBM as (Fa & Fb & Fc).
  pose proof (JF_stable A Kc rho1 HUS HKc) as HST.
  eapply etriple_conseq; [intros w Hw; exact (g3 A Kc rho rho1 rhoE tp w HR Hw) | intros w Hw; exact Hw |].
  apply (run_econt1 FUELF [MSE] C3 l4 (ss_next (ax_S C3)) Ems W3c eq_refl RUN4 Lb MSE (JF A Kc rho1) rhoE tp Q (leaves_at1 _ _ La)).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact NX3'.
  - intros rhoM HagM.
    eapply etriple_conseq; [intros w Hw; exact (g4 A Kc rho rho1 rhoM tp w HR Hw) | intros w Hw; exact Hw |].
    apply (call_econt C4 Pre_memsetA Posts_memsetA (sM_of C4) RM TM0 GW
             (fun Jx r0 t0 Hs => memset_sumA_ex Jx r0 t0 Hs)
             HeM HchkM ltac:(intros P [<-|[]]; exact HTM) Fa Fb ltac:(apply Pos.leb_le; exact Fc) (JF A Kc rho1) rhoM tp Q HST).
    intros rho' Hag'. apply HC.
Qed.
End S4.

Section S5.
Variables (TM Eq EQ TQ0 : axst) (l5 : list leafA) (RQ : list sobj).
Hypothesis NX5 : ltac2:(tb__ "0|1|
S1S0S11S68S4cS5S24VTM;A1M0A1A2S13A3S0S11S9G0A1S17A3A2").
Hypothesis RUN5 : ltac2:(tb__ "0|0|
S0S10S25A1S4eS52S12S1aS5bS14S1aA1A3VTM;A3Vl5;A3").
Hypothesis L5 : ltac2:(tb__ "0|0|
S1S0S11S51Vl5;S12S1aS5bS14S1aA1A3A2S13A3S0S23S4dU0Vl5;A2VEq;A3A2").
Hypothesis AXQ : ltac2:(tb__ "0|0|
S0S18S23A1S7eVEq;S63A2S16S23VEQ;A2A3").
Hypothesis HeQ : ltac2:(tb__ "0|1|
S0S18S10SeA1M0A1S6cVEQ;S50Vq;A1S56VEQ;Vq;A2A3S16G0VRQ;A2A3").
Hypothesis HchkQ : ltac2:(tb__ "0|0|
S0S11S6bVEQ;S50Vq;A1S56VEQ;Vq;A2VRQ;S12S23S53Vq;A1S14S23A1A3A5S13A3").
Hypothesis HTQ : ltac2:(tb__ "0|0|
S0S23S6dS56VEQ;Vq;A2S50Vq;A1S53Vq;A1VEQ;VRQ;A5VTQ0;A3").
Hypothesis FBQ : ltac2:(tb__ "0|3|
S1S0S11S71S6SbS5S24VEQ;A1M0A1M1A1SaG0A1M2A3S13A3S1S0S11S71S6SbS5S24VTQ0;A1A1A1G2A3S13A3S0S11S68S4cG1A2S13A3A2A2").

Lemma seg_Q1_sound : ltac2:(tb__ "0|1|
S1fS2eOF_;S4S10S2cQ40A1A1S1dS22R3R4A3S1eS22S4fR5A3S30S22R5S1cS22R6S50Vq;A1R4R3A5S6aS22S4fR4R3S12S15S23S69A2M0S19S23S69S53Vq;A1S7fR6A1A4S14G0A1A3A5A4F_;F_;Ftp;Frho;Fok;FJx;").
Proof. destruct q; [exact seg_Q1A_sound | exact seg_Q1Be_sound | exact seg_Q1Bf_sound]. Qed.
Lemma seg_Q1_complete : ltac2:(tb__ "0|1|
S1fS4S10S2cQ40A1A1S1eS22S4fR3A3S2fS22S1cS22R4S50Vq;A1R3R2A5S6aS22S4fR3R2S12S15S23S69A2M0S19S23S69S53Vq;A1S7fR4A1A4S14G0A1A3A5A3F_;Ftp;Frho;FJx;").
Proof. destruct q; [exact seg_Q1A_complete | exact seg_Q1Be_complete | exact seg_Q1Bf_complete]. Qed.
Lemma preQ1_nx : ltac2:(tb__ "0|0|
S0S1bS5S24S50Vq;A1A1A1S4fA3").
Proof. destruct q; reflexivity. Qed.
Lemma sumQ1 : ltac2:(tb__ "0|2|
S2eOF_;S1fS4S10S2cQ40A1A1S1dS22R4R3A3S1eS22S5S24S50Vq;A1M0A1A1M1R4A3S30S22R6S1cS22R5G0R4R3A5S21S22R5G1R4R3S12S25S28S53Vq;A1S78A2S14S25A1A3A6A4F_;F_;Ftp;Frho;FJx;Fok;").
Proof.
  intros ok Jx rho tp HOK HST. rewrite preQ1_nx in HST |- *.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA Jx NPRE rho tp (PostQ1 q) w Hw) | exact (seg_Q1_sound Jx ok rho tp HOK HST)].
Qed.
Lemma esumQ1 : ltac2:(tb__ "0|2|
S1fS4S10S2cQ40A1A1S1eS22S5S24S50Vq;A1M0A1A1M1R3A3S2fS22S1cS22R4G0R3R2A5S21S22R4G1R3R2S12S25S28S53Vq;A1S78A2S14S25A1A3A6A3F_;Ftp;Frho;FJx;").
Proof.
  intros Jx rho tp HST. rewrite preQ1_nx in HST |- *.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA Jx NPRE rho tp (PostQ1 q) w Hw) | exact (seg_Q1_complete Jx rho tp HST)].
Qed.

Theorem f0_s5 : ltac2:(tb__ "0|0|
S2eOF_;S32S46S4S10S2cQ40A1A1S31S4bVW;Vst;A2S47R5A1S1dVsegs;R8S20R6A1A3S4S30Vsegs;RaS1cVsegs;S2aR9R8R7A3S6eVTQ0;SaS24VEQ;A1A1A2R1R6A5R5A4FrhoE;S4S30Vsegs;RbS1cVsegs;S2aRaR9R8A3VTM;R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho1 tp Q HUS HKc Hok HC rhoE. destruct NX5 as [Na Nb]. destruct L5 as [La Lb]. destruct FBQ as (Fa & Fb & Fc).
  pose proof (JF_stable A Kc rho1 HUS HKc) as HST. pose proof (JF_okf ok A Kc rho1 Hok) as HOK.
  apply (run_cont1 FUELF [ENQE] TM l5 (ss_next (ax_S TM)) Eq Nb eq_refl RUN5 Lb ENQE (JF A Kc rho1) ok rhoE tp Q (leaves_at1 _ _ La) HOK).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoX HagX.
    eapply triple_conseq; [intros w Hw; exact (SPA_axforms segs _ XQ rhoX Eq EQ tp w AXQ Hw) | intros w Hw; exact Hw |].
    apply (call_cont EQ (PreQ1 q) [mkLeafA (PostQ1 q) RsSymJump] (sQ_of EQ q) RQ TQ0 GW sumQ1
             HeQ HchkQ ltac:(intros P [<-|[]]; exact HTQ) Fa Fb ltac:(apply Pos.leb_le; exact Fc) (JF A Kc rho1) ok rhoX tp Q HOK HST).
    intros rho' Hag'. apply HC.
Qed.
Theorem ef0_s5 : ltac2:(tb__ "0|0|
S32S46S4S10S2cQ40A1A1S2eOF_;S4bVW;Vst;A2S47R5A1S4S2fVsegs;S1cVsegs;S2aR8R7R6A3S6eVTQ0;SaS24VEQ;A1A1A2R1R5A5R4A3FrhoE;S4S2fVsegs;S1cVsegs;S2aR9R8R7A3VTM;R1R6A5R5A3FrhoE;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 tp Q HUS HKc HC rhoE. destruct NX5 as [Na Nb]. destruct L5 as [La Lb]. destruct FBQ as (Fa & Fb & Fc).
  pose proof (JF_stable A Kc rho1 HUS HKc) as HST.
  apply (run_econt1 FUELF [ENQE] TM l5 (ss_next (ax_S TM)) Eq Nb eq_refl RUN5 Lb ENQE (JF A Kc rho1) rhoE tp Q (leaves_at1 _ _ La)).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoX HagX.
    eapply etriple_conseq; [intros w Hw; exact (SPA_axforms segs _ XQ rhoX Eq EQ tp w AXQ Hw) | intros w Hw; exact Hw |].
    apply (call_econt EQ (PreQ1 q) [mkLeafA (PostQ1 q) RsSymJump] (sQ_of EQ q) RQ TQ0 GW esumQ1
             HeQ HchkQ ltac:(intros P [<-|[]]; exact HTQ) Fa Fb ltac:(apply Pos.leb_le; exact Fc) (JF A Kc rho1) rhoX tp Q HST).
    intros rho' Hag'. apply HC.
Qed.
End S5.

Section S6.
Variables (TQ Edr Xf : axst) (l6 : list leafA).
Hypothesis NX6 : ltac2:(tb__ "0|1|
S1S0S11S68S4cS5S24VTQ;A1M0A1A2S13A3S0S11S9G0A1S17A3A2").
Hypothesis RUN6 : ltac2:(tb__ "0|0|
S0S10S25A1S4eS52S12S1aS5aS12S1aS5eS14S1aA1A3A3VTQ;A3Vl6;A3").
Hypothesis L6 : ltac2:(tb__ "0|0|
S1S0S11S51Vl6;S12S1aS5aS12S1aS5eS14S1aA1A3A3A2S13A3S1S0S23S4dU0Vl6;A2VEdr;A3S0S23S4dU1Vl6;A2VXf;A3A2A2").

Theorem f0_s6 : ltac2:(tb__ "0|0|
S2eOF_;S32S46S4S10S2cQ40A1A1S31S4bVW;Vst;A2S47R5A1S1dVsegs;R8S20R6A1A3S4S30Vsegs;RaS1cVsegs;S2aR9R8R7A3VEdr;R1R6A5R5A4FrhoE;S4S30Vsegs;RbS1cVsegs;S2aRaR9R8A3VXf;R1R7A5R6A4FrhoE;S4S30Vsegs;RcS1cVsegs;S2aRbRaR9A3VTQ;R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho1 tp Q HUS HKc Hok HD HX rhoE. destruct NX6 as [Na Nb].
  pose proof (JF_stable A Kc rho1 HUS HKc) as HST.
  apply (run_cont2p FUELF [DRNE; RETF] TQ l6 Edr Xf DRNE RETF Nb RUN6 L6 (JF A Kc rho1) ok rhoE tp Q).
  - apply JF_okf. exact Hok.
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoX _. apply HD.
  - intros rhoX _. apply HX.
Qed.
Theorem ef0_s6 : ltac2:(tb__ "0|0|
S32S46S4S10S2cQ40A1A1S2eOF_;S4bVW;Vst;A2S47R5A1S4S2fVsegs;S1cVsegs;S2aR8R7R6A3VEdr;R1R5A5R4A3FrhoE;S4S2fVsegs;S1cVsegs;S2aR9R8R7A3VXf;R1R6A5R5A3FrhoE;S4S2fVsegs;S1cVsegs;S2aRaR9R8A3VTQ;R1R7A5R6A3FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 tp Q HUS HKc HD HX rhoE. destruct NX6 as [Na Nb].
  pose proof (JF_stable A Kc rho1 HUS HKc) as HST.
  apply (run_econt2p FUELF [DRNE; RETF] TQ l6 Edr Xf DRNE RETF Nb RUN6 L6 (JF A Kc rho1) rhoE tp Q).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoX _. apply HD.
  - intros rhoX _. apply HX.
Qed.
End S6.
End F0.

Definition HDF (nW : nat) (st : ustop) (keep : Z -> Prop) (ok : world -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (ED TD : axst) (Q : assn) : Prop := ltac2:(tb__ "0|1|
S4S10S2cQ40A1A1M0S32S4S4G0S70VA;R4A2S80Vkeep;Vrho1;R4A3S30S22Vok;S1cS22S6fVnW;Vst;S17R6VKc;R5A6VTD;R4R3A5VQ;A4F_;F_;Ftp';FrhoX;Frho1';FA';S30S22Vok;S1cS22S6fVnW;Vst;S13VA;VKc;Vrho1;A6VED;R3R2A5VQ;A4F_;Ftp;FrhoE;").
Definition HDFE (nW : nat) (st : ustop) (keep : Z -> Prop) (A : AA) (Kc : KcA) (rho1 : valuation) (ED TD : axst) (Q : world -> Prop) : Prop := ltac2:(tb__ "0|1|
S4S10S2cQ40A1A1M0S32S4S4G0S70VA;R4A2S80Vkeep;Vrho1;R4A3S2fS22S1cS22S6fVnW;Vst;S17R6VKc;R5A6VTD;R4R3A5VQ;A3F_;F_;Ftp';FrhoX;Frho1';FA';S2fS22S1cS22S6fVnW;Vst;S13VA;VKc;Vrho1;A6VED;R3R2A5VQ;A3F_;Ftp;FrhoE;").

