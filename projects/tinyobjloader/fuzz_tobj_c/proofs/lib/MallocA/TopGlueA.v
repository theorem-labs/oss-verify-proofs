(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "cons"; "prod"; "nil"; "pair"; "app"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SVar"; "rw"; "ss_facts"; "sprop"; "sv"; "SAlu"; "SPUle"; "holds"; "rm"; "sobj"; "ss_objs"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "liftKA"; "smatchA"; "jpredA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "ulink"; "ustop"; "J_alloc_preT"; "UStopLe"; "J_pure_pre"; "V_DEPTH"; "JL_pure"; "J_memcpy_preT"; "J_memset_preT"; "J_stack_free_preT"; "J_stack_malloc_preT"; "L_memcpy"; "V_TOP"; "calloc_size"; "J_free_null_preT"; "J_free_preT"; "J_stack_free_pre"; "J_stack_malloc_pre"; "Pre_callocI"; "Pre_freeI"; "Pre_free_nullI"; "Pre_mallocI"; "Pre_memcpyI"; "Pre_memsetI"; "Pre_stack_freeI"; "Pre_stack_mallocI"; "JL_free"; "JL_free_null"; "JL_stack_free"; "JL_stack_malloc"; "J_alloc_pre"; "L_free"; "L_free_null"; "L_memset"; "L_stack_free"; "L_stack_malloc"; "Posts_calloc"; "Posts_malloc"; "calloc_shape"; "free_shape"; "malloc_shape"; "top_var"; "J_free_null_pre"; "J_free_pre"; "J_memcpy_pre"; "J_memset_pre"; "J_pure_preT"; "Pre_calloc"; "Pre_free"; "Pre_free_null"; "Pre_malloc"; "Pre_memcpy"; "Pre_memset"; "Pre_stack_free"; "Pre_stack_malloc"; "calloc_contractA"; "calloc_contractA_ex"; "free_contractA"; "free_contractA_ex"; "free_null_contractA"; "free_null_contractA_ex"; "malloc_contractA"; "malloc_contractA_ex"; "memcpy_contractA"; "memcpy_contractA_ex"; "memset_contractA"; "memset_contractA_ex"; "pub_facts"; "stack_free_contractA"; "stack_free_contractA_ex"; "stack_malloc_contractA"; "stack_malloc_contractA_ex"; "stack_win"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "le"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue"; "refacts"; "@Stdlib.Lists.List"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA SummaryA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ZEval.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require TopGlue Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma top_high_of_factsA : ltac2:(tb__ "0|4|
S14S7SfR1SeS8S31A1SdS86S8PaM0A1S8S2aA1A3A2A2S81Z0M1S80S1dQ40M2S9R2G0A2A2S83Z40M3S1dG2S9R2S2aA2A2A2A2A2S7fS83G3S1dG2S9R3S2aA2A2A2G1A2S4eR5R4A2S6eR6R5A2F_;F_;F_;F_;Frho;FA;").
Proof.
  intros A rho H Hlo Hneg HT.

  pose proof (TopGlue.top_high_of_facts (MallocIface.mkMA MallocModel.init_state (MallocInv.Layout 0 (fun _ => 0) 0 0 (topG (aa_geom A)))) rho H Hlo Hneg) as X.
  unfold Contract.top_var, Contract.top_high, MallocLayout.topL in X. cbn [MallocIface.ma_L MallocInv.ly_top] in X.
  pose proof (topG_range (aa_geom A)) as TG.
  replace (Z.max 140735332483072 (Z.min (topG (aa_geom A)) 140737479966720)) with (topG (aa_geom A)) in X by lia.
  unfold top_high. rewrite (bv_signed_toS 64 (rw rho V_DEPTH)) by (cbn; lia). change (Z.of_N 64) with 64.
  apply X. exact HT.
Qed.

Lemma triple_by_pure : ltac2:(tb__ "0|1|
S0S84A1S6fOF_;OS72S72S6fR3R1A1R5F_;Fw;R4S71R7R6R4R3A4M0F_;G0F_;F_;FQ;FP;FX;Fok;Fsegs;").
Proof. intros segs ok X P Q HX H. eapply triple_conseq; [intros w Hw; exact (conj (HX w Hw) Hw) | intros w Hw; exact Hw | apply triple_pure; exact H]. Qed.
Lemma etriple_by_pure : ltac2:(tb__ "0|2|
S0S84A1OS6fOF_;M0G0S6fR3R1A1R5F_;Fw;R4S70R6R4R3A3M1F_;G1F_;F_;FQ;FP;FX;Fsegs;").
Proof. intros segs X P Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInvA : ltac2:(tb__ "0|0|
S14S7S0S1cQ40A1A1S7cOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Lemma pub_window : ltac2:(tb__ "0|6|
S7S0S1cQ40M0A1A1S75S1fS2S0S7dA1S85A2S0S11A1M1S0SbA1M2S79S7fZ0M3R5A2S7fR5S82Z2Z28A2A2A2S1aVsegs;R8R7R5R4A5S78G1S12S20R6A1A1S1S11S6dR4A3A3S78G2SaS20R7A1A1S5SbR4S68R8A1A3A3S79S81G3S80S1dG0S9RbPaM4A2A2S83Z40S1dG0S9RbS2aA2A2A2M5A2A2S79S7fG5G3A2SfRbSeS8S31A1SdS86S8G4A1S8S2aA1A3A2A2A2A2F_;F_;F_;F_;FFpre;Frest;Fw;FX;Fd;Ftp;Frho;").
Proof.
  intros rho tp d X w rest Fpre Hd Hsm Hobjs Hfacts.
  apply (TopGlue.pre_window segs rho d (ax_S X) (virt tp w) Hd (smatchA_smatch segs _ _ _ _ Hsm)).
  - exists rest. exact Hobjs.
  - rewrite Hfacts. intros p Hp. apply in_or_app. right. exact Hp.
Qed.

Lemma smatchA_drop_top : ltac2:(tb__ "0|2|
S7S0S1cQ40A1A1S1fS1fS2S0S7dA1S85A2S1aVsegs;R5R4R3R1A5S78S0S2ScScA2A1S21R3A1S21R4A1A3S78ScS22R4A1S22R5A1A3S78S13S20R5A1M0S88S20R6A1M1SaG0A1A2A3S89SbSaG1A1SaS20R7A1A1A3S1aVsegs;RaR9R7R6A5F_;F_;F_;F_;F_;Fw;FXI;FX;Ftp;Frho;").
Proof.
  intros rho tp X XI w (Hsm & HMI & Hwf & Hsh & Hhz) EX EB ES HI.
  split; [rewrite ES; apply TopGlue.smatch_refacts; [exact HI | exact Hsm]|].
  split; [exact HMI|]. split.
  { unfold axwf in *. rewrite ES, EX, EB. unfold TopGlue.refacts. cbn [ss_next]. exact Hwf. }
  split; [|exact Hhz].
  unfold shadow_ok in *. rewrite EX, EB, ES. unfold TopGlue.refacts. cbn [ss_objs]. exact Hsh.
Qed.

Local Ltac drop_incl :=
  intros p Hp;
  unfold Pre_malloc, Pre_mallocI, Pre_calloc, Pre_callocI, Pre_free, Pre_freeI, Pre_free_null, Pre_free_nullI,
         Pre_stack_malloc, Pre_stack_mallocI, Pre_stack_free, Pre_stack_freeI, Pre_memset, Pre_memsetI, Pre_memcpy, Pre_memcpyI in Hp |- *;
  cbn [ax_S mkA ss_facts] in Hp |- *; unfold pub_facts in *;
  rewrite ?in_app_iff in Hp; rewrite ?in_app_iff; tauto.

Lemma SPA_malloc_T : ltac2:(tb__ "0|1|
S0S25A1S26S14S23S7S0S1cQ40A1A1S6fS17Vsegs;S43VAInvA;R7R6R5R4S8PcA1M0A6S57VE;R7R6A3R3R2R1A6S17Vsegs;S27VAInvA;R8R7R6R5G0A6S3aVE;R8R7A3R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w [Hsm (HA & HK & HT & HU & HB & HN & HV)].
  destruct (pub_window rho tp malloc_depth (Pre_malloc E W st) w (unwind_objs W ++ A_globals) (unwind_factsS W st)
              ltac:(unfold malloc_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity | drop_incl].
  - split; [exact HA|]. split; [exact HK|]. split; [exact HT|]. split; [exact HU|]. split; [exact HB|]. split; [exact HN|].
    exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
Qed.

Lemma SPA_calloc_T : ltac2:(tb__ "0|0|
S0S25A1S26S14S23S7S0S1cQ40A1A1S6fS17Vsegs;S43VAInvA;R7R6R5R4S32A6S54VE;R7R6A3R3R2R1A6S17Vsegs;S27VAInvA;R8R7R6R5S32A6S37VE;R8R7A3R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w [Hsm (HA & HK & HT & HU & HB & HN & HV)].
  destruct (pub_window rho tp malloc_depth (Pre_calloc E W st) w (unwind_objs W ++ A_globals) (unwind_factsS W st)
              ltac:(unfold malloc_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity | drop_incl].
  - split; [exact HA|]. split; [exact HK|]. split; [exact HT|]. split; [exact HU|]. split; [exact HB|]. split; [exact HN|].
    exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
Qed.

Lemma SPA_free_T : ltac2:(tb__ "0|0|
S0S25A1S26S14S23S7S0S1cQ40A1A1S6fS17Vsegs;S50VAInvA;R7R6R5R4A5S55VE;R7R6A3R3R2R1A6S17Vsegs;S34VAInvA;R8R7R6R5A5S38VE;R8R7A3R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w [Hsm (HA & HU & HIn & HK & HT & HB & HV)].
  destruct (pub_window rho tp free_depth (Pre_free E W st) w (unwind_objs W ++ [mkObj (SVar 12) (SLit 0) (SVar 13) [] DUnknown] ++ A_globals) (unwind_factsS W st)
              ltac:(unfold free_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity | drop_incl].
  - split; [exact HA|]. split; [exact HU|]. split; [exact HIn|]. split; [exact HK|]. split; [exact HT|]. split; [exact HB|].
    exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
Qed.

Lemma SPA_free_null_T : ltac2:(tb__ "0|0|
S0S25A1S26S14S23S7S0S1cQ40A1A1S6fS17Vsegs;S4fVAInvA;R7R6R5R4A5S56VE;R7R6A3R3R2R1A6S17Vsegs;S33VAInvA;R8R7R6R5A5S39VE;R8R7A3R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w [Hsm (HA & HU & HK & HT & HV)].
  destruct (pub_window rho tp free_depth (Pre_free_null E W st) w (unwind_objs W ++ A_globals) (unwind_factsS W st)
              ltac:(unfold free_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity | drop_incl].
  - split; [exact HA|]. split; [exact HU|]. split; [exact HK|]. split; [exact HT|].
    exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
Qed.

Lemma SPA_stack_malloc_T : ltac2:(tb__ "0|0|
S75S14S23S7S0S1cQ40A1A1S6fS17Vsegs;S36VAInvA;R6R5R4A4S5bVE;R6A2R3R2R1A6S17Vsegs;S2fVAInvA;R7R6R5A4S3eVE;R7A2R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;Fc;").
Proof.
  intros c A Kc rho tp w [Hsm (HA & HK & HT & HN & HS & HV)].
  destruct (pub_window rho tp stack_malloc_depth (Pre_stack_malloc E c) w A_globals []
              ltac:(unfold stack_malloc_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity | drop_incl].
  - split; [exact HA|]. split; [exact HK|]. split; [exact HT|]. split; [exact HN|]. split; [exact HS|].
    exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
Qed.

Lemma SPA_stack_free_T : ltac2:(tb__ "0|0|
S75S14S23S7S0S1cQ40A1A1S6fS17Vsegs;S35VAInvA;R6R5R4A4S5aVE;R6A2R3R2R1A6S17Vsegs;S2eVAInvA;R7R6R5A4S3dVE;R7A2R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;Fc;").
Proof.
  intros c A Kc rho tp w [Hsm (HA & HK & HT & HIn & HF & HV)].
  destruct (pub_window rho tp stack_malloc_depth (Pre_stack_free E c) w
              ([frame_obj (SVar 12) c; flag_obj (SVar 12) c (SVar V_FL); flagbyte_obj (SVar V_FL) []] ++ A_globals) []
              ltac:(unfold stack_malloc_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity | drop_incl].
  - split; [exact HA|]. split; [exact HK|]. split; [exact HT|]. split; [exact HIn|]. split; [exact HF|].
    exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
Qed.

Lemma SPA_memset_T : ltac2:(tb__ "0|0|
S75S14S23S7S0S1cQ40A1A1S6fS17Vsegs;S52VAInvA;R5R4A3S59R6A1R3R2R1A6S17Vsegs;S2dVAInvA;R6R5A3S3cR7A1R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;Fentry;").
Proof.
  intros entry A Kc rho tp w [Hsm ((HA & HK & HT & HV) & HB)].
  destruct (pub_window rho tp memx_depth (Pre_memset entry) w ([mkObj (SVar 12) (SLit 0) (SVar 14) [] DUnknown] ++ A_globals) memset_facts
              ltac:(unfold memx_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity | drop_incl].
  - split; [|exact HB]. split; [exact HA|]. split; [exact HK|]. split; [exact HT|].
    exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
Qed.

Lemma SPA_memcpy_T : ltac2:(tb__ "0|0|
S75S14S23S7S0S1cQ40A1A1S6fS17Vsegs;S51VAInvA;R5R4A3S58R6A1R3R2R1A6S17Vsegs;S2cVAInvA;R6R5A3S3bR7A1R4R3R2A6F_;Fw;Ftp;Frho;FKc;FA;Fentry;").
Proof.
  intros entry A Kc rho tp w [Hsm ((HA & HK & HT & HV) & HB1 & HB2)].
  destruct (pub_window rho tp memx_depth (Pre_memcpy entry) w
              ([mkObj (SVar 12) (SLit 0) (SVar 14) [] DUnknown; mkObj (SVar 13) (SLit 0) (SVar 14) [] DUnknown] ++ A_globals) memcpy_facts
              ltac:(unfold memx_depth; lia) Hsm eq_refl eq_refl) as (Wlo & Wneg & Wf).
  split.
  - eapply smatchA_drop_top; [exact Hsm | reflexivity | reflexivity | reflexivity | drop_incl].
  - split; [|split; [exact HB1 | exact HB2]]. split; [exact HA|]. split; [exact HK|]. split; [exact HT|].
    exact (top_high_of_factsA A rho Wf Wlo Wneg HV).
Qed.

Lemma malloc_contractA_of_T : ltac2:(tb__ "0|0|
S0S25A1S26S6fOF_;S14S23S7S0S1cQ40A1A1S4dR7R6A2S24R4A1S18Vsegs;R7S19R5A1A3S7eVsegs;R8S19R6A1A3S71Vsegs;R9S17Vsegs;S27VAInvA;RbRaR8R7S8PcA1A6S3aVE;RbRaA3R6R5A5S74Vsegs;S77R6R5S4aVE;VAInvA;VCST;VXGL;RbRaR8R7A8A5A4F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;Fst;FW;S62Vsegs;VE;VAInvA;VCST;VXGL;A5F_;").
Proof.
  intros H W st ok A Kc rho tp HW HK HF HP. eapply triple_conseq; [apply SPA_malloc_T | intros w Hw; exact Hw | exact (H W st ok A Kc rho tp HW HK HF HP)].
Qed.
Lemma malloc_contractA_ex_of_T : ltac2:(tb__ "0|0|
S0S25A1S26S14S23S7S0S1cQ40A1A1S4dR6R5A2S24R4A1S70Vsegs;S17Vsegs;S27VAInvA;R8R7R6R5S8PcA1A6S3aVE;R8R7A3R4R3A5S74Vsegs;S77R4R3S4aVE;VAInvA;VCST;VXGL;R8R7R6R5A8A5A3F_;F_;Ftp;Frho;FKc;FA;Fst;FW;S63Vsegs;VE;VAInvA;VCST;VXGL;A5F_;").
Proof. intros H W st A Kc rho tp HW HK w Hw. exact (H W st A Kc rho tp HW HK w (SPA_malloc_T W st A Kc rho tp w Hw)). Qed.

Lemma calloc_contractA_of_T : ltac2:(tb__ "0|0|
S0S25A1S26S6fOF_;S14S23S7S0S1cQ40A1A1S4bR7R6A2S24R4A1S18Vsegs;R7S19R5A1A3S7eVsegs;R8S19R6A1A3S71Vsegs;R9S17Vsegs;S27VAInvA;RbRaR8R7S32A6S37VE;RbRaA3R6R5A5S74Vsegs;S77R6R5S49VE;VAInvA;VCST;VXGL;RbRaR8R7A8A5A4F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;Fst;FW;S5cVsegs;VE;VAInvA;VCST;VXGL;A5F_;").
Proof.
  intros H W st ok A Kc rho tp HW HK HF HP. eapply triple_conseq; [apply SPA_calloc_T | intros w Hw; exact Hw | exact (H W st ok A Kc rho tp HW HK HF HP)].
Qed.
Lemma calloc_contractA_ex_of_T : ltac2:(tb__ "0|0|
S0S25A1S26S14S23S7S0S1cQ40A1A1S4bR6R5A2S24R4A1S70Vsegs;S17Vsegs;S27VAInvA;R8R7R6R5S32A6S37VE;R8R7A3R4R3A5S74Vsegs;S77R4R3S49VE;VAInvA;VCST;VXGL;R8R7R6R5A8A5A3F_;F_;Ftp;Frho;FKc;FA;Fst;FW;S5dVsegs;VE;VAInvA;VCST;VXGL;A5F_;").
Proof. intros H W st A Kc rho tp HW HK w Hw. exact (H W st A Kc rho tp HW HK w (SPA_calloc_T W st A Kc rho tp w Hw)). Qed.

Lemma free_contractA_of_T : ltac2:(tb__ "0|1|
S0S25A1S26S6fOF_;S14S23S7S0S1cQ40A1A1S4cR7R6A2S24R4A1S18Vsegs;R7S19R5A1A3S7eVsegs;R8S19R6A1A3S71Vsegs;R9S17Vsegs;S34VAInvA;RbRaR8R7A5S38VE;RbRaA3R6R5A5S74Vsegs;S77R6R5S1S2S1fS73A2M0S4S1fS73S44VE;RbRaA3S3fVAInvA;VCST;VXGL;R8R7A5A4S3G0A1A3A5A4F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;Fst;FW;S5eVsegs;VE;VAInvA;VCST;VXGL;A5F_;").
Proof.
  intros H W st ok A Kc rho tp HW HK HF HP. eapply triple_conseq; [apply SPA_free_T | intros w Hw; exact Hw | exact (H W st ok A Kc rho tp HW HK HF HP)].
Qed.
Lemma free_contractA_ex_of_T : ltac2:(tb__ "0|1|
S0S25A1S26S14S23S7S0S1cQ40A1A1S4cR6R5A2S24R4A1S70Vsegs;S17Vsegs;S34VAInvA;R8R7R6R5A5S38VE;R8R7A3R4R3A5S74Vsegs;S77R4R3S1S2S1fS73A2M0S4S1fS73S44VE;R8R7A3S3fVAInvA;VCST;VXGL;R6R5A5A4S3G0A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;Fst;FW;S5fVsegs;VE;VAInvA;VCST;VXGL;A5F_;").
Proof. intros H W st A Kc rho tp HW HK w Hw. exact (H W st A Kc rho tp HW HK w (SPA_free_T W st A Kc rho tp w Hw)). Qed.

Lemma free_null_contractA_of_T : ltac2:(tb__ "0|2|
S6fOF_;S14S23S7S0S1cQ40A1A1S24R3A1S18Vsegs;R6S19R4A1A3S7eVsegs;R7S19R5A1A3S71Vsegs;R8S17Vsegs;S33VAInvA;S3S25A1M0S28R7R6A5S39VE;G0S28A3R5R4A5S74Vsegs;S77R5R4S1S2S1fS73A2M1S4S1fS73S45VE;G0S28A3S40VAInvA;VCST;VXGL;R7R6A5A4S3G1A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;S60Vsegs;VE;VAInvA;VCST;VXGL;A5F_;").
Proof.
  intros H ok A Kc rho tp HK HF HP. eapply triple_conseq; [apply SPA_free_null_T | intros w Hw; exact Hw | exact (H ok A Kc rho tp HK HF HP)].
Qed.
Lemma free_null_contractA_ex_of_T : ltac2:(tb__ "0|2|
S14S23S7S0S1cQ40A1A1S24R3A1S70Vsegs;S17Vsegs;S33VAInvA;S3S25A1M0S28R5R4A5S39VE;G0S28A3R3R2A5S74Vsegs;S77R3R2S1S2S1fS73A2M1S4S1fS73S45VE;G0S28A3S40VAInvA;VCST;VXGL;R5R4A5A4S3G1A1A3A5A3F_;Ftp;Frho;FKc;FA;S61Vsegs;VE;VAInvA;VCST;VXGL;A5F_;").
Proof. intros H A Kc rho tp HK w Hw. exact (H A Kc rho tp HK w (SPA_free_null_T [] UStopLe A Kc rho tp w Hw)). Qed.

Lemma stack_malloc_contractA_of_T : ltac2:(tb__ "0|1|
S75S6fOF_;S14S23S7S0S1cQ40A1A1S24R3A1S18Vsegs;R6S36VAInvA;R7R5R4A4A3S71Vsegs;R7S17Vsegs;S2fVAInvA;R8R6R5A4S3eVE;R8A2R4R3A5S74Vsegs;S77R4R3S1S2S1fS73A2M0S4S1fS73S48VE;R8A2S42VAInvA;VCST;VXGL;R8R6R5A6A4S3G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;S6bVsegs;VE;VAInvA;VCST;VXGL;R2A6F_;Fc;").
Proof.
  intros c H ok A Kc rho tp HK HF. eapply triple_conseq; [apply SPA_stack_malloc_T | intros w Hw; exact Hw | exact (H ok A Kc rho tp HK HF)].
Qed.
Lemma stack_malloc_contractA_ex_of_T : ltac2:(tb__ "0|1|
S75S14S23S7S0S1cQ40A1A1S24R3A1S70Vsegs;S17Vsegs;S2fVAInvA;R6R5R4A4S3eVE;R6A2R3R2A5S74Vsegs;S77R3R2S1S2S1fS73A2M0S4S1fS73S48VE;R6A2S42VAInvA;VCST;VXGL;R6R5R4A6A4S3G0A1A3A5A3F_;Ftp;Frho;FKc;FA;S6cVsegs;VE;VAInvA;VCST;VXGL;R2A6F_;Fc;").
Proof. intros c H A Kc rho tp HK w Hw. exact (H A Kc rho tp HK w (SPA_stack_malloc_T c A Kc rho tp w Hw)). Qed.

Lemma stack_free_contractA_of_T : ltac2:(tb__ "0|1|
S75S6fOF_;S14S23S7S0S1cQ40A1A1S24R3A1S18Vsegs;R6S35VAInvA;R7R5R4A4A3S71Vsegs;R7S17Vsegs;S2eVAInvA;R8R6R5A4S3dVE;R8A2R4R3A5S74Vsegs;S77R4R3S1S2S1fS73A2M0S4S1fS73S47VE;R8A2S41VAInvA;VCST;VXGL;R8R6R5A6A4S3G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;S69Vsegs;VE;VAInvA;VCST;VXGL;R2A6F_;Fc;").
Proof.
  intros c H ok A Kc rho tp HK HF. eapply triple_conseq; [apply SPA_stack_free_T | intros w Hw; exact Hw | exact (H ok A Kc rho tp HK HF)].
Qed.
Lemma stack_free_contractA_ex_of_T : ltac2:(tb__ "0|1|
S75S14S23S7S0S1cQ40A1A1S24R3A1S70Vsegs;S17Vsegs;S2eVAInvA;R6R5R4A4S3dVE;R6A2R3R2A5S74Vsegs;S77R3R2S1S2S1fS73A2M0S4S1fS73S47VE;R6A2S41VAInvA;VCST;VXGL;R6R5R4A6A4S3G0A1A3A5A3F_;Ftp;Frho;FKc;FA;S6aVsegs;VE;VAInvA;VCST;VXGL;R2A6F_;Fc;").
Proof. intros c H A Kc rho tp HK w Hw. exact (H A Kc rho tp HK w (SPA_stack_free_T c A Kc rho tp w Hw)). Qed.

Lemma memset_contractA_of_T : ltac2:(tb__ "0|1|
S75S75S6fOF_;S14S23S7S0S1cQ40A1A1S24R3A1S18Vsegs;R6S29VAInvA;R5R4A3A3S71Vsegs;R7S17Vsegs;S2dVAInvA;R6R5A3S3cR9A1R4R3A5S74Vsegs;S77R4R3S1S2S1fS73A2M0S4S1fS73S46R8A1S2bVAInvA;VCST;VXGL;R6R5A5A4S3G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;S66Vsegs;VAInvA;VCST;VXGL;R3R2A6F_;Fretpc;Fentry;").
Proof.
  intros entry retpc H ok A Kc rho tp HK HF. eapply triple_conseq; [apply SPA_memset_T | intros w Hw; exact Hw | exact (H ok A Kc rho tp HK HF)].
Qed.
Lemma memset_contractA_ex_of_T : ltac2:(tb__ "0|1|
S75S75S14S23S7S0S1cQ40A1A1S24R3A1S70Vsegs;S17Vsegs;S2dVAInvA;R5R4A3S3cR7A1R3R2A5S74Vsegs;S77R3R2S1S2S1fS73A2M0S4S1fS73S46R6A1S2bVAInvA;VCST;VXGL;R5R4A5A4S3G0A1A3A5A3F_;Ftp;Frho;FKc;FA;S67Vsegs;VAInvA;VCST;VXGL;R3R2A6F_;Fretpc;Fentry;").
Proof. intros entry retpc H A Kc rho tp HK w Hw. exact (H A Kc rho tp HK w (SPA_memset_T entry A Kc rho tp w Hw)). Qed.

Lemma memcpy_contractA_of_T : ltac2:(tb__ "0|2|
S75S75S75S6fOF_;S14S23S7S0S1cQ40A1A1S24R3A1S18Vsegs;R6S29VAInvA;R5R4A3A3S71Vsegs;R7S17Vsegs;S2cVAInvA;R6R5A3S3bRaA1R4R3A5S74Vsegs;S77R4R3S1S2S1fS73A2M0S4S1fS73S30R9A1S2bVAInvA;VCST;VXGL;R6R5A5M1A4S1G0S4S1fS73S30R8A1G1A4S3G0A1A3A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;S64Vsegs;VAInvA;VCST;VXGL;R4R3R2A7F_;Fretpc2;Fretpc;Fentry;").
Proof.
  intros entry retpc retpc2 H ok A Kc rho tp HK HF. eapply triple_conseq; [apply SPA_memcpy_T | intros w Hw; exact Hw | exact (H ok A Kc rho tp HK HF)].
Qed.
Lemma memcpy_contractA_ex_of_T : ltac2:(tb__ "0|2|
S75S75S75S14S23S7S0S1cQ40A1A1S24R3A1S70Vsegs;S17Vsegs;S2cVAInvA;R5R4A3S3bR8A1R3R2A5S74Vsegs;S77R3R2S1S2S1fS73A2M0S4S1fS73S30R7A1S2bVAInvA;VCST;VXGL;R5R4A5M1A4S1G0S4S1fS73S30R6A1G1A4S3G0A1A3A3A5A3F_;Ftp;Frho;FKc;FA;S65Vsegs;VAInvA;VCST;VXGL;R4R3R2A7F_;Fretpc2;Fretpc;Fentry;").
Proof. intros entry retpc retpc2 H A Kc rho tp HK w Hw. exact (H A Kc rho tp HK w (SPA_memcpy_T entry A Kc rho tp w Hw)). Qed.

Lemma ok_frameA_via : ltac2:(tb__ "0|0|
S6fOF_;S1bS1bS18Vsegs;R3R2A3S7S0S1cQ40A1A1S0S7dA1S7cR6R4R3R2R1A4S7aS7S7R9R1R5R4R3A4Lrho';A2F_;Fmd;Ftr;Ftp;Frho;S18Vsegs;R5R3A3F_;F_;FJi;FJp;Fok;").
Proof. intros ok Jp Ji H HJ rho tp tr ms md msv' Hj. destruct (HJ _ _ _ _ Hj) as [rho' Hj']. exact (H rho' tp tr ms md msv' Hj'). Qed.

Section Vars.
Hypothesis HAvars : ltac2:(tb__ "0|1|
S14S7S7S0S1cQ40A1M0A1S7cVAInvA;R5R4R2R1A4S78G0S6S1cQ8A1A1F_;S10R4A1S10R5A1A3VAInvA;R7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Let setT (A : AA) (rho : valuation) : valuation := ltac2:(tb__ "0|0|
S87Vrho;S31S1eQ40S16S15VA;A1A1A2A3").
Lemma setT_top_var : ltac2:(tb__ "0|0|
S14S7S4eR2VsetT;R2R1A2A2Frho;FA;").
Proof.
  intros A rho. unfold top_var, setT. rewrite rho_set_rw_at. pose proof (topG_range (aa_geom A)).
  rewrite Z_to_bv_unsigned. apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma setT_rw : ltac2:(tb__ "0|0|
S14S7S76S7bS78S76R1S31A3A1S78S1cQ40A1S9VsetT;R4R3A2R2A2S9R3R2A2A3F_;Fi;Frho;FA;").
Proof. intros A rho i Hi. unfold setT. rewrite rho_set_rw_other; [reflexivity | exact Hi]. Qed.
Lemma setT_AInvA : ltac2:(tb__ "0|0|
S14S7S0S1cQ40A1A1S7cVAInvA;R4R3R2R1A4VAInvA;R5VsetT;R5R4A2R3R2A4F_;Fmd;Ftp;Frho;FA;").
Proof. intros A rho tp md H. eapply HAvars; [exact H | reflexivity]. Qed.

Lemma ok_frameA_stack_free_T : ltac2:(tb__ "0|0|
S6fOF_;S75S14S23S18Vsegs;R4S35VAInvA;R3R2R1A4A3S18Vsegs;R5S2eVAInvA;R4R3R2A4A3F_;FKc;FA;Fc;Fok;").
Proof.
  intros ok c A Kc H. eapply ok_frameA_via; [exact H|]. intros rho tp tr md (HA & HK & Htp & Hin & Hfl & _).
  exists (setT A rho). unfold J_stack_free_pre, tp_ok. rewrite !setT_rw by (cbv; discriminate).
  split; [exact (setT_AInvA _ _ _ _ HA)|]. split; [exact HK|]. split; [exact Htp|]. split; [exact Hin|]. split; [exact Hfl|]. apply setT_top_var.
Qed.
Lemma ok_frameA_stack_malloc_T : ltac2:(tb__ "0|0|
S6fOF_;S75S14S23S18Vsegs;R4S36VAInvA;R3R2R1A4A3S18Vsegs;R5S2fVAInvA;R4R3R2A4A3F_;FKc;FA;Fc;Fok;").
Proof.
  intros ok c A Kc H. eapply ok_frameA_via; [exact H|]. intros rho tp tr md (HA & HK & Htp & Hn & Hsz & _).
  exists (setT A rho). unfold J_stack_malloc_pre, tp_ok. rewrite !setT_rw by (cbv; discriminate).
  split; [exact (setT_AInvA _ _ _ _ HA)|]. split; [exact HK|]. split; [exact Htp|]. split; [exact Hn|]. split; [exact Hsz|]. apply setT_top_var.
Qed.
Lemma ok_frameA_pure_T : ltac2:(tb__ "0|0|
S6fOF_;S14S23S18Vsegs;R3S29VAInvA;R2R1A3A3S18Vsegs;R4S53VAInvA;R3R2A3A3F_;FKc;FA;Fok;").
Proof.
  intros ok A Kc H. eapply ok_frameA_via; [exact H|]. intros rho tp tr md (HA & HK & Htp & _).
  exists (setT A rho). unfold J_pure_pre, tp_ok. rewrite !setT_rw by (cbv; discriminate).
  split; [exact (setT_AInvA _ _ _ _ HA)|]. split; [exact HK|]. split; [exact Htp|]. apply setT_top_var.
Qed.
Lemma ok_frameA_memset_T : ltac2:(tb__ "0|0|
S6fOF_;S14S23S18Vsegs;R3S29VAInvA;R2R1A3A3S18Vsegs;R4S2dVAInvA;R3R2A3A3F_;FKc;FA;Fok;").
Proof. intros ok A Kc H. eapply ok_frameA_via; [exact (ok_frameA_pure_T ok A Kc H)|]. intros rho tp tr md [HJ _]. exists rho. exact HJ. Qed.
Lemma ok_frameA_memcpy_T : ltac2:(tb__ "0|0|
S6fOF_;S14S23S18Vsegs;R3S29VAInvA;R2R1A3A3S18Vsegs;R4S2cVAInvA;R3R2A3A3F_;FKc;FA;Fok;").
Proof. intros ok A Kc H. eapply ok_frameA_via; [exact (ok_frameA_pure_T ok A Kc H)|]. intros rho tp tr md [HJ _]. exists rho. exact HJ. Qed.
End Vars.

End WithSegs.
