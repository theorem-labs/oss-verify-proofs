(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "sym_runA"; "ax_setS"; "entailsA"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "true"; "bool"; "Some"; "option"; "pair"; "prod"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow00"; "E_00"; "T2_00"; "T0_00"; "R_00"; "T3_00"; "objs4_00"; "s_00"; "sfin_00"; "P_mszA"; "T1_00"; "T2_00_eq"; "T2_00_objs"; "T3_00_eq"; "bT0_00"; "ent_00"; "ids_00"; "nxE_00"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "ss_next"; "valuation"; "agree_below"; "rm"; "sprop"; "sprop_below"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow"; "W2"; "Jfix"; "CUTS_S"; "FUEL_S"; "O_realms"; "RTCL"; "XF_T2"; "cont_post"; "facts_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "L_set_shadow"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "JL_pure"; "AE_A"; "J_pure_pre"; "alloc_lawsA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Numbers.BinNums"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cells_ok"; "view"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemset ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface Asan_set_shadow.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run_00__R : option (list leafA) := ltac2:(tb__ "0|0|
S5S0S36S35S33Z0A1SdA5").
Local Strategy expand [run_00__R].
Definition E_00 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some [L] => la_state L | _ => W2 0 end)) run_00__R).
Definition P_mszA : axst := liftA P_msz.
Definition s_00 : wsub := Eval vm_compute in infer_sub 1 (ax_S E_00) (ax_S Pre_mszA).
Definition R_00 : list sobj := Eval vm_compute in (match entails_frA E_00 Pre_mszA s_00 with Some R => R | None => [] end).
Definition T0_00 : axst := Eval vm_compute in import_postA s_00 Pre_mszA P_mszA E_00 R_00.
Definition T1_00 : axst := ax_add_facts facts_S T0_00.
Definition T2_00 : axst := Eval vm_compute in T2_of T1_00.
Definition objs4_00 : list sobj := Eval vm_compute in firstn 4 (ss_objs (ax_S T2_00)).
Definition T3_00 : axst := Eval vm_compute in ax_setS T2_00 (set_objs (ax_S T2_00) objs4_00).
Definition sfin_00 : wsub := Eval vm_compute in infer_sub NF (ax_S T3_00) (ax_S (L_set_shadow 0)).

Lemma run_00 : ltac2:(tb__ "0|1|
S9S10SbS2A1M0A1S5S0S36S35S33Z0A1SdA5SfG0SaS2S8S14S4fA2ScS2A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_00__R <: run_00__R = Some [mkLeafA E_00 RsCut]). Qed.
Lemma fr_00 : ltac2:(tb__ "0|1|
S9S10SbS2bA1M0A1S28S14S3fS1aA3SfG0S17A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_00 : ltac2:(tb__ "0|0|
S9SeS27S14S3fS1aS17S47S2S1S4S40A4A5SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T0_00_eq : ltac2:(tb__ "0|0|
S9S1S29S1aS3fS1cS14S17A5S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_00_eq : ltac2:(tb__ "0|0|
S9S10S1A1S51S1dS39A2SfS1S15A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_00_objs : ltac2:(tb__ "0|0|
S9SbS2bA1S32S3S15A1A1S13S2bS19SaS2bS37ScS2bA1A3A3A3"). Proof. reflexivity. Qed.
Lemma T3_00_eq : ltac2:(tb__ "0|0|
S9S1S6S15S50S3S15A1S19A2A2S18A3"). Proof. reflexivity. Qed.
Lemma ent_00 : ltac2:(tb__ "0|0|
S9SeS7S18S3cZ0A1S1bA3SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nxE_00 : ltac2:(tb__ "0|0|
S9S4cS2cS3S14A1A1S2aA3"). Proof. reflexivity. Qed.
Lemma bT0_00 : ltac2:(tb__ "0|0|
S9SeS56S30S31S2cS3S16A1A1A1S3bA3SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_00 : ltac2:(tb__ "0|0|
S9SeS4eS1bS2aA2SdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma posts_mszA_la : ltac2:(tb__ "0|0|
S9SbS1A1S47S2S1S4S40A4SaS1S1cScS1A1A3A3"). Proof. reflexivity. Qed.

Section Contract.
Variable AInvA : ltac2:(tb__ "0|0|
S52S2dSbS4bQ40A1A1S4dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S46S0VAInvA;VCST;A3").
Hypothesis HLV : law_view_stmt AInvA.
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Section Run.
Variables (A : AA) (Kc : KcA) (rho : valuation) (tp : list word).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HR : ltac2:(tb__ "0|0|
S54S55S0S2fVrho;A1A2S38S53VA;A1A1A2").
Hypothesis HFS : Forall (holds rho) facts_S.

Let CP : ltac2:(tb__ "0|1|
S2dSbS4bQ40A1A1S48S2eS2aVrho;R3A3S41S0S34VAInvA;VA;VKc;Vrho;Vtp;A5S16R4R3R2A6S26S0S2aVrho;Vtp;SaS12S1S25A2M0S11S1S25S3cZ0A1S43VAInvA;VCST;VXGL;VA;VKc;A5A4ScG0A1A3R3A6F_;F_;Fw;FtpL;Frho';") := ltac2:(tb__ "0|0|
S3aVAInvA;VCST;VXGL;VALA;VHLV;VHCST;VHXGL;Z0S14S16S15S18S1bS19S1eS1fS20S22S24S21S23VA;VKc;Vrho;Vtp;VHR;VHFS;A1b").

Lemma inst_sound00 : ltac2:(tb__ "0|2|
S48OF_;S42S0R1S45VAInvA;VA;VKc;A3A3S4aS0R2S41S0S34VAInvA;VA;VKc;Vrho;Vtp;A5S33Z0M0A1Vrho;Vtp;A5S26S0S2aVrho;Vtp;SaS12S1S25A2M1S11S1S25S3cG0A1S43VAInvA;VCST;VXGL;VA;VKc;A5A4ScG1A1A3A5A4F_;Fok;").
Proof.
  intros ok Hokf.
  eapply (runA_tr segs ok FUEL_S CUTS_S (W2 0) _ (Jfix AInvA A Kc rho tp) rho tp); [exact run_00 | exact (lenW2 0) | apply Jfix_okf; exact Hokf | apply (Jfix_stable AInvA CST ALA); exact HKc |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite (nxW2 0) in Hag1.
  apply (call_soundA segs ok (Jfix AInvA A Kc rho tp) (Jfix AInvA A Kc rho tp) (Jfix AInvA A Kc rho tp) (Jfix AInvA A Kc rho tp) E_00 Pre_mszA s_00 R_00 Posts_mszA _ rho1 tp fr_00 cc_00).
  - intros rho2 tp2. apply memsetZ_sumA; [apply Jfix_okf; exact Hokf | apply (Jfix_stable AInvA CST ALA); exact HKc].
  - intros tr ms md _ HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' _ _ _ _ HJ. exact HJ.
  - intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. cbn [la_state liftLA lf_state]. change (liftA P_msz) with P_mszA. rewrite T0_00_eq.
    eapply triple_conseq; [ | | apply triple_refl]; [intros w Hw; exact Hw|].
    intros w Hw. apply (CP rho' tpL w); [|exact Hw]. rewrite nxE_00 in Hag. eapply agree_below_trans; [exact Hag1 | exact Hag].
Qed.

Lemma inst_complete00 : ltac2:(tb__ "0|2|
S49S0S41S0S34VAInvA;VA;VKc;Vrho;Vtp;A5S33Z0M0A1Vrho;Vtp;A5S26S0S2aVrho;Vtp;SaS12S1S25A2M1S11S1S25S3cG0A1S43VAInvA;VCST;VXGL;VA;VKc;A5A4ScG1A1A3A5A3").
Proof.
  eapply (erunA_tr segs FUEL_S CUTS_S (W2 0) _ (Jfix AInvA A Kc rho tp) rho tp); [exact run_00 | exact (lenW2 0) | apply (Jfix_stable AInvA CST ALA); exact HKc |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite (nxW2 0) in Hag1.
  apply (call_completeA segs (Jfix AInvA A Kc rho tp) (Jfix AInvA A Kc rho tp) (Jfix AInvA A Kc rho tp) (Jfix AInvA A Kc rho tp) E_00 Pre_mszA s_00 R_00 Posts_mszA _ rho1 tp fr_00 cc_00).
  - intros rho2 tp2. apply memsetZ_sumA_ex. apply (Jfix_stable AInvA CST ALA); exact HKc.
  - intros tr ms md _ HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' _ _ _ _ HJ. exact HJ.
  - intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. cbn [la_state liftLA lf_state]. change (liftA P_msz) with P_mszA. rewrite T0_00_eq.
    eapply etriple_conseq; [ | | apply etriple_refl]; [intros w Hw; exact Hw|].
    intros w Hw. apply (CP rho' tpL w); [|exact Hw]. rewrite nxE_00 in Hag. eapply agree_below_trans; [exact Hag1 | exact Hag].
Qed.
End Run.

Theorem set_shadow_00_contract : ltac2:(tb__ "0|0|
S3dS0S44VAInvA;VCST;VXGL;Z0A6").
Proof.
  intros ok A Kc rho tp HKc Hokf.
  apply (triple_pre ok _ (cells_ok (view segs (rm rho)) (RTCL (aa_geom A)) /\ Forall (holds rho) facts_S)).
  { intros w [Hsm HJ]. pose proof HJ as (HA & _ & _). split; [exact (law_rtc _ _ _ ALA A rho tp _ HA)|].
    rewrite <- (facts_S_eq 0). exact (SPA_facts_hold segs _ rho (PreS 0) tp w (conj Hsm HJ)). }
  intros [HR HFS].
  eapply triple_conseq; [ | intros w Hw; exact Hw | apply (inst_sound00 A Kc rho tp HKc HR HFS ok Hokf)].
  intros w Hw. apply (SPA_W2_of_pre _ 0 rho tp w (aa_geom A) HR).
  destruct Hw as [Hsm (HA & HK & Htp & Htv)]. split; [exact Hsm|]. exact (conj HA (conj HK (conj Htp (conj Htv eq_refl)))).
Qed.

Theorem set_shadow_00_contract_ex : ltac2:(tb__ "0|0|
S3eS0S44VAInvA;VCST;VXGL;Z0A6").
Proof.
  intros A Kc rho tp HKc.
  apply (etriple_pre _ (cells_ok (view segs (rm rho)) (RTCL (aa_geom A)) /\ Forall (holds rho) facts_S)).
  { intros w [Hsm HJ]. pose proof HJ as (HA & _ & _). split; [exact (law_rtc _ _ _ ALA A rho tp _ HA)|].
    rewrite <- (facts_S_eq 0). exact (SPA_facts_hold segs _ rho (PreS 0) tp w (conj Hsm HJ)). }
  intros [HR HFS].
  eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (inst_complete00 A Kc rho tp HKc HR HFS)].
  intros w Hw. apply (SPA_W2_of_pre _ 0 rho tp w (aa_geom A) HR).
  destruct Hw as [Hsm (HA & HK & Htp & Htv)]. split; [exact Hsm|]. exact (conj HA (conj HK (conj Htp (conj Htv eq_refl)))).
Qed.
End Contract.
