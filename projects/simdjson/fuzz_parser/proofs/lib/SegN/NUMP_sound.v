(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Mem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG SLOW_vcs SLOWG_vcok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMP_D.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMP_C1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMP_C2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SFP_sum SFPC_sum PFF_sum PFFC_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Module NUMP.
Local Notation SG := psegs.

(* [comment removed for export] *)
Definition GP0 : nat -> list word -> (word -> option byte) -> Prop := fun _ _ _ => True.
Lemma GP0_frame : SG.gp_frameP GP0 (fun _ _ => []). Proof. intros id args E M M' _ _. exact I. Qed.
Lemma GP0_vc : forall c, (fun _ : SG.vc => false) c = true -> SG.vc_holds SG GP0 c. Proof. intros c H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma summ_ghostfree : forall (GP1 GP2 : nat -> list word -> (word -> option byte) -> Prop) S,
  ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  SP.summ_okH SG GP1 MMP.hmH MMP.hmA MMP.hmC MMP.hmR S -> SP.summ_okH SG GP2 MMP.hmH MMP.hmA MMP.hmC MMP.hmR S.
Proof.
  intros GP1 GP2 S H0 HX H E M rom ms HR HA HW HH HT _.
  destruct (H E M rom ms HR HA HW HH HT) as (ms' & X & E' & M' & H1 & H2 & H3 & _ & H5); [rewrite H0; constructor|].
  exists ms', X, E', M'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  rewrite (proj1 (Forall_forall _ _) HX X H2). constructor.
Qed.

Ltac no_ext := intros TA HTA; destruct HTA.
Ltac no_cs := intros Sm HSm; destruct HSm.

(* [comment removed for export] *)
Lemma mmv_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMV_sum.MMVS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           MMV_defs.MMV MMV_defs.MMV_IT _ _ _ MMV_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ MMV_cert.mmv_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(no_cs) ltac:(cbn; tauto)).
Qed.

Lemma lm_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR LM_sum.LMS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           LM_defs.LM LM_defs.LM_IT _ _ _ LM_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ LM_cert.lm_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[]]]]; [apply MMP.mcpu_ok; lia | apply MMP.mcpu_ok; lia | apply MMP.msp_ok; lia])
           ltac:(cbn; tauto)).
Qed.

Lemma p5_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR P5_sum.P5S.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           P5_defs.P5 P5_defs.P5_IT _ _ _ P5_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ P5_cert.p5_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[]]; exact lm_ok) ltac:(cbn; tauto)).
Qed.

Lemma pdc_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR PDC_sum.PDCS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           PDC_defs.PDC PDC_defs.PDC_IT _ _ _ PDC_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PDC_cert.pdc_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[]]]]; [exact p5_ok | exact mmv_ok | apply MMP.msp_ok; lia]) ltac:(cbn; tauto)).
Qed.

Lemma ndc_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR NDC_sum.NDCS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           NDC_defs.NDC NDC_defs.NDC_IT _ _ _ NDC_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ NDC_cert.ndc_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[<-|[<-|[]]]]]];
                 [apply MMP.msp_ok; lia | exact p5_ok | exact mmv_ok | apply MMP.msp_ok; lia | apply MMP.msp_ok; lia]) ltac:(cbn; tauto)).
Qed.

Lemma pm_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR PM_sum.PMS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           PM_defs.PM PM_defs.PM_IT _ _ _ PM_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PM_cert.pm_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(no_cs) ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Definition GPS := SNG.sng_gp SG.
Lemma slow_vc : forall c, SG.gvc_list SLOWG_GV c = true -> SG.vc_holds SG GPS c.
Proof. intros c H. exact (SG.gvc_list_ok SG GPS SLOWG_GV c SLOWG_GV_ok H). Qed.

Lemma gf0 : forall S, ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR S -> SP.summ_okH SG GPS MMP.hmH MMP.hmA MMP.hmC MMP.hmR S.
Proof. intros S H0 HX H. exact (summ_ghostfree GP0 GPS S H0 HX H). Qed.

Lemma slow_okS : SP.summ_okH SG GPS MMP.hmH MMP.hmA MMP.hmC MMP.hmR SLOW_sum.SLOWS.
Proof.
  exact (SP.summ_of_pcheckH SG GPS _ _ (SNG.sng_frame SG) slow_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           SLOW_defs.SLOW SLOW_defs.SLOW_IT _ _ _ SLOW_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOW_cert.slow_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[<-|[]]]]];
                 [apply MMP.msp_ok; lia
                 | apply gf0; [reflexivity | repeat constructor | exact pm_ok]
                 | apply gf0; [reflexivity | repeat constructor | exact pdc_ok]
                 | apply gf0; [reflexivity | repeat constructor | exact ndc_ok]])
           ltac:(cbn; tauto)).
Qed.

Lemma slow_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR SLOW_sum.SLOWS.
Proof. exact (summ_ghostfree GPS GP0 SLOW_sum.SLOWS eq_refl ltac:(repeat constructor) slow_okS). Qed.

(* [comment removed for export] *)
Lemma pwf_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR PWF_sum.PWFS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           PWF_defs.PWF PWF_defs.PWF_IT _ _ _ PWF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PWF_cert.pwf_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact slow_ok) ltac:(cbn; tauto)).
Qed.

Lemma sfp_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR SFP_sum.SFPS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           SFP_defs.SFP SFP_defs.SFP_IT _ _ _ SFP_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SFP_cert.sfp_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact pwf_ok) ltac:(cbn; tauto)).
Qed.
Lemma sfpc_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR SFPC_sum.SFPCS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           SFPC_defs.SFPC SFPC_defs.SFPC_IT _ _ _ SFPC_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SFPC_cert.sfpc_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact pwf_ok) ltac:(cbn; tauto)).
Qed.
Lemma pff_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR PFF_sum.PFFS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           PFF_defs.PFF PFF_defs.PFF_IT _ _ _ PFF_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PFF_cert.pff_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact pwf_ok) ltac:(cbn; tauto)).
Qed.
Lemma pffc_ok : SP.summ_okH SG GP0 MMP.hmH MMP.hmA MMP.hmC MMP.hmR PFFC_sum.PFFCS.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMP.hmH MMP.hmA MMP.hmC MMP.hmR MMP.HMC_sub MMP.HMF
           PFFC_defs.PFFC PFFC_defs.PFFC_IT _ _ _ PFFC_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PFFC_cert.pffc_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact pwf_ok) ltac:(cbn; tauto)).
Qed.
End NUMP.
Print Assumptions NUMP.sfp_ok.
Print Assumptions NUMP.pff_ok.
