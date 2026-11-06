(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Mem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG NRMG NRMC SLOWU_vcs SLOWUG_vcok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMU_D.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMU_C1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMU_C2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMU_C3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require SFPU_sum SFPCU_sum PFFU_sum PFFCU_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Module NUMU.
Local Notation SG := usegs.

(* [comment removed for export] *)
Definition GP0 : nat -> list word -> (word -> option byte) -> Prop := fun _ _ _ => True.
Lemma GP0_frame : SG.gp_frameP GP0 (fun _ _ => []). Proof. intros id args E M M' _ _. exact I. Qed.
Lemma GP0_vc : forall c, (fun _ : SG.vc => false) c = true -> SG.vc_holds SG GP0 c. Proof. intros c H. discriminate H. Qed.

(* [comment removed for export] *)
Definition GPN := SNU.snu_gp SG.
Lemma GPN_frame : SG.gp_frameP GPN SNU.snu_gfp. Proof. exact (SNU.snu_frame SG). Qed.
Lemma GPN_vc : forall c, NRC.nrc_ok SG c = true -> SG.vc_holds SG GPN c. Proof. intros c H. exact (NRC.nrc_ok_sound SG c H). Qed.
Lemma slowu_vc : forall c, SG.gvc_or (SG.gvc_list SLOWUG_GV) (NRC.nrc_ok SG) c = true -> SG.vc_holds SG GPN c.
Proof.
  apply SG.gvc_or_ok; [|exact GPN_vc]. intros c H. exact (SG.gvc_list_ok SG GPN SLOWUG_GV c SLOWUG_GV_ok H).
Qed.

(* [comment removed for export] *)
Lemma summ_ghostfree : forall (GP1 GP2 : nat -> list word -> (word -> option byte) -> Prop) S,
  ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  SP.summ_okH SG GP1 MMU.hmH MMU.hmA MMU.hmC MMU.hmR S -> SP.summ_okH SG GP2 MMU.hmH MMU.hmA MMU.hmC MMU.hmR S.
Proof.
  intros GP1 GP2 S H0 HX H E M rom ms HR HA HW HH HT _.
  destruct (H E M rom ms HR HA HW HH HT) as (ms' & X & E' & M' & H1 & H2 & H3 & _ & H5); [rewrite H0; constructor|].
  exists ms', X, E', M'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  rewrite (proj1 (Forall_forall _ _) HX X H2). constructor.
Qed.
Lemma toN : forall S, ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
  SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR S -> SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR S.
Proof. intros S H0 HX H. exact (summ_ghostfree GP0 GPN S H0 HX H). Qed.

Ltac no_ext := intros TA HTA; destruct HTA.
Ltac no_cs := intros Sm HSm; destruct HSm.
Ltac mm := first [ apply MMU.mcpu_ok; lia | apply MMU.msp_ok; lia | apply MMU.mcp_ok; lia ].

(* [comment removed for export] *)
Lemma mmvu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMVU_sum.MMVSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           MMVU_defs.MMVU MMVU_defs.MMVU_IT _ _ _ MMVU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ MMVU_cert.mmvu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(no_cs) ltac:(cbn; tauto)).
Qed.
Lemma ladu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR LADU_sum.LADSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           LADU_defs.LADU LADU_defs.LADU_IT _ _ _ LADU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ LADU_cert.ladu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(no_cs) ltac:(cbn; tauto)).
Qed.
Lemma lmu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR LMU_sum.LMSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           LMU_defs.LMU LMU_defs.LMU_IT _ _ _ LMU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ LMU_cert.lmu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[]]]]; [mm | mm | exact ladu_ok]) ltac:(cbn; tauto)).
Qed.
Lemma p5u_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR P5U_sum.P5SU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           P5U_defs.P5U P5U_defs.P5U_IT _ _ _ P5U_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ P5U_cert.p5u_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact lmu_ok) ltac:(cbn; tauto)).
Qed.
Lemma shlu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR SHLU_sum.SHLSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           SHLU_defs.SHLU SHLU_defs.SHLU_IT _ _ _ SHLU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SHLU_cert.shlu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact mmvu_ok) ltac:(cbn; tauto)).
Qed.
Lemma ndcu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR NDCU_sum.NDCSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           NDCU_defs.NDCU NDCU_defs.NDCU_IT _ _ _ NDCU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ NDCU_cert.ndcu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[]]]]; [mm | exact p5u_ok | exact shlu_ok]) ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma mmvun_ok : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMVUN_sum.MMVSUN.
Proof.
  exact (SP.summ_of_pcheckH SG GPN _ _ GPN_frame GPN_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           MMVUN_defs.MMVUN MMVUN_defs.MMVUN_IT _ _ _ MMVUN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ MMVUN_cert.mmvun_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(no_cs) ltac:(cbn; tauto)).
Qed.
Lemma ladun0 : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR LADUN_sum.LADSUN.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           LADUN_defs.LADUN LADUN_defs.LADUN_IT _ _ _ LADUN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ LADUN_cert.ladun_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(no_cs) ltac:(cbn; tauto)).
Qed.
Lemma ladun_ok : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR LADUN_sum.LADSUN.
Proof. exact (toN LADUN_sum.LADSUN eq_refl ltac:(repeat constructor) ladun0). Qed.
Lemma lmun_ok : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR LMUN_sum.LMSUN.
Proof.
  exact (SP.summ_of_pcheckH SG GPN _ _ GPN_frame GPN_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           LMUN_defs.LMUN LMUN_defs.LMUN_IT _ _ _ LMUN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ LMUN_cert.lmun_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[]]]]; [mm | mm | exact ladun_ok]) ltac:(cbn; tauto)).
Qed.
Lemma p5un_ok : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR P5UN_sum.P5SUN.
Proof.
  exact (SP.summ_of_pcheckH SG GPN _ _ GPN_frame GPN_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           P5UN_defs.P5UN P5UN_defs.P5UN_IT _ _ _ P5UN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ P5UN_cert.p5un_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact lmun_ok) ltac:(cbn; tauto)).
Qed.
Lemma shlun_ok : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR SHLUN_sum.SHLSUN.
Proof.
  exact (SP.summ_of_pcheckH SG GPN _ _ GPN_frame GPN_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           SHLUN_defs.SHLUN SHLUN_defs.SHLUN_IT _ _ _ SHLUN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SHLUN_cert.shlun_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact mmvun_ok) ltac:(cbn; tauto)).
Qed.
Lemma hi64u_ok : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR HI64U_sum.HI64SU.
Proof.
  exact (SP.summ_of_pcheckH SG GPN _ _ GPN_frame GPN_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           HI64U_defs.HI64U HI64U_defs.HI64U_IT _ _ _ HI64U_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ HI64U_cert.hi64u_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(no_cs) ltac:(cbn; tauto)).
Qed.
Lemma pdcu_ok : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR PDCU_sum.PDCSU.
Proof.
  exact (SP.summ_of_pcheckH SG GPN _ _ GPN_frame GPN_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           PDCU_defs.PDCU PDCU_defs.PDCU_IT _ _ _ PDCU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PDCU_cert.pdcu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[]]]]; [exact p5un_ok | exact shlun_ok | exact hi64u_ok]) ltac:(cbn; tauto)).
Qed.
Lemma pmun_ok : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR PMUN_sum.PMSUN.
Proof.
  exact (SP.summ_of_pcheckH SG GPN _ _ GPN_frame GPN_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           PMUN_defs.PMUN PMUN_defs.PMUN_IT _ _ _ PMUN_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PMUN_cert.pmun_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(no_cs) ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma slowu_okN : SP.summ_okH SG GPN MMU.hmH MMU.hmA MMU.hmC MMU.hmR SLOWU_sum.SLOWSU.
Proof.
  exact (SP.summ_of_pcheckH SG GPN _ _ GPN_frame slowu_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           SLOWU_defs.SLOWU SLOWU_defs.SLOWU_IT _ _ _ SLOWU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SLOWU_cert.slowu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext)
           ltac:(intros Sm [<-|[<-|[<-|[<-|[]]]]];
                 [mm | exact pmun_ok | exact pdcu_ok | apply toN; [reflexivity | repeat constructor | exact ndcu_ok]])
           ltac:(cbn; tauto)).
Qed.
Lemma slowu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR SLOWU_sum.SLOWSU.
Proof. exact (summ_ghostfree GPN GP0 SLOWU_sum.SLOWSU eq_refl ltac:(repeat constructor) slowu_okN). Qed.

(* [comment removed for export] *)
Lemma pwfu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR PWFU_sum.PWFSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           PWFU_defs.PWFU PWFU_defs.PWFU_IT _ _ _ PWFU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PWFU_cert.pwfu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact slowu_ok) ltac:(cbn; tauto)).
Qed.
Lemma sfpu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPU_sum.SFPSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           SFPU_defs.SFPU SFPU_defs.SFPU_IT _ _ _ SFPU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SFPU_cert.sfpu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact pwfu_ok) ltac:(cbn; tauto)).
Qed.
Lemma sfpcu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPCU_sum.SFPCSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           SFPCU_defs.SFPCU SFPCU_defs.SFPCU_IT _ _ _ SFPCU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ SFPCU_cert.sfpcu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact pwfu_ok) ltac:(cbn; tauto)).
Qed.
Lemma pffu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFU_sum.PFFSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           PFFU_defs.PFFU PFFU_defs.PFFU_IT _ _ _ PFFU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PFFU_cert.pffu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact pwfu_ok) ltac:(cbn; tauto)).
Qed.
Lemma pffcu_ok : SP.summ_okH SG GP0 MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFCU_sum.PFFCSU.
Proof.
  exact (SP.summ_of_pcheckH SG GP0 _ _ GP0_frame GP0_vc MMU.hmH MMU.hmA MMU.hmC MMU.hmR MMU.HMC_sub MMU.HMF
           PFFCU_defs.PFFCU PFFCU_defs.PFFCU_IT _ _ _ PFFCU_defs.T0 (SP.pcheck_pcheckH _ _ _ _ _ _ _ _ PFFCU_cert.pffcu_cert)
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(no_ext) ltac:(intros Sm [<-|[]]; exact pwfu_ok) ltac:(cbn; tauto)).
Qed.

(* [comment removed for export] *)
Lemma sfpu_okG : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPU_sum.SFPSU.
Proof. intros GP. exact (summ_ghostfree GP0 GP SFPU_sum.SFPSU eq_refl ltac:(repeat constructor) sfpu_ok). Qed.
Lemma sfpcu_okG : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR SFPCU_sum.SFPCSU.
Proof. intros GP. exact (summ_ghostfree GP0 GP SFPCU_sum.SFPCSU eq_refl ltac:(repeat constructor) sfpcu_ok). Qed.
Lemma pffu_okG : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFU_sum.PFFSU.
Proof. intros GP. exact (summ_ghostfree GP0 GP PFFU_sum.PFFSU eq_refl ltac:(repeat constructor) pffu_ok). Qed.
Lemma pffcu_okG : forall GP, SP.summ_okH SG GP MMU.hmH MMU.hmA MMU.hmC MMU.hmR PFFCU_sum.PFFCSU.
Proof. intros GP. exact (summ_ghostfree GP0 GP PFFCU_sum.PFFCSU eq_refl ltac:(repeat constructor) pffcu_ok). Qed.
End NUMU.
Print Assumptions NUMU.sfpu_okG.
Print Assumptions NUMU.pffu_okG.
