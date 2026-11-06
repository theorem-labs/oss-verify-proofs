(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "ACEIL"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "J_pure_pre"; "KcA"; "JL_pure"; "Kc_ok"; "alloc_lawsA"; "@Corelib.Init.Logic"; "and"; "eq"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "add"; "opp"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "agree_below"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_memcpyR_contract.ContractR"; "JcontR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "white_hv"; "white_lo"; "L_memcpyR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ageom"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Asan_memcpyR"; "PreWR"; "certR"; "CR"; "PR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_memcpy_contract"; "RTCL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cells_ok"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_memcpyR_contract"; "PZR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemcpy ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_memcpy_contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Asan_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Asan_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_memcpy_contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Asan_memcpyR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import RegionAddr AMCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' r i" := (bv_unsigned (rw r i)) (at level 10, r at level 9, i at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Definition PZR (rho : valuation) : Prop := ltac2:(tb__ "0|6|
SdSfS37S14Q40M0S16Vrho;PcA2A2M1A2SdSfG1S10Z2M2Z2fA2M3A2SdSfS11S1Z900A2S14G0S16Vrho;PaA2A2M4A2SdSfG4G3A2SdSfS12S10G2Z28A2A1S36S14G0S16Vrho;PfA2A2A1M5A2SfG5N900A2A2A2A2A2A2").

Lemma PZR_of_pre : ltac2:(tb__ "0|0|
S19S1cS15S2S13Q40A1A1S1aS1bS0R4S2bR5A1R3R2R1A6S35R4A1F_;Fw;Ftp;Frho;FJ;Fsrc;").
Proof.
  intros src J rho tp [tr [ms md]] [(Hsm & HMI & Hwf & Hsh & Hhz) _].
  pose proof (smatch_facts_hold segs rho _ _ Hsm) as HF. cbn [ax_S PreWR] in HF.
  pose proof (urange (rw rho 53)) as R53. pose proof (urange (rw rho 12)) as R12.
  pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 15)) as R15.
  have_fact A1 HF (SPUle (SVar 53) (SVar 12)).
  have_fact A4 HF (SPUle (SLit IMG_HI) (SVar 53)).
  have_fact A9 HF (SPUle (SVar 12) (SLit (2 ^ 47))).
  have_fact A10 HF (SPUle (SVar 10) (SLit (2 ^ 47))).
  have_fact A12 HF (SPUle (SLit 140735332483072) (SAlu ALU_ADD (SVar 10) (SVar V_DEPTH))).
  have_fact A13 HF (SPBranch BC_GE (SLit (- memx_depth)) (SVar V_DEPTH)).
  have_fact A14 HF (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40))).
  cbn [eval] in A1, A4, A9, A10, A12.
  rewrite add_val in A12.
  rewrite !lit_unsigned in A4, A9, A10, A12.
  unfold IMG_HI in A4.
  rewrite !Z.mod_small in A4, A9, A10 by lia.
  rewrite (Z.mod_small 140735332483072) in A12 by lia.

  assert (SW : ACEIL + 2304 <= UU rho 10).
  { unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S PreWR] in Hsm.
    destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
    apply Forall_inv in Hall. unfold obj_holds, obj_lo_of, obj_hi_of, stack_win in Hall. cbn [ob_base ob_lo ob_hi eval] in Hall.
    destruct Hall as ((B1 & _ & _ & _) & _). unfold soff in B1. cbn [eval] in B1. rewrite bv_signed_U in B1.
    cbn [holds branch_taken eval] in A13. unfold bv_lts in A13. rewrite !bv_signed_U in A13.
    rewrite lit_unsigned in A13. unfold memx_depth in A13.
    change ((- (2304)) mod 2 ^ 64) with 18446744073709549312 in A13.
    destruct (Z.ltb_spec (Zsigned 18446744073709549312) (Zsigned (UU rho V_DEPTH))) as [Hlt|Hge]; [discriminate A13|].
    destruct (Zsigned_spec 18446744073709549312) as [[X _]|[_ E0]]; [lia|]. rewrite E0 in Hge.
    unfold ACEIL. unfold V_DEPTH in *.
    destruct (Zsigned_spec (UU rho 15)) as [[X15 E15]|[X15 E15]]; rewrite E15 in Hge, B1.
    - lia.
    - replace ((UU rho 10 + UU rho 15) mod 2 ^ 64) with (UU rho 10 + UU rho 15 - 2 ^ 64) in A12; [lia|].
      symmetry. replace (UU rho 10 + UU rho 15) with ((UU rho 10 + UU rho 15 - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (SD : - 2 ^ 40 <= Zsigned (UU rho 15) <= - 2304).
  { unfold V_DEPTH in *.
    cbn [holds branch_taken eval] in A13, A14. unfold bv_lts in A13, A14. rewrite !bv_signed_U in A13, A14.
    rewrite !lit_unsigned in A13, A14. unfold memx_depth in A13.
    change ((- (2304)) mod 2 ^ 64) with 18446744073709549312 in A13.
    change ((- 2 ^ 40) mod 2 ^ 64) with 18446742974197923840 in A14.
    destruct (Z.ltb_spec (Zsigned 18446744073709549312) (Zsigned (UU rho 15))) as [Hlt|Hge]; [discriminate A13|].
    destruct (Z.ltb_spec (Zsigned (UU rho 15)) (Zsigned 18446742974197923840)) as [Hlt'|Hge']; [discriminate A14|].
    destruct (Zsigned_spec 18446744073709549312) as [[X _]|[_ E0]]; [lia|]. rewrite E0 in Hge.
    destruct (Zsigned_spec 18446742974197923840) as [[X _]|[_ E1]]; [lia|]. rewrite E1 in Hge'. lia. }
  unfold PZR, IMG_HI. repeat (split; [lia|]). lia.
Qed.

Lemma SPA_CR_of_pre : ltac2:(tb__ "0|0|
S19S1cS15S2S13Q40A1A1S1aS28S33S34S0S17R4A1A2S2fR1A1A2S1bS0R6S2bR7A1R5R4R3A6S1bS0R7S2dR8A1R6R5R4A6F_;F_;FG;Fw;Ftp;Frho;FJ;Fsrc;").
Proof.
  intros src J rho tp w G HR HS. pose proof (PZR_of_pre src J rho tp w HS) as HP.
  unfold PZR, IMG_HI, ACEIL in HP. destruct HP as (P1 & P2 & P3 & P4 & P5).
  pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 12)) as R12. pose proof (urange (rw rho 15)) as R15.
  destruct (rtc_nth G) as (N18 & N19 & N20 & N21 & N22 & N2).
  pose proof (cell_of _ G _ _ HR N18) as C18. pose proof (cell_of _ G _ _ HR N19) as C19. pose proof (cell_of _ G _ _ HR N20) as C20.
  pose proof (cell_of _ G _ _ HR N21) as C21. pose proof (cell_of _ G _ _ HR N22) as C22. pose proof (cell_of _ G _ _ HR N2) as C2.
  unfold CR, carve_S.
  apply (SPA_carve_list segs J rho (PreWR src) tp w N_rtc NF HS (swf_CR src) ltac:(apply Pos.le_refl)).
  -
    unfold N_rtc. repeat apply Forall_cons; try apply Forall_nil; cbv beta iota zeta; cbn [eval];
      rewrite !lit_unsigned; rewrite !(Z.mod_small 0) by lia.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      split; [intros off Hoff; split; [apply wok_of_imageA; lia|];
              destruct (Z_lt_ge_dec off 0xf20d9); [eapply (cell_rd _ _ _ _ _ C18); cbn; lia | eapply (cell_rd _ _ _ _ _ C19); cbn; lia]|].
      split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj;
              [apply (cell_civ rho _ _ _ _ C18); cbn; lia | apply (cell_civ rho _ _ _ _ C19); cbn; lia]|].
      intros rr y j Hin Hy Hj. change (ax_base (PreWR src)) with (SLit SHB). cbn [eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
      pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
      change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      split; [intros off Hoff; split; [apply wok_of_imageA; lia|];
              destruct (Z_lt_ge_dec off 0xf20e8); [eapply (cell_rd _ _ _ _ _ C20); cbn; lia|];
              destruct (Z_lt_ge_dec off 0xf20f0); [eapply (cell_rd _ _ _ _ _ C21); cbn; lia | eapply (cell_rd _ _ _ _ _ C22); cbn; lia]|].
      split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj;
              [apply (cell_civ rho _ _ _ _ C20); cbn; lia | apply (cell_civ rho _ _ _ _ C21); cbn; lia | apply (cell_civ rho _ _ _ _ C22); cbn; lia]|].
      intros rr y j Hin Hy Hj. change (ax_base (PreWR src)) with (SLit SHB). cbn [eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
      pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
      change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
    + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      split; [intros off Hoff; split; [apply wok_of_imageA; lia | eapply (cell_rd _ _ _ _ _ C2); cbn; lia]|].
      split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj; apply (cell_civ rho _ _ _ _ C2); cbn; lia|].
      intros rr y j Hin Hy Hj. change (ax_base (PreWR src)) with (SLit SHB). cbn [eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
      pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
      change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
  -
    pose proof (Zsigned_spec (UU rho 15)) as Z15.
    cbn [ax_S PreWR Pre_memcpyR mkA ss_objs app]. unfold N_rtc. cbn [map carve_obj carved lit_cells].
    repeat apply Forall_cons; try apply Forall_nil;
      unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, carved, stack_win, A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI;
      cbn [ob_base ob_lo ob_hi fst snd];
      rewrite ?soff_lit_small by lia; unfold soff; cbn [eval]; rewrite ?bv_signed_U; rewrite ?lit_unsigned; rewrite ?(Z.mod_small 0) by lia;
      unfold V_DEPTH in *; lia.
  -
    unfold N_rtc. cbn [map carve_obj pairwise_disjoint].
    repeat split; repeat apply Forall_cons; try apply Forall_nil;
      unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, carved; cbn [ob_base ob_lo ob_hi fst snd];
      rewrite ?soff_lit_small by lia; cbn [eval]; rewrite ?lit_unsigned; rewrite ?(Z.mod_small 0) by lia; lia.
Qed.

Section ContractR.
Variable AInvA : ltac2:(tb__ "0|0|
S26S15S2S13Q40A1A1S29OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
ScS0VAInvA;VCST;A3").

Hypothesis HLV : law_view_stmt AInvA.
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Definition JcontR (A : AA) (Kc : KcA) (tp0 : list word) : jpredA := ltac2:(tb__ "0|1|
S15S2S13Q40A1A1M0S2S2aA1S29SdS8VAInvA;VA;VKc;R4R3R2R1A7SeG0R3Vtp0;A3A2Lmd;Ltr;Lt;Lr;").

Lemma JcontR_stable : ltac2:(tb__ "0|0|
S26S9S2S13Q40A1A1SbR2A1S1eS0S25S1fR4R3R2A3A3F_;Ftp0;FKc;FA;").
Proof.
  intros A Kc tp0 HKc rho rho' tp tr md md' Hag Hme ((HA & HK & Htp & Htv) & ->).
  pose proof Hag as (Hrw & _ & Hrm).
  split; [split; [|split; [|split]]|reflexivity].
  - eapply (law_mat _ _ _ ALA); [|exact Hme]. eapply (law_vars _ _ _ ALA); [exact HA|].
    apply functional_extensionality. intros a. symmetry. apply Hrm.
  - eapply mat_blind_equiv; [apply Kc_mat_blind; exact HKc | exact Hme | exact HK].
  - unfold tp_ok in *. rewrite <- (Hrw 24%positive) by reflexivity. exact Htp.
  - unfold top_var in *. rewrite <- (Hrw _) by reflexivity. exact Htv.
Qed.

Lemma JcontR_okf : ltac2:(tb__ "0|0|
S1aOF_;S26S9S2S13Q40A1A1S1dS0R4S8VAInvA;R3R2A3A3S1dS0R5S1fR4R3R2A3A3F_;Ftp0;FKc;FA;Fok;").
Proof. intros ok A Kc tp0 H rho tp tr ms md msv' [HJ _]. eapply H. exact HJ. Qed.

Section Inst.
Variable src : Z.
Variable A : AA. Variable Kc : KcA.
Variables (rho : valuation) (tp : list word).
Hypothesis HR : ltac2:(tb__ "0|0|
S33S34S0S17Vrho;A1A2S2fS27VA;A1A1A2").

Lemma cont_postR : ltac2:(tb__ "0|1|
S15S1aS18S25Vrho;R2A3S1bS0S1fVA;VKc;Vtp;A3S2eVsrc;A1R3Vtp;R2A6S32S0S25Vrho;Vtp;S3S6S30S31A2M0S5S30S31S24S7Vsrc;ZcA3SaVAInvA;VCST;VXGL;VA;VKc;A5A4S4G0A1A3R3A6F_;F_;Fw;Frho';").
Proof.
  intros rho' [tr [ms md]] Hag HS2.
  pose proof Hag as (Hrw & Hrl & Hrm).

  pose proof (SPA_unobj segs (JcontR A Kc tp) rho' (PR src) objsLR R_rtc tp tr ms md (PR_objs src) HS2) as HS3. cbn zeta in HS3.
  set (rho'' := rho_absorb rho' R_rtc (vms md tp ms)) in HS3.
  assert (RMout : forall a, ~ rtc3_rng (bv_unsigned a) -> rm rho'' a = rm rho a).
  { intros a Ha. unfold rho''. rewrite rm_absorb_out; [symmetry; apply Hrm|]. intros Hi. apply Ha. apply (in_ranges_R rho'). exact Hi. }
  assert (HJ3 : JcontR A Kc tp rho' tp tr md -> JcontR A Kc tp rho'' tp tr md).
  { intros [(HA & HK & Htp & Htv) _]. split; [split; [|split; [|split]]|reflexivity].
    - apply (HLV A rho' rho'' tp md HA). intros a.
      destruct (in_ranges_dec rho' R_rtc a) as [Hin|Hout].
      +
        pose proof (proj1 (proj1 HS2)) as Hsm2. unfold virt in Hsm2. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm2.
        assert (RR : forall a', rd_of segs (rm rho') a' = rd_of segs (rm rho) a') by (intros a'; unfold rd_of; rewrite <- (Hrm a'); reflexivity).
        rewrite RR. apply (in_ranges_R rho') in Hin.
        destruct (rtc_nth (aa_geom A)) as (N18 & N19 & N20 & N21 & N22 & N2).
        pose proof (fun n c Hn => cell_of _ (aa_geom A) n c HR Hn) as CO.
        assert (AC : forall lo hi cs, In (carved (SLit 0) lo hi cs) R_rtc -> - 2 ^ 63 <= lo -> lo <= hi -> hi < 2 ^ 63 -> cells_inside lo hi cs ->
                  cells_in_view rho'' (rd_of segs (rm rho'')) 0 cs).
        { intros lo hi cs Hin' H1 H2 H3 H4.
          pose proof (absorb_carved_cells segs rho' (ax_S (PR src)) tr (vms md tp ms) (vmd md) objsLR R_rtc (SLit 0) lo hi cs Hsm2 (PR_objs src) Hin' H1 H2 H3 H4) as [X _].
          cbn [eval] in X. rewrite lit_unsigned in X. exact X. }
        rewrite <- (Z_to_bv_bv_unsigned 64 a).
        destruct Hin as [H|[H|H]].
        * pose proof (AC 0xf20d8 0xf20da [(0xf20d8, 1%nat, SLit 1); (0xf20d9, 1%nat, SLit 1)] ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as CV.
          apply Forall_cons_iff in CV as [CV1 CV]. apply Forall_cons_iff in CV as [CV2 _]. cbn [eval] in CV1, CV2.
          destruct (Z_lt_ge_dec (bv_unsigned a) 0xf20d9).
          -- apply (rd_cell_eq _ _ 0xf20d8 1 (Z_to_bv 64 1)); [intros j Hj; rewrite <- (CV1 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 18%nat _ N18 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
          -- apply (rd_cell_eq _ _ 0xf20d9 1 (Z_to_bv 64 1)); [intros j Hj; rewrite <- (CV2 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 19%nat _ N19 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
        * pose proof (AC 0xf20e0 0xf20f8 [(0xf20e0, 8%nat, SLit KHME); (0xf20e8, 8%nat, SLit 0); (0xf20f0, 8%nat, SLit 0)]
                        ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as CV.
          apply Forall_cons_iff in CV as [CV1 CV]. apply Forall_cons_iff in CV as [CV2 CV]. apply Forall_cons_iff in CV as [CV3 _]. cbn [eval] in CV1, CV2, CV3.
          destruct (Z_lt_ge_dec (bv_unsigned a) 0xf20e8); [|destruct (Z_lt_ge_dec (bv_unsigned a) 0xf20f0)].
          -- apply (rd_cell_eq _ _ 0xf20e0 8 (Z_to_bv 64 KHME)); [intros j Hj; rewrite <- (CV1 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 20%nat _ N20 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
          -- apply (rd_cell_eq _ _ 0xf20e8 8 (Z_to_bv 64 0)); [intros j Hj; rewrite <- (CV2 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 21%nat _ N21 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
          -- apply (rd_cell_eq _ _ 0xf20f0 8 (Z_to_bv 64 0)); [intros j Hj; rewrite <- (CV3 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 22%nat _ N22 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
        * pose proof (AC 0xe9ae8 0xe9af0 [(0xe9ae8, 8%nat, SLit musl_memcpy)] ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as CV.
          apply Forall_cons_iff in CV as [CV1 _]. cbn [eval] in CV1.
          apply (rd_cell_eq _ _ 0xe9ae8 8 (Z_to_bv 64 musl_memcpy)); [intros j Hj; rewrite <- (CV1 j Hj); f_equal; f_equal; lia | | lia].
          intros j Hj. pose proof (CO 1%nat _ N2 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
      + unfold rd_of. unfold rho''. rewrite (rm_absorb_out rho' R_rtc _ a Hout). reflexivity.
    - exact HK.
    - exact Htp.
    - exact Htv. }
  specialize (HS3 HJ3). rewrite PR_unobj in HS3.
  destruct HS3 as [Hsm5 HJ5].
  exists (L_memcpyR AE_A src 12), (JL_pure AInvA CST XGL A Kc), rho'', tp.
  split; [left; reflexivity|]. split.
  - split; [intros i Hi; unfold rho''; cbn [rho_absorb rw]; apply Hrw; exact Hi | intros l; unfold rho''; cbn [rho_absorb rl]; apply Hrl].
  - split; [exact Hsm5|]. cbn [w_tr w_cfg cfg_model fst snd] in HJ5 |- *. destruct HJ5 as [(HA5 & HK5 & Htp5 & _) _].
    unfold JL_pure. split; [exact HA5|].
    split; [reflexivity|]. split; [|exact HK5].
    split.
    + intros a Ha Hc. apply RMout. rewrite u64_lit by lia. intros Hr.
      destruct Hc as [[Hcl _]|[Hsh _]].
      * exact (client_not_rtc3 AInvA CST ALA HCST A rho'' tp md a HA5 Hcl Hr).
      * destruct Hsh as [(x & Hx & ->)|(x & Hx & ->)].
        -- pose proof (topG_range (aa_geom A)) as TG.
           destruct (law_client_app _ _ _ ALA A rho'' tp md x HA5 Hx) as [X|[X|X]]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI, Sh, SHADOW_OFF, rtc3_rng in *;
             pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia.
        -- destruct (HXGL x Hx). unfold IMG_HI, Sh, SHADOW_OFF, rtc3_rng in *.
           pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia.
    + intros x j Hx Hj Hdef.
      assert (X0 : 0 <= x < 2 ^ 47).
      { destruct Hx as [[Hcl _]|Hgl].
        - pose proof (topG_range (aa_geom A)) as TG. destruct (law_client_app _ _ _ ALA A rho'' tp md x HA5 Hcl) as [X|[X|X]]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *; lia.
        - destruct (HXGL x Hgl). unfold IMG_HI in *. lia. }
      rewrite RMout; [exact Hdef|]. unfold word_byte. rewrite u64_lit.
      2:{ unfold Sh, SHADOW_OFF. pose proof (Z.div_mod (x / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 8 + 2147450880) 8 ltac:(lia)).
          assert (0 <= x / 8 <= 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. }
      unfold Sh, SHADOW_OFF, rtc3_rng. pose proof (Z.div_mod (x / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 8 + 2147450880) 8 ltac:(lia)).
      assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.
End Inst.

Theorem mcR_of_cert : ltac2:(tb__ "0|0|
S19S2cR1A1S20S0S7VAInvA;VCST;VXGL;R2ZcA7F_;Fsrc;").
Proof.
  intros src Hcert ok A Kc rho tp HKc Hokf.
  apply (triple_pre ok _ (cells_ok (view segs (rm rho)) (RTCL (aa_geom A)))).
  { intros w Hw. destruct Hw as [Hsm HJ]. pose proof HJ as (HA & _ & _). exact (law_rtc _ _ _ ALA A rho tp _ HA). }
  intros HR.
  eapply triple_conseq; [ | | apply (coreR_sum src Hcert ok (JcontR A Kc tp) (JcontR_okf ok A Kc tp Hokf) (JcontR_stable A Kc tp HKc) rho tp)].
  - intros w Hw. apply (SPA_CR_of_pre src (JcontR A Kc tp) rho tp w (aa_geom A) HR).
    destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact HJ | reflexivity]].
  - intros w (L & rho' & HinL & Hag & Hsm & HJ). destruct HinL as [<-|[]]. cbn [la_state] in Hsm.
    exact (cont_postR src A Kc rho tp HR rho' w Hag (conj Hsm HJ)).
Qed.

Theorem mcRx_of_cert : ltac2:(tb__ "0|0|
S19S2cR1A1S21S0S7VAInvA;VCST;VXGL;R2ZcA7F_;Fsrc;").
Proof.
  intros src Hcert A Kc rho tp HKc.
  apply (etriple_pre _ (cells_ok (view segs (rm rho)) (RTCL (aa_geom A)))).
  { intros w Hw. destruct Hw as [Hsm HJ]. pose proof HJ as (HA & _ & _). exact (law_rtc _ _ _ ALA A rho tp _ HA). }
  intros HR.
  eapply etriple_conseq; [ | | apply (coreR_sum_ex src Hcert (JcontR A Kc tp) (JcontR_stable A Kc tp HKc) rho tp)].
  - intros w Hw. apply (SPA_CR_of_pre src (JcontR A Kc tp) rho tp w (aa_geom A) HR).
    destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact HJ | reflexivity]].
  - intros w (L & rho' & HinL & Hag & Hsm & HJ). destruct HinL as [<-|[]]. cbn [la_state] in Hsm.
    exact (cont_postR src A Kc rho tp HR rho' w Hag (conj Hsm HJ)).
Qed.

Theorem mcR_hv_of_laws : ltac2:(tb__ "0|0|
S20S0S7VAInvA;VCST;VXGL;S22ZcA7").
Proof. exact (mcR_of_cert white_hv echeckR_hv). Qed.
Theorem mcRx_hv_of_laws : ltac2:(tb__ "0|0|
S21S0S7VAInvA;VCST;VXGL;S22ZcA7").
Proof. exact (mcRx_of_cert white_hv echeckR_hv). Qed.
Theorem mcR_lo_of_laws : ltac2:(tb__ "0|0|
S20S0S7VAInvA;VCST;VXGL;S23ZcA7").
Proof. exact (mcR_of_cert white_lo echeckR_lo). Qed.
Theorem mcRx_lo_of_laws : ltac2:(tb__ "0|0|
S21S0S7VAInvA;VCST;VXGL;S23ZcA7").
Proof. exact (mcRx_of_cert white_lo echeckR_lo). Qed.
End ContractR.

