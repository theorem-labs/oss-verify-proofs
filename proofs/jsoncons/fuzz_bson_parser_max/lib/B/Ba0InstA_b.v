(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB ArtRuns ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatFsInv_b BatHandoffRi_b BatIfaceInst_b BatIfaceInstFree_b BatIfaceLayout_b
  BatWrapSmallocI_b BatIcptInst_b Ba0DefsK_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0MainPhaseA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx StrictOfB. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatIfaceInstAnn_b BatIfaceInstSfree_b.      (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAImgGap_b BatIcptLawsGap_b.      (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Theorem as0_h4e : forall BUDGET, h4e_stmt BUDGET.
Proof. intros BUDGET MAPS0 RESV0 NOACC0 BASE rn gfs0 k0 K0 B0 A0 M V HT. exact (art_handoff_ri art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn gfs0 k0 K0 B0 A0 M V HT). Qed.

(* [comment removed for export] *)
Theorem as0_dla_ok : forall scfg IL, as0_icpt_layout IL -> dla_ok_stmt scfg art_L art_C IL.
Proof.
  intros scfg IL ILY ar HI sp0 HIok Hs. pose proof (aicl_memcpy IL ILY) as HM. constructor; try reflexivity; try exact HM; try exact Hs.
  - cbn. lia.
  - intros lo hi a Hin Ha. exact (art_L_client lo hi a Hin Ha).
  - intros lo hi a Hin Ha. exact (art_L_w_not_ro lo hi a Hin Ha).
  - exact art_L_ro_img.
Qed.

(* [comment removed for export] *)
Theorem as0_drv_consts : forall IL, as0_icpt_layout IL -> drv_consts_stmt art_L art_C IL.
Proof.
  intros IL ILY. split; [exact ILY|]. split; [|split; [cbn; lia|split; [cbn; lia|split; [cbn; lia|split; [|split; [|split; [|split]]]]]]].
  - intros c Hc. unfold RD_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold Ba0DrvStdio_b.PR_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold Ba0DrvStdio_b.EX_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold Ba0DrvStdio_b.DG_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold Ba0DrvStdio_b.DGS_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem as0_inst_ok : forall scfg BUDGET, sc_alloc scfg = false -> inst_ok_stmt scfg art_L art_C BUDGET.
Proof.
  intros scfg BUDGET Halloc MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  assert (SM : forall k, In k [0; 1; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) k)
    by exact (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
  split; [exact art_L_img_low|]. split.
  - exact (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp Hkey Htsd Hloff
             (art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp) SM).
  - exact (art_inst_flag_in_fs MAPS0 RESV0 NOACC0 BASE BUDGET rn).
Qed.

(* [comment removed for export] *)
Definition ext_open_stmt (scfg : SpuriousCfg) (BUDGET : Z) (EX : HAJ.ext_consts) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET BatInv_b.LENMAX BatInv_b.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x673d00 -> rn_key rn = 0 -> rn_tsd rn = 0x6951b8 -> rn_loff rn = 0x10 ->
    HAJ.cxa_atexit_spec art_L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) (HAJ.ec_cxa_pc EX) (HAJ.ec_cxa_scr EX) (HAJ.ec_atexit EX)
         (HAJ.ec_f0 EX) (HAJ.ec_a0 EX) (HAJ.ec_f1 EX) (HAJ.ec_a1 EX) (HAJ.ec_atc EX) (HAJ.ec_nl EX).
Theorem as0_ext_ok : forall scfg BUDGET EX, HAJ.ec_ann_pc EX = 0x7ba7c -> HAJ.ec_ann_scr EX = 2304 -> HAJ.ec_sf_pc EX = 0x5e2e8 -> HAJ.ec_sf_scr EX = 16 -> ext_open_stmt scfg BUDGET EX ->      (* [comment removed for export] *)
  ext_ok_stmt scfg art_L EX BUDGET.
Proof.
  intros scfg BUDGET EX EPC ESCR SPC SSCR OPEN MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  pose proof (OPEN MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff) as CXA.
  apply HAJ.AEXT; [rewrite EPC, ESCR; exact (art_inst_annotate MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp)|exact CXA| | |rewrite SPC, SSCR; exact (art_inst_sfree5 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp)].
  - exact (art_inst_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rn Htp Hkey Htsd Hloff).
  - exact (art_inst_free_null MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
Qed.


(* [comment removed for export] *)
Theorem as0_free_null : forall scfg BUDGET, free_null_stmt scfg art_L BUDGET.
Proof.
  intros scfg BUDGET MAPS0 RESV0 NOACC0 BASE rn _ _ Htp _ _ _.
  exact (art_inst_free_null MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem as0_gap_ok : forall BUDGET, gap_ok_stmt BUDGET.
Proof. intros BUDGET MAPS0 RESV0 NOACC0 BASE rn _ _ _ _ _ _. exact (art_law_img_gap MAPS0 RESV0 NOACC0 BASE BUDGET rn). Qed.

Theorem as0_icpt_ok : forall scfg IL BUDGET, as0_icpt_layout IL -> icpt_ok_stmt scfg art_L IL BUDGET.
Proof.
  intros scfg IL BUDGET ILY MAPS0 RESV0 NOACC0 BASE rn _ _ Htp Hkey Htsd Hloff.
  exact (art_icpt_ok scfg IL BUDGET asegs_wx ILY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey Htsd Hloff).
Qed.
