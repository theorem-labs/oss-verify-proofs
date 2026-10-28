(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b BatIfaceLaws_b BatIfaceInst_b BatIfaceLayout_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PnStatics. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAa_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma art_pm_dep_not_static : forall a, PMST.dep PMA.AD a -> ~ hl_rt_static art_L a.
Proof.
  intros a D. cbn [art_L hl_rt_static]. unfold art_static.
  unfold PMST.dep, pm_foot, pm_initc in D. cbn [PMA.AD ADDR_A pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock app] in D.
  destruct D as [(iv & Hiv & Hr) | [Hc | (iv & Hiv & Hr)]].
  - cbn [In] in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv.
  - lia.
  - cbn [In] in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv.
Qed.
(* [comment removed for export] *)
Lemma art_pn_dep_not_static : forall a, PNST.dep PMA.AD PMA.AN a -> ~ hl_rt_static art_L a.
Proof.
  intros a D. destruct D as [(iv & Hiv & Hr) | [Hc | (iv & Hiv & Hr)]].
  - unfold PNST.pn_foot in Hiv. apply in_app_or in Hiv as [Hiv|Hiv].
    + apply art_pm_dep_not_static. left. exists iv. split; [exact Hiv| exact Hr].
    + cbn [art_L hl_rt_static]. unfold art_static. unfold PNL.pn_d128_foot in Hiv.
      cbn [PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_inf_obj PNL.pn_nan_guard PNL.pn_nan_obj In] in Hiv.
      repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; lia|]). destruct Hiv.
  - apply art_pm_dep_not_static. right. left. exact Hc.
  - apply art_pm_dep_not_static. right. right. exists iv. split; [exact Hiv| exact Hr].
Qed.

Theorem art_pma_layout : PMA.layout art_L art_C.
Proof.
  constructor.
  - exact art_as0_layout.
  - reflexivity.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
  - cbn. split; [reflexivity | split; reflexivity].
  - exact art_pn_dep_not_static.
  - intros a Ha. cbn [art_L hl_rt_static]. unfold art_static. lia.
  - intros a Ha. cbn [art_L hl_rt_ro] in Ha. unfold art_ro in Ha. lia.
  - cbn [art_C art_statics_cells asc_cells]. split; apply in_or_app; right; cbn [art_cells_drv In]; tauto.
  - intros a Ha. cbn [art_L hl_rt_static hl_tp] in *. unfold art_static. lia.
Qed.
