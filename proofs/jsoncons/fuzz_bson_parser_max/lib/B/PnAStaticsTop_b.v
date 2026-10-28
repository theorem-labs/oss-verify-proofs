(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA LibIface LibIfaceAB L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx
     PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnTopAL_b PnAHarnessStmts_b PnAHarness_b Ba0ExitCells_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSTT.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section T.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells).
Hypothesis LY : PMA.layout L C.
Let LYa := PMA.ly_as0 L C LY.
Local Notation Lay := (PNHA.LayA L).
Local Notation LSt := (PNSTA.TopLSA RSEGS PMA.AD PMA.AAD PMA.AN).

Lemma u8_of_cellz (M : word -> option byte) a : cellz RSEGS M a 1 0 -> L5.u8_at RSEGS M a 0.
Proof. unfold cellz, L5.u8_at. intros H. rewrite H. reflexivity. Qed.

Theorem statics_initA : lib_statics_initA Lay ar LSt.
Proof.
  unfold lib_statics_initA. intros av uid rnd tid canary hw M (IF & CELLS).
  unfold lib_init_facts in IF. cbv zeta in IF.
  cbn [lib_view heap_view ll_heap ll_init_img ll_guard HeapIface.hl_segs lla_L lla_init_img lla_guard PNHA.LayA PNTAL.TopLayA_a] in IF.
  cbn [lla_L lla_init_cells PNHA.LayA PNTAL.TopLayA_a] in CELLS. unfold PNTAL.init_cells_a in CELLS.
  rewrite (L5A.aly_segs L C LYa) in IF, CELLS.
  destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & _).
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end. clear CELLS.
  cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in *.
  assert (IC : forall lo hi, In (lo, hi) [(0x10000, 0x139000); (0x13bbf8, 0x13bca0); (0x672295, 0x673c30)] -> L5.img_clear M lo hi).
  { intros lo hi Hin i Hi. exact (IMG (lo, hi) i Hin Hi). }
  pose proof (IC _ _ ltac:(left; reflexivity)) as I1. pose proof (IC _ _ ltac:(right; right; left; reflexivity)) as I3. clear IC IMG.
  cbn [LibIface.ls_ok ls_g0 PNSTA.TopLSA]. unfold PNSTA.ls_okA, PNST.g0. cbn [PNST.st_loc PNST.st_sys PNST.st_ax].
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + cbn [pa_rw_lo PMA.AD ADDR_A]. exact I1.
    + exists canary. split; [exact HC| exact GU].
    + apply u8_of_cellz. cbn [pa_need_locks PMA.AD ADDR_A]. assumption.
    + cbn [pa_locale_lock PMA.AD ADDR_A]. assumption.
  - unfold PMST.loc_ok. intros iv Hin. cbn [pa_loc_foot PMA.AD ADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; intros i Hi; apply I3; cbn [fst snd] in *; lia.
  - unfold PMST.sys_ok. cbn [pa_syscat_guard PMA.AD ADDR_A]. intros i Hi. apply I3. lia.
  - split; [|split].
    + cbn [PNST.bax_cat pa_errcat_guard PMA.AD ADDR_A]. intros i Hi. apply I3. lia.
    + unfold PNST.bdec_ok. cbn [PNST.bax_dec PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A].
      repeat split; intros i Hi; apply I3; lia.
    + unfold PNSTA.atexit_stA, HAJ.atexit_cells. cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PNL.pn_drv_call PNL.pn_drv_guard PNST.bax_list PMA.AD PMA.AAD PMA.AN ADDR_A AADDR_A NADDR_A length Z.of_nat Z.mul Z.add].
      split; [apply u8_of_cellz; assumption|]. repeat (split; [assumption|]). intros i f a Hi. destruct i; discriminate.
Qed.

Theorem statics_frameA : lib_statics_frameA Lay ar LSt.
Proof.
  unfold lib_statics_frameA, lib_statics_frame. intros g M M' OK FOOT RO INITC.
  cbn [LibIface.ls_ok PNSTA.TopLSA] in *.
  apply (PNSTA.ls_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M'); [| | exact OK].
  - intros a Ha [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
    + apply FOOT; [exact Ha|]. exists iv. cbn [lib_view ll_foot lla_foot PNHA.LayA PNTAL.TopLayA_a]. unfold PNTAL.foot_a. split; [exact Hin| exact Hr].
    + apply INITC; [exact Ha|]. left. exists (0x693d40, 0x693d48). cbn [lib_view ll_initc lla_initc PNHA.LayA PNTAL.TopLayA_a]. cbn [pa_canary PMA.AD ADDR_A] in Hc.
      split; [cbn; tauto| cbn; lia].
    + apply INITC; [exact Ha|]. left. unfold pm_initc in Hin. cbn in Hin.
      cbn [lib_view ll_initc lla_initc PNHA.LayA PNTAL.TopLayA_a].
      destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [exists (0x693f93, 0x693f94)| exists (0x694070, 0x694074)]; (split; [cbn; tauto| cbn; lia]).
  - intros a Ha Hn. apply RO; [| exact Hn]. cbn [lib_view ll_rw_lo lla_rw_lo PNHA.LayA PNTAL.TopLayA_a]. rewrite L5.unsigned_lit by (cbn [pa_rw_lo PMA.AD ADDR_A] in Ha; lia).
    cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. lia.
Qed.

(* [comment removed for export] *)
Definition axmap (ax : PNST.bax) : axv := match ax with PNST.AX0 => AX0 | PNST.AXc => AXc | PNST.AXs => AXs | PNST.AXcs => AXcs | PNST.AXsc => AXsc end.

Theorem lsx_atexit : forall (ar0 : asan_run) (g : PNST.st) (M : word -> option byte), LibIface.ls_ok LSt g M -> exists ax : axv, atexit_cellsA M ax.
Proof.
  intros ar0 g M OK. destruct (PNSTA.pn_statics_exitA RSEGS PMA.AD PMA.AAD PMA.AN g M OK) as (AX & DEC). exists (axmap (PNST.st_ax g)).
  unfold PNSTA.atexit_stA, HAJ.atexit_cells in AX.
  cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit PNL.pn_drv_call PNL.pn_drv_guard pa_errcat_dtor pa_errcat_obj PNL.pn_str_dtor PNL.pn_inf_obj PNL.pn_nan_obj PMA.AD PMA.AAD PMA.AN ADDR_A AADDR_A NADDR_A] in AX.
  unfold atexit_cellsA, AX_CELLS, ax_cell, axmap.
  destruct (PNST.st_ax g); cbn [PNST.bax_list PNST.bax_dec length Z.of_nat Z.mul Z.add Pos.of_succ_nat Pos.mul Pos.add Pos.succ] in AX, DEC;
    destruct AX as (_ & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296 & EXT).
  - repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
  - destruct (EXT 0%nat _ _ eq_refl) as (E1 & E2 & E3 & E4). cbn [Z.of_nat Z.mul Z.add] in E1, E2, E3, E4.
    repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
  - destruct (EXT 0%nat _ _ eq_refl) as (E1 & E2 & E3 & E4). destruct (EXT 1%nat _ _ eq_refl) as (F1 & F2 & F3 & F4).
    cbn [Z.of_nat Z.mul Z.add Pos.of_succ_nat Pos.mul Pos.add] in E1, E2, E3, E4, F1, F2, F3, F4.
    unfold PNST.bdec_ok in DEC. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A] in DEC. destruct DEC as (_ & _ & (SI & _) & (SN & _)).
    repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
  - destruct (EXT 0%nat _ _ eq_refl) as (E1 & E2 & E3 & E4). destruct (EXT 1%nat _ _ eq_refl) as (F1 & F2 & F3 & F4). destruct (EXT 2%nat _ _ eq_refl) as (G1 & G2 & G3 & G4).
    cbn [Z.of_nat Z.mul Z.add Pos.of_succ_nat Pos.mul Pos.add Pos.succ] in E1, E2, E3, E4, F1, F2, F3, F4, G1, G2, G3, G4.
    unfold PNST.bdec_ok in DEC. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A] in DEC. destruct DEC as (_ & _ & (SI & _) & (SN & _)).
    repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
  - destruct (EXT 0%nat _ _ eq_refl) as (E1 & E2 & E3 & E4). destruct (EXT 1%nat _ _ eq_refl) as (F1 & F2 & F3 & F4). destruct (EXT 2%nat _ _ eq_refl) as (G1 & G2 & G3 & G4).
    cbn [Z.of_nat Z.mul Z.add Pos.of_succ_nat Pos.mul Pos.add Pos.succ] in E1, E2, E3, E4, F1, F2, F3, F4, G1, G2, G3, G4.
    unfold PNST.bdec_ok in DEC. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A] in DEC. destruct DEC as (_ & _ & (SI & _) & (SN & _)).
    repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
Qed.
End T.
End PNSTT.
