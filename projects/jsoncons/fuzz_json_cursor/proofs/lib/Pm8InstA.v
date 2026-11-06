(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec HeapIface HeapIfaceA PmHeapIfaceA HeapIfaceANull IcptIfaceA PmIcptIfaceA Pm8IcptLayout PmIcptDrvA LibIface PmLibIfaceA ArtRuns ArtBridge Pm8ArtInv Pm8ArtFsInv Pm8ArtHandoffRi Pm8ArtIfaceInst Pm8ArtIfaceInstFree Pm8ArtIfaceLayout
  Pm8ArtIfaceInstX Pm8ArtIcptInstX Pm8DefsK Pm8Drv_defs Pm8DrvLib Pm8DrvRead Pm8MainPhaseA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance PropExec.fx0.

Theorem as0_h4e : forall BUDGET, h4e_stmt BUDGET.
Proof. intros BUDGET MAPS0 RESV0 NOACC0 BASE rn gfs0 k0 K0 B0 A0 M V HT. exact (art_handoff_ri art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn gfs0 k0 K0 B0 A0 M V HT). Qed.

Theorem as0_dla_ok : forall scfg IL, as0_icpt_layout IL -> dla_ok_stmt scfg art_L art_C IL.
Proof.
  intros scfg IL ILY ar HI sp0 HIok Hs. pose proof (aicl_memcpy IL ILY) as HM. constructor; try reflexivity; try exact HM; try exact Hs.
  - cbn. lia.
  - intros lo hi a Hin Ha. exact (art_L_client lo hi a Hin Ha).
  - intros lo hi a Hin Ha. exact (art_L_w_not_ro lo hi a Hin Ha).
  - exact art_L_ro_img.
Qed.

Theorem as0_drv_consts : forall IL, as0_icpt_layout IL -> drv_consts_stmt art_L art_C IL.
Proof.
  intros IL ILY. split; [exact ILY|]. split; [|split; [cbn; lia|split; [cbn; lia|split; [cbn; lia|split; [|split; [|split; [|split]]]]]]].
  - intros c Hc. unfold RD_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold Pm8DrvStdio.PR_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold Pm8DrvStdio.EX_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold Pm8DrvStdio.DG_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold Pm8DrvStdio.DGS_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
Qed.

Theorem as0_inst_ok : forall scfg BUDGET, sc_alloc scfg = false -> inst_ok_stmt scfg art_L art_C BUDGET.
Proof.
  intros scfg BUDGET Halloc MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  exact (pio_base _ _ _ _ _ _ (art_pm_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp Hkey Htsd Hloff)).
Qed.

Theorem as0_sfree_ok : forall scfg BUDGET, sc_alloc scfg = false -> sfree_ok_stmt scfg art_L art_LX BUDGET.
Proof.
  intros scfg BUDGET Halloc MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  exact (pio_stack_free5 _ _ _ _ _ _ (art_pm_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp Hkey Htsd Hloff)).
Qed.

Theorem as0_free_null : forall scfg BUDGET, free_null_stmt scfg art_L BUDGET.
Proof.
  intros scfg BUDGET MAPS0 RESV0 NOACC0 BASE rn _ _ Htp _ _ _.
  exact (art_inst_free_null MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
Qed.

Definition icptx_stmt (scfg : SpuriousCfg) (ILX : icpt_layout_x) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn, rn_tp rn = 0x690a50 -> rn_key rn = 0 -> rn_tsd rn = 0x6b1f08 -> rn_loff rn = 0x10 ->
    pm_icptx_open art_L (rn_ar rn) ILX scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Theorem as0_icpt_ok : forall scfg IL ILX BUDGET, as0_icpt_layout IL -> pm_icpt_layout_x ILX -> icptx_stmt scfg ILX BUDGET -> icpt_ok_stmt scfg art_L IL ILX BUDGET.
Proof.
  intros scfg IL ILX BUDGET ILY ILXY ICPTX MAPS0 RESV0 NOACC0 BASE rn _ _ Htp Hkey Htsd Hloff.
  exact (art_pm_icpt_ok_annot scfg IL ILX BUDGET asegs_wx ILY ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey Htsd Hloff (ICPTX MAPS0 RESV0 NOACC0 BASE rn Htp Hkey Htsd Hloff)).
Qed.

Theorem as0_icptx : forall scfg ILX BUDGET, pm_icpt_layout_x ILX -> icptx_stmt scfg ILX BUDGET.
Proof.
  intros scfg ILX BUDGET ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey Htsd Hloff.
  exact (art_pm_icptx scfg ILX BUDGET asegs_wx ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey Htsd Hloff).
Qed.
Theorem as0_icpt_ok_closed : forall scfg IL ILX BUDGET, as0_icpt_layout IL -> pm_icpt_layout_x ILX -> icpt_ok_stmt scfg art_L IL ILX BUDGET.
Proof.
  intros scfg IL ILX BUDGET ILY ILXY. exact (as0_icpt_ok scfg IL ILX BUDGET ILY ILXY (as0_icptx scfg ILX BUDGET ILXY)).
Qed.
