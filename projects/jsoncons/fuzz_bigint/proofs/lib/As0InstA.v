(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA LibIface LibIfaceA ArtRuns ArtBridge ArtInv ArtFsInv ArtHandoffRi ArtIfaceInst ArtIfaceInstFree ArtIfaceLayout
  ArtWrapSmallocI ArtIcptInst As0DefsK As0Drv_defs As0DrvLib As0DrvRead As0MainPhaseA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  - intros c Hc. unfold As0DrvStdio.PR_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold As0DrvStdio.EX_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold As0DrvStdio.DG_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. unfold As0DrvStdio.DGS_CELLS in Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
  - intros c Hc. cbn [In] in Hc. cbn.
    repeat (destruct Hc as [<-|Hc]; [tauto|]). destruct Hc.
Qed.

(* [comment removed for export] *)
Theorem as0_inst_ok : forall scfg BUDGET, sc_alloc scfg = false -> inst_ok_stmt scfg art_L art_C BUDGET.
Proof.
  intros scfg BUDGET Halloc MAPS0 RESV0 NOACC0 BASE rn BS ROK Htp Hkey Htsd Hloff.
  exact (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp Hkey Htsd Hloff
           (art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Halloc asegs_wx BS Htp)
           (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp)).
Qed.

(* [comment removed for export] *)
Theorem as0_free_null : forall scfg BUDGET, free_null_stmt scfg art_L BUDGET.
Proof.
  intros scfg BUDGET MAPS0 RESV0 NOACC0 BASE rn _ _ Htp _ _ _.
  exact (art_inst_free_null MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg asegs_wx Htp).
Qed.

(* [comment removed for export] *)
Theorem as0_icpt_ok : forall scfg IL BUDGET, as0_icpt_layout IL -> icpt_ok_stmt scfg art_L IL BUDGET.
Proof.
  intros scfg IL BUDGET ILY MAPS0 RESV0 NOACC0 BASE rn _ _ Htp Hkey Htsd Hloff.
  exact (art_icpt_ok scfg IL BUDGET asegs_wx ILY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey Htsd Hloff).
Qed.
