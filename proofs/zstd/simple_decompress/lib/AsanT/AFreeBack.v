(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA StepF SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ARepQR ARepQD ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts ASec AFreeModel AFreeRep AFreeGeo AFreeRead F_afree_iseg F_afree_tail F_afree_icpt F_afreeC_iface F_afree_arep ARecGeo F_adorec AQrecP
     AFrameD AFreeC_kit_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma Q_MIN_lt_MAX : Q_MIN < Q_MAX.
Proof. unfold Q_MIN, Q_MAX. lia. Qed.

Theorem afree_back : forall DI AFK CI, afree_back_stmt DI AFK CI.
Proof.
  intros DI AFK CI. unfold afree_back_stmt. intros until ms2. cbv zeta.
  intros ALO CEIL LO CI_OK CI_OK2 FPLE WFR BLR HP0 FRP FRA SZA FRT SZT FRS RIMG RSTK RET QL0 QLB0.
  destruct RET as (t0 & t1 & t2 & a0 & a1 & a2 & a3' & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & R1 & -> & FPLE1 & ARNG1 & T1 & PB1 & PE1 & LOC1
                   & AR1 & BL1 & AF1 & MI1 & ST & MU1 & CP1 & ELIVE & ENEXT & EQLOC & EQLB & ENRES & EPA & ESB & GB1).
  unfold AFREE_STACK in *.
  word_range sp SPR.
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  assert (HS80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 2128 - 80)) = bv_unsigned sp - 2128 - 80) by (apply unsigned_lit; lia).
  rewrite HS80 in MU1, ST, CP1. clear HS80.
  (* [comment removed for export] *)
  assert (D : forall A n, bv_unsigned sp - 2128 - 80 <= A -> disjoint_from [(0, bv_unsigned sp - 2128 - 80)]%Z A n).
  { intros A n HA. cbn. lia. }
  pose proof (cells_frameD _ _ _ _ _ FRP MU1 ltac:(apply D; lia)) as FRP1.
  pose proof (cells_frameD _ _ _ _ _ FRA MU1 ltac:(apply D; lia)) as FRA1.
  pose proof (cells_frameD _ _ _ _ _ FRT MU1 ltac:(apply D; lia)) as FRT1.
  pose proof (cells_frameD _ _ _ _ _ FRS MU1 ltac:(apply D; lia)) as FRS1.
  clear FRP FRA FRT FRS.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x37ce4)) with (Z_to_bv 64 0x37ce4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  replace (bv_unsigned sp - 2128 - 80) with (bv_unsigned sp + -2208) in * by lia.
  replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2112) in * by lia.
  replace (bv_unsigned sp - 2128) with (bv_unsigned sp + -2128) in * by lia.
  replace (bv_unsigned sp - 72) with (bv_unsigned sp + -72) in * by lia.
  rename MI1 into MI.
  pose proof (munch_refl (@nil (Z * Z)) m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  unfold put_frame in FRP1.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE1| exact RSTK]).
  pose proof ARNG1 as ARNGx. destruct ARNGx as (RIMG1 & _).
  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
  zstep.                                       (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  try replace (bv_unsigned sp + -2208 + 80) with (bv_unsigned sp + -2128) in * by lia.
  release_frame FRP1 ST (bv_unsigned sp + -2128).
  (* [comment removed for export] *)
  eapply evtF_mono.
  { (eapply (ficptD_spec RNG1 sp gp (Z_to_bv 64 ATP)); [exact ST | atop_facts; lia | lia | exact MI
      | eexists; split; [exact FRA1 | exact SZA]
      | eexists; split; [exact FRT1 | exact SZT]
      | exact FRS1 | exact RIMG1 | exact RSTK1 ]). }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  unfold afree_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE1]|].
  do 15 eexists. exists m1. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST3|].
  split.
  - eapply aheap_pres_trans; [exact HP0|].
    eapply (cpres_aheap_pres CI L (bv_unsigned sp + -2208) (lb_remove p LB) (bv_unsigned sp) stR XR mR m1 ALO WFR BLR CI_OK CI_OK2); [lia|].
    exact CP1.
  - (* [comment removed for export] *)
    split; [exact ALO|]. split; [exact ARNG1|]. split; [| exact AF1].
    exists X1. split; [| exact BL1].
    pose proof AR1 as (A1 & A2 & A3 & A4 & A5 & HQ & HS & HD & A9 & A10 & A11 & A12).
    cbn [ah_quar ah_sec ah_depot AHq] in HQ, HS, HD.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    split; [| split; [| split; [exact HD| exact (conj A9 (conj A10 (conj A11 A12)))]]].
    + (* [comment removed for export] *)
      cbn [ah_quar AHQ]. exists (mkQConc (qr_loc R1) (qr_glob R1) (qr_ia R1) (qr_qpend R1)).
      apply AQUAR_at_of_dr; [exact HQ| exact T1| exact PB1| exact PE1| rewrite EQLB, QLB0; unfold Q_CACHE; lia|].
      pose proof Q_MIN_lt_MAX. lia.
    + (* [comment removed for export] *)
      cbn [ah_sec AHQ]. unfold ASEC_of. unfold csx, inflight, secsT in HS. rewrite T1, PE1 in HS. cbn [esecs map flat_map app] in HS.
      rewrite app_nil_r in HS. exact HS.
Qed.
End CANSEC1.
