(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import PrimaryShadow0.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes ALayout ARep AHeapP ARepInit_kit ARepInit_A.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section D.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis SH0 : bshadow0 V m.
  Let L := mkALayout (LV V) w U.

  Lemma sb_eq : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536.
  Proof. unfold al_space_beg. cbn [al_V L LV Nat.eqb]. lia. Qed.
  Lemma sb_eq' : aspace_beg V = al_space_beg L.
  Proof. unfold aspace_beg. rewrite sb_eq. lia. Qed.
  Lemma sb_facts : 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
                   /\ 0 <= al_space_beg L < 2^47.
  Proof. exact (alayout_space _ (alayout_ok_init V w U HP HU HAT)). Qed.

  (* [comment removed for export] *)
  Lemma ri_zero : forall i, 0 <= i < 4096 -> m (wa (al_space_beg L + K_SPACE_SIZE + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. mf V m HM (MZero (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096) ZR.
    rewrite sb_eq. unfold K_SPACE_SIZE. replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37 + i)
      with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008 + i) by lia. apply ZR. lia.
  Qed.
  Lemma ri_wr : wr_at bsegs m (al_space_beg L + K_SPACE_SIZE) 4096.
  Proof.
    mwr V m HM (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096 W.
    rewrite sb_eq. unfold K_SPACE_SIZE. replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
      with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia. exact W.
  Qed.

  Ltac ri_cells c Hc :=
    apply zcells; [reflexivity
      | cbn [cells_size csize Nat.add]; intros i Hi; unfold aregion_info, ARI_STRIDE;
        match goal with |- m (wa ?x) = _ => replace x with (al_space_beg L + K_SPACE_SIZE + (x - (al_space_beg L + K_SPACE_SIZE))) by lia end;
        apply ri_zero; lia
      | unfold aregion_info, ARI_STRIDE; eapply wr_at_sub; [exact ri_wr| unfold K_SPACE_SIZE; lia| lia| cbn; lia] ].

  Theorem aregion_cells_init : forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L (ST0 V) m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aregion_cells. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user aclass0].
    split; [ri_cells c Hc|]. split; [ri_cells c Hc|].
    split; [exists (repeat (Z_to_bv 8 0) 4); ri_cells c Hc|].
    split; [ri_cells c Hc|]. exists (repeat (Z_to_bv 8 0) 56); ri_cells c Hc.
  Qed.

  (* [comment removed for export] *)
  Lemma shad_add : forall a k, a mod 8 = 0 -> shad (a + k) = shad a + k / 8.
  Proof. intros a k Ha. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.
  Lemma shlen_eq : forall n, shlen n = n / 8.
  Proof. intros n. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

  Theorem afreearray_init : forall c, 1 <= c < K_NUM_CLASSES -> afreearray L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold afreearray. rewrite get_cls_ST0. cbn [c_num_freed c_mapped_free_array aclass0 x_cls X0 xc_free map].
    unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    split; [apply u32arr_nil; lia|]. split.
    - exists []. rewrite Z.add_0_r. change (Z.to_nat (0 - 4 * 0)) with 0%nat. apply rw_cells_CB0; lia.
    - exists []. change (Z.to_nat (shlen 0)) with 0%nat. apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
  Qed.

  Theorem aslots_init : forall c, 1 <= c < K_NUM_CLASSES -> aslots L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aslots. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. split; [intros k Hk; lia|].
    exists []. unfold aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (0 - 0)) with 0%nat. apply rw_cells_CB0; lia.
  Qed.

  Theorem aslot_shadow_init : forall c, 1 <= c < K_NUM_CLASSES -> aslot_shadow L (ST0 V) X0 m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    unfold aslot_shadow. rewrite get_cls_ST0, ndist_ST0. cbn [c_allocated_user c_mapped_user aclass0]. split; [intros k Hk; lia|].
    unfold fill_at, aregion, K_REGION. change (2^32) with 4294967296. rewrite Z.add_0_r. change (Z.to_nat (shlen (0 - 0))) with 0%nat. cbn [repeat].
    apply rw_cells_CB0; unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ashadow_avail_init : forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L (ST0 V) m c.
  Proof.
    intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof sb_facts as (S1 & S2 & S3 & S4). unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in S1, S2, S3, S4.
    destruct (primary_shadow0 V m SH0 HP) as [Z0' W0]. rewrite sb_eq' in Z0', W0.
    assert (A8 : al_space_beg L mod 8 = 0) by (clear - S3; Z.div_mod_to_equations; lia).
    unfold ashadow_avail. rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. rewrite !Z.add_0_r, !Z.sub_0_r.
    unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX. change (2^32) with 4294967296.
    replace (shad (al_space_beg L + c * 4294967296 + 3758096384)) with (shad (al_space_beg L) + (c * 536870912 + 469762048))
      by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; Z.div_mod_to_equations; lia).
    replace (shad (al_space_beg L + c * 4294967296)) with (shad (al_space_beg L) + c * 536870912)
      by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - A8; Z.div_mod_to_equations; lia).
    rewrite !shlen_eq. change (3758096384 / 8) with 469762048. change (536870912 / 8) with 67108864.
    split; split.
    - intros i Hi. replace (shad (al_space_beg L) + c * 536870912 + i) with (shad (al_space_beg L) + (c * 536870912 + i)) by lia. apply Z0'. lia.
    - eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia| lia| lia].
    - intros i Hi. replace (shad (al_space_beg L) + (c * 536870912 + 469762048) + i) with (shad (al_space_beg L) + (c * 536870912 + 469762048 + i)) by lia. apply Z0'. lia.
    - eapply wr_at_sub; [exact W0| unfold shad, AsanEmbed.ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia| lia| lia].
  Qed.
End D.
End CANSEC1.
