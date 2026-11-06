(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)

Section LocalK.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  Definition rep_cells_nk (st : ast) (Lc FF : list (Z * Z)) (a : Z) : Prop :=
    False
    \/ instance_cells bt st a
    \/ thread_cells bt a
    \/ (exists c, 1 <= c <= 30 /\ foot_region bt st c a)
    \/ (exists b, In b (a_tq st ++ a_gq st) /\ foot_batch b a)
    \/ (exists sc, In sc (a_sec st) /\ foot_sec sc a)
    \/ (exists p n, (In (p, n) Lc \/ In (p - 16, n) (quar st)) /\ foot_hdr p n a)
    \/ foot_depot_static bt a
    \/ (exists id, 1 <= id <= dp_nids (a_dep st) /\ foot_node bt (a_dep st) id a)
    \/ foot_fake_static bt a
    \/ (exists f k, In (f, k) FF /\ foot_fword f k a)
    \/ ialloc_cells bt a
    \/ (exists c, 1 <= c <= 30 /\ foot_shreg bt st Lc c a)
    \/ (exists sc, In sc (a_sec st) /\ foot_shsec st sc a)
    \/ rtc_cells bt a.
  Definition rep_supp_nk (st : ast) (Lc FF : list (Z * Z)) (a : Z) : Prop := rep_cells_nk st Lc FF a \/ rep_wr bt st Lc FF a.

  Tactic Notation "pickc" integer(n) := left; do n right; left.
  Tactic Notation "pickw" integer(n) := right; do n right; left.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  Theorem Rep_local_k : forall st Lc FF M M' mdl {qt qg : Z},
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M mdl ->
    cells_hold SG M' (bt_consts bt) ->
    (forall i, rep_supp_nk st Lc FF i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    Rep bt st Lc FF M' mdl.
  Proof using.
    intros st Lc FF M M' mdl qt qg W R KC' AG.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & YC).
    ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in *.
    pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _).
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    unfold Rep, rep_supp_nk, rep_cells_nk, rep_wr in *.
    split. { (* [comment removed for export] *) exact KC'. }
    split. { (* [comment removed for export] *)
             eapply rep_instance_local; [exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i [Hi|Hi] Hr; apply AG; [pickc 1; exact Hi | exact Hr | pickw 0; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_thread_local; [exact R3 | ulia | ulia | ulia | ulia | exact (cache_len bt st Lc FF W) |].
             intros i [Hi|Hi] Hr; apply AG; [pickc 2; exact Hi | exact Hr | pickw 1; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) intros c Hc. destruct (R4 c Hc) as [G F]. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
             destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
             eapply rep_region_local; [exact G | exact F | ulia | ulia | ulia | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. unfold region_supp in Hi.
             destruct Hi as [Hi | [Hi | Hi]].
             - destruct (decide (reginfo bt c + 64 <= i < reginfo bt c + 68)) as [J|J].
               + apply AG; [pickw 2; exists c; split; [exact Hc | left; lia] | exact Hr].
               + destruct (decide (i < reginfo bt c + 72)) as [J2|J2].
                 * apply AG; [pickc 3; exists c; split; [exact Hc | left; split; [lia | exact J]] | exact Hr].
                 * apply AG; [pickw 2; exists c; split; [exact Hc | left; lia] | exact Hr].
             - apply AG; [pickw 2; exists c; split; [exact Hc | right; left; exact Hi] | exact Hr].
             - apply AG; [pickw 2; exists c; split; [exact Hc | right; right; exact Hi] | exact Hr]. }
    assert (BR : forall b, In b (a_tq st ++ a_gq st) -> 0 <= ba_addr b /\ ba_addr b + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b)) <= BATCHCAP).
    { intros b Hb. destruct (batch_facts bt st Lc FF W b Hb) as (_ & L1 & L2 & L3). unfold BATCHSZ in *. repeat split; ulia. }
    split. { (* [comment removed for export] *) eapply rep_batches_local; [exact R5 | intros b Hb; apply BR; apply in_app_iff; left; exact Hb |].
             intros b i Hb Hi Hr. apply AG; [pickw 3; exists b; split; [apply in_app_iff; left; exact Hb | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_batches_local; [exact R6 | intros b Hb; apply BR; apply in_app_iff; right; exact Hb |].
             intros b i Hb Hi Hr. apply AG; [pickw 3; exists b; split; [apply in_app_iff; right; exact Hb | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_secondary_local; [exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). pose proof (rz_range (sc_n sc)). unfold sc_user, sec_user_off in *. ulia.
             - intros sc i Hs Hi Hr. apply AG; [pickw 4; exists sc; split; [exact Hs | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_headers_local; [exact R8 | | | |].
             - intros p n Hin. destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n). ulia.
             - intros m n Hin. destruct (quar_item_range bt st Lc FF W m n Hin) as (A1 & A2 & A3). pose proof (rz_range n). ulia.
             - intros p n i Hin [Hi|Hi] Hr; apply AG; [pickc 6; exists p, n; split; [left; exact Hin | exact Hi] | exact Hr | | exact Hr].
               pickw 5. exists p, n. split; [exact Hin|]. left. destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). lia.
             - intros m n i Hin [[Hi|Hi]|Hi] Hr; apply AG; try exact Hr.
               + pickc 6. exists (m + 16), n. split; [right; replace (m + 16 - 16) with m by lia; exact Hin | exact Hi].
               + pickw 6. exists m, n. split; [exact Hin | lia].
               + pickw 6. exists m, n. split; [exact Hin | lia]. }
    split. { (* [comment removed for export] *) eapply rep_depot_local; [exact R9 | ulia | ulia | ulia | ulia | | | | | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros b Hb. destruct (node_blocks_range bt st Lc FF W b Hb) as (A1 & A2 & _). ulia.
             - intros b Hb. destruct (store_blocks_range bt st Lc FF W b Hb) as (A1 & A2 & _). ulia.
             - intros i Hi Hr. apply AG; [pickc 7; exact Hi | exact Hr].
             - intros id i Hid Hi Hr. apply AG; [pickc 8; exists id; split; [exact Hid | exact Hi] | exact Hr].
             - intros b i Hb Hi Hr. apply AG; [pickw 7; exists b; split; [exact Hb | exact Hi] | exact Hr].
             - intros b i Hb Hi Hr. apply AG; [pickw 8; exists b; split; [exact Hb | exact Hi] | exact Hr]. }
    split. { (* [comment removed for export] *) pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_local; [exact R10 | ulia | ulia | ulia | ulia | ulia | ulia | | |].
             - intros f k Hin. destruct (fake_frame_facts bt st Lc FF W f k Hin) as (A1 & A2 & A3 & A4 & _). (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end). ulia.
             - intros i Hi Hr. apply AG; [pickc 9; exact Hi | exact Hr].
             - intros i Hi Hr. apply AG; [pickw 9; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. apply AG; [pickc 11; exact Hi | exact Hr]. }
    split. { (* [comment removed for export] *) eapply rep_shadow_local; [exact R12 | | | |].
             - intros c Hc. pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
               destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). ulia.
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros c i Hc [Hi|Hi] Hr; apply AG; [pickc 12; exists c; split; [exact Hc | exact Hi] | exact Hr | pickw 11; exists c; split; [exact Hc | exact Hi] | exact Hr].
             - intros sc i Hs [Hi|Hi] Hr; apply AG; [pickc 13; exists sc; split; [exact Hs | exact Hi] | exact Hr | pickw 12; exists sc; split; [exact Hs | exact Hi] | exact Hr]. }
    split; [exact R13|]. split; [exact R14|].
    split. { intros p n Hin. destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4). pose proof (rz_range n).
             destruct (R15 p n Hin) as [W1 W2]. split.
             - eapply (writableZ_local _ _ _ _ _ W1); [ulia | ulia |]. intros i Hi Hr. apply AG; [pickw 5; exists p, n; split; [exact Hin | left; lia] | exact Hr].
             - eapply (writableZ_local _ _ _ _ _ W2); [(lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold sh_hi in G in change_no_check G' end); ulia |]. intros i Hi Hr. apply AG; [pickw 5; exists p, n; split; [exact Hin | right; exact Hi] | exact Hr]. }
    split. { intros f k Hin. destruct (fake_frame_facts bt st Lc FF W f k Hin) as (A1 & A2 & A3 & A4 & _).
             eapply (writableZ_local _ _ _ _ _ (R16 f k Hin)); [unfold sh_lo, FAKE_SIZE in *; ulia | unfold sh_hi, FAKE_SIZE in *; ulia |].
             intros i Hi Hr. apply AG; [pickw 10; exists f, k; split; [exact Hin | exact Hi] | exact Hr]. }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R17); [ulia | ulia |]. intros i Hi. apply AG; [left; do 14 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia | ulia]. }
    split. { eapply (cellZ_frame _ _ _ _ _ _ R18); [ulia | ulia |]. intros i Hi. apply AG; [left; do 14 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia | ulia]. }
    split.
    - intros z Hz. rewrite (AG z ltac:(right; do 13 right; exact Hz) ltac:(unfold shmaps, AS_GAPLO, AS_GAPHI in Hz; ulia)). exact (proj1 R19 z Hz).
    - intros NE a Ha. pose proof (bv_unsigned_in_range 64 a) as RA.
      assert (EA : Z_to_bv 64 (bv_unsigned a) = a) by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; exact RA).
      change (bv_modulus 64) with (2 ^ 64) in RA.
      rewrite <- EA. rewrite (AG (bv_unsigned a)); [rewrite EA; exact (proj2 R19 NE a Ha) | | lia].
      left. right. left. (lazymatch goal with |- ?G => let G' := eval unfold instance_cells in G in change_no_check G' end). cbn zeta. do 5 right. left. lia.
  Qed.
End LocalK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ImgZone.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uall := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *.

  Variable i : Z.
  Hypothesis HI : ia_img_lo IA <= i < ia_img_hi IA.

  Lemma img_offs :
    (forall lo hi, In (lo, hi) (bt_fixed bt) -> lo <= i < hi -> False)
    /\ (forall lo hi, In (lo, hi) (dyn_ranges st) -> lo <= i < hi -> False)
    /\ (SBEG <= i -> False) /\ (in_band i -> False).
  Proof using HI W qg qt FF Lc RUN.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
    pose proof (img_lits bt st Lc FF W) as [L1 L2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    split; [intros lo hi Hin Hlo; destruct (fixed_range bt st Lc FF W lo hi Hin) as ((_ & _ & _ & D4 & _) & _); lia|].
    split; [intros lo hi Hin Hlo; destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((_ & _ & _ & D4 & _) & _); lia|].
    split; [intros HS; clear -HS HI L2 B3; ulia | intros HB; unfold in_band in HB; clear -HB HI L2; ulia].
  Qed.

  Theorem img_not_wr : rep_wr bt st Lc FF i -> False.
  Proof using HI W qg qt RUN.
    intros HC. destruct img_offs as (FIXoff & DYNoff & SPACEoff & BANDoff).
    pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PWS & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (img_lits bt st Lc FF W) as [L1 L2].
    unfold rep_wr in HC.
    destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]].
    - exact (FIXoff _ _ IN8 ltac:(clear -K SS3; lia)).
    - exact (FIXoff _ _ INT K).
    - destruct K as (c0 & Hc0 & K). pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
      destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
      apply SPACEoff. unfold reginfo, fa_beg, KFAOFF, KSPACE in *. clear -K Q1 Q7 Q9 R6a Hc0. destruct K as [K|[K|K]]; lia.
    - destruct K as (b & Hb & K). destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & BB1 & BB2). apply SPACEoff. lia.
    - destruct K as (sc & Hs' & K). exact (DYNoff _ _ (sec_dyn st sc Hs') K).
    - destruct K as (p & n & Hin & K).
      destruct (live_ext bt st Lc FF W p n Hin) as (lo & hi & E & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
      pose proof (up8_facts n ltac:(lia)) as (U1 & _). destruct (live_range bt st Lc FF W p n Hin) as (A1 & A2 & A3 & A4).
      destruct K as [K|K].
      + unfold boxed in Y11. lia.
      + apply BANDoff. unfold in_band, sh_lo, sh_hi in *.
        assert (0 <= p / 8) by (apply Z.div_pos; ulia). assert ((p + n + 7) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; ulia). ulia.
    - destruct K as (m & n & Hin & K). destruct (quar_item bt st Lc FF W m n Hin) as (N1 & _).
      destruct (is_primary n) eqn:HP.
      + destruct (quar_chunk bt st Lc FF W m n Hin HP) as (C1 & C2 & _ & C4 & _).
        destruct (carved_range bt st Lc FF W _ _ C1 C2) as (_ & _ & A3 & _). unfold prim_alloc_beg in *. pose proof (rz_range n). apply SPACEoff. lia.
      + destruct (quar_sec bt st Lc FF W m n Hin HP) as (sc & Hsc & Eu & En).
        destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hsc)). unfold sc_user, sec_user_off in Eu. pose proof (rz_range (sc_n sc)). rewrite En in *. clear -K Eu A5 A6 A7 H N1. ulia.
    - destruct K as (b & [<-|Hb] & K); [exact (FIXoff _ _ INN K) | exact (DYNoff _ _ (node_dyn st b Hb) K)].
    - destruct K as (b & [<-|Hb] & K); [exact (FIXoff _ _ INS K) | exact (DYNoff _ _ (store_dyn st b Hb) K)].
    - exact (FIXoff _ _ INFS K).
    - destruct K as (f & k & Hf & K). destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & _ & F4 & _).
      pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & X5 & X6 & _).
      apply BANDoff. unfold in_band, sh_lo, sh_hi in *.
      assert (0 <= f / 8) by (apply Z.div_pos; ulia). assert ((f + FS k + 7) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; ulia). ulia.
    - destruct K as (c0 & Hc0 & K). apply BANDoff. apply (shreg_in_band bt st Lc FF W c0 i Hc0). left. exact K.
    - destruct K as (sc & Hs' & K). apply BANDoff. exact (shsec_in_band bt st Lc FF W sc i Hs' K).
    - apply BANDoff. unfold in_band, shmaps, AS_GAPLO, AS_GAPHI in *. ulia.
  Qed.
End ImgZone.

Lemma u64l : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. (lazymatch goal with |- ?G => let G' := eval unfold bv_modulus in G in change_no_check G' end). lia. Qed.

Section ConstRw.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  #[local] Abbreviation T := (bt_thread bt).
  (* [comment removed for export] *)
  Variable Zn : Z -> Prop.
  Hypothesis HZI : forall i, Zn i -> ia_img_lo IA <= i < ia_img_hi IA.
  Hypothesis HZD : forall i, Zn i -> ~ img_dyn IA i.
  Hypothesis HZT : forall i, Zn i -> ~ (bt_tls_fs bt <= i < bt_tls_fs bt + 16).
  Hypothesis HZR : forall i, Zn i -> ~ rtc_cells bt i.

  Section W.
  Variables (st : ast) (Lc FF : list (Z * Z)).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uall := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *.

  Theorem zone_not_cells_nk : forall i, Zn i -> rep_cells_nk bt st Lc FF i -> False.
  Proof using W qg qt HZR HZT HZD HZI RUN.
    intros i Hz HC. pose proof (HZI i Hz) as HI. pose proof (HZD i Hz) as ND. pose proof (HZT i Hz) as NT. pose proof (HZR i Hz) as NR.
    destruct (img_offs bt st Lc FF W i HI) as (FIXoff & DYNoff & SPACEoff & BANDoff).
    pose proof W as ((WR1 & WR2) & WC & WQ & (SS1 & SS2 & SS3 & _) & WL & WK & WD & WM & (RNG & PWS & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    unfold rep_cells_nk in HC.
    destruct HC as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]]]].
    - exact K.
    - unfold instance_cells in K. cbn zeta in K.
      destruct K as [K|[K|[K|[K|[K|[K|K]]]]]]; try (apply ND; unfold img_dyn, IB in *; lia). exact (FIXoff _ _ IN8 ltac:(clear -K SS1 SS3; lia)).
    - destruct (thread_cells_where bt i K) as [A|A]; [exact (FIXoff _ _ INT ltac:(unfold T_UNW, PG in *; lia)) | exact (FIXoff _ _ INC ltac:(lia))].
    - destruct K as (c0 & Hc0 & K). unfold foot_region in K.
      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _).
      apply SPACEoff. unfold fa_beg, KFAOFF in *. clear -K Q1 Q7 Q9 R6a. destruct K as [[K _]|K]; ulia.
    - destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CVb & BL & BB1 & BB2). apply SPACEoff. lia.
    - destruct K as (sc & Hs' & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      apply (DYNoff _ _ (sec_dyn st sc Hs')). pose proof (rz_range (sc_n sc)). clear -K A5 A6 A7 H. ulia.
    - destruct K as (p & n & Hown & K).
      destruct (hdr_zone bt st Lc FF W p n i Hown K) as [(HP & Hi & S1 & S2 & CV & Hc1 & N1 & S3) | (HP & sc & Hsc & Eu & En & Hi & N1)].
      + apply SPACEoff. lia.
      + destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNoff _ _ (sec_dyn st sc Hsc)). rewrite Eu, En in *. clear -Hi A5 A6 N1. ulia.
    - apply ND. unfold foot_depot_static in K. (lazymatch goal with |- ?G => let G' := eval unfold img_dyn in G in change_no_check G' end). uall. clear -K. lia.
    - destruct K as (id & Hid & K). unfold foot_node in K. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
      pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
      destruct HIn as [Eb | Hnb]; [apply (FIXoff _ _ INN); rewrite Eb; lia | apply (DYNoff _ _ (node_dyn st bb Hnb)); lia].
    - unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
      1-3: apply (FIXoff _ _ INFS); ulia.
      + exact (NT K).
      + apply (FIXoff _ _ (dtls_member bt st Lc FF W)); ulia.
    - destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (A1 & A2 & A3 & A4 & _).
      apply (FIXoff _ _ INFS). ulia.
    - apply ND. unfold ialloc_cells in K. (lazymatch goal with |- ?G => let G' := eval unfold img_dyn in G in change_no_check G' end). uall. clear -K. lia.
    - destruct K as (c0 & Hc0 & K). unfold foot_shreg in K. apply BANDoff. apply (shreg_in_band bt st Lc FF W c0 i Hc0). destruct K as [[K _]|K]; [left; exact K | right; exact K].
    - destruct K as (sc & Hs' & K). unfold foot_shsec in K. destruct K as [K _]. apply BANDoff. exact (shsec_in_band bt st Lc FF W sc i Hs' K).
    - exact (NR K).
  Qed.

  (* [comment removed for export] *)
  Theorem Rep_const_rw : forall M M' mdl, Rep bt st Lc FF M mdl ->
    cells_hold SG M' (bt_consts bt) -> (forall a : word, M' a <> M a -> Zn (bv_unsigned a)) -> Rep bt st Lc FF M' mdl.
  Proof using W qg qt HZR HZT HZD HZI.
    intros M M' mdl R KC' CH. apply (Rep_local_k bt st Lc FF M M' mdl W R KC'). intros i [Hs|Hs] Hr.
    - destruct (decide (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))) as [E|NE]; [exact E | exfalso].
      pose proof (CH _ NE) as Hz. rewrite u64l in Hz by lia. exact (zone_not_cells_nk i Hz Hs).
    - destruct (decide (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))) as [E|NE]; [exact E | exfalso].
      pose proof (CH _ NE) as Hz. rewrite u64l in Hz by lia. exact (img_not_wr bt st Lc FF W i (HZI i Hz) Hs).
  Qed.

  (* [comment removed for export] *)
  Lemma cells_hold_rw : forall M M', cells_hold SG M (bt_consts bt) -> (forall a : word, M' a <> M a -> Zn (bv_unsigned a)) ->
    Forall (fun c : Z * nat * Z => (forall i, fst (fst c) <= i < fst (fst c) + Z.of_nat (snd (fst c)) -> ~ Zn i)
                                   \/ cellZ SG M' (fst (fst c)) (snd (fst c)) (snd c)) (bt_consts bt) ->
    cells_hold SG M' (bt_consts bt).
  Proof using W qg qt FF Lc st RUN.
    intros M M' KC CH RW. pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & YC).
    unfold cells_hold in *. rewrite Forall_forall in *. intros c Hc. destruct (YC c Hc) as [Y1 Y2].
    destruct (RW c Hc) as [AP | RE]; [| exact RE].
    apply (cellZ_frame SG M M' _ _ _ (KC c Hc) Y1 Y2). intros i Hi.
    destruct (decide (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))) as [E|NE]; [exact E | exfalso].
    pose proof (CH _ NE) as Hz. rewrite u64l in Hz by lia. exact (AP i Hi Hz).
  Qed.
  End W.

  (* [comment removed for export] *)
  Theorem AAINVP_const_rw : forall (P : ast -> Prop) Lc FF B C K M M' mdl,
    AAINVP P bt Lc FF B C K M mdl ->
    (forall a : word, M' a <> M a -> Zn (bv_unsigned a)) ->
    Forall (fun c : Z * nat * Z => (forall i, fst (fst c) <= i < fst (fst c) + Z.of_nat (snd (fst c)) -> ~ Zn i)
                                   \/ cellZ SG M' (fst (fst c)) (snd (fst c)) (snd c)) (bt_consts bt) ->
    AAINVP P bt Lc FF B C K M' mdl.
  Proof using HZR HZT HZD HZI.
    intros P Lc FF B C K M M' mdl (st & W & R & BP & MW) CH RW. exists st. split; [exact W|]. split; [| split; [exact BP | exact MW]].
    pose proof R as (KC & _).
    exact (Rep_const_rw st Lc FF W M M' mdl R (cells_hold_rw st Lc FF W M M' KC CH RW) CH).
  Qed.
End ConstRw.
