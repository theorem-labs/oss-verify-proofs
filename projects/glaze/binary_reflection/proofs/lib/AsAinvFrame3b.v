(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section Geom2.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.

  (* [comment removed for export] *)
  Lemma bt_ok_W : bt_ok bt.
  Proof using W qg qt FF Lc st RUN. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BT & _). exact BT. Qed.


  Lemma img_lits : 0 <= ia_img_lo IA /\ ia_img_hi IA <= AS_LO.
  Proof using W qg qt FF Lc st RUN. pose proof bt_ok_W as (I1 & I2 & _). split; assumption. Qed.

  Lemma priv_cover_wins : forall lo hi a, priv_cover IA lo hi -> lo <= a < hi ->
    in_wins (ia_priv IA) a /\ ia_img_lo IA <= a < ia_img_hi IA.
  Proof using W qg qt FF Lc st RUN.
    intros lo hi a (plo & phi & Hin & H1 & H2) Ha. pose proof bt_ok_W as (I1 & I2 & PR & _). destruct (PR plo phi (or_introl Hin)).
    split; [exists plo, phi; split; [exact Hin | ulia] | ulia].
  Qed.
  Lemma const_cover_wins : forall lo hi a, const_cover IA lo hi -> lo <= a < hi ->
    in_wins (ia_const IA) a /\ ia_img_lo IA <= a < ia_img_hi IA.
  Proof using W qg qt FF Lc st RUN.
    intros lo hi a (plo & phi & Hin & H1 & H2) Ha. pose proof bt_ok_W as (I1 & I2 & PR & _). destruct (PR plo phi (or_intror Hin)).
    split; [exists plo, phi; split; [exact Hin | ulia] | ulia].
  Qed.

  (* [comment removed for export] *)
  Definition img_kind (a : Z) : Prop :=
    ia_img_lo IA <= a < ia_img_hi IA /\ (in_wins (ia_priv IA) a \/ in_rtc IA a \/ in_wins (ia_const IA) a).

  Lemma img_kinds : forall a,
    consts_cells bt a \/ (instance_cells bt st a /\ ~ (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st))))
    \/ foot_depot_static bt a \/ (bt_tls_fs bt <= a < bt_tls_fs bt + 16) \/ ialloc_cells bt a \/ rtc_cells bt a ->
    img_kind a.
  Proof using W qg qt FF Lc RUN.
    intros a H. pose proof bt_ok_W as (I1 & I2 & PR & C1 & C2 & C3 & C4 & C5 & C6 & CC & R1 & R2 & R3 & R4 & DC & DT & DR & DJ).
    (lazymatch goal with |- ?G => let G' := eval unfold img_kind in G in change_no_check G' end).
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    - destruct H as (c & Hc & Ha). rewrite Forall_forall in CC. destruct (CC c Hc) as [CV | CV].
      + destruct (priv_cover_wins _ _ a CV Ha). split; [ulia | left; assumption].
      + destruct (const_cover_wins _ _ a CV Ha). split; [ulia | right; right; assumption].
    - destruct H as [H NP]. unfold instance_cells, IB in H.
      assert (Ha : ia_instance IA + 112 <= a < ia_instance IA + 985) by ulia.
      destruct (priv_cover_wins _ _ a C1 Ha). split; [ulia | left; assumption].
    - unfold foot_depot_static, DEPOT_NIDS, DEPOT_MAP1, DEPOT_TAB, SSOBJ in H.
      destruct H as [H | [H | [H | [H | H]]]].
      1-3: destruct (priv_cover_wins _ _ a C2 ltac:(ulia)); split; [ulia | left; assumption].
      1-2: destruct (priv_cover_wins _ _ a C3 ltac:(ulia)); split; [ulia | left; assumption].
    - destruct (priv_cover_wins _ _ a C6 H). split; [ulia | left; assumption].
    - unfold ialloc_cells, IA_FLAG, IA_INST in H. destruct H as [H | [H | H]].
      1: destruct (priv_cover_wins _ _ a C4 ltac:(ulia)); split; [ulia | left; assumption].
      1-2: destruct (priv_cover_wins _ _ a C5 ltac:(ulia)); split; [ulia | left; assumption].
    - unfold rtc_cells in H. split; [ulia | right; left; exact H].
  Qed.

  (* [comment removed for export] *)
  Definition dyn_kind (a : Z) : Prop := exists lo hi, In (lo, hi) (all_ranges bt st) /\ lo <= a < hi.

  Lemma dyn_kind_facts : forall a, dyn_kind a ->
    0 < a /\ a < CEIL /\ ~ (ia_img_lo IA <= a < ia_img_hi IA) /\ ~ in_band a.
  Proof using W qg qt FF Lc.
    intros a (lo & hi & Hin & Ha). pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
    destruct (RNG lo hi Hin) as ((D1 & D2 & D3 & D4 & D5) & _). (lazymatch goal with |- ?G => let G' := eval unfold in_band in G in change_no_check G' end). ulia.
  Qed.

  Lemma dyn_kind_fixed : forall lo hi a, In (lo, hi) (bt_fixed bt) -> lo <= a < hi -> dyn_kind a.
  Proof using. intros lo hi a Hin Ha. exists lo, hi. split; [apply all_ranges_fixed; exact Hin | exact Ha]. Qed.
  Lemma dyn_kind_dyn : forall lo hi a, In (lo, hi) (dyn_ranges st) -> lo <= a < hi -> dyn_kind a.
  Proof using. intros lo hi a Hin Ha. exists lo, hi. split; [apply all_ranges_dyn; exact Hin | exact Ha]. Qed.
  (* [comment removed for export] *)
  Lemma dyn_kind_space : forall a, SBEG <= a < SBEG + KSPACE + PG -> dyn_kind a.
  Proof using W qg qt FF Lc RUN.
    intros a Ha. pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & IN6 & R6a & R6b & _) & _).
    apply (dyn_kind_fixed _ _ a IN6). ulia.
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_zone : forall p n i, In (p, n) Lc \/ In (p - 16, n) (quar st) -> foot_hdr p n i ->
    (is_primary n = true /\ prim_alloc_beg p n <= i < p /\ SBEG <= prim_alloc_beg p n /\ p + n <= prim_alloc_beg p n + csize (blk_class n)
       /\ carved bt st (blk_class n) (prim_alloc_beg p n) /\ 1 <= blk_class n <= 30 /\ 1 <= n
       /\ prim_alloc_beg p n + csize (blk_class n) <= SBEG + KSPACE)
    \/ (is_primary n = false /\ exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n /\ sc_map sc + PG <= i < p /\ 1 <= n).
  Proof using W qg qt FF RUN.
    intros p n i Hown Hf. pose proof (rz_range n) as RZ. unfold foot_hdr in Hf.
    assert (N1 : 1 <= n).
    { destruct Hown as [HL | HQ]; [destruct (live_range bt st Lc FF W p n HL); ulia | destruct (quar_item_range bt st Lc FF W (p - 16) n HQ); ulia]. }
    destruct (is_primary n) eqn:HP.
    - left. split; [reflexivity|].
      assert (K : 1 <= blk_class n <= 30 /\ carved bt st (blk_class n) (prim_alloc_beg p n) /\ p + n <= prim_alloc_beg p n + csize (blk_class n)).
      { destruct Hown as [HL | HQ].
        - pose proof (live_chunk bt st Lc FF W p n HL HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6). repeat split; assumption || ulia.
        - pose proof (quar_chunk bt st Lc FF W (p - 16) n HQ HP) as G. cbn zeta in G. replace (p - 16 + 16) with p in G by ulia.
          destruct G as (G1 & G2 & G3 & G4 & G5 & G6). repeat split; assumption || ulia. }
      destruct K as (K1 & K2 & K3). destruct (carved_range bt st Lc FF W _ _ K1 K2) as (C1 & C2 & C3 & C4 & C5).
      unfold prim_alloc_beg in *. repeat split; try assumption; ulia.
    - right. split; [reflexivity|].
      assert (K : exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n).
      { destruct Hown as [HL | HQ]; [exact (live_sec bt st Lc FF W p n HL HP)|].
        destruct (quar_sec bt st Lc FF W (p - 16) n HQ HP) as (sc & A & B & C). exists sc. repeat split; assumption || ulia. }
      destruct K as (sc & Hs & Eu & En). exists sc. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      rewrite En in A8. repeat split; try assumption; ulia.
  Qed.



  (* [comment removed for export] *)
  Lemma rep_cells_zone : forall a, rep_cells bt st Lc FF a ->
    img_kind a
    \/ dyn_kind a
    \/ ((SB <= a < SB + CEIL / 8)
        /\ ((exists c, 1 <= c <= 30 /\ foot_shreg bt st Lc c a) \/ (exists sc, In sc (a_sec st) /\ foot_shsec st sc a))).
  Proof using W qg qt.
    intros a RC.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN6)) as ((Z1 & _ & Z3 & _ & _) & _).
    destruct RC as [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | K]]]]]]]]]]]]]].
    - left. exact (img_kinds a ltac:(left; exact K)).
    - destruct (decide (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
      + right; left. pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _). apply (dyn_kind_fixed _ _ a IN8). ulia.
      + left. apply img_kinds. right; left. split; [exact K | exact NI].
    - right; left. unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K.
      destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; first [apply (dyn_kind_fixed _ _ a INT); (first [clear - K | idtac]; ulia) | apply (dyn_kind_fixed _ _ a INC); (first [clear - K | idtac]; ulia)].
    - right; left. destruct K as (c & Hc & K). pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
      destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _). unfold foot_region in K. apply dyn_kind_space. ulia.
    - right; left. destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CV & BL & B1 & B2).
      apply dyn_kind_space. ulia.
    - right; left. destruct K as (sc & Hs & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      apply (dyn_kind_dyn _ _ a (sec_dyn st sc Hs)). ulia.
    - right; left. destruct K as (p' & n' & Hown & K). pose proof (rz_range n') as RZ'.
      destruct (hdr_zone p' n' a Hown K) as [(HP' & Z1' & Z2 & Z3' & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1' & N1')];
        [apply dyn_kind_space; ulia|].
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). apply (dyn_kind_dyn _ _ a (sec_dyn st sc' Hs')). ulia.
    - left. exact (img_kinds a ltac:(right; right; left; exact K)).
    - right; left. destruct K as (id & Hid & K). unfold foot_node in K.
      destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3).
      pose proof (node_addr_block bt st id Hid) as Hb.
      set (b := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody b. destruct HIn as [Eb | Hnb].
      + apply (dyn_kind_fixed _ _ a INN). rewrite Eb. ulia.
      + apply (dyn_kind_dyn _ _ a (node_dyn st b Hnb)). ulia.
    - unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
      1-3: right; left; apply (dyn_kind_fixed _ _ a INFS); ulia.
      + left. exact (img_kinds a ltac:(do 3 right; left; exact K)).
      + right; left. apply (dyn_kind_fixed _ _ a (dtls_member bt st Lc FF W)). ulia.
    - right; left. destruct K as (f & k & Hf & K). unfold foot_fword in K. destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _).
      apply (dyn_kind_fixed _ _ a INFS). ulia.
    - left. exact (img_kinds a ltac:(do 4 right; left; exact K)).
    - right; right. split; [| left; exact K]. destruct K as (c & Hc & K). unfold foot_shreg, sh_lo in K.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). ulia.
    - right; right. split; [| right; exact K]. destruct K as (sc & Hs & K). unfold foot_shsec, sh_lo in K.
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). ulia.
    - left. exact (img_kinds a ltac:(do 5 right; exact K)).
  Qed.

  Lemma hi_vs_rep : forall a, CEIL <= a -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt.
    intros a Ha RC. pose proof img_lits as [I1 I2].
    destruct (rep_cells_zone a RC) as [[Z1 _] | [D | [Z1 _]]]; [ulia | destruct (dyn_kind_facts a D); ulia | ulia].
  Qed.

  Lemma ssh_vs_rep : forall a, in_stack_shadow a -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt.
    intros a Ha RC. unfold in_stack_shadow, sh_lo in Ha. pose proof img_lits as [I1 I2].
    destruct (rep_cells_zone a RC) as [[Z1 _] | [D | [Z1 _]]]; [ulia | | ulia].
    destruct (dyn_kind_facts a D) as (D1 & D2 & D3 & D4). unfold in_band in D4. ulia.
  Qed.

  Lemma ish_vs_rep : forall a, in_image_shadow IA a -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt RUN.
    intros a Ha RC. unfold in_image_shadow, sh_lo, sh_hi in Ha. pose proof img_lits as [I1 I2].
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & _) & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN6)) as ((Z61 & _ & Z63 & Z64 & _) & _ & Z66 & _).
    destruct (rep_cells_zone a RC) as [[Z1 _] | [D | [Z1 [K|K]]]]; [ulia | destruct (dyn_kind_facts a D) as (D1 & D2 & D3 & D4); unfold in_band in D4; ulia | |].
    - destruct K as (c & Hc & K). unfold foot_shreg, sh_lo in K.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _).
      unfold PG in Z66. ulia.
    - destruct K as (sc & Hs & K). unfold foot_shsec, sh_lo in K. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & _).
      pose proof (RNG _ _ (all_ranges_dyn bt st _ (sec_dyn st sc Hs))) as ((E1 & _ & E3 & E4 & _) & _ & E6 & _). unfold PG in E6, A3. ulia.
  Qed.

  Lemma win_vs_rep : forall Wn a, as_wins_ok IA Wn -> in_wins Wn a -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt RUN.
    intros Wn a WOK Ha RC. destruct (WOK a Ha) as (R1 & R2 & R3 & R4). pose proof img_lits as [I1 I2].
    destruct (rep_cells_zone a RC) as [[Z1 [Z2|[Z2|Z2]]] | [D | [Z1 _]]];
      [exact (R2 Z2) | exact (R3 Z2) | exact (R4 Z2) | destruct (dyn_kind_facts a D); ulia | ulia].
  Qed.

  Lemma pg8 : forall x, x mod PG = 0 -> x mod 8 = 0.
  Proof using RUN. intros x H. unfold PG in H. ulia. Qed.

  (* [comment removed for export] *)
  Lemma blk_vs_rep : forall p n a, In (p, n) Lc -> p <= a < p + n -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt RUN.
    intros p n a Hin Ha RC.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    destruct (live_range bt st Lc FF W p n Hin) as (L1 & L2 & L3 & L4).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & _).
    (* [comment removed for export] *)
    assert (LOC : (is_primary n = true /\ SBEG <= p /\ p + n <= SBEG + KSPACE)
                  \/ (is_primary n = false /\ exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n
                                               /\ sc_map sc + PG + 16 <= p /\ p + n <= sc_map sc + sc_mapsz sc)).
    { destruct (is_primary n) eqn:HP.
      - left. pose proof (prim_block_in_space bt st Lc FF p n W Hin HP). pose proof (rz_range n). repeat split; ulia.
      - right. split; [reflexivity|]. destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En). exists sc.
        destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). rewrite Eu, En in *. repeat split; assumption || ulia. }
    (* [comment removed for export] *)
    assert (FIX : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> lo <= a < hi -> False).
    { intros lo hi Hf Hlen Hr. destruct LOC as [(HP & S1 & S2) | (HP & sc & Hs & Eu & En & S1 & S2)].
      - destruct (space_vs_fixed bt st Lc FF W lo hi Hf Hlen); ulia.
      - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hf (sec_dyn st sc Hs)) as D. hnf in D. cbn in D. ulia. }
    assert (SPC : is_primary n = false -> SBEG <= a < SBEG + KSPACE + PG -> False).
    { intros HP Hr. destruct LOC as [(HP' & _) | (_ & sc & Hs & Eu & En & S1 & S2)]; [rewrite HP in HP'; discriminate HP'|].
      destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)); ulia. }
    (* [comment removed for export] *)
    assert (DK : dyn_kind a).
    { destruct LOC as [(HP & S1 & S2) | (HP & sc & Hs & Eu & En & S1 & S2)].
      - apply dyn_kind_space. ulia.
      - apply (dyn_kind_dyn _ _ a (sec_dyn st sc Hs)). ulia. }
    destruct (dyn_kind_facts a DK) as (O1 & O2 & O3 & O4). unfold in_band in O4. pose proof img_lits as [I1 I2].
    destruct RC as [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | K]]]]]]]]]]]]]].
    - (* [comment removed for export] *) destruct (img_kinds a ltac:(left; exact K)) as [B _]. ulia.
    - (* [comment removed for export] *) destruct (decide (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
      + pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _). apply (FIX _ _ IN8); ulia.
      + destruct (img_kinds a ltac:(right; left; split; [exact K | exact NI])) as [B _]. ulia.
    - (* [comment removed for export] *) unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K.
      destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; first [apply (FIX _ _ INT); (first [clear - K | idtac]; ulia) | apply (FIX _ _ INC); (first [clear - K | idtac]; ulia)].
    - (* [comment removed for export] *) destruct K as (c & Hc & K). pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
      destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _). unfold foot_region in K.
      destruct LOC as [(HP & S1 & S2) | (HP & _)]; [| apply (SPC HP); ulia].
      pose proof (live_chunk bt st Lc FF W p n Hin HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
      destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5).
      pose proof (region_facts bt st Lc FF W _ G1) as RF. cbn zeta in RF. destruct RF as (P1 & P2 & P3 & P4 & P5 & _).
      destruct K as [[K _] | K]; [ulia|].
      (* [comment removed for export] *)
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy (blk_class n) c) as [LT|[EQ|GT]].
      + assert (blk_class n * 2 ^ 32 + 2 ^ 32 <= c * 2 ^ 32).
        { replace (blk_class n * 2 ^ 32 + 2 ^ 32) with ((blk_class n + 1) * 2 ^ 32) by ulia. apply Z.mul_le_mono_nonneg_r; ulia. }
        ulia.
      + subst c. ulia.
      + assert (c * 2 ^ 32 + 2 ^ 32 <= blk_class n * 2 ^ 32).
        { replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by ulia. apply Z.mul_le_mono_nonneg_r; ulia. }
        ulia.
    - (* [comment removed for export] *) destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CV & BL & B1 & B2).
      destruct LOC as [(HP & S1 & S2) | (HP & _)]; [| apply (SPC HP); ulia].
      pose proof (live_chunk bt st Lc FF W p n Hin HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
      destruct (chunk_cases bt st Lc FF W (blk_class n) (prim_alloc_beg p n) BATCHCLASS (ba_addr b) G1 ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); ulia) G2 CV) as [[EC EA] | D].
      + (* [comment removed for export] *)
        destruct W as ((WR & _) & _). destruct (WR BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); ulia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK).
        destruct PART as (_ & _ & _ & _ & _ & _ & _ & NB & _).
        apply (NB (ba_addr b) ltac:(exists b; split; [exact Hb | reflexivity]) eq_refl). left. rewrite <- EC, <- EA. exact G3.
      + change (csize BATCHCLASS) with 8192 in D. ulia.
    - (* [comment removed for export] *) destruct K as (sc' & Hs' & K). unfold foot_sec in K.
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      destruct LOC as [(HP & S1 & S2) | (HP & sc & Hs & Eu & En & S1 & S2)].
      + destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc' Hs')); ulia.
      + destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; ulia.
    - (* [comment removed for export] *) destruct K as (p' & n' & Hown & K).
      pose proof (rz_range n') as RZ'. pose proof (rz_range n) as RZ.
      destruct (hdr_zone p' n' a Hown K) as [(HP' & Z1 & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1 & N1')].
      + (* [comment removed for export] *)
        destruct LOC as [(HP & S1 & S2) | (HP & _)]; [| apply (SPC HP); ulia].
        pose proof (live_chunk bt st Lc FF W p n Hin HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
        destruct (chunk_cases bt st Lc FF W (blk_class n) (prim_alloc_beg p n) (blk_class n') (prim_alloc_beg p' n') G1 HC' G2 CV') as [[EC EA] | D]; [| unfold prim_alloc_beg in *; ulia].
        (* [comment removed for export] *)
        destruct Hown as [HL' | HQ'].
        * (* [comment removed for export] *)
          pose proof (rz_unif n n' ltac:(ulia) N1' HP HP' EC) as ER. unfold prim_alloc_beg in EA.
          assert (EP : p = p') by ulia. subst p'.
          destruct (Z.eq_dec n n') as [<- | NE].
          -- unfold foot_hdr in K. ulia.
          -- destruct W as (_ & _ & _ & _ & (_ & _ & SEP) & _). destruct (SEP p n p n' Hin HL' ltac:(intros E; injection E; ulia)); ulia.
        * (* [comment removed for export] *)
          pose proof (quar_chunk bt st Lc FF W (p' - 16) n' HQ' HP') as G'. cbn zeta in G'. replace (p' - 16 + 16) with p' in G' by ulia.
          destruct G' as (_ & _ & Q3 & _).
          destruct W as ((WR & _) & _). destruct (WR _ G1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PART & FHK). destruct PART as (_ & LQ & _).
          apply (LQ (prim_alloc_beg p n)). split; [exact G3|]. rewrite EC, EA. exact Q3.
      + (* [comment removed for export] *)
        destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        destruct LOC as [(HP & S1 & S2) | (HP & sc & Hs & Eu & En & S1 & S2)].
        * destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc' Hs')); ulia.
        * destruct (sec_cases bt st Lc FF W sc sc' Hs Hs') as [<- | D]; [| ulia].
          (* [comment removed for export] *)
          assert (p' = p /\ n' = n) as [-> ->] by (split; congruence).
          destruct Hown as [HL' | HQ']; [unfold foot_hdr in K; ulia|].
          apply (sec_live_not_quar bt st Lc FF W sc Hs); rewrite Eu, En; [exact Hin | exact HQ'].
    - (* [comment removed for export] *) destruct (img_kinds a ltac:(right; right; left; exact K)) as [B _]. ulia.
    - (* [comment removed for export] *) destruct K as (id & Hid & K). unfold foot_node in K.
      destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3).
      pose proof (node_addr_block bt st id Hid) as Hb.
      set (b := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *.
      clearbody b. destruct HIn as [Eb | Hnb].
      + apply (FIX _ _ INN); [ulia|]. rewrite Eb. ulia.
      + destruct LOC as [(HP & S1 & S2) | (HP & sc & Hs & Eu & En & S1 & S2)].
        * destruct (space_vs_dyn bt st Lc FF W _ _ (node_dyn st b Hnb)); ulia.
        * destruct (sec_vs_node bt st Lc FF W sc b Hs Hnb) as [D|D]; clear - S1 S2 Ha Hb K D; ulia.
    - (* [comment removed for export] *) unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]].
      1-3: apply (FIX _ _ INFS); (first [clear - K | idtac]; ulia).
      + destruct (img_kinds a ltac:(do 3 right; left; exact K)) as [B _]. ulia.
      + apply (FIX _ _ (dtls_member bt st Lc FF W)); ulia.
    - (* [comment removed for export] *) destruct K as (f & k & Hf & K). unfold foot_fword in K.
      destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & _). apply (FIX _ _ INFS); ulia.
    - (* [comment removed for export] *) destruct (img_kinds a ltac:(do 4 right; left; exact K)) as [B _]. ulia.
    - (* [comment removed for export] *) destruct K as (c & Hc & K). unfold foot_shreg, sh_lo in K.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). ulia.
    - (* [comment removed for export] *) destruct K as (sc & Hs & K). unfold foot_shsec, sh_lo in K.
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). ulia.
    - (* [comment removed for export] *) destruct (img_kinds a ltac:(do 5 right; exact K)) as [B _]. ulia.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_vs_rep : forall f k a, In (f, k) FF -> f <= a < f + FS k - 8 -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt RUN.
    intros f k a Hf Ha RC.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). clear F3.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & _).
    assert (FIX : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> FAKE_SIZE -> lo <= a < hi -> False).
    { intros lo hi Hin Hlen Hr. destruct (fs_vs_fixed bt st Lc FF W lo hi Hin Hlen); ulia. }
    assert (DYN : forall lo hi, In (lo, hi) (dyn_ranges st) -> lo <= a < hi -> False).
    { intros lo hi Hin Hr. destruct (fs_vs_dyn bt st Lc FF W lo hi Hin); ulia. }
    assert (SPC : SBEG <= a < SBEG + KSPACE + PG -> False).
    { intros Hr. destruct (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); ulia)); ulia. }
    destruct (dyn_kind_facts a (dyn_kind_fixed _ _ a INFS ltac:(ulia))) as (O1 & O2 & O3 & O4). unfold in_band in O4. pose proof img_lits as [I1 I2].
    destruct (rep_cells_zone a RC) as [[Z1 _] | [Z1 | [Z1 _]]]; [ulia | | ulia].
    destruct RC as [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | [K | K]]]]]]]]]]]]]].
    - destruct (img_kinds a ltac:(left; exact K)) as [B _]. ulia.
    - destruct (decide (bt_ptrarr bt <= a < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
      + pose proof W as (_ & _ & _ & (S1 & S2 & S3 & _) & _). apply (FIX _ _ IN8); ulia.
      + destruct (img_kinds a ltac:(right; left; split; [exact K | exact NI])) as [B _]. ulia.
    - unfold thread_cells, T_QC, T_PC, PC_SZ, T_UNW in K.
      destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; first [apply (FIX _ _ INT); (first [clear - K | idtac]; ulia) | apply (FIX _ _ INC); (first [clear - K | idtac]; ulia)].
    - destruct K as (c & Hc & K). pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
      destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & _). unfold foot_region in K. apply SPC. ulia.
    - destruct K as (b & Hb & K). unfold foot_batch in K. destruct (batch_facts bt st Lc FF W b Hb) as (CV & BL & B1 & B2). apply SPC. ulia.
    - destruct K as (sc & Hs & K). unfold foot_sec in K. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      apply (DYN _ _ (sec_dyn st sc Hs)). ulia.
    - destruct K as (p' & n' & Hown & K). pose proof (rz_range n') as RZ'.
      destruct (hdr_zone p' n' a Hown K) as [(HP' & Z1' & Z2 & Z3 & CV' & HC' & N1' & Z4) | (HP' & sc' & Hs' & Eu' & En' & Z1' & N1')]; [apply SPC; ulia|].
      destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). apply (DYN _ _ (sec_dyn st sc' Hs')). ulia.
    - destruct (img_kinds a ltac:(right; right; left; exact K)) as [B _]. ulia.
    - destruct K as (id & Hid & K). unfold foot_node in K.
      destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3).
      pose proof (node_addr_block bt st id Hid) as Hb.
      set (b := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *.
      clearbody b. destruct HIn as [Eb | Hnb].
      + apply (FIX _ _ INN); [ulia|]. rewrite Eb. ulia.
      + apply (DYN _ _ (node_dyn st b Hnb)). ulia.
    - unfold foot_fake_static in K. destruct K as [K|[K|[K|[K|K]]]]; [ulia | ulia | ulia | |].
      + destruct (img_kinds a ltac:(do 3 right; left; exact K)) as [B _]. ulia.
      + apply (FIX _ _ (dtls_member bt st Lc FF W)); ulia.
    - destruct K as (f' & k' & Hf' & K). unfold foot_fword in K.
      destruct (fake_frame_facts bt st Lc FF W f' k' Hf') as (G1 & G2 & G3 & G4 & G5 & G6 & G7). clear G3.
      destruct (decide ((k, fpos bt f k) = (k', fpos bt f' k'))) as [E | NE].
      + injection E as E1 E2. assert (f = f') by (rewrite F7, G7, <- E2, <- E1; reflexivity). subst f'. subst k'. clear - Ha K F4. ulia.
      + pose proof (frames_apart (bt_fs bt) k (fpos bt f k) k' (fpos bt f' k') X7 F5 F6 G5 G6 NE) as D.
        rewrite <- F7, <- G7 in D. clear - Ha K D F4 G4. ulia.
    - destruct (img_kinds a ltac:(do 4 right; left; exact K)) as [B _]. ulia.
    - destruct K as (c & Hc & K). unfold foot_shreg, sh_lo in K.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _). ulia.
    - destruct K as (sc & Hs & K). unfold foot_shsec, sh_lo in K. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _). ulia.
    - destruct (img_kinds a ltac:(do 5 right; exact K)) as [B _]. ulia.
  Qed.


  (* [comment removed for export] *)
  Lemma bsh_vs_rep : forall p n a, In (p, n) Lc -> sh_lo p <= a < sh_hi p n -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt RUN.
    intros p n a Hin Ha RC. unfold sh_lo, sh_hi in Ha.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    destruct (live_range bt st Lc FF W p n Hin) as (L1 & L2 & L3 & L4).
    assert (LOC : (is_primary n = true /\ SBEG <= p /\ p + n <= fa_beg SBEG (blk_class n) /\ 1 <= blk_class n <= 30
                     /\ region_beg SBEG (blk_class n) <= p)
                  \/ (is_primary n = false /\ exists sc, In sc (a_sec st) /\ sc_user sc = p /\ sc_n sc = n
                                               /\ sc_map sc + PG + 16 <= p /\ p + n <= sc_map sc + sc_mapsz sc)).
    { destruct (is_primary n) eqn:HP.
      - left. pose proof (live_chunk bt st Lc FF W p n Hin HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
        destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5).
        pose proof (region_facts bt st Lc FF W _ G1) as RF. cbn zeta in RF. destruct RF as (P1 & P2 & P3 & P4 & _).
        split; [reflexivity|]. clear - G1 G4 G5 G6 C1 C2 C3 C4 P1 P2 P3 P4. unfold prim_alloc_beg in *. repeat split; ulia.
      - right. split; [reflexivity|]. destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En). exists sc.
        destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). rewrite Eu, En in *. repeat split; assumption || ulia. }
    pose proof img_lits as [I1 I2].
    destruct (rep_cells_zone a RC) as [[Z1 _] | [Z1 | [Z1 [K | K]]]];
      [ulia | destruct (dyn_kind_facts a Z1) as (O1 & O2 & O3 & O4); unfold in_band in O4; ulia | |].
    - (* [comment removed for export] *) destruct K as (c & Hc & K). unfold foot_shreg, sh_lo in K.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
      destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
      destruct K as [[K NL] | K].
      + apply NL. exists p, n. split; [exact Hin|]. (lazymatch goal with |- ?G => let G' := eval unfold user_granule in G in change_no_check G' end). ulia.
      + pose proof (pg8 _ Q12) as AL.
        destruct LOC as [(HP & S1 & S2 & HC & S3) | (HP & sc & Hs & Eu & En & S1 & S2)].
        * pose proof (region_facts bt st Lc FF W _ HC) as RF. cbn zeta in RF. destruct RF as (P1 & P2 & P3 & P4 & P5 & _).
          apply (gran_sep (fa_beg SBEG c) (fa_beg SBEG c + r_mapped_fa (a_reg st c)) p n (a - SB)); [| (first [clear - Ha | idtac]; ulia) | (first [clear - K | idtac]; ulia)].
          unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
          destruct (Z.le_gt_cases (blk_class n) c) as [LE|GT].
          -- left. split; [| exact AL]. assert (blk_class n * 2 ^ 32 <= c * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; (first [clear - Q6 K S3 Ha | idtac]; ulia)). ulia.
          -- right. assert (c * 2 ^ 32 + 2 ^ 32 <= blk_class n * 2 ^ 32).
             { replace (c * 2 ^ 32 + 2 ^ 32) with ((c + 1) * 2 ^ 32) by ulia. apply Z.mul_le_mono_nonneg_r; (first [clear - K S2 X16 Ha | idtac]; ulia). }
             ulia.
        * apply (gran_sep (fa_beg SBEG c) (fa_beg SBEG c + r_mapped_fa (a_reg st c)) p n (a - SB)); [| (first [clear - Ha | idtac]; ulia) | (first [clear - K | idtac]; ulia)].
          destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [D|D]; [left; split; [(first [clear - D Q4 Q3 Q2 Q1 S2 | idtac]; ulia) | exact AL] | right; (first [clear - D Q6 Q5 S1 | idtac]; ulia)].
    - (* [comment removed for export] *) destruct K as (sc & Hs & K). unfold foot_shsec, sh_lo in K. destruct K as [K ALT].
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof (pg8 _ A3) as AL.
      destruct LOC as [(HP & S1 & S2 & HC & S3) | (HP & s & Hs' & Eu & En & S1 & S2)].
      + pose proof (region_facts bt st Lc FF W _ HC) as RF. cbn zeta in RF. destruct RF as (P1 & P2 & P3 & P4 & P5 & _).
        apply (gran_sep (sc_map sc) (sc_map sc + sc_mapsz sc) p n (a - SB)); [| ulia | ulia].
        destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [D|D]; [right; ulia | left; split; [ulia | exact AL]].
      + destruct (sec_cases bt st Lc FF W s sc Hs' Hs) as [<- | D].
        * destruct ALT as [NU | HQ].
          -- apply NU. (lazymatch goal with |- ?G => let G' := eval unfold user_granule in G in change_no_check G' end). rewrite Eu, En. ulia.
          -- apply (sec_live_not_quar bt st Lc FF W s Hs'); [rewrite Eu, En; exact Hin | exact HQ].
        * destruct (sec_facts bt st Lc FF W s Hs') as (B1 & B2 & _).
          apply (gran_sep (sc_map sc) (sc_map sc + sc_mapsz sc) p n (a - SB)); [| ulia | ulia].
          destruct D as [D|D]; [left; split; [ulia | exact AL] | right; ulia].
  Qed.

  (* [comment removed for export] *)
  Lemma fsh_vs_rep : forall f k a, In (f, k) FF -> sh_lo f <= a < sh_hi f (FS k) -> rep_cells bt st Lc FF a -> False.
  Proof using W qg qt RUN.
    intros f k a Hf Ha RC. unfold sh_lo, sh_hi in Ha.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). clear F3.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & _) & _).
    pose proof img_lits as [I1 I2].
    destruct (rep_cells_zone a RC) as [[Z1 _] | [Z1 | [Z1 [K | K]]]];
      [ulia | destruct (dyn_kind_facts a Z1) as (O1 & O2 & O3 & O4); unfold in_band in O4; ulia | |].
    - destruct K as (c & Hc & K). unfold foot_shreg, sh_lo in K.
      pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
      destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
      pose proof (pg8 _ Q11) as AL1. pose proof (pg8 _ Q12) as AL2.
      destruct (space_vs_fixed bt st Lc FF W _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); ulia)) as [D|D].
      + destruct K as [[K _] | K].
        * apply (gran_sep (region_beg SBEG c) (region_beg SBEG c + r_mapped_user (a_reg st c)) f (FS k) (a - SB)); [left; split; [(first [clear - D Q1 F2 | idtac]; ulia) | exact AL1] | (first [clear - Ha | idtac]; ulia) | (first [clear - K | idtac]; ulia)].
        * apply (gran_sep (fa_beg SBEG c) (fa_beg SBEG c + r_mapped_fa (a_reg st c)) f (FS k) (a - SB)); [left; split; [(first [clear - D Q4 Q3 Q2 Q1 F2 | idtac]; ulia) | exact AL2] | (first [clear - Ha | idtac]; ulia) | (first [clear - K | idtac]; ulia)].
      + destruct K as [[K _] | K].
        * apply (gran_sep (region_beg SBEG c) (region_beg SBEG c + r_mapped_user (a_reg st c)) f (FS k) (a - SB)); [right; (first [clear - D Q5 Q2 F1 | idtac]; ulia) | (first [clear - Ha | idtac]; ulia) | (first [clear - K | idtac]; ulia)].
        * apply (gran_sep (fa_beg SBEG c) (fa_beg SBEG c + r_mapped_fa (a_reg st c)) f (FS k) (a - SB)); [right; (first [clear - D Q6 Q5 F1 | idtac]; ulia) | (first [clear - Ha | idtac]; ulia) | (first [clear - K | idtac]; ulia)].
    - destruct K as (sc & Hs & K). unfold foot_shsec, sh_lo in K. destruct K as [K ALT].
      destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof (pg8 _ A3) as AL.
      apply (gran_sep (sc_map sc) (sc_map sc + sc_mapsz sc) f (FS k) (a - SB)); [| (first [clear - Ha | idtac]; ulia) | (first [clear - K | idtac]; ulia)].
      destruct (fs_vs_dyn bt st Lc FF W _ _ (sec_dyn st sc Hs)) as [D|D]; [right; (first [clear - D F1 | idtac]; ulia) | left; split; [(first [clear - D F2 | idtac]; ulia) | exact AL]].
  Qed.

  (* [comment removed for export] *)
  Theorem app_owned_not_rep : forall Wn a, as_wins_ok IA Wn -> as_app_owned IA Wn Lc FF a -> ~ rep_cells bt st Lc FF a.
  Proof using W qg qt.
    intros Wn a WOK H RC.
    destruct H as [(p & n & Hin & Ha) | [(f & k & Hf & Ha) | [H | [H | [(p & n & Hin & Ha) | [(f & k & Hf & Ha) | [H | H]]]]]]].
    - exact (blk_vs_rep p n a Hin Ha RC).
    - exact (frame_vs_rep f k a Hf Ha RC).
    - exact (hi_vs_rep a H RC).
    - exact (win_vs_rep Wn a WOK H RC).
    - exact (bsh_vs_rep p n a Hin Ha RC).
    - exact (fsh_vs_rep f k a Hf Ha RC).
    - exact (ssh_vs_rep a H RC).
    - exact (ish_vs_rep a H RC).
  Qed.
End Geom2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section A1.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Variable HP0 : ast -> Prop.



  Theorem AAINV_frame : AAINV_frame_stmt (bt_ia bt) (AAINVP HP0 bt).
  Proof using.
    intros W Lc FF B C K M M' mdl WOK (st & WFH & R & Bd) CH. exists st. split; [exact WFH|]. split; [|exact Bd].
    apply (Rep_frame bt st Lc FF M M' mdl WFH R). intros a Ha. destruct (CH a Ha) as [OWN D]. split; [|exact D].
    exact (app_owned_not_rep bt st Lc FF WFH W (bv_unsigned a) WOK OWN).
  Qed.

  (* [comment removed for export] *)
  Theorem AAINV_nolazy : AAINV_nolazy_stmt (AAINVP HP0 bt).
  Proof using.
    intros Lc FF B C K M mdl z (st & W & R & Bd) Hz.
    (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). destruct (page_in_ranges (page_base (Z_to_bv 64 z)) (m_vm_lazy mdl)) eqn:E; [| reflexivity]. exfalso.
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & LZ & _) & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & LZ0 & LZB & LRI & M06 & M0K) & _).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    (* [comment removed for export] *)
    assert (CASES : forall lo hi, 0 < lo -> hi <= CEIL -> lo <= z < hi -> ~ in_band z ->
              (forall l h, In (l, h) (bt_fixed bt) -> h - l < KSPACE -> h - l <> FAKE_SIZE -> l <= z < h -> (bt_resv6 bt <= z < bt_resv6 bt + bt_resv6_len bt -> False) -> False) ->
              (forall b, In b (dp_storeblocks (a_dep st)) -> b <= z < b + 2 ^ 23 -> False) ->
              (bt_resv6 bt <= z < bt_resv6 bt + bt_resv6_len bt -> ~ committed bt st z -> False) -> False).
    { intros lo hi Hlo Hhi Hz' Hnb HF HS H6. assert (ZR : 0 <= z < 2 ^ 64) by (pose proof ceil_rng; lia). destruct (proj1 (LZ z) (conj ZR E)) as [(P0 & NC & NH) | (b & Hb & Zb)]; [| exact (HS b Hb Zb)].
      destruct (LZ0 z P0 ltac:(lia) Hnb) as [Z6 | [Z8 | ZS]].
      - exact (H6 Z6 NC).
      - apply (HF _ _ IN8); [(lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); lia | lia | intros C6].
        pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ IN6) (all_ranges_fixed bt st _ IN8)
                      ltac:(intros EQ; injection EQ; intros; unfold KSPACE, PG in *; lia)) as D. hnf in D. cbn in D. lia.
      - apply (HF _ _ INS); [(lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE in G in change_no_check G' end); lia | lia | intros C6].
        pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ IN6) (all_ranges_fixed bt st _ INS)
                      ltac:(intros EQ; injection EQ; intros; unfold KSPACE, PG in *; lia)) as D. hnf in D. cbn in D. lia. }
    destruct Hz as [(p & n & Hin & Hz) | (f & k & Hf & Hz)].
    - destruct (live_range bt st Lc FF W p n Hin) as (L1 & L2 & L3 & L4).
      destruct (is_primary n) eqn:HP.
      + pose proof (live_chunk bt st Lc FF W p n Hin HP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
        destruct (carved_range bt st Lc FF W _ _ G1 G2) as (C1 & C2 & C3 & C4 & C5).
        pose proof (region_facts bt st Lc FF W _ G1) as RF. cbn zeta in RF. destruct RF as (P1 & P2 & P3 & _).
        destruct (dyn_kind_facts bt st Lc FF W z (dyn_kind_space bt st Lc FF W z ltac:(unfold prim_alloc_beg, KSPACE, PG in *; lia))) as (O1 & O2 & O3 & O4).
        apply (CASES p (p + n)); [unfold PTRLO in *; lia | lia | lia | exact O4 | | |].
        * intros l h Hl Hlen _ Hz' _. destruct (space_vs_fixed bt st Lc FF W l h Hl Hlen); unfold prim_alloc_beg, KSPACE, PG in *; lia.
        * intros b Hb Zb. destruct (space_vs_dyn bt st Lc FF W _ _ (store_dyn st b Hb)); unfold prim_alloc_beg, KSPACE, PG in *; lia.
        * intros _ NC. apply NC. left. exists (blk_class n). split; [exact G1|]. left. unfold prim_alloc_beg in *. lia.
      + destruct (live_sec bt st Lc FF W p n Hin HP) as (sc & Hs & Eu & En).
        destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). rewrite Eu, En in *.
        destruct (dyn_kind_facts bt st Lc FF W z (dyn_kind_dyn bt st _ _ z (sec_dyn st sc Hs) ltac:(unfold PG in *; lia))) as (O1 & O2 & O3 & O4).
        apply (CASES p (p + n)); [unfold PG in *; lia | lia | lia | exact O4 | | |].
        * intros l h Hl _ _ Hz' _. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hl (sec_dyn st sc Hs)) as D. hnf in D. cbn in D. unfold PG in *. lia.
        * intros b Hb Zb. destruct (sec_vs_store bt st Lc FF W sc b Hs Hb); unfold PG in *; lia.
        * intros C6 _. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN6 (sec_dyn st sc Hs)) as D. hnf in D. cbn in D. unfold PG in *. lia.
    - destruct (fake_frame_facts bt st Lc FF W f k Hf) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). clear F3.
      destruct (dyn_kind_facts bt st Lc FF W z (dyn_kind_fixed bt st _ _ z INFS ltac:(unfold FAKE_SIZE in *; lia))) as (O1 & O2 & O3 & O4).
      apply (CASES f (f + FS k)); [unfold FAKE_SIZE in *; lia | lia | lia | exact O4 | | |].
      + intros l h Hl _ Hlen Hz' _. destruct (fs_vs_fixed bt st Lc FF W l h Hl Hlen); unfold FAKE_SIZE in *; lia.
      + intros b Hb Zb. destruct (fs_vs_dyn bt st Lc FF W _ _ (store_dyn st b Hb)); unfold FAKE_SIZE in *; lia.
      + intros C6 _. destruct (fs_vs_fixed bt st Lc FF W _ _ IN6 ltac:(unfold FAKE_SIZE, KSPACE, PG in *; lia)); unfold FAKE_SIZE, KSPACE, PG in *; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem AAINV_props_all : AAINV_props (bt_ia bt) (AAINVP HP0 bt) (bt_fs bt) (bt_segs bt).
  Proof using. exact (AAINV_props_geom bt HP0 AAINV_frame AAINV_nolazy). Qed.
End A1.
