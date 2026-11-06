(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section R.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma split_keep_taken : forall (l : list Z) (m : Z), 0 <= m <= Z.of_nat (length l) ->
    let keep := firstn (Z.to_nat (Z.of_nat (length l) - m)) l in
    let taken := skipn (Z.to_nat (Z.of_nat (length l) - m)) l in
    l = keep ++ taken /\ Z.of_nat (length keep) = Z.of_nat (length l) - m /\ Z.of_nat (length taken) = m
    /\ (forall i, (i < length keep)%nat -> nth_error keep i = nth_error l i)
    /\ (forall i, nth_error taken i = nth_error l (Z.to_nat (Z.of_nat (length l) - m) + i)%nat).
  Proof using.
    intros l m Hm. cbn zeta. set (j := Z.to_nat (Z.of_nat (length l) - m)).
    assert (Hj : (j <= length l)%nat) by ((lazymatch goal with |- ?G => let G' := eval unfold j in G in change_no_check G' end); lia).
    split; [symmetry; apply firstn_skipn|].
    split; [rewrite (firstn_length_le l Hj); (lazymatch goal with |- ?G => let G' := eval unfold j in G in change_no_check G' end); lia|].
    split; [rewrite length_skipn; (lazymatch goal with |- ?G => let G' := eval unfold j in G in change_no_check G' end); lia|].
    split.
    - intros i Hi. rewrite nth_error_firstn. rewrite (firstn_length_le l Hj) in Hi.
      destruct (PeanoNat.Nat.ltb_spec i j); [reflexivity | lia].
    - intros i. apply nth_error_skipn.
  Qed.


  Lemma nodup_split_disj : forall (keep taken : list Z) x, List.NoDup (keep ++ taken) -> In x keep -> In x taken -> False.
  Proof using.
    intros keep taken x ND Hk Ht. destruct (in_split _ _ Hk) as (l1 & l2 & ->). rewrite <- app_assoc in ND. cbn in ND.
    apply (NoDup_remove_2 l1 (l2 ++ taken) x ND). apply in_app_iff. right. apply in_app_iff. right. exact Ht.
  Qed.

  (* [comment removed for export] *)
  Lemma partition_keep : forall st st' Lc c,
    (forall a, carved bt st' c a <-> carved bt st c a) -> quar st' = quar st -> a_tq st' ++ a_gq st' = a_tq st ++ a_gq st ->
    a_cache st' c = a_cache st c -> r_free (a_reg st' c) = r_free (a_reg st c) ->
    partition_c bt st Lc c -> partition_c bt st' Lc c.
  Proof using.
    intros st st' Lc c CV EQ EB EC EF P. unfold partition_c, in_quar_c, in_cache_c, in_fa_c, in_batch in *.
    rewrite EQ, EB, EC, EF. destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    split; [intros a; rewrite (CV a); exact (P1 a)|].
    exact (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 (conj P9 P10)))))))).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem OPS_WF_refill_pf : OPS_WF_refill bt.
  Proof using.
    intros st Lc FF c m W Hc HC0 HCI Hm Hle.
    pose proof W as ((WR1 & WR2) & WC & WQ & WS & WL & WK & WD & WM & WMP & G).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
    assert (Hm0 : 0 <= m <= Z.of_nat (length (r_free (a_reg st c)))) by (subst m; unfold cache_hint in *; lia).
    pose proof (split_keep_taken (r_free (a_reg st c)) m Hm0) as SPL. cbn zeta in SPL.
    set (j := Z.to_nat (Z.of_nat (length (r_free (a_reg st c))) - m)) in *.
    set (keep := firstn j (r_free (a_reg st c))) in *. set (taken := skipn j (r_free (a_reg st c))) in *.
    destruct SPL as (EL & LK & LTk & NK & NT).
    pose proof PART as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    assert (ND : List.NoDup (keep ++ taken)) by (rewrite <- EL; exact P10).
    (lazymatch goal with |- ?G => let G' := eval unfold WF, op_refill in G in change_no_check G' end). cbn zeta. fold j. fold keep. fold taken.
    (lazymatch goal with |- ?G => let G' := eval unfold set_cache, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in G in change_no_check G' end).
    set (st' := AST (fupdZ (a_reg st) c (REG (r_mapped_user (a_reg st c)) (r_alloc_user (a_reg st c)) (r_mapped_fa (a_reg st c)) keep (r_uhole (a_reg st c)) (r_fhole (a_reg st c))))
                    (a_cinit st) (fupdZ (a_cache st) c taken) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st)).
    assert (CVE : forall c' a, carved bt st' c' a <-> carved bt st c' a).
    { intros c' a. (lazymatch goal with |- ?G => let G' := eval unfold carved, st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn [r_alloc_user] in G in change_no_check G' end); am_tauto. }
    assert (WBE : forall b, wf_batch bt st b -> wf_batch bt st' b).
    { intros b (B1 & B2 & B3). split; [exact B1|]. split; [apply CVE; exact B2|]. intros m0 n0 Hmn. destruct (B3 m0 n0 Hmn) as [N [[HP CV] | [HP RG]]].
      - split; [exact N|]. left. split; [exact HP|]. apply CVE. exact CV.
      - split; [exact N|]. right. split; [exact HP|]. exact RG. }
    assert (WQ' : wf_quarantine_q bt st' (2 ^ 20) (2 ^ 28)).
    { destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (a_tq st). change (a_gq st') with (a_gq st). change (quar st') with (quar st).
      split; [eapply Forall_impl; [exact WBE | exact Q1]|]. split; [eapply Forall_impl; [| exact Q2]; intros b0; apply wf_batch0_mono; [intros c0 a0; apply CVE | intros p0 n0 H0; exact H0]|].
      split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5 | exact Q6]. }
    assert (WL' : wf_live bt st' Lc).
    { destruct WL as (L1' & L2' & L3'). (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [| split; [exact L2' | exact L3']].
      intros p n Hin. destruct (L1' p n Hin) as (A1 & A2 & A3 & CVL). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      intros HP. apply CVE. exact (CVL HP). }
    assert (WM' : wf_meter st').
    { apply (wf_meter_transfer st st' eq_refl eq_refl eq_refl); [| exact WM].
      intros c' Hc'. (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE]; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); split; reflexivity. }
    split; [| split; [| split; [exact WQ' | split; [exact WS | split; [exact WL' | split; [exact WK | split; [exact WD | split; [exact WM' | split; [exact WMP | exact G]]]]]]]]].
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end).
      split; [| intros c' Hc'; destruct (WR2 c' Hc') as [E1 E2]; (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cache] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c' c); [lia | split; [exact E1 | exact E2]]].
      intros c' Hc'. destruct (WR1 c' Hc') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & PART' & FHK').
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cache] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE].
      + (lazymatch goal with |- ?G => let G' := eval cbn [r_mapped_user r_alloc_user r_mapped_fa r_free] in G in change_no_check G' end). repeat (split; [first [assumption | lia] |]).
        split. { intros k Hk. destruct (Y9 k ltac:(rewrite EL; apply in_app_iff; left; exact Hk)) as [A B]. split; [exact A | apply CVE; exact B]. }
        split; [| exact FHK].
        (* [comment removed for export] *)
        unfold partition_c in *. unfold in_cache_c, in_fa_c, in_batch, carved in *. cbn [a_cache a_reg a_tq a_gq r_alloc_user r_free] in *.
        (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). rewrite Z.eqb_refl. (lazymatch goal with |- ?G => let G' := eval cbn [r_alloc_user r_free] in G in change_no_check G' end).
        rewrite HC0 in P1, P3, P5, P7, P8.
        assert (SPLIT : forall a, (exists k, In k (r_free (a_reg st c)) /\ a = chunk_of_compact SBEG c k) <->
                                  ((exists k, In k taken /\ a = chunk_of_compact SBEG c k) \/ (exists k, In k keep /\ a = chunk_of_compact SBEG c k))).
        { intros a. rewrite EL. split.
          - intros (k & Hk & E). apply in_app_iff in Hk. destruct Hk as [Hk|Hk]; [right | left]; exists k; split; assumption.
          - intros [(k & Hk & E) | (k & Hk & E)]; exists k; (split; [apply in_app_iff | exact E]); [right | left]; exact Hk. }
        assert (NOC : forall a, ~ (exists k, In k (@nil Z) /\ a = chunk_of_compact SBEG c k)) by (intros a (k & Hk & _); exact Hk).
        split. { intros a. rewrite (P1 a), (SPLIT a). pose proof (NOC a). am_tauto. }
        split; [exact P2|].
        split. { intros a [X Y]. apply (P4 a). split; [exact X|]. apply SPLIT. left. exact Y. }
        split. { intros a [X Y]. apply (P4 a). split; [exact X|]. apply SPLIT. right. exact Y. }
        split. { intros a [X Y]. apply (P6 a). split; [exact X|]. apply SPLIT. left. exact Y. }
        split. { intros a [X Y]. apply (P6 a). split; [exact X|]. apply SPLIT. right. exact Y. }
        split. { intros a [(k & Hk & E) (k' & Hk' & E')]. rewrite E in E'. apply (f_equal (compact_of SBEG c)) in E'.
                 rewrite !compact_roundtrip_k in E'. subst k'. exact (nodup_split_disj keep taken _ ND Hk' Hk). }
        split. { intros a Hb Hc24 X. apply (P8 a Hb Hc24). destruct X as [X|[X|[X|X]]]; [left; exact X | right; left; exact X | |];
                 right; right; right; apply SPLIT; [left | right]; exact X. }
        split; [exact (NoDup_app_remove_l _ _ ND) | exact (NoDup_app_remove_r _ _ ND)].
      + repeat (split; [assumption|]).
        split. { intros k Hk. destruct (Z9 k Hk) as [A B]. split; [exact A | apply CVE; exact B]. }
        split; [| exact FHK'].
        apply (partition_keep st st' Lc c'); [exact (CVE c') | reflexivity | reflexivity | | | exact PART'].
        * (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache] in G in change_no_check G' end). apply fupdZ_other. exact NE.
        * (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). rewrite fupdZ_other by exact NE. reflexivity.
    - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end).
      intros c' Hc'. (lazymatch goal with |- ?G => let G' := eval cbn [a_cache a_cinit a_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE].
      + split; [rewrite LTk; subst m; (lazymatch goal with |- ?G => let G' := eval unfold cache_max in G in change_no_check G' end); lia|]. split; [intros F; rewrite HCI in F; discriminate F|].
        intros k Hk. destruct (Y9 k ltac:(rewrite EL; apply in_app_iff; right; exact Hk)) as [A B]. split; [exact A | apply CVE; exact B].
      + destruct (WC c' Hc') as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
        intros k Hk. destruct (C3 k Hk) as [A B]. split; [exact A | apply CVE; exact B].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition foot_refill (c m : Z) (a : Z) : Prop :=
    (reginfo bt c <= a < reginfo bt c + 8) \/ (reginfo bt c + 16 <= a < reginfo bt c + 24) \/ (reginfo bt c + 72 <= a < reginfo bt c + 128)
    \/ (T + T_PC + PC_SZ * c <= a < T + T_PC + PC_SZ * c + 4)
    \/ (T + T_PC + PC_SZ * c + 16 <= a < T + T_PC + PC_SZ * c + 16 + 4 * m)
    \/ (T + 2768 <= a < T + 3168) \/ CEIL <= a.

  Definition OPS_REP_refill : Prop := forall st Lc FF (M M' : mem) mdl mdl' c m,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= c <= 30 -> a_cache st c = [] -> a_cinit st = true ->
    m = cache_hint c -> m <= Z.of_nat (length (r_free (a_reg st c))) ->
    let n := Z.of_nat (length (r_free (a_reg st c))) in
    let taken := skipn (Z.to_nat (n - m)) (r_free (a_reg st c)) in
    agrees_off (foot_refill c m) M M' ->
    cellZ SG M' (reginfo bt c) 8 0 ->
    cellZ SG M' (reginfo bt c + 16) 8 (n - m) ->
    cellZ SG M' (T + T_PC + PC_SZ * c) 4 m ->
    (forall i k, nth_error taken i = Some k -> cellZ SG M' (T + T_PC + PC_SZ * c + 16 + 4 * Z.of_nat i) 4 k) ->
    same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
    Rep bt (op_refill st c m) Lc FF M' mdl'.

  Theorem OPS_REP_refill_pf : OPS_REP_refill.
  Proof using.
    intros st Lc FF M M' mdl mdl' c m W R Hc HC0 HCI Hm Hle. cbn zeta. intros AGR CMU CNF CCNT CCH SBM MI.
    pose proof W as ((WR1 & WR2) & WC & WQ & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    destruct (WR1 c Hc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & PART & FHK).
    assert (Hm0 : 0 <= m <= Z.of_nat (length (r_free (a_reg st c)))) by (subst m; unfold cache_hint in *; lia).
    assert (Hm8 : m <= 8) by (subst m; (lazymatch goal with |- ?G => let G' := eval unfold cache_hint in G in change_no_check G' end); lia).
    pose proof (split_keep_taken (r_free (a_reg st c)) m Hm0) as SPL. cbn zeta in SPL.
    set (j := Z.to_nat (Z.of_nat (length (r_free (a_reg st c))) - m)) in *.
    set (keep := firstn j (r_free (a_reg st c))) in *. set (taken := skipn j (r_free (a_reg st c))) in *.
    destruct SPL as (EL & LK & LTk & NK & NT).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    pose proof (agrees_DEFK _ _ _ AGR) as DEF. pose proof (agrees_at' _ _ _ AGR) as AGF.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (first [clear - SPH R6a | idtac]; lia).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((TD1 & TD2 & TD3 & TD4 & TD5) & _). box TD4. box TD5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    (* [comment removed for export] *)
    set (RZc := fun i => reginfo bt c <= i < reginfo bt c + 128).
    set (Tz := fun i => (T + T_PC + PC_SZ * c <= i < T + T_PC + PC_SZ * c + 80) \/ (T + 2768 <= i < T + 3168)).
    assert (FZ : forall i, foot_refill c m i -> RZc i \/ Tz i \/ CEIL <= i).
    { intros i Hf. unfold foot_refill in Hf. (lazymatch goal with |- ?G => let G' := eval unfold RZc, Tz in G in change_no_check G' end). destruct Hf as [A|[A|[A|[A|[A|[A|A]]]]]]; clear -A Hm8 Hm0; lia. }
    assert (AGZ : forall i, 0 <= i -> i < CEIL -> ~ RZc i -> ~ Tz i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i H0 H1 N1 N2. apply AGF; [| clear -H0 H1; ulia]. intros Hf. destruct (FZ i Hf) as [A|[A|A]]; [exact (N1 A) | exact (N2 A) | clear -A H1; ulia]. }
    assert (IMGfree : forall i, ia_img_lo IA <= i < ia_img_hi IA -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply AGZ; [clear -Hi I1; ulia | clear -Hi I2; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi I2 E9 SBH; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi TD4 Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); Zlia]. }
    (* [comment removed for export] *)
    assert (FIXfree : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo <> PG -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ Hlo) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; (first [clear - H0 H Hlen | idtac]; ulia))) as D. hnf in D. cbn in D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hlo Hlen2) as [SP|SP];
        (apply AGZ; [clear -Hi A1; ulia | clear -Hi A2 A3; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi SP E9 E10; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi D Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia]). }
    (* [comment removed for export] *)
    assert (FIXfreeT : forall lo hi, In (lo, hi) (bt_fixed bt) -> (hi <= T \/ T + PG <= lo) -> hi - lo < KSPACE ->
                      forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo Hlen Hlen2 i Hi Hr. destruct (RNG _ _ (all_ranges_fixed bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof Hlen as D.
      destruct (space_vs_fixed bt st Lc FF W lo hi Hlo Hlen2) as [SP|SP];
        (apply AGZ; [clear -Hi A1; ulia | clear -Hi A2 A3; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi SP E9 E10; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi D Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia]). }
    assert (DYNfree : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall i, lo <= i < hi -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hlo i Hi Hr. destruct (RNG _ _ (all_ranges_dyn bt st _ Hlo)) as ((A1 & A1' & A3 & A4 & A5) & A2 & _).
      pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT Hlo) as D. hnf in D. cbn in D.
      destruct (space_vs_dyn bt st Lc FF W lo hi Hlo) as [SP|SP];
        (apply AGZ; [clear -Hi A1; ulia | clear -Hi A2 A3; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi SP E9 E10; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi D Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia]). }
    assert (SPCfree : forall i, SBEG <= i < SBEG + KSPACE -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi Hr. apply AGZ; [clear -Hi X14; ulia | clear -Hi X15; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi E9; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi TPG Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia]. }
    (* [comment removed for export] *)
    assert (RIfree : forall c', 1 <= c' <= 30 -> c' <> c -> forall i, reginfo bt c' <= i < reginfo bt c' + 128 -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros c' Hc' NE i Hi Hr. unfold reginfo in *. apply AGZ; [clear -Hi Hc' X14; ulia | clear -Hi Hc' X15; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold reginfo in G in change_no_check G' end); clear -Hi Hc' Hc NE; lia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi TPG Hc Hc'; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia]. }
    (* [comment removed for export] *)
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
    pose proof ceil_rng as CR. pose proof ceil_pg as CP. unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Z2, Z4, Z6, Z8, Z10, Z12, Z14, Z16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold op_refill in G in change_no_check G' end). cbn zeta. fold j. fold keep. fold taken.
    (lazymatch goal with |- ?G => let G' := eval unfold set_cache, set_reg in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in G in change_no_check G' end).
    set (r' := REG (r_mapped_user (a_reg st c)) (r_alloc_user (a_reg st c)) (r_mapped_fa (a_reg st c)) keep (r_uhole (a_reg st c)) (r_fhole (a_reg st c))).
    set (st' := AST (fupdZ (a_reg st) c r') (a_cinit st) (fupdZ (a_cache st) c taken) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st)
                    (a_hint st) (a_ialloc st) (a_aa st) (a_kact st) (a_shsec st)).
    assert (RMU : forall c0, r_mapped_user (a_reg st' c0) = r_mapped_user (a_reg st c0))
      by (intros c0; (lazymatch goal with |- ?G => let G' := eval unfold st', r' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity).
    assert (RFA : forall c0, r_mapped_fa (a_reg st' c0) = r_mapped_fa (a_reg st c0))
      by (intros c0; (lazymatch goal with |- ?G => let G' := eval unfold st', r' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity).
    assert (RUH : forall c0, r_uhole (a_reg st' c0) = r_uhole (a_reg st c0))
      by (intros c0; (lazymatch goal with |- ?G => let G' := eval unfold st', r' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity).
    assert (RFH : forall c0, r_fhole (a_reg st' c0) = r_fhole (a_reg st c0))
      by (intros c0; (lazymatch goal with |- ?G => let G' := eval unfold st', r' in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end); destruct (Z.eqb_spec c0 c) as [-> | NE]; reflexivity).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact R1 | exact YC |]. intros c0 i Hc0 Hi.
             destruct (img_kinds bt st Lc FF W i ltac:(left; exists c0; split; [exact Hc0 | exact Hi])) as [LT _]. exact (IMGfree i LT). }
    (* [comment removed for export] *)
    split. { change (rep_instance bt st' M') with (rep_instance bt st M'). eapply rep_instance_frame; [exact DEF | exact R2 | ulia | ulia | ulia | ulia | exact S1 |].
             intros i Hi Hr. destruct (decide (bt_ptrarr bt <= i < bt_ptrarr bt + 8 * Z.of_nat (length (a_sec st)))) as [IN | NI].
             - apply (FIXfree _ _ IN8); [ulia | ulia | clear -IN S1 S3; ulia | exact Hr].
             - destruct (img_kinds bt st Lc FF W i ltac:(right; left; split; [exact Hi | exact NI])) as [LT _]. exact (IMGfree i LT). }
    (* [comment removed for export] *)
    split. { destruct R3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end).
             change (a_tq st') with (a_tq st). change (a_cinit st') with (a_cinit st). change (a_cache st') with (fupdZ (a_cache st) c taken).
             assert (AGT : forall i, ((T <= i < T + T_PC + PC_SZ * c \/ T + T_PC + PC_SZ * c + 80 <= i < T + 2768 \/ T + 3168 <= i < T + PG)
                                     \/ (bt_tctx bt <= i < bt_tctx bt + 160)) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi Hr. destruct Hi as [Hi | Hi].
               - unfold T_PC, PC_SZ in Hi. apply AGZ; [clear -Hi X1 Hc; ulia | clear -Hi X2 Hc; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi TPG E9 E10 Hc X2; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -Hi Hc; lia].
               - apply (FIXfree _ _ INC); [ulia | ulia | clear -Hi; lia | exact Hr]. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { eapply rep_list_frame; [exact TL | ulia | ulia |]. intros i Hi Hr. apply AGT; [| exact Hr]. left. clear -Hi Hc. lia. }
             split. { intros c' Hc'. (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c' c) as [-> | NE].
                      - destruct (TP c Hc) as (Q1 & Q2 & Q3 & Q4). rewrite HCI in Q2, Q3. (lazymatch goal with |- ?G => let G' := eval unfold rep_pclass in G in change_no_check G' end). rewrite HCI. unfold T_PC, PC_SZ in *.
                        split; [rewrite LTk; exact CCNT|].
                        split. { eapply (cellZ_frame _ _ _ _ _ _ Q2); [clear -X1 Hc; ulia | clear -X2 Hc; ulia |]. intros i Hi. apply AGF; [| clear -Hi X1 X2 Hc; ulia].
                                 intros Hf. unfold foot_refill, reginfo in Hf. unfold T_PC, PC_SZ in Hf. clear -Hf Hi Hc Hm0 Hm8 TPG E9 X1 X2. ulia. }
                        split. { eapply (cellZ_frame _ _ _ _ _ _ Q3); [clear -X1 Hc; ulia | clear -X2 Hc; ulia |]. intros i Hi. apply AGF; [| clear -Hi X1 X2 Hc; ulia].
                                 intros Hf. unfold foot_refill, reginfo in Hf. unfold T_PC, PC_SZ in Hf. clear -Hf Hi Hc Hm0 Hm8 TPG E9 X1 X2. ulia. }
                        intros i k Hk. exact (CCH i k Hk).
                      - pose proof (cache_len bt st Lc FF W c' Hc') as CL'.
                        eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -Hc' X1; ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); clear -Hc' X2; ulia | exact CL' |].
                        (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). intros i Hi Hr. apply AGT; [| exact Hr]. left. clear -Hi Hc' Hc NE. lia. }
             split; [frW DEF TW|]. split; [frZ AGT TC1|]. split; [frZ AGT TC2|]. split; [frZ AGT TC3 | frZ AGT TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. change (a_reg st') with (fupdZ (a_reg st) c r'). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb_spec c0 c) as [-> | NE].
             - destruct (R4 c Hc) as [G0 F0]. destruct G0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). destruct F0 as (F1 & F2 & F3). (lazymatch goal with |- ?G => let G' := eval unfold r' in G in change_no_check G' end).
               assert (AGR' : forall i, (reginfo bt c + 8 <= i < reginfo bt c + 16 \/ reginfo bt c + 24 <= i < reginfo bt c + 72) -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
               { intros i Hi Hr. apply AGF; [| exact Hr]. intros Hf. unfold foot_refill in Hf. unfold reginfo, T_PC, PC_SZ in *. clear -Hf Hi Hc Hm0 Hm8 TPG E9 E10 X1 X2 X15. ulia. }
               split.
               + unfold rep_reginfo in *. cbn zeta in *. (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_alloc_user r_mapped_user] in G in change_no_check G' end). unfold KSPACE, PG in E9, E10.
                 split; [exact CMU|]. split; [frZ AGR' G2|]. split; [rewrite LK; exact CNF|]. split; [frZ AGR' G4|]. split; [frZ AGR' G5|].
                 split; [frZ AGR' G6|]. split; [frZ AGR' G7|]. split; [frZ AGR' G8|]. destruct G9 as [G9a G9b]. split; [frB AGR' G9a | frW DEF G9b].
               + (lazymatch goal with |- ?G => let G' := eval unfold rep_freearray in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [r_free r_mapped_fa r_mapped_user] in G in change_no_check G' end). split; [| split; [frW DEF F2 | frW DEF F3]].
                 intros i k Hk. pose proof (nth_error_lt _ _ _ Hk) as Hl. rewrite (NK i Hl) in Hk. pose proof (F1 i k Hk) as C.
                 eapply (cellZ_frame _ _ _ _ _ _ C); [clear -E1 E2 E3 E4 X14; ulia | clear -Hl LK E5 E6 E7 X15 Hm0; ulia |].
                 intros i0 Hi0. apply SPCfree; [clear -Hi0 Hl LK E1 E2 E3 E4 E5 E6 E7 Hm0; ulia | clear -Hi0 Hl LK E1 E2 E3 E4 E5 E6 E7 X14 X15 Hm0; ulia].
             - destruct (R4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
               destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & _).
               eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | (first [clear - D9 X14 | idtac]; ulia) | (first [clear - D10 X15 | idtac]; ulia) | (first [clear - D4 D3 D2 D1 X14 | idtac]; ulia) | (first [clear - D6 D5 X15 | idtac]; ulia) | (first [clear - D7 | idtac]; ulia) |].
               intros i Hi Hr. unfold foot_region in Hi. destruct Hi as [[Hi _] | Hi]; [apply (RIfree c0 Hc0 NE); [clear -Hi; lia | exact Hr] | apply SPCfree; [clear -Hi D1 D2 D3 D4 D5 D6 D7; ulia | exact Hr]]. }
    (* [comment removed for export] *)
    assert (BAfree : forall q, rep_batches bt M q -> (forall b, In b q -> In b (a_tq st ++ a_gq st)) -> rep_batches bt M' q).
    { intros q RB SUB. eapply rep_batches_frame; [exact DEF | exact RB | |].
      - intros b Hb. destruct (batch_facts bt st Lc FF W b (SUB b Hb)) as (_ & BL & B1 & B2). ulia.
      - intros b i Hb Hi Hr. unfold foot_batch in Hi. destruct (batch_facts bt st Lc FF W b (SUB b Hb)) as (_ & BL & B1 & B2).
        apply SPCfree; [clear -Hi BL B1 B2; ulia | exact Hr]. }
    split; [change (a_tq st') with (a_tq st); apply (BAfree _ R5); intros b Hb; apply in_app_iff; left; exact Hb|].
    split; [change (a_gq st') with (a_gq st); apply (BAfree _ R6); intros b Hb; apply in_app_iff; right; exact Hb|].
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (rep_secondary bt st M'). eapply rep_secondary_frame; [exact DEF | exact R7 | |].
             - intros sc Hs. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). ulia.
             - intros sc i Hs Hi Hr. unfold foot_sec in Hi. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _).
               apply (DYNfree _ _ (sec_dyn st sc Hs)); [(first [clear - A7 A6 A5 Hi | idtac]; ulia) | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_headers bt st' Lc M') with (rep_headers bt st Lc M'). destruct R8 as [HLh HQh].
             assert (HDRfree : forall p' n' i, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' i -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros p' n' i Hown Hf Hr. pose proof (rz_range n') as RZ'.
               destruct (hdr_zone bt st Lc FF W p' n' i Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
               - apply SPCfree; [clear -W1 W2 W3 W4 N1'; lia | exact Hr].
               - apply (DYNfree _ _ (sec_dyn st sc' Hs')); [| exact Hr]. destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
                 rewrite Eu', En' in *. (first [clear - A6 N1' W1 | idtac]; ulia). }
             split.
             - intros p' n' Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n').
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | ulia | ulia |]. intros i Hi Hr. exact (HDRfree p' n' i (or_introl Hin') Hi Hr).
             - intros m0 n' Hq. destruct (HQh m0 n' Hq) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq) as (B1 & B2 & B3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -B1 B2 B3 RZn; ulia | clear -B1 B2 B3 RZn; ulia |]. intros i Hi Hr.
               apply (HDRfree (m0 + 16) n' i); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq | exact Hi | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact R9 | ulia | ulia | ulia | ulia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). ulia.
             - intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(right; right; left; exact Hi)) as [LT _]. exact (IMGfree i LT).
             - intros id i Hid Hi Hr. unfold foot_node in Hi. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXfree _ _ INN); [ulia | ulia | rewrite Eb; lia | exact Hr].
               + apply (DYNfree _ _ (node_dyn st bb Hnb)); [lia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact R10 | ulia | ulia | ulia | ulia | ulia | ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). ulia.
             - intros i Hi Hr. unfold foot_fake_static in Hi. destruct Hi as [Hi|[Hi|[Hi|[Hi|Hi]]]].
               1-3: apply (FIXfree _ _ INFS); ulia.
               + destruct (img_kinds bt st Lc FF W i ltac:(do 3 right; left; exact Hi)) as [LT _]. exact (IMGfree i LT).
               + apply (FIXfreeT _ _ (dtls_member bt st Lc FF W) (dtls_vs_thread bt st Lc FF W)); ulia.
             - intros f k0 i Hf Hi Hr. unfold foot_fword in Hi. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXfree _ _ INFS); (first [clear - A4 A2 A1 Hi Hr | idtac]; ulia). }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact R11 | ulia | ulia | ulia | ulia |].
             intros i Hi Hr. destruct (img_kinds bt st Lc FF W i ltac:(do 4 right; left; exact Hi)) as [LT _]. exact (IMGfree i LT). }
    (* [comment removed for export] *)
    split. { destruct R12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end). change (a_sec st') with (a_sec st). change (quar st') with (quar st).
             assert (AGS : forall i, SB <= i < AS_HEAPLO -> 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
             { intros i Hi Hr. apply AGZ; [clear -Hi; ulia | clear -Hi; ulia | (lazymatch goal with |- ?G => let G' := eval unfold RZc in G in change_no_check G' end); clear -Hi E9 SBH; ulia | (lazymatch goal with |- ?G => let G' := eval unfold Tz in G in change_no_check G' end); clear -Hi TD5 Hc; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); Zlia]. }
             assert (SHR : forall lo hi g, lo / 8 <= g < hi / 8 -> 0 <= lo -> hi <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo hi g Hg Hg0 Hg1. clear -Hg Hg0 Hg1. Zlia. }
             split. { intros c0 g Hc0 Hg NL'. rewrite RMU in Hg. pose proof (SH1 c0 g Hc0 Hg NL') as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (Q1 & Q2 & Q3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact Q2 | exact Q3 | apply AGS; [exact Q1 | lia]]. }
             split. { intros c0 g Hc0 Hg. rewrite RFA in Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (Q1 & Q2 & Q3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact Q2 | exact Q3 | apply AGS; [exact Q1 | lia]]. }
             split. { intros sc g Hs Hg NUG. pose proof (SH3 sc g Hs Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (Q1 & Q2 & Q3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact Q2 | exact Q3 | apply AGS; [exact Q1 | lia]]. }
             split. { intros sc g Hs HQ HU. pose proof (SH4 sc g Hs HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (Q1 & Q2 & Q3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact Q2 | exact Q3 | apply AGS; [exact Q1 | lia]]. }
             split. { intros c0 g Hc0 Hg. rewrite RMU in Hg. exact (def_keep M M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hs Hg. exact (def_keep M M' _ DEF (SH6 sc g Hs Hg)). }
    (* [comment removed for export] *)
    split. { pose proof (rep_ledger_sbm bt st mdl mdl' SBM R13) as (L1 & L2 & L3 & L4 & L5). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             change (dyn_maps st') with (dyn_maps st). change (a_dep st') with (a_dep st).
             assert (COMM : forall a, committed bt st' a <-> committed bt st a).
             { intros a. (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end). change (a_nres st') with (a_nres st). split.
               - intros [(c1 & Hc1 & X) | X]; [left; exists c1; rewrite RMU, RFA in X; exact (conj Hc1 X) | right; exact X].
               - intros [(c1 & Hc1 & X) | X]; [left; exists c1; rewrite RMU, RFA; exact (conj Hc1 X) | right; exact X]. }
             assert (HOL : forall a, holes bt st' a <-> holes bt st a).
             { intros a. (lazymatch goal with |- ?G => let G' := eval unfold holes in G in change_no_check G' end). split.
               - intros (c1 & Hc1 & X). exists c1. rewrite RMU, RFA, RUH, RFH in X. exact (conj Hc1 X).
               - intros (c1 & Hc1 & X). exists c1. rewrite RMU, RFA, RUH, RFH. exact (conj Hc1 X). }
             split. { destruct L1 as (F6 & P1 & P2 & P3 & P4). exists F6. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
                      intros a Ha. rewrite (HOL a). exact (P4 a Ha). }
             split; [intros a; rewrite (COMM a), (HOL a); exact (L2 a)|]. split; [intros a; rewrite (COMM a), (HOL a); exact (L3 a)|].
             split; [exact L4 | exact L5]. }
    (* [comment removed for export] *)
    split. { destruct R14 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). (lazymatch goal with |- ?G => let G' := eval unfold rep_budget in G in change_no_check G' end).
             change (a_aa st') with (a_aa st). change (a_sec st') with (a_sec st). change (a_dep st') with (a_dep st). change (a_shsec st') with (a_shsec st). change (a_nres st') with (a_nres st).
             pose proof (same_but_materialized_frame mdl mdl' SBM) as Fm.
             destruct Fm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3').
             split; [exact B1|]. split; [exact MI|]. split; [exact B3|]. split; [exact B4|].
             split. { intros c0 Hc0. rewrite RMU, RFA. exact (B5 c0 Hc0). }
             split; [exact B6|]. split; [exact B7|].
             rewrite E3'. change (sec_charge st') with (sec_charge st). change (depot_charge st') with (depot_charge st).
             assert (PC : prim_charge st' = prim_charge st).
             { (lazymatch goal with |- ?G => let G' := eval unfold prim_charge in G in change_no_check G' end).
               assert (EQ : forall k, sum_classes (fun c0 : Z => r_mapped_user (a_reg st' c0) + r_mapped_user (a_reg st' c0) / 8 + r_mapped_fa (a_reg st' c0) + r_mapped_fa (a_reg st' c0) / 8) k
                                  = sum_classes (fun c0 : Z => r_mapped_user (a_reg st c0) + r_mapped_user (a_reg st c0) / 8 + r_mapped_fa (a_reg st c0) + r_mapped_fa (a_reg st c0) / 8) k).
               { induction k as [|k IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_classes] in G in change_no_check G' end). rewrite IH, RMU, RFA. reflexivity. }
               apply EQ. }
             rewrite PC. exact B8. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin'. destruct (R15 p' n' Hin') as [V1 V2]. split; [frW DEF V1 | frW DEF V2]. }
    split. { intros f k0 Hf. frW DEF (R16 f k0 Hf). }
    split; [eapply (cellZ_frame _ _ _ _ _ _ R17); [ulia | ulia | intros i Hi; exact (IMGfree i (proj1 (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); left; cbn in Hi; lia))))] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ R18); [ulia | ulia | intros i Hi; exact (IMGfree i (proj1 (img_kinds bt st Lc FF W i ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); right; cbn in Hi; lia))))] |].
    exact (rep_last_keep bt _ _ M M' DEF R19 (fun H => H)).
  Qed.
End R.
