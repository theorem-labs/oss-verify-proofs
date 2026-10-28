(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Sorting.Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AModelXE AModelC24 APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreeRB () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

Section RecB.
  Variables (h : ahst) (dr : bool) (cnt : nat) (f : option bool) (b0 : batch) (tb : list batch).
  Let L := h_L h.
  Let c := kBatchClass.
  Let p := h_cache h c.
  Let r := h_reg h c.
  Let q := compact L c (b_addr b0).
  Let h' := h_recb h dr cnt f.

  Hypothesis WF : WFR h.
  Hypothesis CI : h_cinit h = true.
  Hypothesis HB : q_batches (h_tq h) = b0 :: tb.
  Hypothesis HE : b_elems b0 = [].
  Hypothesis DR : if dr then pc_count p = max_count c /\ cnt = Z.to_nat (max_count c / 2) else pc_count p < max_count c.
  Hypothesis FOK : f = None \/ f = Some true.
  Hypothesis NF4 : dr = true -> 4 * (r_nfreed r + Z.of_nat cnt) <= r_mapped_fa r + funit f.
  Hypothesis FX : f = Some true -> dr = true /\ r_mapped_fa r < 4 * (r_nfreed r + Z.of_nat cnt).

  Local Ltac clr := clear WF CI HB HE DR FOK NF4 FX.

  #[using="Type"] Lemma c24 : c = 24. Proof. reflexivity. Qed.
  #[using="Type"] Lemma GC : 1 <= c <= 31. Proof. clr. clear. rewrite c24. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma recb_L : h_L h' = h_L h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_chunks : h_chunks h' = h_chunks h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="b0 HB"] Lemma recb_tq : q_batches (h_tq h') = tb.
  Proof. clear WF CI HE DR FOK NF4 FX. subst h'. unfold h_recb, h_lcd, h_poptb. destruct dr; [destruct f as [[|]|]|]; cbn; rewrite HB; reflexivity. Qed.
  #[using="Type"] Lemma recb_gq : h_gq h' = h_gq h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_sec : h_sec h' = h_sec h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_dep : h_dep h' = h_dep h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_acct : h_acct h' = h_acct h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_havol : h_havol h' = h_havol h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_cinit : h_cinit h' = h_cinit h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_pa : h_pa_committed h' = h_pa_committed h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_ia : h_ia h' = h_ia h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recb_fake : h_fake h' = h_fake h. Proof. clr. subst h'. unfold h_recb, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  
  #[using="tb HB"] Lemma recb_q : compact (h_L h) kBatchClass (b_addr (hd (BA 0 [] 0) (q_batches (h_tq h)))) = q.
  Proof. clear WF CI HE DR FOK NF4 FX. subst q L c. rewrite HB. reflexivity. Qed.

  #[using="b0 tb L q HB"] Lemma recb_reg : forall c', h_reg h' c' =
    if (c' =? c) && dr then RG (r_mapped_user r) (r_alloc_user r) (r_mapped_fa r + funit f) (r_fa r ++ pc_lastn p cnt) else h_reg h c'.
  Proof.
    intros c'. clear WF CI HE DR FOK NF4 FX. subst h' r p. unfold h_recb. rewrite recb_q. subst c q L.
    unfold h_lcd, h_poptb, h_push, h_drain, fgrow, h_fagrow. destruct dr; [destruct f as [[|]|]|]; cbn;
      rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; unfold fupd; destruct (Z.eqb_spec c' kBatchClass) as [->|NE]; cbn;
      rewrite ?Z.eqb_refl, ?fupd_same, ?Z.add_0_r; try reflexivity.
    all: try (rewrite (proj2 (Z.eqb_neq _ _) NE); reflexivity).
  Qed.

  #[using="tb HB"] Lemma recb_cache : forall c', h_cache h' c' = if c' =? c then pc_push (if dr then pc_dropn p cnt else p) q else h_cache h c'.
  Proof.
    intros c'. clear WF CI HE DR FOK NF4 FX. subst h' r p. unfold h_recb. rewrite recb_q. subst c q L.
    unfold h_lcd, h_poptb, h_push, h_drain, fgrow, h_fagrow. destruct dr; [destruct f as [[|]|]|]; cbn;
      unfold fupd; destruct (Z.eqb_spec c' kBatchClass) as [->|NE]; cbn; rewrite ?Z.eqb_refl; try reflexivity.
  Qed.

  #[using="b0 tb L c p r q HB"] Lemma recb_carved : forall c', carved h' c' = carved h c'.
  Proof. intros c'. unfold carved. rewrite recb_reg. destruct ((c' =? c) && dr) eqn:E; [| reflexivity]. apply andb_prop in E as [E _]. apply Z.eqb_eq in E. subst c'. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="hAR cnt tb WF HB"] Lemma recb_bfacts : ltac2:(CDefT.buildp (gd_tbl_AW_FreeRB ()) "(0.$1.Lj,$1.(2.(2.(3.=R1.)(4.R1.(5.Vh,Vc,)))(2.(6.$1.(7.Vb0,)(8.VL,Vc,R1.))(2.(6.$1.Vq,(9.R1.(:.(;.Vc,)+10.)))(6.$1.(9.+10.Vq,)(9.R1.(;.Vc,)))))))")
(* [comment removed for export] *).
  Proof.
    dpose WF as (WL & WC & WR & WK & WQ & _). destruct WQ as (WT & _). rewrite HB in WT. ddestruct WT as [(B1 & B2 & (j & Hj & EB)) _]. change kBatchClass with c in Hj, EB.
    exists j. split; [exact Hj|]. split; [exact EB|].
    pose proof (class_size_mod16 c GC) as M16. pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D16.
    subst q L. rewrite EB, compact_chunk_at by exact M16. split; [reflexivity| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma chunk_set_same : forall c', chunk_set h' c' = chunk_set h c'.
  Proof. intros c'. unfold chunk_set. rewrite recb_chunks, recb_L. reflexivity. Qed.

  #[using="tb HB"] Lemma batch_set_split : exists B, batch_set h c = q :: B /\ batch_set h' c = B.
  Proof.
    unfold batch_set. rewrite recb_tq, recb_gq, recb_L, HB. subst c. rewrite Z.eqb_refl. cbn [map app].
    eexists. split; reflexivity.
  Qed.

  #[using="Type"] Lemma batch_set_other : forall c', c' <> c -> batch_set h' c' = batch_set h c'.
  Proof. intros c' NE. unfold batch_set. subst c. rewrite (proj2 (Z.eqb_neq _ _) NE). reflexivity. Qed.

  #[using="b0 tb L c p r q HB DR NF4 FX"] Lemma owned_perm : forall c', 0 <= c' < kNumClasses -> Permutation (owned h' c') (owned h c').
  Proof.
    intros c' Hc'. unfold owned, fa_set, cache_set. rewrite recb_reg, recb_cache, chunk_set_same.
    destruct (Z.eqb_spec c' c) as [->|NE].
    - ddestruct batch_set_split as (B & -> & ->). cbn [andb].
      destruct dr.
      + cbn [r_fa pc_chunks pc_push pc_dropn]. unfold pc_lastn. fold p. fold r.
        set (n0 := (length (pc_chunks p) - cnt)%nat). rewrite <- (firstn_skipn n0 (pc_chunks p)) at 3.
        rewrite <- !app_assoc. apply Permutation_app_head.
        (* [comment removed for export] *)
        eapply Permutation_trans. { apply Permutation_app_swap_app. }
        rewrite <- ?app_assoc. apply Permutation_app_head. apply Permutation_app_head. cbn [app]. apply (Permutation_middle (chunk_set h c) B q).
      + cbn [pc_chunks pc_push]. fold p. rewrite <- ?app_assoc. apply Permutation_app_head. apply Permutation_app_head. cbn [app]. apply (Permutation_middle (chunk_set h c) B q).
    - cbn [andb]. rewrite (batch_set_other c' NE). apply Permutation_refl.
  Qed.

  
  Let okq (c' : Z) : Z -> Prop := fun x => 0 <= x /\ exists kk, 0 <= kk < carved h c' /\ 16 * x = kk * class_size c'.

  #[using="hAR cnt tb WF HB"] Lemma q_ok : okq c q.
  Proof.
    ddestruct recb_bfacts as (j & Hj & EB & Hq & H16). split; [| exists j; split; [exact Hj| exact H16]].
    rewrite Hq. pose proof (class_size_range c GC). apply Z.mul_nonneg_nonneg; [lia|]. apply Z.div_pos; lia.
  Qed.

  #[using="b0 tb L c p r q HB"] Lemma wf_batch_same : forall b, wf_batch h b -> wf_batch h' b.
  Proof.
    (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). split; [exact B1|]. split; [rewrite recb_chunks; exact B2|]. split; [rewrite recb_chunks; exact B3|].
    rewrite recb_carved, recb_L. exact B4.
  Qed.

  #[using="b0 tb L c p r q HB"] Lemma wf_batch_r_same : forall b, wf_batch_r h b -> wf_batch_r h' b.
  Proof. (intros b dd_H; ddestruct dd_H as (B1 & B3 & B4)). split; [exact B1|]. split; [rewrite recb_chunks; exact B3|]. rewrite recb_carved, recb_L. exact B4. Qed.

  #[using="b0 tb L c p r q WF CI HB HE DR FOK NF4 FX okq"] Theorem WFR_recb : WFR h'.
  Proof.
    dpose WF as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    dpose WK as (WKF & ND & WKSEC). ddestruct recb_bfacts as (j & Hj & EB & Hq & H16).
    pose proof (class_size_range c GC) as CSR. pose proof (max_count_range c GC) as MCR.
    assert (HMAX : pc_max p = max_count c /\ pc_csize p = class_size c).
    { pose proof (WC c ltac:(unfold kNumClasses; pose proof GC; lia)) as X. cbn zeta in X. rewrite CI in X. destruct X as (X & _). apply X. pose proof GC; lia. }
    destruct HMAX as [HMAX HCSZ].
    split; [rewrite recb_L; exact WL|].
    split. { (* [comment removed for export] *)
      intros c' Hc'. cbn zeta. rewrite recb_cinit, CI, recb_cache, recb_carved.
      pose proof (WC c' Hc') as X. cbn zeta in X. rewrite CI in X. ddestruct X as (X1 & X2 & X3 & X4 & X5).
      destruct (Z.eqb_spec c' c) as [->|NE]; [| exact (conj X1 (conj X2 (conj X3 (conj X4 X5))))].
      fold p in X1, X2, X3, X4, X5 |- *. unfold pc_count in *.
      assert (LEN : forall dr' : bool, length (pc_chunks (pc_push (if dr' then pc_dropn p cnt else p) q)) = (length (pc_chunks (if dr' then pc_dropn p cnt else p)) + 1)%nat).
      { intros dr'. cbn [pc_chunks pc_push]. rewrite length_app. reflexivity. }
      split; [intros _; cbn [pc_max pc_csize pc_push]; destruct dr; cbn [pc_max pc_csize pc_dropn]; exact (X1 ltac:(pose proof GC; lia))|].
      split; [intros E0; exfalso; rewrite c24 in E0; lia|].
      assert (CNT' : Z.of_nat (length (pc_chunks (pc_push (if dr then pc_dropn p cnt else p) q))) <= max_count c
                     /\ Z.of_nat (length (pc_chunks (pc_push (if dr then pc_dropn p cnt else p) q))) <= 16).
      { rewrite LEN. destruct dr; cbn [pc_chunks pc_dropn].
        - destruct DR as [D1 D2]. rewrite firstn_length_le by lia. assert (1 <= max_count c / 2) by (apply Z.div_le_lower_bound; lia). lia.
        - lia. }
      split; [destruct dr; cbn [pc_max pc_push pc_dropn]; rewrite HMAX; lia|]. split; [lia|].
      cbn [pc_chunks pc_push]. apply Forall_app. split.
      - destruct dr; cbn [pc_chunks pc_dropn]; [| exact X5]. apply Forall_forall. intros x Hx.
        exact (proj1 (Forall_forall _ _) X5 x (In_firstn_In _ _ _ Hx)).
      - constructor; [| constructor]. exact q_ok. }
    split. { (* [comment removed for export] *)
      intros c' Hc'. cbn zeta. rewrite recb_reg, recb_carved.
      pose proof (WR c' Hc') as X. cbn zeta in X. ddestruct X as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
      assert (NDP : NoDup (owned h' c') /\ (forall kk, 0 <= kk < carved h c' <-> In (kk * class_size c' / 16) (owned h' c'))).
      { split; [exact (Permutation_NoDup (Permutation_sym (owned_perm c' Hc')) X10)|].
        intros kk. rewrite (X11 kk). split; intros H; [eapply Permutation_in; [apply Permutation_sym, owned_perm; exact Hc'| exact H]
                                                    | eapply Permutation_in; [apply owned_perm; exact Hc'| exact H]]. }
      destruct NDP as [NDo PARTo].
      destruct ((c' =? c) && dr) eqn:E.
      - apply andb_prop in E as [E ->]. apply Z.eqb_eq in E. subst c'. fold r in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9 |- *.
        cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa]. destruct DR as [D1 D2].
        unfold r_nfreed in *. cbn [r_fa]. rewrite length_app. unfold pc_lastn. rewrite length_skipn.
        assert (FU : 0 <= funit f <= kFreeArrayMapSize /\ funit f mod kFreeArrayMapSize = 0) by (destruct f as [[|]|]; cbn; unfold kFreeArrayMapSize; (split; [lia| reflexivity])).
        assert (CNTL : (cnt <= length (pc_chunks p))%nat) by (unfold pc_count in D1; subst cnt; assert (max_count c / 2 <= max_count c) by (apply Z.div_le_upper_bound; lia); lia).
        split; [intros E0; exfalso; rewrite c24 in E0; lia|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        split. { unfold kFreeArrayMapSize in *. destruct FU as [[F0 F1] F2].
                 rewrite Z.add_mod, X6, F2 by lia. reflexivity. }
        split. {
          split; [lia|]. destruct f as [[|]|]; cbn [funit]; [| lia| lia].
          destruct (FX eq_refl) as [_ LT]. unfold r_nfreed in LT. subst cnt.
          pose proof WX as (WX1 & _). pose proof (WX1 c ltac:(unfold kNumClasses; pose proof GC; lia)) as B. fold r in B.
          unfold kFreeArraySize, kFreeArrayMapSize, kUserLimit in *. unfold carved in *. fold r in B |- *.
          assert (CB : r_alloc_user r / class_size c <= 3758096384 / 32)
            by (apply Z.le_trans with (m := 3758096384 / class_size c); [apply Z.div_le_mono; lia| apply Z.div_le_compat_l; lia]).
          change (3758096384 / 32) with 117440512 in CB. lia. }
        split. { specialize (NF4 eq_refl). unfold r_nfreed in NF4. clear - NF4 CNTL. lia. }
        split. { apply Forall_app. split; [exact X9|]. pose proof (WC c ltac:(unfold kNumClasses; pose proof GC; lia)) as Y. cbn zeta in Y. ddestruct Y as (_ & _ & _ & _ & Y5).
                 fold p in Y5. apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) Y5 x (In_skipn_In _ _ _ Hx)). }
        split; [exact NDo| exact PARTo].
      - split; [exact X0|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|].
        split; [exact X7|]. split; [exact X8|]. split; [exact X9|]. split; [exact NDo| exact PARTo]. }
    split. { (* [comment removed for export] *)
      split; [| split].
      - apply Forall_forall. intros k' Hk'. rewrite recb_chunks in Hk'.
        pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as X. unfold wf_chunk' in *. rewrite recb_carved, recb_L, recb_sec. exact X.
      - rewrite recb_chunks. exact ND.
      - rewrite recb_sec, recb_chunks. exact WKSEC. }
    split. { (* [comment removed for export] *)
      ddestruct WQ as (WT & WGQ & NDA & UQ). rewrite HB in WT. destruct WT as [WB0 WTB].
      split; [| split; [| split]].
      - rewrite recb_tq. pose proof recb_chunks as CH. pose proof recb_carved as CV. pose proof recb_L as HL.
        assert (WTB2 : Forall (wf_batch_r h') tb) by (apply Forall_forall; intros b Hb; apply wf_batch_r_same; exact (proj1 (Forall_forall _ _) WTB b Hb)).
        (* [comment removed for export] *)
        clear - WTB2. destruct tb as [|b1 tb']; [exact I|].
        inversion WTB2 as [|? ? X2 W2]; subst. exact (conj X2 W2).
      - rewrite recb_gq. ddestruct WGQ as (G1 & G2 & G3). split; [| exact (conj G2 G3)].
        apply Forall_forall. intros b Hb. apply wf_batch_same. exact (proj1 (Forall_forall _ _) G1 b Hb).
      - rewrite recb_tq, recb_gq. rewrite HB in NDA. cbn [map app] in NDA. inversion NDA; subst. assumption.
      - intros k' Hk' S'. rewrite recb_tq, recb_gq. rewrite recb_chunks in Hk'.
        ddestruct (UQ k' Hk' S') as (b & [Hb Hin] & U). rewrite HB in Hb.
        destruct Hb as [<-|Hb]; [rewrite HE in Hin; destruct Hin|].
        exists b. split; [split; [exact Hb| exact Hin]|].
        intros b' [Hb' Hin']. apply U. split; [rewrite HB; right; exact Hb'| exact Hin']. }
    split; [unfold wf_sec; rewrite recb_sec, recb_pa; exact WS|].
    split; [unfold wf_depot'; rewrite recb_dep; exact WD|].
    split; [unfold wf_budget, SECC; rewrite recb_acct, recb_havol, recb_sec; exact WB|].
    split; [unfold wf_big; rewrite recb_sec, recb_acct, recb_L; exact WBIG|].
    split. { (* [comment removed for export] *)
      ddestruct WX as (WX1 & WX2 & WX3 & WX4 & WX5 & WX67).
      assert (X67' : wf_x67 h').   (* [comment removed for export] *)
      { apply (wf_x67_frame_acct h h' recb_L recb_acct); [| | exact WX67].
        - intros c' Hc'. rewrite recb_reg.
          destruct ((c' =? c) && dr) eqn:E; [| split; reflexivity]. apply andb_prop in E as [E _]. apply Z.eqb_eq in E. subst c'. split; reflexivity.
        - (* [comment removed for export] *) rewrite !blocks_blk_of, recb_chunks. apply Z.le_refl. }
      split; [| split; [| split; [| rewrite recb_sec, recb_havol; split; [exact WX4| split; [exact WX5| exact X67']]]]].
      - intros c' Hc'. rewrite recb_reg, recb_carved. destruct ((c' =? c) && dr) eqn:E; [| exact (WX1 c' Hc')].
        apply andb_prop in E as [E ->]. apply Z.eqb_eq in E. subst c'. cbn [r_mapped_fa]. fold r.
        destruct f as [[|]|]; cbn [funit]; [| rewrite Z.add_0_r; exact (WX1 c Hc')| rewrite Z.add_0_r; exact (WX1 c Hc')].
        destruct (FX eq_refl) as [_ LT].
        assert (LE : r_nfreed r + Z.of_nat cnt <= carved h c); [| unfold kFreeArrayMapSize; lia].
        pose proof (WR c ltac:(unfold kNumClasses; pose proof GC; lia)) as X. cbn zeta in X. ddestruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X9 & X10 & _).
        pose proof (WC c ltac:(unfold kNumClasses; pose proof GC; lia)) as Y. cbn zeta in Y. ddestruct Y as (_ & _ & _ & _ & Y5). fold p in Y5. fold r in X9.
        unfold owned, fa_set, cache_set in X10. fold r in X10. fold p in X10.
        assert (ND2 : NoDup (r_fa r ++ pc_chunks p)).
        { replace (r_fa r ++ pc_chunks p ++ chunk_set h c ++ batch_set h c) with ((r_fa r ++ pc_chunks p) ++ (chunk_set h c ++ batch_set h c)) in X10
            by (rewrite <- ?app_assoc; reflexivity). exact (NoDup_app_remove_r _ _ X10). }
        pose proof (NoDup_codes_le (r_fa r ++ pc_chunks p) (carved h c) (class_size c / 16)
                      ltac:(apply Z.div_str_pos; pose proof (class_size_mod16 c ltac:(pose proof GC; lia)); lia)
                      ltac:(unfold carved; apply Z.div_pos; [pose proof (WR c ltac:(unfold kNumClasses; pose proof GC; lia)) as Z0; cbn zeta in Z0; lia| lia]) ND2) as CNT'.
        rewrite length_app, Nat2Z.inj_add in CNT'. unfold r_nfreed. destruct DR as [D1 D2]. unfold pc_count in D1.
        assert (Z.of_nat cnt <= Z.of_nat (length (pc_chunks p))) by (subst cnt; assert (max_count c / 2 <= max_count c) by (apply Z.div_le_upper_bound; lia); lia).
        enough (OK : Forall (fun q0 => exists kk, 0 <= kk < carved h c /\ q0 = kk * (class_size c / 16)) (r_fa r ++ pc_chunks p)) by (specialize (CNT' OK); lia).
        apply Forall_app. pose proof (class_size_mod16 c ltac:(pose proof GC; lia)) as M16. pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D16.
        split; apply Forall_forall; intros x Hx.
        + destruct (proj1 (Forall_forall _ _) X9 x Hx) as (_ & kk & Hkk & E16). exists kk. split; [exact Hkk| lia].
        + destruct (proj1 (Forall_forall _ _) Y5 x Hx) as (_ & kk & Hkk & E16). exists kk. split; [exact Hkk| lia].
      - rewrite recb_tq, recb_gq. rewrite HB in WX2. cbn [flat_map app] in WX2. rewrite HE in WX2. cbn [app] in WX2. exact WX2.
      - rewrite recb_cinit, CI. intros X; discriminate X. }
    unfold wf_ghost. rewrite recb_acct, recb_L. exact WG.
  Qed.

  (* [comment removed for export] *)
  #[using="b0 tb L p r q HB FOK FX"] Lemma kview_recb : kview_eq (fsel h c f) h'.
  Proof.
    clear WF CI HE DR NF4. unfold kview_eq. rewrite recb_L, recb_dep, recb_sec, recb_pa, recb_acct. split; [destruct f; reflexivity|].
    split; [| destruct f; cbn; repeat split; reflexivity].
    intros c'. rewrite recb_reg. unfold fsel. destruct f as [b|].
    - cbn [h_reg h_fagrow set_reg]. unfold fupd. destruct (Z.eqb_spec c' c) as [->|NE]; cbn [andb].
      + destruct dr; cbn; [| destruct (FX ltac:(destruct FOK as [E|E]; [discriminate E| exact E])) as [D _]; discriminate D].
        destruct b; cbn; split; reflexivity || (destruct FOK as [E|E]; discriminate E).
      + split; reflexivity.
    - destruct (Z.eqb_spec c' c) as [->|NE]; cbn [andb]; [| split; reflexivity].
      destruct dr; cbn [r_mapped_user r_mapped_fa funit]; split; try reflexivity. rewrite Z.add_0_r. reflexivity.
  Qed.
End RecB.

End ARUN_1.
