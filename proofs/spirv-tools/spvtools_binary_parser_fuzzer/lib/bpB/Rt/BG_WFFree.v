(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocWf BllocKit BG_MallocModel BG_WFHit BS_Refill1 BG_RefillModel BG_ColdModel BG_FreeModel BG_RepQ.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition others (st : astate) (ch : chunk) : list chunk :=
  filter (fun y => negb (ch_user_beg y =? ch_user_beg ch)) (chunk_list st).

Lemma filter_app' {A} : forall (f : A -> bool) l1 l2, filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof. induction l1; intros; cbn; [reflexivity|]. rewrite IHl1. destruct (f a); reflexivity. Qed.

Lemma filter_all {A} : forall (f : A -> bool) l, (forall x, In x l -> f x = true) -> filter f l = l.
Proof. induction l as [|y l IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros x Hx; apply H; right; exact Hx. Qed.

Section Replace.
  Variables (st : astate) (ch x : chunk).
  Hypothesis KEYS : keys_ok (as_chunks st).
  Hypothesis INJ : forall a b, In a (chunk_list st) -> In b (chunk_list st) -> ch_user_beg a = ch_user_beg b -> a = b.
  Hypothesis IN : In ch (chunk_list st).
  Hypothesis KX : ch_user_beg x = ch_user_beg ch.

  Lemma others_perm : Permutation (chunk_list st) (ch :: others st ch).
  Proof.
    destruct (in_split _ _ IN) as (A & B & E). unfold others. rewrite E.
    pose proof (chunk_list_nodup st KEYS) as ND. rewrite E in ND.
    assert (HA : forall y, In y (A ++ B) -> negb (ch_user_beg y =? ch_user_beg ch) = true).
    { intros y Hy. apply Bool.negb_true_iff, Z.eqb_neq. intros EQ.
      assert (y = ch) by (apply INJ; [rewrite E; apply in_app_iff; destruct (in_app_iff A B y) as [H _]; destruct (H Hy); [left|right; right]; assumption| exact IN| exact EQ]).
      subst y. apply NoDup_remove_2 in ND. exact (ND Hy). }
    rewrite filter_app'. cbn [filter]. rewrite Z.eqb_refl. cbn [negb].
    rewrite !filter_all by (intros y Hy; apply HA; apply in_app_iff; auto).
    apply Permutation_sym. apply Permutation_middle.
  Qed.

  Lemma others_in : forall y, In y (others st ch) <-> In y (chunk_list st) /\ ch_user_beg y <> ch_user_beg ch.
  Proof. intros y. unfold others. rewrite filter_In, Bool.negb_true_iff, Z.eqb_neq. tauto. Qed.

  Lemma others_nodup : NoDup (others st ch).
  Proof. unfold others. apply NoDup_filter. apply chunk_list_nodup. exact KEYS. Qed.

  Lemma upd_perm : Permutation (chunk_list (upd_chunk st x)) (x :: others st ch).
  Proof.
    apply NoDup_Permutation.
    - apply chunk_list_nodup. apply keys_ok_upd; [exact KEYS|]. rewrite KX. exact (proj2 (KEYS _ _ (proj1 (chunk_list_find st ch KEYS) IN))).
    - constructor; [| apply others_nodup]. rewrite others_in. intros [_ NE]. exact (NE KX).
    - intros y. rewrite chunk_list_upd_iff. cbn [In]. rewrite others_in. split.
      + intros [->|[k [F NE]]]; [left; reflexivity| right]. split; [apply chunk_list_in_iff; exists k; exact F|].
        destruct (KEYS _ _ F) as [-> _]. rewrite <- KX. intros EQ. apply NE. rewrite EQ. reflexivity.
      + intros [<-|[Hy NE]]; [left; reflexivity| right]. apply (chunk_list_find st y KEYS) in Hy.
        exists (ckey (ch_user_beg y)). split; [exact Hy|]. rewrite KX. intros EQ. apply NE.
        destruct (KEYS _ _ Hy) as [_ POS]. pose proof (proj2 (KEYS _ _ (proj1 (chunk_list_find st ch KEYS) IN))) as POS2.
        unfold ckey in EQ. apply Z2Pos.inj; assumption.
  Qed.

  Lemma find_upd_same : find_chunk (as_chunks (upd_chunk st x)) (ch_user_beg ch) = Some x.
  Proof.
    pose proof (proj2 (KEYS _ _ (proj1 (chunk_list_find st ch KEYS) IN))) as POS.
    unfold find_chunk. replace (ch_user_beg ch <=? 0) with false by (symmetry; apply Z.leb_gt; exact POS).
    unfold upd_chunk, set_chunks. cbn [as_chunks]. rewrite gadd_find, KX. destruct (PositiveMap.E.eq_dec _ _); [reflexivity| congruence].
  Qed.
  Lemma find_upd_other : forall u, u <> ch_user_beg ch -> find_chunk (as_chunks (upd_chunk st x)) u = find_chunk (as_chunks st) u.
  Proof.
    intros u NE. unfold find_chunk. destruct (u <=? 0) eqn:LE; [reflexivity|]. apply Z.leb_gt in LE.
    unfold upd_chunk, set_chunks. cbn [as_chunks]. rewrite gadd_find, KX. destruct (PositiveMap.E.eq_dec _ _) as [E|NE']; [| reflexivity].
    exfalso. apply NE. unfold ckey in E. pose proof (proj2 (KEYS _ _ (proj1 (chunk_list_find st ch KEYS) IN))) as POS. apply Z2Pos.inj; [exact LE| exact POS| symmetry; exact E].
  Qed.
End Replace.

Lemma fold_used_app : forall (F : Z -> Z) l1 l2,
  fold_right (fun q acc => F q + acc) 0 (l1 ++ l2) = fold_right (fun q acc => F q + acc) 0 l1 + fold_right (fun q acc => F q + acc) 0 l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.
Lemma fold_qb_app : forall l1 l2,
  fold_right (fun b acc => qb_size b + acc) 0 (l1 ++ l2) = fold_right (fun b acc => qb_size b + acc) 0 l1 + fold_right (fun b acc => qb_size b + acc) 0 l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.
Lemma flat_map_app' {A B} : forall (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. induction l1; intros; cbn; [reflexivity|]. rewrite IHl1, app_assoc. reflexivity. Qed.
Lemma last_app1 {A} : forall (l : list A) x d, last (l ++ [x]) d = x.
Proof. induction l; intros; cbn; [reflexivity|]. rewrite IHl. destruct (l ++ [x]) eqn:E; [| reflexivity]. destruct l; discriminate. Qed.
Lemma firstn_removelast {A} : forall (l : list A) x, firstn (length (l ++ [x]) - 1) (l ++ [x]) = l.
Proof. intros l x. rewrite length_app. cbn [length]. replace (length l + 1 - 1)%nat with (length l) by lia. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Section WFFree.
  Variables (st : astate) (ch : chunk).
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let m := ch_chunk_beg ch.
  Let st1 := upd_chunk st (qch ch).
  Hypothesis W : WF st.
  Hypothesis IN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.

  Let KEYS : keys_ok (as_chunks st). Proof. apply WF_keys. exact W. Qed.
  Let INJ : forall a b, In a (chunk_list st) -> In b (chunk_list st) -> ch_user_beg a = ch_user_beg b -> a = b.
  Proof. destruct W as (_ & _ & _ & Winj & _). exact Winj. Qed.
  Let FIND : find_chunk (as_chunks st) U = Some ch.
  Proof.
    pose proof (proj1 (chunk_list_find st ch KEYS) IN) as F. unfold find_chunk. fold U in F.
    replace (U <=? 0) with false by (symmetry; apply Z.leb_gt; exact (proj2 (KEYS _ _ F))). exact F.
  Qed.
  Let UPOS : 0 < U. Proof. exact (proj2 (KEYS _ _ (proj1 (chunk_list_find st ch KEYS) IN))). Qed.
  Let MU : m + kChunkHeaderSize = U. Proof. subst m U. unfold ch_chunk_beg. lia. Qed.
  Let PERM0 : Permutation (chunk_list st) (ch :: others st ch). Proof. apply others_perm; assumption. Qed.
  Let PERM1 : Permutation (chunk_list st1) (qch ch :: others st ch). Proof. apply upd_perm; try assumption. reflexivity. Qed.
  Let IN1 : forall y, In y (chunk_list st1) <-> y = qch ch \/ (In y (chunk_list st) /\ ch_user_beg y <> U).
  Proof.
    intros y. rewrite (Permutation_in' eq_refl PERM1). cbn [In]. rewrite (others_in st ch). split; (intros [H|H]; [left; symmetry + idtac; exact H| right; exact H]).
  Qed.
  Let F1same : find_chunk (as_chunks st1) U = Some (qch ch). Proof. apply find_upd_same; try assumption. reflexivity. Qed.
  Let F1other : forall u, u <> U -> find_chunk (as_chunks st1) u = find_chunk (as_chunks st) u.
  Proof. intros u NE. apply (find_upd_other st ch); try assumption. reflexivity. Qed.

  Let OLDQ : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) -> q + kChunkHeaderSize <> U.
  Proof.
    intros b q Hb Hq E. destruct (WF_batch st b W Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & B9). destruct (B9 q Hq) as [x [Fx Qx]].
    rewrite E, FIND in Fx. inversion Fx; subst. rewrite ALLOC in Qx. discriminate.
  Qed.
  Let FCB : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) ->
    find_chunk (as_chunks st1) (q + kChunkHeaderSize) = find_chunk (as_chunks st) (q + kChunkHeaderSize).
  Proof. intros b q Hb Hq. apply F1other. eapply OLDQ; eassumption. Qed.

  Let MNEW : ~ In m (flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st))).
  Proof. intros H. apply in_flat_map in H as [b [Hb Hq]]. exact (OLDQ b m Hb Hq MU). Qed.

  Definition sum_used (s : astate) (l : list Z) : Z :=
    fold_right (fun q acc => match find_chunk (as_chunks s) (q + kChunkHeaderSize) with Some c => ch_used c | None => 0 end + acc) 0 l.

  Lemma batch_ok_old : forall s' b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
    as_chunks s' = as_chunks st1 -> as_space_beg s' = as_space_beg st -> as_regions s' = as_regions st ->
    batch_ok st b -> batch_ok s' b.
  Proof.
    intros s' b Hb EC ES ER BO. destruct BO as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    assert (EP : forall a, in_primary s' a = in_primary st a) by (intros a; unfold in_primary; rewrite ES; reflexivity).
    assert (ECA : forall a, class_of_addr s' a = class_of_addr st a) by (intros a; unfold class_of_addr; rewrite ES; reflexivity).
    assert (ERB : forall c, region_beg s' c = region_beg st c) by (intros c; unfold region_beg; rewrite ES; reflexivity).
    assert (EGR : forall c, get_region s' c = get_region st c) by (intros c; unfold get_region; rewrite ER; reflexivity).
    unfold batch_ok. rewrite EP, ECA, !ERB, EGR, EC.
    refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj _ _)))))))).
    - rewrite B8. f_equal. apply fold_used_ext. intros q Hq. rewrite (FCB b q Hb Hq). reflexivity.
    - intros q Hq. rewrite (FCB b q Hb Hq). apply B9. exact Hq.
  Qed.

  Lemma chunk_ok_geom : forall s' y, as_space_beg s' = as_space_beg st -> as_regions s' = as_regions st -> as_sec s' = as_sec st ->
    chunk_ok st y -> chunk_ok s' y.
  Proof.
    intros s' y ES ER ESEC CO. unfold chunk_ok in *.
    assert (EP : forall a, in_primary s' a = in_primary st a) by (intros a; unfold in_primary; rewrite ES; reflexivity).
    assert (ECA : forall a, class_of_addr s' a = class_of_addr st a) by (intros a; unfold class_of_addr; rewrite ES; reflexivity).
    assert (ERB : forall c, region_beg s' c = region_beg st c) by (intros c; unfold region_beg; rewrite ES; reflexivity).
    assert (EGR : forall c, get_region s' c = get_region st c) by (intros c; unfold get_region; rewrite ER; reflexivity).
    rewrite EP, ECA, !ERB, EGR, ESEC. exact CO.
  Qed.
  Lemma chunk_ok_qch : forall s', chunk_ok s' ch -> chunk_ok s' (qch ch).
  Proof. intros s' CO. unfold chunk_ok, qch, ch_primary in *. cbn [ch_used ch_rz ch_user_beg ch_alloc_beg ch_class] in *. exact CO. Qed.

  Lemma free_chunks_in : forall y, In y (chunk_list st1) <-> y = qch ch \/ (In y (chunk_list st) /\ ch_user_beg y <> U).
  Proof. exact IN1. Qed.

  Lemma free_find : find_chunk (as_chunks st) U = Some ch.
  Proof. exact FIND. Qed.

  Section App.
    Hypothesis NN : need_new (as_tq st) = false.
    Hypothesis NOD : qc_bytes (as_tq st) + size <= as_qcache st.
    Let st' := free_app_state st ch.
    Let l := qc_list (as_tq st).
    Let lb := last l (mkQB 0 0 0 []).
    Let lb' := mkQB (qb_addr lb) (qb_size lb + size) (qb_count lb + 1) (qb_chunks lb ++ [m]).

    Let LSPLIT : exists l0, l = l0 ++ [lb] /\ qb_count lb < kBatchCount.
    Proof.
      unfold need_new in NN. subst l lb. destruct (qc_list (as_tq st)) as [|b0 r] eqn:EL; [discriminate|].
      exists (removelast (b0 :: r)). split; [apply app_removelast_last; discriminate| apply Z.leb_gt; exact NN].
    Qed.
    Let TQ' : as_tq st' = mkQC (firstn (length l - 1)%nat l ++ [lb']) (qc_bytes (as_tq st) + size).
    Proof. reflexivity. Qed.
    Let SAME : as_chunks st' = as_chunks st1 /\ as_space_beg st' = as_space_beg st /\ as_regions st' = as_regions st /\ as_sec st' = as_sec st
               /\ as_gq st' = as_gq st /\ as_cache st' = as_cache st /\ as_cache_inited st' = as_cache_inited st /\ chunk_list st' = chunk_list st1.
    Proof. repeat split; reflexivity. Qed.

    Theorem WFQ_free_app : WFQ st' [] [].
    Proof.
      destruct LSPLIT as (l0 & EL & CNT).
      assert (LST : firstn (length l - 1)%nat l ++ [lb'] = l0 ++ [lb']) by (rewrite EL at 1 2; rewrite firstn_removelast; reflexivity).
      pose proof W as WW.
      destruct WW as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wtqb & Wgqb & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys).
      assert (INlb : In lb (qc_list (as_tq st) ++ qc_list (as_gq st))) by (apply in_app_iff; left; fold l; rewrite EL; apply in_app_iff; right; left; reflexivity).
      assert (INl0 : forall b, In b l0 -> In b (qc_list (as_tq st) ++ qc_list (as_gq st))) by (intros b Hb; apply in_app_iff; left; fold l; rewrite EL; apply in_app_iff; left; exact Hb).
      unfold WFQ. fold st'. rewrite !app_nil_r.
      replace (chunk_list st') with (chunk_list st1) by reflexivity.
      replace (as_sec st') with (as_sec st) by reflexivity. replace (as_n_reserved st') with (as_n_reserved st) by reflexivity.
      replace (as_gq st') with (as_gq st) by reflexivity. replace (as_qcache st') with (as_qcache st) by reflexivity.
      replace (as_qmax st') with (as_qmax st) by reflexivity. replace (as_qmin st') with (as_qmin st) by reflexivity.
      replace (as_regions st') with (as_regions st) by reflexivity. replace (as_cache st') with (as_cache st) by reflexivity.
      replace (as_chunks st') with (as_chunks st1) by reflexivity.
      rewrite TQ', LST. cbn [qc_list qc_bytes].
      split. { intros c Hc. destruct (Wrc c Hc) as [R0 C0]. split; [destruct R0; constructor; assumption| destruct C0; constructor; assumption]. }
      split. {
        apply (Permutation_NoDup (l := carved_addr_list st)); [| exact Wnd]. apply Permutation_sym. unfold carved_addr_list.
        apply Permutation_app; [apply Permutation_refl|]. apply Permutation_app.
        - change (chunk_list st') with (chunk_list st1).
          eapply Permutation_trans; [apply Permutation_map; apply Permutation_filter; exact PERM1|].
          eapply Permutation_trans; [| apply Permutation_map; apply Permutation_filter; apply Permutation_sym; exact PERM0].
          cbn [filter]. change (ch_primary (qch ch)) with (ch_primary ch). destruct (ch_primary ch); cbn [map]; apply Permutation_refl.
        - rewrite TQ', LST. cbn [qc_list]. replace (as_gq st') with (as_gq st) by reflexivity. fold l. rewrite EL, !map_app. cbn [map qb_addr]. apply Permutation_refl. }
      split. { intros y Hy. apply IN1 in Hy as [->|[Hy _]].
        - apply chunk_ok_qch. apply (chunk_ok_geom st'); try reflexivity. exact (Wch ch IN).
        - apply (chunk_ok_geom st'); try reflexivity. exact (Wch y Hy). }
      split. { intros a b Ha Hb E. apply IN1 in Ha as [->|[Ha NA]]; apply IN1 in Hb as [->|[Hb NB]]; [reflexivity| exfalso; apply NB; rewrite <- E; reflexivity| exfalso; apply NA; exact E| exact (Winj a b Ha Hb E)]. }
      split. { unfold zlen in *. rewrite (Permutation_length (Permutation_filter _ _ _ PERM1)), <- Wsec, (Permutation_length (Permutation_filter _ _ _ PERM0)).
               cbn [filter]. change (ch_primary (qch ch)) with (ch_primary ch). destruct (ch_primary ch); reflexivity. }
      split; [exact Wsnd|]. split; [exact Wres1|]. split; [exact Wres2|].
      split. {   split.
        - intros b Hb. apply in_app_iff in Hb as [Hb|[<-|[]]].
          + apply (batch_ok_old st'); try reflexivity; [apply INl0; exact Hb|]. apply (proj1 Wtq). fold l. rewrite EL. apply in_app_iff. left. exact Hb.
          + pose proof (proj1 Wtq lb ltac:(fold l; rewrite EL; apply in_app_iff; right; left; reflexivity)) as BO.
            destruct BO as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
            unfold batch_ok. unfold lb'. cbn [qb_count qb_chunks qb_addr qb_size].
            replace (in_primary st' (qb_addr lb)) with (in_primary st (qb_addr lb)) by reflexivity.
            replace (class_of_addr st' (qb_addr lb)) with (class_of_addr st (qb_addr lb)) by reflexivity.
            replace (region_beg st' kBatchClass) with (region_beg st kBatchClass) by reflexivity.
            replace (get_region st' kBatchClass) with (get_region st kBatchClass) by reflexivity.
            replace (as_chunks st') with (as_chunks st1) by reflexivity.
            refine (conj _ (conj _ (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj _ _)))))))).
            * rewrite zlen_app, B1. reflexivity.
            * unfold kBatchCount in *. lia.
            * rewrite B8, fold_used_app. cbn [fold_right]. fold U in F1same. rewrite MU, F1same. cbn [ch_used qch]. fold size.
              rewrite (fold_used_ext (fun q => match find_chunk (as_chunks st1) (q + kChunkHeaderSize) with Some c => ch_used c | None => 0 end)
                                     (fun q => match find_chunk (as_chunks st) (q + kChunkHeaderSize) with Some c => ch_used c | None => 0 end) (qb_chunks lb));
                [lia|]. intros q Hq. rewrite (FCB lb q INlb Hq). reflexivity.
            * intros q Hq. apply in_app_iff in Hq as [Hq|[<-|[]]].
              -- rewrite (FCB lb q INlb Hq). apply B9. exact Hq.
              -- exists (qch ch). rewrite MU. fold U in F1same. split; [exact F1same| reflexivity].
        - cbn [qc_bytes qc_list]. rewrite fold_qb_app. unfold lb'. cbn [fold_right qb_size]. rewrite (proj2 Wtq). fold l. rewrite EL, fold_qb_app. cbn [fold_right]. lia. }
      split. { split; [| exact (proj2 Wgq)]. intros b Hb. apply (batch_ok_old st'); try reflexivity; [apply in_app_iff; right; exact Hb| exact (proj1 Wgq b Hb)]. }
      split. {
        apply (Permutation_NoDup (l := m :: flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st)))); [| constructor; [exact MNEW| exact Wndb]].
        fold l. rewrite EL, !flat_map_app'. unfold lb'. cbn [flat_map qb_chunks]. rewrite !app_nil_r, <- !app_assoc. cbn [app].
        rewrite (app_assoc (flat_map qb_chunks l0) (qb_chunks lb)). rewrite (app_assoc (flat_map qb_chunks l0) (qb_chunks lb)) at 1. apply Permutation_middle. }
      split. { intros y Hy Q. left. apply IN1 in Hy as [->|[Hy NE]].
        - exists lb'. split; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity|]. unfold lb'. cbn [qb_chunks]. apply in_app_iff. right. left. reflexivity.
        - destruct (Wq y Hy Q) as [b [Hb Hq]]. apply in_app_iff in Hb. fold l in Hb. rewrite EL in Hb.
          destruct Hb as [Hb|Hb]; [apply in_app_iff in Hb as [Hb|[<-|[]]]|].
          + exists b. split; [apply in_app_iff; left; apply in_app_iff; left; exact Hb| exact Hq].
          + exists lb'. split; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity|]. unfold lb'. cbn [qb_chunks]. apply in_app_iff. left. exact Hq.
          + exists b. split; [apply in_app_iff; right; exact Hb| exact Hq]. }
      split; [exact Wm0|]. split; [exact Wm31|]. split; [exact Wpc0|]. split; [exact Wpc31|]. split; [exact WlenR|]. split; [exact WlenC|].
      split; [exact Wqmax|]. split; [exact Wqmin|]. split; [exact Wqc|].
      split; [apply keys_ok_upd; [exact KEYS| exact UPOS]|]. split; [intros q0 []| intros B0 []].
    Qed.

    Theorem WF_free_app : WF st'.
    Proof.
      apply (proj2 (WF_WFQ st')). split; [exact WFQ_free_app|]. split; [| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 W))))))))))))].
      cbn [as_tq free_app_state set_tq qc_bytes]. change (as_qcache st') with (as_qcache st). exact NOD.
    Qed.
  End App.

  Section New.
    Variables (cp : Z) (rest : list Z).
    Hypothesis PCS : pc_chunks (get_pc st kBatchClass) = cp :: rest.
    Hypothesis NOD : qc_bytes (as_tq st) + size + kBatchSize <= as_qcache st.
    Hypothesis SB0 : 0 <= as_space_beg st.
    Let B := compact_to_addr st kBatchClass cp.
    Let cnt := pc_count (get_pc st kBatchClass).
    Let nb := mkQB B (size + kBatchSize) 1 [m].
    Let st' := free_new_state st ch cp rest.
    Let l := qc_list (as_tq st).

    Let CO : cache_ok st kBatchClass. Proof. apply WF_cache; [exact W| unfold kBatchClass, kNumClasses; lia]. Qed.
    Let RO : region_ok st kBatchClass. Proof. apply WF_region; [exact W| unfold kBatchClass, kNumClasses; lia]. Qed.
    Let CV : carved st kBatchClass B. Proof. apply carved_cache; [exact W| unfold kBatchClass, kNumClasses; lia| rewrite PCS; left; reflexivity]. Qed.
    Let CNT1 : cnt = zlen rest + 1. Proof. unfold cnt. rewrite (co_count _ _ CO), PCS. apply zlen_cons. Qed.
    Let LENC : length (as_cache st) = 32%nat.
    Proof. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
    Let PCc : get_pc st' kBatchClass = mkPC (cnt - 1) rest.
    Proof. unfold st', free_new_state, get_pc, set_tq, upd_chunk, set_chunks, set_pc. cbn [as_cache]. apply znth_upd_nth_eq. rewrite LENC. unfold zidx, kBatchClass. lia. Qed.
    Let PCo : forall c', 0 <= c' -> c' <> kBatchClass -> get_pc st' c' = get_pc st c'.
    Proof. intros c' H1 H2. unfold st', free_new_state, get_pc, set_tq, upd_chunk, set_chunks, set_pc. cbn [as_cache]. apply znth_upd_nth_neq. unfold zidx, kBatchClass in *. lia. Qed.
    Let TQ' : as_tq st' = mkQC (l ++ [nb]) (qc_bytes (as_tq st) + size + kBatchSize).
    Proof. reflexivity. Qed.
    Let RNG : region_beg st kBatchClass <= B /\ B + class_size kBatchClass <= region_beg st kBatchClass + kFreeArrayOffset /\ 0 < class_size kBatchClass <= 65536.
    Proof. apply carved_range; [exact W| exact CV]. Qed.

    Theorem WFQ_free_new : WFQ st' [] [].
    Proof.
      pose proof W as WW.
      destruct WW as (Wrc & Wnd & Wch & Winj & Wsec & Wsnd & Wres1 & Wres2 & Wtq & Wgq & Wtqb & Wgqb & Wndb & Wq & Wm0 & Wm31 & Wpc0 & Wpc31 & WlenR & WlenC & Wqmax & Wqmin & Wqc & Wkeys).
      pose proof RNG as RNG2. unfold B in RNG2. rewrite compact_to_addr_eq in RNG2. rewrite region_beg_eq in RNG2.
      assert (COA : class_of_addr st B = kBatchClass). { unfold B. rewrite compact_to_addr_eq. apply class_of_addr_region; unfold kBatchClass, kFreeArrayOffset in *; lia. }
      assert (INP : in_primary st B = true). { unfold B. rewrite compact_to_addr_eq. apply in_primary_region; unfold kBatchClass, kFreeArrayOffset in *; lia. }
      assert (CS24 : class_size kBatchClass = 8192) by reflexivity.
      pose proof (Nat2Z.is_nonneg (length rest)) as NNr. unfold zlen in CNT1.
      unfold WFQ. fold st'. rewrite !app_nil_r.
      replace (chunk_list st') with (chunk_list st1) by reflexivity.
      replace (as_sec st') with (as_sec st) by reflexivity. replace (as_n_reserved st') with (as_n_reserved st) by reflexivity.
      replace (as_gq st') with (as_gq st) by reflexivity. replace (as_qcache st') with (as_qcache st) by reflexivity.
      replace (as_qmax st') with (as_qmax st) by reflexivity. replace (as_qmin st') with (as_qmin st) by reflexivity.
      replace (as_regions st') with (as_regions st) by reflexivity.
      replace (as_chunks st') with (as_chunks st1) by reflexivity.
      replace (as_cache_inited st') with (as_cache_inited st) by reflexivity.
      rewrite TQ'. cbn [qc_list qc_bytes].
      split. { intros c0 Hc0. destruct (Wrc c0 Hc0) as [R0 C0]. split; [destruct R0; constructor; assumption|].
        destruct (Z.eq_dec c0 kBatchClass) as [->|NE].
        - constructor; rewrite PCc; cbn [pc_count pc_chunks].
          + unfold zlen. lia.
          + pose proof (co_bound _ _ C0) as Bd. fold cnt in Bd. change (as_cache_inited st') with (as_cache_inited st). destruct (as_cache_inited st); lia.
          + intros cp0 Hin. replace (get_region st' kBatchClass) with (get_region st kBatchClass) by reflexivity. apply (co_elems _ _ C0). rewrite PCS. right. exact Hin.
        - destruct C0 as [A0 B0 C0]; constructor; rewrite PCo by lia; assumption. }
      split. {
        apply (Permutation_NoDup (l := carved_addr_list st)); [| exact Wnd]. apply Permutation_sym. unfold carved_addr_list.
        set (L := map Z.of_nat (seq 0 32)).
        set (g := fun c0 : Z => map (compact_to_addr st c0) (rg_free_array (get_region st c0)) ++ map (compact_to_addr st c0) (pc_chunks (get_pc st c0))).
        set (g' := fun c0 : Z => map (compact_to_addr st' c0) (rg_free_array (get_region st' c0)) ++ map (compact_to_addr st' c0) (pc_chunks (get_pc st' c0))).
        change (qc_list (as_tq st')) with (l ++ [nb]). change (as_gq st') with (as_gq st). change (chunk_list st') with (chunk_list st1).
        rewrite !map_app. unfold nb at 1. cbn [map qb_addr].
        set (BT := map qb_addr l). set (BG := map qb_addr (qc_list (as_gq st))). set (IU1 := map ch_alloc_beg (filter ch_primary (chunk_list st1))).
        fold l. fold BT. set (IU := map ch_alloc_beg (filter ch_primary (chunk_list st))).
        assert (P1 : Permutation IU1 IU).
        { subst IU1 IU. eapply Permutation_trans; [apply Permutation_map; apply Permutation_filter; exact PERM1|].
          eapply Permutation_trans; [| apply Permutation_map; apply Permutation_filter; apply Permutation_sym; exact PERM0].
          cbn [filter]. change (ch_primary (qch ch)) with (ch_primary ch). destruct (ch_primary ch); cbn [map]; apply Permutation_refl. }

        assert (PB : Permutation (flat_map g' L ++ IU1 ++ (BT ++ [B]) ++ BG) (B :: flat_map g' L ++ IU1 ++ BT ++ BG)).
        { rewrite <- (app_assoc BT [B] BG). cbn [app].
          rewrite (app_assoc (flat_map g' L) IU1), (app_assoc (flat_map g' L ++ IU1) BT).
          rewrite (app_assoc (flat_map g' L) IU1 (BT ++ BG)) at 1. rewrite (app_assoc (flat_map g' L ++ IU1) BT BG).
          apply Permutation_sym. apply Permutation_middle. }
        eapply Permutation_trans; [exact PB|].
        change (B :: flat_map g' L ++ IU1 ++ BT ++ BG) with ((B :: flat_map g' L) ++ (IU1 ++ BT ++ BG)).
        apply Permutation_app; [| apply Permutation_app_tail; exact P1].
        apply (flat_map_perm_remove g g' L kBatchClass B (map (compact_to_addr st kBatchClass) (rg_free_array (get_region st kBatchClass))) (map (compact_to_addr st kBatchClass) rest)).
        - apply classes_nodup.
        - apply classes_in. unfold kBatchClass. lia.
        - intros x Hx Hne. unfold g, g'. assert (0 <= x) by (unfold L in Hx; apply in_map_iff in Hx as [y [<- _]]; lia). rewrite PCo by lia. reflexivity.
        - unfold g. rewrite PCS. reflexivity.
        - unfold g'. rewrite PCc. reflexivity. }
      split. { intros y Hy. apply IN1 in Hy as [->|[Hy _]].
        - apply chunk_ok_qch. apply (chunk_ok_geom st'); try reflexivity. exact (Wch ch IN).
        - apply (chunk_ok_geom st'); try reflexivity. exact (Wch y Hy). }
      split. { intros a b Ha Hb E. apply IN1 in Ha as [->|[Ha NA]]; apply IN1 in Hb as [->|[Hb NB]]; [reflexivity| exfalso; apply NB; rewrite <- E; reflexivity| exfalso; apply NA; exact E| exact (Winj a b Ha Hb E)]. }
      split. { unfold zlen in *. rewrite (Permutation_length (Permutation_filter _ _ _ PERM1)), <- Wsec, (Permutation_length (Permutation_filter _ _ _ PERM0)).
               cbn [filter]. change (ch_primary (qch ch)) with (ch_primary ch). destruct (ch_primary ch); reflexivity. }
      split; [exact Wsnd|]. split; [exact Wres1|]. split; [exact Wres2|].
      split. {   split.
        - intros b Hb. apply in_app_iff in Hb as [Hb|[<-|[]]].
          + apply (batch_ok_old st'); try reflexivity; [apply in_app_iff; left; exact Hb|]. apply (proj1 Wtq). exact Hb.
          + unfold batch_ok. unfold nb. cbn [qb_count qb_chunks qb_addr qb_size].
            replace (in_primary st' B) with (in_primary st B) by reflexivity.
            replace (class_of_addr st' B) with (class_of_addr st B) by reflexivity.
            replace (region_beg st' kBatchClass) with (region_beg st kBatchClass) by reflexivity.
            replace (get_region st' kBatchClass) with (get_region st kBatchClass) by reflexivity.
            replace (as_chunks st') with (as_chunks st1) by reflexivity.
            destruct CV as (_ & _ & V3 & V4 & V5). rewrite CS24 in *.
            refine (conj eq_refl (conj _ (conj INP (conj COA (conj V4 (conj V3 (conj V5 (conj _ _)))))))).
            * unfold kBatchCount. lia.
            * cbn [fold_right]. fold U in F1same. rewrite MU, F1same. cbn [ch_used qch]. fold size. unfold kBatchSize. lia.
            * intros q [<-|[]]. exists (qch ch). rewrite MU. fold U in F1same. split; [exact F1same| reflexivity].
        - cbn [qc_bytes qc_list]. rewrite fold_qb_app. unfold nb. cbn [fold_right qb_size]. rewrite (proj2 Wtq). fold l. lia. }
      split. { split; [| exact (proj2 Wgq)]. intros b Hb. apply (batch_ok_old st'); try reflexivity; [apply in_app_iff; right; exact Hb| exact (proj1 Wgq b Hb)]. }
      split. {
        apply (Permutation_NoDup (l := m :: flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st)))); [| constructor; [exact MNEW| exact Wndb]].
        fold l. rewrite !flat_map_app'. unfold nb. cbn [flat_map qb_chunks]. rewrite <- !app_assoc. cbn [app]. apply Permutation_middle. }
      split. { intros y Hy Q. left. apply IN1 in Hy as [->|[Hy NE]].
        - exists nb. split; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity|]. unfold nb. cbn [qb_chunks]. left. reflexivity.
        - destruct (Wq y Hy Q) as [b [Hb Hq]]. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
          + exists b. split; [apply in_app_iff; left; apply in_app_iff; left; exact Hb| exact Hq].
          + exists b. split; [apply in_app_iff; right; exact Hb| exact Hq]. }
      split; [exact Wm0|]. split; [exact Wm31|].
      split. { rewrite PCo by (unfold kBatchClass; lia). exact Wpc0. }
      split. { rewrite PCo by (unfold kBatchClass; lia). exact Wpc31. }
      split; [exact WlenR|].
      split. { unfold st', free_new_state, set_tq, upd_chunk, set_chunks, set_pc. cbn [as_cache]. rewrite length_upd_nth. exact WlenC. }
      split; [exact Wqmax|]. split; [exact Wqmin|]. split; [exact Wqc|].
      split; [apply keys_ok_upd; [exact KEYS| exact UPOS]|]. split; [intros q0 []| intros B0 []].
    Qed.

  End New.
End WFFree.
