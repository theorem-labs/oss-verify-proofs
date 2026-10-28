(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit AG_RefillModel AG_FreeModel AG_WFFree AG_RepQ AW_Efs AS_Rta AW_MergeBatches AW_Recycle.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xbatch (st : astate) (b : qbatch) : Prop :=
  qb_chunks b = [] /\ qb_count b = 0 /\ qb_size b = kBatchSize /\ xb_ok st (qb_addr b).

Lemma batch_ok_xb : forall st b, batch_ok st b -> xb_ok st (qb_addr b).
Proof.
  intros st b (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold xb_ok, carved. rewrite B4.
  split; [unfold kBatchClass, kNumClasses; lia|].
  split; [pose proof (class_size_table_facts kBatchClass ltac:(unfold kBatchClass; lia)) as (_ & _ & T & _); specialize (T ltac:(unfold kBatchClass; lia)); lia|].
  split; [exact B6|]. split; [exact B5| exact B7].
Qed.

Lemma fold_used_app' : forall (F : Z -> Z) l1 l2,
  fold_right (fun q acc => F q + acc) 0 (l1 ++ l2) = fold_right (fun q acc => F q + acc) 0 l1 + fold_right (fun q acc => F q + acc) 0 l2.
Proof. intros F l1 l2. induction l1 as [|x l1 IH]; cbn; [lia|]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
Lemma batch_ok_merge : forall st cur nx,
  batch_ok st cur -> batch_ok st nx -> qb_count cur + qb_count nx <= kBatchCount ->
  batch_ok st (mkQB (qb_addr cur) (qb_size cur + (qb_size nx - kBatchSize)) (qb_count cur + qb_count nx) (qb_chunks cur ++ qb_chunks nx)).
Proof.
  intros st cur nx (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9) (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9) K.
  unfold batch_ok; cbn [qb_addr qb_size qb_count qb_chunks].
  split; [unfold zlen in *; rewrite length_app; lia|]. split; [lia|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
  split; [exact C6|]. split; [exact C7|]. split; [rewrite fold_used_app', C8, N8; lia|].
  intros m Hm. apply in_app_or in Hm. destruct Hm as [Hm|Hm]; [exact (C9 m Hm)| exact (N9 m Hm)].
Qed.

Lemma flat_map_rev_perm : forall (l : list qbatch), Permutation (flat_map qb_chunks (rev l)) (flat_map qb_chunks l).
Proof.
  intros l. induction l as [|b l IH]; [reflexivity|]. cbn [rev flat_map]. rewrite flat_map_app'. cbn [flat_map]. rewrite app_nil_r.
  rewrite IH. apply Permutation_app_comm.
Qed.

(* [comment removed for export] *)
Lemma merge_aux_facts : forall st fuel cur rest rdone rex xb l' ex xb',
  merge_batches_aux fuel cur rest rdone rex xb = Some (l', ex, xb') ->
  batch_ok st cur -> Forall (batch_ok st) rest -> Forall (batch_ok st) rdone -> Forall (xbatch st) rex ->
     Forall (batch_ok st) l' /\ Forall (xbatch st) ex
  /\ Permutation (flat_map qb_chunks l') (flat_map qb_chunks (rdone ++ cur :: rest))
  /\ Permutation (map qb_addr (l' ++ ex)) (map qb_addr (rdone ++ cur :: rest ++ rex)).
Proof.
  intros st fuel. induction fuel as [|fuel IH]; intros cur rest rdone rex xb l' ex xb' H OC OR OD OX; [discriminate H|].
  cbn [merge_batches_aux] in H. destruct rest as [|nx rest'].
  - injection H as <- <- <-. cbn [rev app].
    split; [apply Forall_app; split; [apply Forall_rev; exact OD| constructor; [exact OC| constructor]]|].
    split; [apply Forall_rev; exact OX|].
    split.
    + rewrite !flat_map_app'. cbn [flat_map]. rewrite app_nil_r. apply Permutation_app_tail. apply flat_map_rev_perm.
    + rewrite !map_app, !map_rev. cbn [map].
      change (map qb_addr rdone ++ qb_addr cur :: map qb_addr rex) with (map qb_addr rdone ++ ([qb_addr cur] ++ map qb_addr rex)).
      rewrite (app_assoc (map qb_addr rdone)). apply Permutation_app; [apply Permutation_app_tail|]; symmetry; apply Permutation_rev.
  - apply Forall_cons_iff in OR. destruct OR as [ON OR'].
    destruct (Z.leb_spec (qb_count cur + qb_count nx) kBatchCount) as [LE|GT].
    + destruct (qb_size cur <? kBatchSize); [discriminate H|].
      pose proof (IH _ _ _ _ _ _ _ _ H (batch_ok_merge st cur nx OC ON LE) OR' OD) as IH'.
      destruct IH' as (F1 & F2 & P1 & P2).
      { constructor; [| exact OX]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. cbn [qb_addr]. exact (batch_ok_xb st nx ON). }
      split; [exact F1|]. split; [exact F2|]. split.
      * rewrite P1. rewrite !flat_map_app'. cbn [flat_map qb_chunks]. rewrite <- !app_assoc. reflexivity.
      * rewrite P2. rewrite !map_app. cbn [map qb_addr]. rewrite !map_app. cbn [map].
        apply Permutation_app_head. apply perm_skip. symmetry. cbn [qb_addr app]. apply Permutation_middle.
    + pose proof (IH _ _ _ _ _ _ _ _ H ON OR' ltac:(constructor; [exact OC| exact OD]) OX) as (F1 & F2 & P1 & P2).
      split; [exact F1|]. split; [exact F2|]. split.
      * rewrite P1. cbn [app flat_map]. rewrite !flat_map_app'. cbn [flat_map]. apply Permutation_app_swap_app.
      * rewrite P2. cbn [app map]. rewrite !map_app. cbn [map]. apply Permutation_middle.
Qed.

Lemma merge_facts : forall st l qb l' qb' ex xb,
  merge_batches (mkQC l qb) = Some (mkQC l' qb', ex, xb) -> Forall (batch_ok st) l ->
     Forall (batch_ok st) l' /\ Forall (xbatch st) ex
  /\ Permutation (flat_map qb_chunks l') (flat_map qb_chunks l)
  /\ Permutation (map qb_addr (l' ++ ex)) (map qb_addr l).
Proof.
  intros st l qb l' qb' ex xb H OK. unfold merge_batches in H. cbn [qc_list qc_bytes] in H. destruct l as [|b r].
  - injection H as <- <- <- <-. repeat split; constructor.
  - destruct (merge_batches_aux (S (length r)) b r [] [] 0) as [[[l1 ex1] xb1]|] eqn:E; [| discriminate H].
    injection H as <- <- <- <-. apply Forall_cons_iff in OK. destruct OK as [OB OR].
    pose proof (merge_aux_facts st _ _ _ _ _ _ _ _ _ E OB OR ltac:(constructor) ltac:(constructor)) as (F1 & F2 & P1 & P2).
    rewrite app_nil_r in P2. exact (conj F1 (conj F2 (conj P1 P2))).
Qed.

Lemma flat_map_nil_batches : forall ex, Forall (fun b => qb_chunks b = []) ex -> flat_map qb_chunks ex = [].
Proof. intros ex F. induction ex as [|b ex IH]; [reflexivity|]. apply Forall_cons_iff in F. destruct F as [E F]. cbn [flat_map]. rewrite E, (IH F). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pop.
  Variables (st : astate) (min_size : Z) (l2 ex rp : list qbatch) (b2 : Z).
  Hypothesis W : WFQ st [] [].
  Hypothesis RS : rsplit (as_gq st) min_size = Some (mkQC l2 b2, ex, rp).
  Let T := ex ++ rev rp.
  Let st' := set_gq st (mkQC l2 b2).
  Let XC := flat_map qb_chunks T.
  Let XB := map qb_addr T.

  Let gl := qc_list (as_gq st).
  Let OKG : Forall (batch_ok st) gl.
  Proof. apply (proj2 (Forall_forall _ _)). exact (proj1 (WFQ_gq st [] [] W)). Qed.

  (* [comment removed for export] *)
  Lemma rsplit_facts :
    exists lF popped, lF = popped ++ l2 /\ rp = rev popped
      /\ Forall (batch_ok st) lF /\ Forall (xbatch st) ex
      /\ Permutation (flat_map qb_chunks lF) (flat_map qb_chunks gl)
      /\ Permutation (map qb_addr (lF ++ ex)) (map qb_addr gl)
      /\ b2 = fold_right (fun b acc => qb_size b + acc) 0 l2 /\ b2 <= min_size.
  Proof.
    pose proof RS as R. unfold rsplit in R. fold gl in R.
    destruct (qc_bytes (as_gq st) <? zlen gl * kBatchSize); [discriminate R|].
    pose proof (proj2 (WFQ_gq st [] [] W)) as QB. fold gl in QB.
    assert (BS : forall l, fold_right (fun b acc => qb_size b + acc) 0 l = bsum l) by (intros l; induction l as [|x l IH]; [reflexivity|]; cbn [fold_right]; rewrite bsum_cons, IH; reflexivity).
    destruct ((zlen gl * kBatchSize <? qc_bytes (as_gq st)) && (qc_bytes (as_gq st) * 100 <? zlen gl * kBatchSize * 200)).
    - destruct (merge_batches (as_gq st)) as [[[g' ex'] xb]|] eqn:MB; [| discriminate R]. destruct g' as [lF qbF]. cbn [qc_list qc_bytes] in R.
      destruct (pop_while (S (length lF)) lF qbF min_size []) as [[[l2' b2'] rp']|] eqn:PW; [| discriminate R].
      injection R as <- <- <- <-.
      replace (as_gq st) with (mkQC gl (qc_bytes (as_gq st))) in MB by (destruct (as_gq st); reflexivity).
      pose proof (merge_facts st _ _ _ _ _ _ MB OKG) as (F1 & F2 & P1 & P2). pose proof (merge_batches_bsum _ _ _ _ _ _ MB) as (S1 & S2 & S3 & S4).
      pose proof (pop_while_shape _ _ _ _ _ _ _ _ PW) as (popped & EL & ERP & EB & LE). rewrite app_nil_r in ERP.
      exists lF, popped. split; [exact EL|]. split; [exact ERP|]. split; [exact F1|]. split; [exact F2|]. split; [exact P1|]. split; [exact P2|].
      rewrite BS. rewrite QB, BS in S2. rewrite EL, bsum_app in S1. split; [clear - S1 S2 EB; lia| exact LE].
    - cbn [qc_list qc_bytes] in R. fold gl in R.
      destruct (pop_while (S (length gl)) gl (qc_bytes (as_gq st)) min_size []) as [[[l2' b2'] rp']|] eqn:PW; [| discriminate R].
      injection R as <- <- <- <-.
      pose proof (pop_while_shape _ _ _ _ _ _ _ _ PW) as (popped & EL & ERP & EB & LE). rewrite app_nil_r in ERP.
      exists gl, popped. split; [exact EL|]. split; [exact ERP|]. split; [exact OKG|]. split; [constructor|]. split; [reflexivity|]. split; [rewrite app_nil_r; reflexivity|].
      rewrite BS. rewrite QB, BS, EL, bsum_app in EB. split; [clear - EB; lia| exact LE].
  Qed.

  Theorem WFQ_pop :
       WFQ st' XC XB
    /\ (forall b, In b (l2 ++ T) -> In (qb_addr b) (map qb_addr gl))
    /\ Forall (batch_ok st) l2 /\ Forall (fun b => batch_ok st b \/ xbatch st b) T
    /\ b2 = bsum l2 /\ b2 <= min_size
    /\ List.NoDup (map qb_addr (l2 ++ T)).
  Proof.
    destruct rsplit_facts as (lF & popped & EL & ERP & OKF & OKX & PC & PA & EB2 & LE).
    assert (ET : T = ex ++ popped) by (unfold T; rewrite ERP, rev_involutive; reflexivity).
    assert (XCE : XC = flat_map qb_chunks popped).
    { unfold XC. rewrite ET, flat_map_app', (flat_map_nil_batches ex); [reflexivity|].
      apply (proj2 (Forall_forall _ _)). intros b Hb. exact (proj1 (proj1 (Forall_forall _ _) OKX b Hb)). }
    (* [comment removed for export] *)
    assert (PCH : Permutation (flat_map qb_chunks gl) (flat_map qb_chunks l2 ++ XC)).
    { rewrite XCE, <- PC, EL, flat_map_app'. apply Permutation_app_comm. }
    assert (PAD : Permutation (map qb_addr gl) (map qb_addr l2 ++ XB)).
    { unfold XB. rewrite ET, <- PA, EL, !map_app. rewrite <- app_assoc.
      apply Permutation_trans with (map qb_addr l2 ++ map qb_addr popped ++ map qb_addr ex); [apply Permutation_app_swap_app|].
      apply Permutation_app_head. apply Permutation_app_comm. }
    pose proof W as WW.
    destruct WW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
    assert (OK2 : Forall (batch_ok st) l2) by (rewrite EL in OKF; apply Forall_app in OKF; exact (proj2 OKF)).
    assert (OKP : Forall (batch_ok st) popped) by (rewrite EL in OKF; apply Forall_app in OKF; exact (proj1 OKF)).
    split.
    { unfold st'. split. { intros c Hc. destruct (W1 c Hc) as [R0 C0]. split; [destruct R0; constructor; assumption| destruct C0; constructor; assumption]. }
      split. { (* [comment removed for export] *)
        unfold carved_addr_list in W2 |- *. cbn [as_regions as_cache as_chunks as_space_beg as_tq as_gq set_gq qc_list] in *.
        rewrite app_nil_r in W2. rewrite !map_app in W2 |- *. fold gl in W2.
        eapply Permutation_NoDup; [| exact W2]. rewrite <- !app_assoc. do 3 apply Permutation_app_head. exact PAD. }
      split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|]. split; [exact W7|]. split; [exact W8|]. split; [exact W9|].
      split. { (* [comment removed for export] *)
        split; [| exact EB2]. cbn [as_gq set_gq qc_list]. intros b Hb. exact (proj1 (Forall_forall _ _) OK2 b Hb). }
      split. { cbn [as_tq as_gq set_gq qc_list]. rewrite app_nil_r in W11. fold gl in W11. rewrite !flat_map_app' in W11 |- *.
               eapply Permutation_NoDup; [| exact W11]. rewrite <- app_assoc. apply Permutation_app_head. exact PCH. }
      split. { cbn [as_tq as_gq set_gq qc_list as_chunks]. intros ch Hin Hq. destruct (W12 ch Hin Hq) as [[b [Hb Hm]]|[]]. fold gl in Hb.
               apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; exists b; split; [apply in_or_app; left; exact Hb| exact Hm]|].
               assert (IN : In (ch_chunk_beg ch) (flat_map qb_chunks l2 ++ XC)).
               { eapply Permutation_in; [exact PCH|]. apply in_flat_map. exists b. exact (conj Hb Hm). }
               apply in_app_or in IN. destruct IN as [IN|IN]; [| right; exact IN]. left. apply in_flat_map in IN. destruct IN as [b' [Hb' Hm']].
               exists b'. split; [apply in_or_app; right; exact Hb'| exact Hm']. }
      split; [exact W13|]. split; [exact W14|]. split; [exact W15|]. split; [exact W16|]. split; [exact W17|]. split; [exact W18|].
      split; [exact W19|]. split; [exact W20|]. split; [exact W21|]. split; [exact W22|].
      split. { (* [comment removed for export] *)
        intros m Hm. rewrite XCE in Hm. apply in_flat_map in Hm. destruct Hm as [b [Hb Hmb]].
        pose proof (proj1 (Forall_forall _ _) OKP b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & B9). exact (B9 m Hmb). }
      (* [comment removed for export] *)
      intros B HB. unfold XB in HB. rewrite ET, map_app in HB. apply in_app_or in HB. destruct HB as [HB|HB]; apply in_map_iff in HB; destruct HB as [b [<- Hb]].
      - exact (proj2 (proj2 (proj2 (proj1 (Forall_forall _ _) OKX b Hb)))).
      - exact (batch_ok_xb st b (proj1 (Forall_forall _ _) OKP b Hb)). }
    split. { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PAD|]. unfold XB. rewrite <- map_app. apply in_map. exact Hb. }
    split; [exact OK2|].
    split. { rewrite ET. apply Forall_app. split; [| apply (proj2 (Forall_forall _ _)); intros b Hb; left; exact (proj1 (Forall_forall _ _) OKP b Hb)].
             apply (proj2 (Forall_forall _ _)). intros b Hb. right. exact (proj1 (Forall_forall _ _) OKX b Hb). }
    split; [rewrite EB2; clear; induction l2 as [|x l IH]; [reflexivity| cbn [fold_right]; rewrite bsum_cons, IH; reflexivity]|].
    split; [exact LE|].
    (* [comment removed for export] *)
    unfold carved_addr_list in W2. rewrite app_nil_r, !map_app in W2. fold gl in W2.
    apply NoDup_app_remove_l in W2. apply NoDup_app_remove_l in W2. apply NoDup_app_remove_l in W2.
    eapply Permutation_NoDup; [apply Permutation_sym|]. 2: exact (Permutation_NoDup PAD W2). rewrite map_app. reflexivity.
  Qed.
End Pop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition del_state (st : astate) (ch : chunk) : astate := set_chunks st (remove_chunk (as_chunks st) (ch_user_beg ch)).

Lemma find_remove_same : forall mp U, find_chunk (remove_chunk mp U) U = None.
Proof.
  intros mp U. unfold find_chunk, remove_chunk. destruct (U <=? 0); [reflexivity|]. apply PositiveMap.grs.
Qed.
Lemma find_remove_other : forall mp U u, 0 < U -> 0 < u -> u <> U -> find_chunk (remove_chunk mp U) u = find_chunk mp u.
Proof.
  intros mp U u HU Hu NE. unfold find_chunk, remove_chunk. destruct (u <=? 0); [reflexivity|]. apply PositiveMap.gro.
  unfold ckey. intros E. apply NE. apply Z2Pos.inj; assumption.
Qed.

Section Del.
  Variables (st : astate) (ch : chunk).
  Let U := ch_user_beg ch.
  Let st2 := del_state st ch.
  Hypothesis KEYS : keys_ok (as_chunks st).
  Hypothesis INJ : forall a b, In a (chunk_list st) -> In b (chunk_list st) -> ch_user_beg a = ch_user_beg b -> a = b.
  Hypothesis IN : In ch (chunk_list st).

  Lemma del_keys : keys_ok (as_chunks st2).
  Proof.
    intros k x F. unfold st2, del_state, set_chunks, remove_chunk in F. cbn [as_chunks] in F.
    destruct (PositiveMap.E.eq_dec k (ckey U)) as [->|NE]; [rewrite PositiveMap.grs in F; discriminate F|].
    rewrite PositiveMap.gro in F by exact NE. exact (KEYS _ _ F).
  Qed.
  Lemma del_upos : 0 < U. Proof. exact (proj2 (KEYS _ _ (proj1 (chunk_list_find st ch KEYS) IN))). Qed.
  Lemma del_in : forall y, In y (chunk_list st2) <-> In y (chunk_list st) /\ ch_user_beg y <> U.
  Proof.
    intros y. rewrite !chunk_list_in_iff. unfold st2, del_state, set_chunks, remove_chunk. cbn [as_chunks]. split.
    - intros [k F]. destruct (PositiveMap.E.eq_dec k (ckey U)) as [->|NE]; [rewrite PositiveMap.grs in F; discriminate F|].
      rewrite PositiveMap.gro in F by exact NE. split; [exists k; exact F|]. destruct (KEYS _ _ F) as [-> POS]. intros E. apply NE. rewrite E. reflexivity.
    - intros [[k F] NE]. exists k. destruct (KEYS _ _ F) as [-> POS]. rewrite PositiveMap.gro; [exact F|].
      unfold ckey. intros E. apply NE. apply Z2Pos.inj; [exact POS| apply del_upos| exact E].
  Qed.
  Lemma del_perm : Permutation (chunk_list st2) (others st ch).
  Proof.
    apply NoDup_Permutation; [apply chunk_list_nodup; apply del_keys| apply others_nodup; exact KEYS|].
    intros y. rewrite del_in, (others_in st ch). reflexivity.
  Qed.
  Lemma del_perm0 : Permutation (chunk_list st) (ch :: chunk_list st2).
  Proof. rewrite del_perm. apply others_perm; assumption. Qed.
  Lemma del_find_same : find_chunk (as_chunks st2) U = None.
  Proof. unfold st2, del_state, set_chunks. cbn [as_chunks]. apply find_remove_same. Qed.
  Lemma del_find_other : forall u, 0 < u -> u <> U -> find_chunk (as_chunks st2) u = find_chunk (as_chunks st) u.
  Proof. intros u Hu NE. unfold st2, del_state, set_chunks. cbn [as_chunks]. apply find_remove_other; [apply del_upos| exact Hu| exact NE]. Qed.
  Lemma del_find : find_chunk (as_chunks st) U = Some ch.
  Proof.
    pose proof (proj1 (chunk_list_find st ch KEYS) IN) as F. unfold find_chunk. fold U in F.
    replace (U <=? 0) with false by (symmetry; apply Z.leb_gt; apply del_upos). exact F.
  Qed.
End Del.

(* [comment removed for export] *)
Lemma class_of_addr_range : forall st a, 0 <= class_of_addr st a < kNumClasses.
Proof.
  intros st a. unfold class_of_addr, kNumClasses. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.shiftr (a - as_space_beg st) kRegionSizeLog) (2^5) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma xb_ok_ext : forall a b B, as_space_beg a = as_space_beg b -> as_regions a = as_regions b -> xb_ok b B -> xb_ok a B.
Proof. intros a b B. destruct a, b; cbn. intros -> -> H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DelPrim.
  Variables (st : astate) (XC XB : list Z) (ch : chunk).
  Let U := ch_user_beg ch.
  Let m := ch_chunk_beg ch.
  Let p := ch_alloc_beg ch.
  Let c := ch_class ch.
  Let st2 := del_state st ch.
  Hypothesis W : WFQ st (m :: XC) XB.
  Hypothesis IN : In ch (chunk_list st).
  Hypothesis PRIM : ch_primary ch = true.

  Let KEYS : keys_ok (as_chunks st). Proof. exact (WFQ_keys st _ _ W). Qed.
  Let INJ : forall a b, In a (chunk_list st) -> In b (chunk_list st) -> ch_user_beg a = ch_user_beg b -> a = b.
  Proof. exact (WFQ_inj st _ _ W). Qed.
  Let MU : m + kChunkHeaderSize = U. Proof. subst m U. unfold ch_chunk_beg. lia. Qed.
  Let PERM0 : Permutation (chunk_list st) (ch :: chunk_list st2). Proof. apply del_perm0; assumption. Qed.
  Let IN2 : forall y, In y (chunk_list st2) <-> In y (chunk_list st) /\ ch_user_beg y <> U. Proof. apply del_in; assumption. Qed.
  Let COK : chunk_ok st ch. Proof. exact (WFQ_chunk st _ _ ch W IN). Qed.
  (* [comment removed for export] *)
  Let MNEW : ~ In m (flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st))).
  Proof. intros H. pose proof (WFQ_qnodup st _ _ W) as ND. apply (NoDup_remove_2 _ _ _ ND). apply in_or_app. left. exact H. Qed.
  Let OLDQ : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) -> q + kChunkHeaderSize <> U.
  Proof. intros b q Hb Hq E. apply MNEW. apply in_flat_map. exists b. split; [exact Hb|]. replace m with q by (clear - E MU; lia). exact Hq. Qed.
  Let FCB : forall b q, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> In q (qb_chunks b) ->
    find_chunk (as_chunks st2) (q + kChunkHeaderSize) = find_chunk (as_chunks st) (q + kChunkHeaderSize).
  Proof.
    intros b q Hb Hq. destruct (Z.le_gt_cases (q + kChunkHeaderSize) 0) as [LE|GT].
    - unfold find_chunk. replace (q + kChunkHeaderSize <=? 0) with true by (symmetry; apply Z.leb_le; exact LE). reflexivity.
    - apply del_find_other; [exact KEYS| exact IN| exact GT| exact (OLDQ b q Hb Hq)].
  Qed.
  Let BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> batch_ok st b -> batch_ok st2 b.
  Proof.
    intros b Hb (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). unfold batch_ok. unfold st2, del_state, set_chunks.
    cbn [as_space_beg as_regions as_chunks in_primary class_of_addr region_beg get_region].
    refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj B6 (conj B7 (conj _ _)))))))).
    - rewrite B8. f_equal. apply fold_used_ext. intros q Hq. pose proof (FCB b q Hb Hq) as E. unfold st2, del_state, set_chunks in E. cbn [as_chunks] in E. rewrite E. reflexivity.
    - intros q Hq. pose proof (FCB b q Hb Hq) as E. unfold st2, del_state, set_chunks in E. cbn [as_chunks] in E. rewrite E. apply B9. exact Hq.
  Qed.

  Lemma del_class : 0 <= c < kNumClasses /\ class_size c <> 0 /\ c = class_of_addr st p /\ carved st c p.
  Proof.
    destruct COK as (K1 & K2 & K3 & K4 & K5). rewrite PRIM in K5. destruct K5 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). fold c p in P3, P4, P5, P6, P7, P8.
    pose proof (compute_req_facts (ch_used ch) ltac:(lia)) as (_ & RZ & RR & _ & RN & _).
    assert (HC : 0 <= c < kNumClasses) by (rewrite P3; apply class_of_addr_range).
    assert (NZ : class_size c <> 0) by (rewrite P1 in RN; clear - RN RZ RR P8; lia).
    split; [exact HC|]. split; [exact NZ|]. split; [exact P3|]. unfold carved. split; [exact HC|]. split; [exact NZ|]. split; [exact P6|]. split; [exact P5| exact P7].
  Qed.

  Theorem WFQ_del_prim : WFQ st2 XC (p :: XB).
  Proof.
    pose proof W as WW.
    destruct WW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
    pose proof del_class as (HC & NZ & EC & CV).
    unfold WFQ. unfold st2, del_state, set_chunks.
    cbn [as_space_beg as_regions as_cache as_cache_inited as_n_reserved as_sec as_tq as_gq as_qmax as_qmin as_qcache as_chunks].
    fold (del_state st ch). fold st2.
    split. { intros c0 Hc. destruct (W1 c0 Hc) as [R0 C0]. split; [destruct R0; constructor; assumption| destruct C0; constructor; assumption]. }
    split. { (* [comment removed for export] *)
      unfold carved_addr_list in W2 |- *.
      cbn [as_space_beg as_regions as_cache as_chunks as_tq as_gq get_region get_pc compact_to_addr region_beg] in W2 |- *.
      change (map snd (PositiveMap.elements (remove_chunk (as_chunks st) (ch_user_beg ch)))) with (chunk_list st2).
      change (map snd (PositiveMap.elements (as_chunks st))) with (chunk_list st) in W2.
      eapply Permutation_NoDup; [| exact W2]. rewrite <- !app_assoc. apply Permutation_app_head.
      rewrite (Permutation_map ch_alloc_beg (Permutation_filter ch_primary _ _ PERM0)). cbn [filter]. rewrite PRIM. cbn [map]. fold p.
      rewrite !app_assoc. apply Permutation_middle. }
    split. { intros y Hy. apply IN2 in Hy as [Hy _]. exact (W3 y Hy). }
    split. { intros a b Ha Hb. apply IN2 in Ha as [Ha _]. apply IN2 in Hb as [Hb _]. exact (W4 a b Ha Hb). }
    split. { rewrite <- W5. unfold zlen. erewrite (Permutation_length (Permutation_filter _ _ _ PERM0)). cbn [filter]. rewrite PRIM. reflexivity. }
    split; [exact W6|]. split; [exact W7|]. split; [exact W8|].
    split. { split; [| exact (proj2 W9)]. intros b Hb. apply BOK; [apply in_or_app; left; exact Hb| exact (proj1 W9 b Hb)]. }
    split. { split; [| exact (proj2 W10)]. intros b Hb. apply BOK; [apply in_or_app; right; exact Hb| exact (proj1 W10 b Hb)]. }
    split. { eapply NoDup_remove_1. exact W11. }
    split. { intros y Hy Hq. apply IN2 in Hy as [Hy NE]. destruct (W12 y Hy Hq) as [E|[E|E]]; [left; exact E| | right; exact E].
             exfalso. apply NE. rewrite <- MU, E. unfold ch_chunk_beg, kChunkHeaderSize. lia. }
    split; [exact W13|]. split; [exact W14|]. split; [exact W15|]. split; [exact W16|]. split; [exact W17|]. split; [exact W18|].
    split; [exact W19|]. split; [exact W20|]. split; [exact W21|].
    split. { exact (del_keys st ch KEYS). }
    split. { intros m' Hm'. destruct (W23 m' ltac:(right; exact Hm')) as [x [Fx Qx]]. exists x. split; [| exact Qx].
             cbn [as_chunks]. rewrite find_remove_other; [exact Fx| exact (del_upos st ch KEYS IN)| |].
             - destruct (Z.le_gt_cases (m' + kChunkHeaderSize) 0) as [LE|GT]; [| exact GT]. exfalso. unfold find_chunk in Fx.
               replace (m' + kChunkHeaderSize <=? 0) with true in Fx by (symmetry; apply Z.leb_le; exact LE). discriminate Fx.
             - intros E. apply (NoDup_remove_2 _ _ _ W11). apply in_or_app. right. replace m with m' by (clear - E MU; lia). exact Hm'. }
    intros B [<-|HB]; (apply (xb_ok_ext _ st); [reflexivity| reflexivity|]); [| exact (W24 B HB)]. unfold xb_ok. rewrite <- EC. exact CV.
  Qed.
End DelPrim.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma addr_to_compact_eq : forall st c p, (p - region_beg st c) mod 16 = 0 -> addr_to_compact st c p = (p - region_beg st c) / 16.
Proof. intros st c p Hm. unfold addr_to_compact, kCompactPtrScale. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Section Push.
  Variables (st : astate) (XC XB : list Z) (c p : Z).
  Let cp := addr_to_compact st c p.
  Let pc := get_pc st c.
  Definition push_state : astate := set_pc st c (mkPC (pc_count (get_pc st c) + 1) (addr_to_compact st c p :: pc_chunks (get_pc st c))).
  Let st' := push_state.
  Hypothesis W : WFQ st XC (p :: XB).
  Hypothesis EC : class_of_addr st p = c.
  Hypothesis INIT : as_cache_inited st = true.
  Hypothesis ROOM : pc_count (get_pc st c) + 1 <= max_count c.

  Let CV : carved st c p. Proof. rewrite <- EC. exact (WFQ_xb st _ _ p W ltac:(left; reflexivity)). Qed.
  Let HC : 0 <= c < kNumClasses. Proof. exact (proj1 CV). Qed.
  Let T : 0 <= class_size c <= 65536 /\ class_size c mod 32 = 0 /\ (1 <= c -> 32 <= class_size c)
          /\ 0 <= max_count c <= 16 /\ (1 <= c -> 2 <= max_count c) /\ max_count c mod 2 = 0.
  Proof. apply class_size_table_facts. unfold kNumClasses in HC. exact HC. Qed.
  Let AL16 : (p - region_beg st c) mod 16 = 0.
  Proof. destruct CV as (_ & NZ & _ & M & _). destruct T as (_ & M32 & _). clear - NZ M M32. Z.div_mod_to_equations. nia. Qed.
  Let CPE : cp * 16 = p - region_beg st c.
  Proof. unfold cp. rewrite addr_to_compact_eq by exact AL16. clear - AL16. Z.div_mod_to_equations. lia. Qed.
  Let CTA : compact_to_addr st c cp = p. Proof. rewrite compact_to_addr_eq. clear - CPE. lia. Qed.
  Let LENC : length (as_cache st) = 32%nat. Proof. exact (proj2 (WFQ_lens st _ _ W)). Qed.
  Let PCc : get_pc st' c = mkPC (pc_count pc + 1) (cp :: pc_chunks pc).
  Proof. unfold st', push_state, get_pc, set_pc. cbn [as_cache]. apply znth_upd_nth_eq. rewrite LENC. unfold zidx. unfold kNumClasses in HC. lia. Qed.
  Let PCo : forall c', 0 <= c' -> c' <> c -> get_pc st' c' = get_pc st c'.
  Proof. intros c' H1 H2. unfold st', push_state, get_pc, set_pc. cbn [as_cache]. apply znth_upd_nth_neq. unfold zidx. lia. Qed.

  Lemma push_facts : 0 <= cp /\ cp * 16 + class_size c <= rg_allocated_user (get_region st c) /\ (cp * 16) mod class_size c = 0 /\ compact_to_addr st c cp = p.
  Proof. destruct CV as (_ & NZ & G0 & M & LE). rewrite CPE. split; [clear - CPE G0; lia|]. split; [exact LE|]. split; [exact M| exact CTA]. Qed.

  Theorem WFQ_push : WFQ st' XC XB.
  Proof.
    pose proof W as WW.
    destruct WW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
    pose proof push_facts as (F1 & F2 & F3 & F4). pose proof (proj1 (proj2 CV)) as NZ. destruct T as (T1 & _).
    unfold WFQ.
    replace (chunk_list st') with (chunk_list st) by reflexivity. replace (as_sec st') with (as_sec st) by reflexivity.
    replace (as_n_reserved st') with (as_n_reserved st) by reflexivity. replace (as_tq st') with (as_tq st) by reflexivity.
    replace (as_gq st') with (as_gq st) by reflexivity. replace (as_qmax st') with (as_qmax st) by reflexivity.
    replace (as_qmin st') with (as_qmin st) by reflexivity. replace (as_qcache st') with (as_qcache st) by reflexivity.
    replace (as_chunks st') with (as_chunks st) by reflexivity. replace (as_regions st') with (as_regions st) by reflexivity.
    replace (as_cache_inited st') with (as_cache_inited st) by reflexivity.
    replace (get_region st') with (get_region st) by reflexivity.
    split. { intros c0 Hc0. destruct (W1 c0 Hc0) as [R0 C0]. split; [destruct R0; constructor; assumption|].
      destruct (Z.eq_dec c0 c) as [->|NE].
      - constructor; rewrite PCc; cbn [pc_count pc_chunks]; try change (get_region st') with (get_region st).
        + unfold pc. rewrite (co_count _ _ C0). rewrite zlen_cons. clear; lia.
        + change (as_cache_inited st') with (as_cache_inited st). rewrite INIT. exact ROOM.
        + intros cp0 [<-|Hin]; [| exact (co_elems _ _ C0 cp0 Hin)]. rewrite shiftl4. split; [exact F1|]. split; [clear - F2 T1 NZ; lia|]. split; [exact NZ| exact F3].
      - destruct C0 as [A0 B0 C0]; constructor; rewrite PCo by lia; assumption. }
    split. 2:{
      split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|]. split; [exact W7|]. split; [exact W8|].
      split; [exact W9|]. split; [exact W10|]. split; [exact W11|]. split; [exact W12|]. split; [exact W13|]. split; [exact W14|].
      split. { destruct (Z.eq_dec c 0) as [E|NE]; [exfalso; rewrite E in NZ; apply NZ; reflexivity| rewrite PCo by lia; exact W15]. }
      split. { destruct (Z.eq_dec c 31) as [E|NE]; [| rewrite PCo by lia; exact W16]. exfalso.
               destruct T as (_ & _ & T3 & _). pose proof (ro_alloc_le _ _ (proj1 (W1 31 ltac:(unfold kNumClasses; lia)))) as LE. rewrite W14 in LE.
               rewrite E in F2, T3. specialize (T3 ltac:(lia)). clear - F1 F2 T3 LE. lia. }
      split; [exact W17|]. split; [unfold st', push_state, set_pc; cbn [as_cache]; rewrite length_upd_nth; exact W18|].
      split; [exact W19|]. split; [exact W20|]. split; [exact W21|]. split; [exact W22|].
      split; [exact W23|]. intros B HB. apply (xb_ok_ext _ st); [reflexivity| reflexivity| exact (W24 B ltac:(right; exact HB))]. }
    (* [comment removed for export] *)
    unfold carved_addr_list in W2 |- *.
    replace (compact_to_addr st') with (compact_to_addr st) by reflexivity. replace (get_region st') with (get_region st) by reflexivity.
    replace (chunk_list st') with (chunk_list st) by reflexivity. replace (as_tq st') with (as_tq st) by reflexivity. replace (as_gq st') with (as_gq st) by reflexivity.
    set (L := map Z.of_nat (seq 0 32)) in *.
    set (g := fun c0 : Z => map (compact_to_addr st c0) (rg_free_array (get_region st c0)) ++ map (compact_to_addr st c0) (pc_chunks (get_pc st c0))) in W2.
    set (g' := fun c0 : Z => map (compact_to_addr st c0) (rg_free_array (get_region st c0)) ++ map (compact_to_addr st c0) (pc_chunks (get_pc st' c0))).
    set (IU := map ch_alloc_beg (filter ch_primary (chunk_list st))) in *.
    set (BQ := map qb_addr (qc_list (as_tq st) ++ qc_list (as_gq st))) in *.
    assert (PG : Permutation (p :: flat_map g L) (flat_map g' L)).
    { apply (flat_map_perm_remove g' g L c p (map (compact_to_addr st c) (rg_free_array (get_region st c))) (map (compact_to_addr st c) (pc_chunks pc))).
      - apply classes_nodup.
      - apply classes_in. unfold kNumClasses in HC. exact HC.
      - intros x Hx Hne. unfold g, g'. assert (0 <= x) by (unfold L in Hx; apply in_map_iff in Hx as [y [<- _]]; lia). rewrite PCo by lia. reflexivity.
      - unfold g'. rewrite PCc. cbn [pc_chunks map]. rewrite CTA. reflexivity.
      - unfold g. reflexivity. }
    eapply Permutation_NoDup; [| exact W2]. rewrite <- !app_assoc.
    apply Permutation_trans with ((p :: flat_map g L) ++ IU ++ BQ ++ XB).
    - symmetry. cbn [app]. rewrite !app_assoc. apply (Permutation_middle ((flat_map g L ++ IU) ++ BQ) XB p).
    - rewrite PG. reflexivity.
  Qed.
End Push.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma flat_map_perm_pointwise : forall (g g' : Z -> list Z) (L : list Z),
  (forall x, In x L -> Permutation (g' x) (g x)) -> Permutation (flat_map g' L) (flat_map g L).
Proof.
  intros g g' L H. induction L as [|x L IH]; [reflexivity|]. cbn [flat_map].
  apply Permutation_app; [apply H; left; reflexivity| apply IH; intros y Hy; apply H; right; exact Hy].
Qed.

Section Rta.
  Variables (st : astate) (XC XB : list Z) (c : Z).
  Let pc := get_pc st c.
  Let r := get_region st c.
  Let mc := max_count c.
  Let n := mc / 2.
  Let k := Z.to_nat n.
  Let chunks := pc_chunks pc.
  Let nf := rg_num_freed r.
  Let mfa := rg_mapped_free_array r.
  Let mfa' := rta_mfa nf n mfa.
  Definition rta_region : region := mkRegion (rg_mapped_user r) (rg_allocated_user r) (nf + n) (firstn k chunks ++ rg_free_array r) mfa'.
  Definition rta_pc : pclass := mkPC (pc_count pc - n) (skipn k chunks).
  Definition rta_maps : list mapping :=
    (if 4 * (nf + n) <=? mfa then [] else [mkMap (free_array_base st c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false]) ++ as_maps st.
  Definition rta_state : astate :=
    mkState (as_space_beg st) (as_ptr_array st) (upd_nth (as_regions st) (zidx c) rta_region) (as_cache_inited st)
            (upd_nth (as_cache st) (zidx c) rta_pc) (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st)
            (as_internal_init st) rta_maps (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
  Let st' := rta_state.
  Hypothesis W : WFQ st XC XB.
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis INIT : as_cache_inited st = true.
  Hypothesis FULL : pc_count pc = mc.
  (* [comment removed for export] *)
  Hypothesis FROOM : efs_new (nf + n) <= kFreeArraySize.

  Let T : 0 <= class_size c <= 65536 /\ class_size c mod 32 = 0 /\ (1 <= c -> 32 <= class_size c)
          /\ 0 <= max_count c <= 16 /\ (1 <= c -> 2 <= max_count c) /\ max_count c mod 2 = 0.
  Proof. apply class_size_table_facts. unfold kNumClasses in HC. lia. Qed.
  Let CO : cache_ok st c. Proof. exact (WFQ_cache st _ _ c W ltac:(unfold kNumClasses in *; lia)). Qed.
  Let RO : region_ok st c. Proof. exact (WFQ_region st _ _ c W ltac:(unfold kNumClasses in *; lia)). Qed.
  Let LENC : length (as_cache st) = 32%nat. Proof. exact (proj2 (WFQ_lens st _ _ W)). Qed.
  Let LENR : length (as_regions st) = 32%nat. Proof. exact (proj1 (WFQ_lens st _ _ W)). Qed.
  Lemma rta_region_c : get_region st' c = rta_region.
  Proof. unfold st', rta_state, get_region. cbn [as_regions]. apply znth_upd_nth_eq. rewrite LENR. unfold zidx. unfold kNumClasses in HC. lia. Qed.
  Lemma rta_region_o : forall c', 0 <= c' -> c' <> c -> get_region st' c' = get_region st c'.
  Proof. intros c' H1 H2. unfold st', rta_state, get_region. cbn [as_regions]. apply znth_upd_nth_neq. unfold zidx. lia. Qed.
  Lemma rta_pc_c : get_pc st' c = rta_pc.
  Proof. unfold st', rta_state, get_pc. cbn [as_cache]. apply znth_upd_nth_eq. rewrite LENC. unfold zidx. unfold kNumClasses in HC. lia. Qed.
  Lemma rta_pc_o : forall c', 0 <= c' -> c' <> c -> get_pc st' c' = get_pc st c'.
  Proof. intros c' H1 H2. unfold st', rta_state, get_pc. cbn [as_cache]. apply znth_upd_nth_neq. unfold zidx. lia. Qed.
  Lemma rta_same : as_space_beg st' = as_space_beg st /\ as_sec st' = as_sec st /\ as_chunks st' = as_chunks st /\ as_tq st' = as_tq st /\ as_gq st' = as_gq st
    /\ chunk_list st' = chunk_list st /\ (forall c', region_beg st' c' = region_beg st c') /\ (forall c', compact_to_addr st' c' = compact_to_addr st c')
    /\ (forall a, in_primary st' a = in_primary st a) /\ (forall a, class_of_addr st' a = class_of_addr st a)
    /\ (forall c', rg_allocated_user (get_region st' c') = rg_allocated_user (get_region st c')).
  Proof.
    repeat split; try reflexivity. intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite rta_region_c; reflexivity|].
    destruct (Z.le_gt_cases 0 c') as [LE|GT]; [rewrite (rta_region_o c' LE NE); reflexivity|].
    unfold get_region, zidx. replace (Z.to_nat c') with 0%nat by lia. destruct (Z.eq_dec c 0) as [E0|N0]; [exfalso; lia|].
    unfold st', rta_state. cbn [as_regions]. rewrite znth_upd_nth_neq; [reflexivity|]. unfold zidx. lia.
  Qed.

  Lemma rta_facts : pc_count pc = zlen chunks /\ (k <= length chunks)%nat /\ Z.of_nat k = n /\ 1 <= n /\ 2 * n = mc /\ nf = zlen (rg_free_array r)
    /\ 4 * (nf + n) <= mfa' /\ mfa <= mfa' /\ mfa' mod kFreeArrayMapSize = 0 /\ 0 <= nf /\ 0 <= mfa.
  Proof.
    destruct T as (_ & _ & _ & T4 & T5 & T6). specialize (T5 ltac:(lia)). fold mc in T4, T5, T6.
    pose proof (co_count _ _ CO) as C1. fold pc chunks in C1.
    assert (N2 : 2 * n = mc) by (unfold n; clear - T6 T4; Z.div_mod_to_equations; lia).
    assert (N1 : 1 <= n) by (clear - N2 T5; lia).
    assert (KN : Z.of_nat k = n) by (unfold k; clear - N1; lia).
    pose proof (ro_numfreed _ _ RO) as F1. pose proof (ro_fa_le _ _ RO) as F2. pose proof (ro_fa_mod _ _ RO) as F3. fold r nf mfa in F1, F2, F3.
    assert (NF0 : 0 <= nf) by (rewrite F1; unfold zlen; clear; lia).
    split; [exact C1|]. split; [unfold zlen in C1; rewrite FULL in C1; clear - C1 KN N2 T4; lia|]. split; [exact KN|]. split; [exact N1|]. split; [exact N2|]. split; [exact F1|].
    unfold mfa', rta_mfa. destruct (Z.leb_spec (4 * (nf + n)) mfa) as [LE|GT].
    - repeat split; try assumption; clear - LE F2 NF0 N1; lia.
    - unfold efs_new, round_up, kFreeArrayMapSize. clear - GT F2 F3 NF0 N1. Z.div_mod_to_equations. repeat split; lia.
  Qed.

  Theorem WFQ_rta : WFQ st' XC XB.
  Proof.
    pose proof rta_facts as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    pose proof rta_same as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11).
    pose proof W as WW.
    destruct WW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19 & W20 & W21 & W22 & W23 & W24).
    destruct T as (T1 & T2 & T3 & T4 & T5 & T6). pose proof (proj1 (proj2 (proj2 (co_elems _ _ CO _ ltac:(idtac))))) as NZf || idtac.
    assert (INch : forall cp, In cp (skipn k chunks) \/ In cp (firstn k chunks) -> In cp chunks).
    { intros cp H. rewrite <- (firstn_skipn k chunks). apply in_app_iff. clear - H. tauto. }
    unfold WFQ. rewrite !S6, !S2, !S3, !S4, !S5.
    replace (as_n_reserved st') with (as_n_reserved st) by reflexivity. replace (as_qmax st') with (as_qmax st) by reflexivity.
    replace (as_qmin st') with (as_qmin st) by reflexivity. replace (as_qcache st') with (as_qcache st) by reflexivity.
    split.
    { intros c0 Hc0. destruct (W1 c0 Hc0) as [R0 C0]. unfold kNumClasses in Hc0, HC. destruct (Z.eq_dec c0 c) as [->|NE].
      - split.
        + destruct RO as [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12]; constructor; rewrite rta_region_c;
            cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array rta_region]; fold r nf mfa; try assumption.
          * rewrite zlen_app, (zlen_firstn k chunks Q2), Q3, <- Q6. clear; lia.
          * unfold mfa', rta_mfa. fold r mfa in X11. destruct (4 * (nf + n) <=? mfa); [exact X11| exact FROOM].
          * intros cp Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [| exact (X12 cp Hin)].
            pose proof (co_elems _ _ CO cp (INch cp (or_intror Hin))) as E. fold r in E. exact E.
        + destruct CO as [Y1 Y2 Y3]; constructor; rewrite rta_pc_c; cbn [pc_count pc_chunks rta_pc].
          * fold pc chunks in Y1. rewrite zlen_skipn, Nat.min_l by exact Q2. rewrite Q3, Y1. reflexivity.
          * change (as_cache_inited st') with (as_cache_inited st). rewrite INIT. rewrite INIT in Y2. fold pc mc in Y2 |- *. clear - Y2 Q4 Q5; lia.
          * intros cp Hin. rewrite rta_region_c. cbn [rg_allocated_user rta_region]. pose proof (Y3 cp (INch cp (or_introl Hin))) as E. fold r in E. exact E.
      - split.
        + destruct R0; constructor; rewrite (rta_region_o c0) by (clear - Hc0 NE; lia); assumption.
        + destruct C0 as [Y1 Y2 Y3]; constructor; rewrite (rta_pc_o c0) by (clear - Hc0 NE; lia); [exact Y1| change (as_cache_inited st') with (as_cache_inited st); exact Y2|].
          rewrite (rta_region_o c0) by (clear - Hc0 NE; lia). exact Y3. }
    split. 2:{
      split. { intros x Hx. pose proof (W3 x Hx) as CK. unfold chunk_ok in CK |- *. rewrite !S9, !S10, !S7, !S11. exact CK. }
      split; [exact W4|]. split; [exact W5|]. split; [exact W6|]. split; [exact W7|]. split; [exact W8|].
      assert (QOK : forall q, qcache_ok st q -> qcache_ok st' q).
      { intros q [X1 X2]. split; [| exact X2]. intros b Hb. pose proof (X1 b Hb) as BO. unfold batch_ok in BO |- *. rewrite !S9, !S10, !S7, !S11. exact BO. }
      split; [apply QOK; exact W9|]. split; [apply QOK; exact W10|]. split; [exact W11|]. split; [exact W12|].
      unfold kNumClasses in HC.
      assert (N31 : c <> 31).
      { intros E. specialize (T5 ltac:(clear - HC; lia)). fold mc in T5. assert (Z0 : pc_count pc = 0) by (unfold pc; rewrite E; exact W16). clear - FULL T5 Z0. lia. }
      split; [rewrite (rta_region_o 0) by (clear - HC; lia); exact W13|].
      split; [rewrite (rta_region_o 31) by (clear - HC N31; lia); exact W14|].
      split; [rewrite (rta_pc_o 0) by (clear - HC; lia); exact W15|].
      split; [rewrite (rta_pc_o 31) by (clear - HC N31; lia); exact W16|].
      split; [unfold st', rta_state; cbn [as_regions]; rewrite length_upd_nth; exact W17|].
      split; [unfold st', rta_state; cbn [as_cache]; rewrite length_upd_nth; exact W18|].
      split; [exact W19|]. split; [exact W20|]. split; [exact W21|]. split; [exact W22|]. split; [exact W23|].
      intros B HB. pose proof (W24 B HB) as XB0. unfold xb_ok, carved in XB0 |- *. rewrite !S10, !S7, !S11. exact XB0. }
    (* [comment removed for export] *)
    unfold carved_addr_list in W2 |- *. rewrite !S6, !S4, !S5.
    replace (compact_to_addr st') with (compact_to_addr st) by reflexivity.
    set (L := map Z.of_nat (seq 0 32)) in *.
    set (g := fun c0 : Z => map (compact_to_addr st c0) (rg_free_array (get_region st c0)) ++ map (compact_to_addr st c0) (pc_chunks (get_pc st c0))) in W2.
    set (g' := fun c0 : Z => map (compact_to_addr st c0) (rg_free_array (get_region st' c0)) ++ map (compact_to_addr st c0) (pc_chunks (get_pc st' c0))).
    eapply Permutation_NoDup; [| exact W2]. apply Permutation_app_tail. symmetry. apply Permutation_app_tail. apply flat_map_perm_pointwise.
    intros x Hx. unfold g, g'. assert (X0 : 0 <= x) by (unfold L in Hx; apply in_map_iff in Hx as [y [<- _]]; lia).
    destruct (Z.eq_dec x c) as [->|NE]; [| rewrite (rta_region_o x), (rta_pc_o x) by (clear - X0 NE; lia); reflexivity].
    rewrite rta_region_c, rta_pc_c. cbn [rg_free_array rta_region pc_chunks rta_pc]. fold pc chunks r.
    rewrite !map_app. rewrite <- (firstn_skipn k chunks) at 3. rewrite map_app.
    rewrite <- !app_assoc. apply Permutation_trans with (map (compact_to_addr st c) (firstn k chunks) ++ map (compact_to_addr st c) (rg_free_array r) ++ map (compact_to_addr st c) (skipn k chunks)); [reflexivity|].
    rewrite (app_assoc (map _ (firstn k chunks))). rewrite (Permutation_app_comm (map _ (firstn k chunks))). rewrite <- app_assoc. reflexivity.
  Qed.
End Rta.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma upd_nth_twice {A} : forall (l : list A) i (x y : A), upd_nth (upd_nth l i x) i y = upd_nth l i y.
Proof. intros l. induction l as [|a l IH]; intros [|i] x y; cbn; [reflexivity| reflexivity| reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma znth_upd_nth_eq' {A} : forall (l : list A) i (x d : A), (i < length l)%nat -> znth (upd_nth l i x) i d = x.
Proof. intros. apply znth_upd_nth_eq. assumption. Qed.

Section CacheDeallocEval.
  Variables (stA st : astate) (c p : Z).
  Hypothesis SBS : same_but_shadow stA st.
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis INIT : as_cache_inited st = true.
  Hypothesis LENC : length (as_cache st) = 32%nat.
  Hypothesis LENR : length (as_regions st) = 32%nat.

  Let CC : (c =? 0) || (kNumClasses <=? c) = false.
  Proof. apply Bool.orb_false_iff. split; [apply Z.eqb_neq; lia| apply Z.leb_gt; lia]. Qed.

  (* [comment removed for export] *)
  Lemma cache_dealloc_eval_push : pc_count (get_pc st c) < max_count c ->
    exists stA', cache_dealloc stA c p = Some (stA', []) /\ same_but_shadow stA' (push_state st c p).
  Proof.
    intros LT. destruct stA as [sb pa rg ci ca nr sc cm tq gq ii mp shA env trA qx qn qc0], st as [sb' pa' rg' ci' ca' nr' sc' cm' tq' gq' ii' mp' sh env' tr qx' qn' qc'].
    unfold same_but_shadow in SBS. cbn in SBS. destruct SBS as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
    cbn in INIT. subst ci'. unfold cache_dealloc. rewrite CC. unfold ensure_cache_inited. cbn [as_cache_inited].
    unfold get_pc in LT |- *. cbn [as_cache] in LT |- *.
    replace (pc_count (znth ca' (zidx c) pclass0) =? max_count c) with false by (symmetry; apply Z.eqb_neq; clear - LT; lia).
    eexists. split; [reflexivity|]. unfold push_state, set_pc, get_pc, addr_to_compact, region_beg. cbn. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cache_dealloc_eval_drain :
    pc_count (get_pc st c) = max_count c ->
    efs_new (rg_num_freed (get_region st c) + max_count c / 2) <= kFreeArraySize ->
    (* [comment removed for export] *)
    (let r := get_region st c in let cur := free_array_base st c + rg_mapped_free_array r in
     let sz := efs_new (rg_num_freed r + max_count c / 2) - rg_mapped_free_array r in
     rg_mapped_free_array r < 4 * (rg_num_freed r + max_count c / 2) ->
     Z.land cur 7 = 0 /\ addr_is_in_mem cur = true /\ Z.land sz 7 = 0 /\ addr_is_in_mem (cur + sz - 8) = true) ->
    exists stA' ev, cache_dealloc stA c p = Some (stA', ev) /\ same_but_shadow stA' (push_state (rta_state st c) c p).
  Proof.
    intros FULL FROOM GEO.
    pose proof (class_size_table_facts c ltac:(unfold kNumClasses in HC; lia)) as (_ & _ & _ & T4 & T5 & T6). specialize (T5 ltac:(lia)).
    assert (N2 : 2 * (max_count c / 2) = max_count c) by (clear - T6 T4; Z.div_mod_to_equations; lia).
    destruct stA as [sb pa rg ci ca nr sc cm tq gq ii mp shA env trA qx qn qc0], st as [sb' pa' rg' ci' ca' nr' sc' cm' tq' gq' ii' mp' sh env' tr qx' qn' qc'].
    unfold same_but_shadow in SBS. cbn in SBS. destruct SBS as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
    cbn in INIT, LENC, LENR. subst ci'. unfold get_pc, get_region, free_array_base, region_beg in FULL, FROOM, GEO |- *. cbn [as_cache as_regions as_space_beg] in FULL, FROOM, GEO |- *.
    unfold cache_dealloc. rewrite CC. unfold ensure_cache_inited, get_pc. cbn [as_cache_inited as_cache].
    rewrite FULL, Z.eqb_refl. replace (max_count c <? max_count c / 2) with false by (symmetry; apply Z.ltb_ge; clear - N2 T5; lia).
    unfold return_to_allocator, get_region, set_pc. cbn [as_regions].
    unfold ensure_free_array_space, get_region, free_array_base, region_beg. cbn [as_regions as_space_beg].
    set (r := znth rg' (zidx c) region0) in *. set (n := max_count c / 2) in *.
    unfold push_state, rta_state, rta_maps, rta_pc, rta_region, get_pc, get_region, free_array_base, region_beg, addr_to_compact, set_pc, set_region, rta_mfa.
    cbn [as_cache as_regions as_space_beg as_ptr_array as_cache_inited as_n_reserved as_sec as_chunks as_tq as_gq as_internal_init as_maps as_shadow as_env as_track_shadow as_qmax as_qmin as_qcache].
    fold r n. rewrite FULL.
    assert (IDX : (zidx c < length ca')%nat) by (rewrite LENC; unfold zidx; unfold kNumClasses in HC; lia).
    destruct (Z.leb_spec (4 * (rg_num_freed r + n)) (rg_mapped_free_array r)) as [LE|GT].
    - replace ((rg_num_freed r + n) * 4 <=? rg_mapped_free_array r) with true by (symmetry; apply Z.leb_le; clear - LE; lia).
      cbn [app]. do 2 eexists. split; [reflexivity|].
      unfold same_but_shadow, region_beg, get_pc, addr_to_compact.
      cbn [as_cache as_regions as_space_beg as_ptr_array as_cache_inited as_n_reserved as_sec as_chunks as_tq as_gq as_internal_init as_maps as_shadow as_env as_track_shadow as_qmax as_qmin as_qcache].
      rewrite !(znth_upd_nth_eq' ca' (zidx c)) by exact IDX. cbn [pc_count pc_chunks]. rewrite !upd_nth_twice.
      repeat split; reflexivity.
    - replace ((rg_num_freed r + n) * 4 <=? rg_mapped_free_array r) with false by (symmetry; apply Z.leb_gt; clear - GT; lia).
      replace (round_up ((rg_num_freed r + n) * 4) kFreeArrayMapSize) with (efs_new (rg_num_freed r + n)) by (unfold efs_new; f_equal; clear; lia).
      replace (kFreeArraySize <? efs_new (rg_num_freed r + n)) with false by (symmetry; apply Z.ltb_ge; exact FROOM).
      unfold map_fixed, add_map. cbn [as_space_beg as_ptr_array as_regions as_cache_inited as_cache as_n_reserved as_sec as_chunks as_tq as_gq as_internal_init as_maps as_shadow as_env as_track_shadow as_qmax as_qmin as_qcache].
      destruct (GEO GT) as (G1 & G2 & G3 & G4).
      destruct (poison_shadow_some
                  (mkState sb' pa' rg' true (upd_nth ca' (zidx c) (mkPC (max_count c - n) (skipn (Z.to_nat n) (pc_chunks (znth ca' (zidx c) pclass0)))))
                           nr' sc' cm' tq' gq' ii'
                           (mkMap (sb' + Z.shiftl c kRegionSizeLog + kFreeArrayOffset + rg_mapped_free_array r) (efs_new (rg_num_freed r + n) - rg_mapped_free_array r) (MkFreeArrayMap c) PROT_RW false :: mp')
                           shA env' trA qx' qn' qc')
                  _ _ kAsanHeapLeftRedzoneMagic G1 G2 G3 G4) as (st2 & ev2 & EPS & SB2).
      rewrite EPS. destruct st2 as [sb2 pa2 rg2 ci2 ca2 nr2 sc2 cm2 tq2 gq2 ii2 mp2 sh2 env2 tr2 qx2 qn2 qc2]. unfold same_but_shadow in SB2. cbn in SB2.
      destruct SB2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16).
      unfold set_region, get_region. cbn [as_regions as_space_beg as_ptr_array as_cache_inited as_cache as_n_reserved as_sec as_chunks as_tq as_gq as_internal_init as_maps as_shadow as_env as_track_shadow as_qmax as_qmin as_qcache].
      do 2 eexists. split; [reflexivity|].
      assert (IDXR : (zidx c < length rg')%nat) by (rewrite LENR; unfold zidx; unfold kNumClasses in HC; lia).
      unfold same_but_shadow, region_beg, get_pc, addr_to_compact.
      cbn [as_cache as_regions as_space_beg as_ptr_array as_cache_inited as_n_reserved as_sec as_chunks as_tq as_gq as_internal_init as_maps as_shadow as_env as_track_shadow as_qmax as_qmin as_qcache].
      subst sb2 pa2 rg2 ci2 ca2 nr2 sc2 cm2 tq2 gq2 ii2 mp2 env2 qx2 qn2 qc2.
      rewrite !(znth_upd_nth_eq' rg' (zidx c)) by exact IDXR. cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array].
      rewrite !(znth_upd_nth_eq' ca' (zidx c)) by exact IDX. cbn [pc_count pc_chunks]. rewrite !upd_nth_twice.
      repeat split; reflexivity.
  Qed.
End CacheDeallocEval.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land7_round_up8 : forall x, 0 <= x -> Z.land (round_up x 8) 7 = 0.
Proof.
  intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by (unfold round_up; Z.div_mod_to_equations; nia). change (2 ^ 3) with 8.
  unfold round_up. apply Z_mod_mult.
Qed.

Section RecyclePrimEval.
  Variables (stA st : astate) (XC XB : list Z) (ch : chunk).
  Let U := ch_user_beg ch.
  Let m := ch_chunk_beg ch.
  Let p := ch_alloc_beg ch.
  Let c := ch_class ch.
  Let stD := del_state st ch.
  Hypothesis SBS : same_but_shadow stA st.
  Hypothesis W : WFQ st (m :: XC) XB.
  Hypothesis IN : In ch (chunk_list st).
  Hypothesis PRIM : ch_primary ch = true.
  Hypothesis QUAR : ch_state ch = CQuarantine.
  Hypothesis INIT : as_cache_inited st = true.
  (* [comment removed for export] *)
  Hypothesis GEOU : Z.land U 7 = 0 /\ addr_is_in_mem U = true /\ addr_is_in_mem (U + round_up (ch_used ch) 8 - 8) = true.

  Let KEYS : keys_ok (as_chunks st). Proof. exact (WFQ_keys st _ _ W). Qed.
  Let COK : chunk_ok st ch. Proof. exact (WFQ_chunk st _ _ ch W IN). Qed.
  Let LENC : length (as_cache st) = 32%nat. Proof. exact (proj2 (WFQ_lens st _ _ W)). Qed.
  Let LENR : length (as_regions st) = 32%nat. Proof. exact (proj1 (WFQ_lens st _ _ W)). Qed.

  (* [comment removed for export] *)
  Lemma prim_chunk_geom :
       1 <= c < kNumClasses /\ 32 <= class_size c <= 65536 /\ c = class_of_addr st m /\ in_primary st m = true
    /\ region_beg st c <= p /\ p + class_size c <= region_beg st c + rg_allocated_user (get_region st c)
    /\ rg_allocated_user (get_region st c) <= rg_mapped_user (get_region st c)
    /\ (p - region_beg st c) mod class_size c = 0 /\ p <= m /\ m + kChunkHeaderSize = U /\ U = p + ch_rz ch /\ 16 <= ch_rz ch /\ m < p + class_size c
    /\ (m - region_beg st c) / class_size c * class_size c = p - region_beg st c.
  Proof.
    destruct COK as (K1 & K2 & K3 & K4 & K5). rewrite PRIM in K5. destruct K5 as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). fold c p in P3, P4, P5, P6, P7, P8.
    pose proof (compute_req_facts (ch_used ch) ltac:(lia)) as (_ & RZ & RR & _ & RN & _). rewrite P1 in RN. rewrite <- K3 in RZ, RN.
    assert (HC : 0 <= c < kNumClasses) by (rewrite P3; apply class_of_addr_range).
    pose proof (class_size_table_facts c ltac:(unfold kNumClasses in HC; lia)) as (T1 & T2 & T3 & _).
    assert (NZ : class_size c <> 0) by (clear - RN RZ RR P8; lia).
    assert (C1 : 1 <= c) by (destruct (Z.eq_dec c 0) as [E|NE]; [exfalso; apply NZ; rewrite E; reflexivity| clear - HC NE; lia]).
    specialize (T3 C1).
    assert (MU : m + kChunkHeaderSize = U) by (unfold m, U, ch_chunk_beg; lia).
    assert (UP : U = p + ch_rz ch) by (unfold U, p; exact K4).
    assert (PM : p <= m /\ m < p + class_size c) by (unfold kChunkHeaderSize in MU; clear - MU UP RZ RN RR P8; lia).
    pose proof (ro_alloc_le _ _ (WFQ_region st _ _ c W HC)) as AL. pose proof (ro_mapped_bound _ _ (WFQ_region st _ _ c W HC)) as MB.
    assert (DIV : (m - region_beg st c) / class_size c * class_size c = p - region_beg st c).
    { pose proof (Z.div_mod (p - region_beg st c) (class_size c) NZ) as DM. rewrite P5, Z.add_0_r in DM.
      set (j := (p - region_beg st c) / class_size c) in DM.
      replace (m - region_beg st c) with (j * class_size c + (m - p)) by (clear - DM PM; lia).
      rewrite Z.div_add_l by exact NZ. rewrite Z.div_small by (clear - PM; lia). clear - DM; lia. }
    assert (CM : c = class_of_addr st m).
    { symmetry. replace m with (region_beg st c + (m - region_beg st c)) by lia. apply class_of_addr_region; [unfold kNumClasses in HC; exact HC|].
      unfold kUserMapSize, kFreeArrayOffset in MB. clear - PM P6 P7 AL MB. lia. }
    assert (IPM : in_primary st m = true).
    { replace m with (region_beg st c + (m - region_beg st c)) by lia. apply in_primary_region; [unfold kNumClasses in HC; exact HC|].
      unfold kUserMapSize, kFreeArrayOffset in MB. clear - PM P6 P7 AL MB. lia. }
    split; [exact (conj C1 (proj2 HC))|]. split; [clear - T1 T3; lia|]. split; [exact CM|]. split; [exact IPM|].
    split; [clear - P6; lia|]. split; [clear - P7; lia|]. split; [exact AL|]. split; [exact P5|]. split; [exact (proj1 PM)|]. split; [exact MU|].
    split; [exact UP|]. split; [clear - RZ; lia|]. split; [exact (proj2 PM)| exact DIV].
  Qed.

  (* [comment removed for export] *)
  Definition rec_prim_state : astate :=
    push_state (if pc_count (get_pc st c) =? max_count c then rta_state stD c else stD) c p.

  Lemma cb_recycle_prim_eval :
    (pc_count (get_pc st c) = max_count c -> efs_new (rg_num_freed (get_region st c) + max_count c / 2) <= kFreeArraySize) ->
    (pc_count (get_pc st c) = max_count c ->
     let r := get_region st c in let cur := free_array_base st c + rg_mapped_free_array r in
     let sz := efs_new (rg_num_freed r + max_count c / 2) - rg_mapped_free_array r in
     rg_mapped_free_array r < 4 * (rg_num_freed r + max_count c / 2) ->
     Z.land cur 7 = 0 /\ addr_is_in_mem cur = true /\ Z.land sz 7 = 0 /\ addr_is_in_mem (cur + sz - 8) = true) ->
    exists stA' ev, cb_recycle stA m = Some (stA', ev) /\ same_but_shadow stA' rec_prim_state.
  Proof.
    intros FROOM GEO.
    pose proof prim_chunk_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
    destruct GEOU as (A1 & A2 & A3).
    pose proof (del_find st ch KEYS IN) as FIND. fold U in FIND.
    pose proof (sbs_fields _ _ SBS) as SF || idtac.
    pose proof SBS as SB. unfold same_but_shadow in SB. destruct SB as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16).
    unfold cb_recycle.
    replace (find_chunk (as_chunks stA) (m + kChunkHeaderSize)) with (Some ch) by (rewrite E8, G10; symmetry; exact FIND).
    rewrite QUAR.
    replace (in_primary stA m) with true by (unfold in_primary; rewrite E1; symmetry; exact G4).
    replace (class_of_addr stA m) with c by (unfold class_of_addr; rewrite E1; exact G3).
    replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; clear - G1; lia).
    assert (ERB : region_beg stA c = region_beg st c) by (unfold region_beg; rewrite E1; reflexivity).
    assert (EGR : get_region stA c = get_region st c) by (unfold get_region; rewrite E3; reflexivity).
    rewrite ERB, EGR, G14.
    replace (rg_mapped_user (get_region st c) <? ((m - region_beg st c) / class_size c + 1) * class_size c) with false.
    2: { symmetry. apply Z.ltb_ge. rewrite Z.mul_add_distr_r, G14. clear - G6 G7; lia. }
    replace (region_beg st c + (p - region_beg st c)) with p by (clear; lia).
    change (ch_alloc_beg ch) with p. rewrite Z.eqb_refl. cbn [negb].
    assert (U0 : 0 <= ch_used ch) by (pose proof COK as CK; destruct CK as (K1 & _); clear - K1; lia).
    destruct (poison_shadow_some stA U (round_up (ch_used ch) 8) kAsanHeapLeftRedzoneMagic A1 A2 (land7_round_up8 _ U0) A3) as (st1 & ev1 & EPS & SB1).
    change (ch_user_beg ch) with U. rewrite EPS.
    (* [comment removed for export] *)
    assert (SBD : same_but_shadow (set_chunks st1 (remove_chunk (as_chunks st1) U)) stD).
    { pose proof (sbs_trans _ _ _ SB1 SBS) as X. unfold stD, del_state. fold U. destruct st1, st; unfold same_but_shadow in X |- *; cbn in X |- *.
      destruct X as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->). repeat split; reflexivity. }
    assert (INITD : as_cache_inited stD = true) by exact INIT.
    assert (LENCD : length (as_cache stD) = 32%nat) by exact LENC. assert (LENRD : length (as_regions stD) = 32%nat) by exact LENR.
    unfold rec_prim_state. change (get_pc st c) with (get_pc stD c) in *. change (get_region st c) with (get_region stD c) in FROOM, GEO. change (free_array_base st c) with (free_array_base stD c) in GEO.
    destruct (Z.eqb_spec (pc_count (get_pc stD c)) (max_count c)) as [FULL|NF].
    - destruct (cache_dealloc_eval_drain _ stD c p SBD G1 INITD LENCD LENRD FULL (FROOM FULL) (GEO FULL)) as (st3 & ev3 & E & SB3).
      rewrite E. do 2 eexists. split; [reflexivity| exact SB3].
    - pose proof (co_bound _ _ (WFQ_cache st _ _ c W ltac:(clear - G1; lia))) as B. rewrite INIT in B.
      assert (B' : pc_count (get_pc stD c) <= max_count c) by exact B.
      assert (LT : pc_count (get_pc stD c) < max_count c) by (clear - B' NF; lia).
      destruct (cache_dealloc_eval_push _ stD c p SBD G1 INITD LENCD LENRD LT) as (st3 & E & SB3).
      rewrite E. do 2 eexists. split; [reflexivity| exact SB3].
  Qed.
End RecyclePrimEval.
