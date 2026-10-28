(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freestmt RT_freeD RT_freeF RT_freeG RT_freeI RT_freeS RT_freeT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma pe_n : forall Σ M n, rt_wf0 Σ -> qent_ok Σ (M, n) -> 1 <= n <= 2 ^ 28.
Proof.
  intros Σ M n HW [(c & i & Hc & Hi & _)|(t & Ht & Htq & Htn & _)]; cbn [snd] in *.
  - pose proof (pq_fit Σ c i n HW Hc Hi) as (F1 & F2). pose proof (ClassSize_range c Hc) as ((_ & CS2) & _). pose proof (rz_facts n) as (_ & R).
    clear - F1 F2 CS2 R. lia.
  - pose proof HW as (_ & _ & _ & (_ & _ & _ & SF & _ & _ & SQ) & _). pose proof (proj1 (Forall_forall _ _) SF t Ht) as (X & _).
    pose proof (proj1 (Forall_forall _ _) SQ t Ht Htq) as Y. rewrite Htn in X, Y. lia.
Qed.

Lemma pe_qok : forall Σ Σ' M n, qent_ok Σ (M, n) -> l_SB (lay Σ') = l_SB (lay Σ) -> sec Σ' = sec Σ ->
  (forall c i st, nth_error (r_st (pr Σ c)) i = Some (CkQuar st) -> nth_error (r_st (pr Σ' c)) i = Some (CkQuar st)) ->
  qent_ok Σ' (M, n).
Proof.
  intros Σ Σ' M n [(c & i & Hc & Hi & E)|X] ESB ES Hst; [left|right; rewrite ES; exact X].
  exists c, i. split; [exact Hc|]. split; [exact (Hst c i _ Hi)|]. rewrite ESB. exact E.
Qed.

Theorem app_wfx_e : forall (Σ1 : rtsA) M n (pre : list (Z * list (Z * Z))) j0 (ents : list (Z * Z)), rt_wf0 Σ1 -> pend_e Σ1 M n ->
  ql Σ1 = pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents)] -> (length ents < 1021)%nat ->
  rt_wfx (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])]))
  /\ rt_count (set_ql Σ1 (pre ++ [(p_abeg (l_SB (lay Σ1)) 24 j0, ents ++ [(M, n)])])).
Proof.
  intros Σ1 M n pre j0 ents HW HP HQL HL. pose proof HP as (QE & FR & RC1 & RC2). pose proof (pe_n Σ1 M n HW QE) as Hn.
  pose proof HW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
  unfold qents in Q6, Q7, FR, RC1, RC2. rewrite HQL in Q1, Q3, Q4, Q5, Q6, Q7, Q8, FR, RC1, RC2. rewrite qents_app in Q6, Q7, FR, RC1, RC2.
  split.
  { split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split.
  { unfold quar_wfx. cbn [set_ql ql qg pr lay]. split.
    { rewrite qbytes_app_ent; cbn [snd]. clear - Q1 Hn. unfold QMAX_L in *. lia. }
    split; [exact Q2|].
    split; [rewrite Forall_app in Q3 |- *; destruct Q3 as [Q3a Q3b]; rewrite Forall_app in Q3a |- *; destruct Q3a as [Q3a Q3c]; split; [split; [exact Q3a|]|exact Q3b];
            inversion Q3c as [|? ? X _]; subst; constructor; [exact X | constructor]|].
    split; [rewrite !map_app in Q4 |- *; cbn [map fst] in Q4 |- *; exact Q4|].
    split; [rewrite Forall_app in Q5 |- *; destruct Q5 as [Q5a Q5b]; rewrite Forall_app in Q5a |- *; destruct Q5a as [Q5a Q5c]; split; [split; [exact Q5a|]|exact Q5b];
            constructor; [cbn [snd]; rewrite length_app; cbn [length]; lia | constructor]|].
    unfold qents. cbn [set_ql ql qg]. rewrite qents_app_snoc. split; [|split].
    - rewrite Forall_app in Q6 |- *. destruct Q6 as [Q6a Q6b]. rewrite Forall_app in Q6b. destruct Q6b as [Q6b Q6c].
      split; [exact Q6a|]. rewrite Forall_app. split; [exact Q6b|]. constructor; [|exact Q6c].
      exact (pe_qok Σ1 _ M n QE eq_refl eq_refl (fun c i st H => H)).
    - rewrite !map_app in Q7 |- *. cbn [map fst] in Q7 |- *. rewrite !map_app in FR. rewrite app_assoc in Q7, FR |- *. apply nodup_insert; [exact Q7 | exact FR].
    - intros c' i' Hc' Hi'. destruct (Q8 c' i' Hc' Hi') as (Ec & Hin). split; [exact Ec|]. rewrite !map_app in Hin |- *. cbn [map fst] in Hin |- *. exact Hin. }
  split; [exact W6|]. split; [exact W7|]. split; [exact W8|]. split; [exact W9|]. split; [exact W10|]. exact W11. }

  split.
  - intros c' i' n' Hc' Hi'. unfold qents. cbn [set_ql ql qg lay] in *. rewrite qents_app_snoc.
    destruct (Z.eq_dec (p_abeg (l_SB (lay Σ1)) c' i' + rz_size n' - 16) M) as [E|Hne].
    + assert (QE' : qent_ok Σ1 (M, n')) by (left; exists c', i'; split; [exact Hc'|]; split; [exact Hi' | exact (eq_sym E)]).
      rewrite E, <- (hdr_unique Σ1 M n n' HW QE QE'). apply in_or_app. right. apply in_or_app. right. left. reflexivity.
    + pose proof (RC1 c' i' n' Hc' Hi' Hne) as X. rewrite !in_app_iff in X |- *. cbn [In]. tauto.
  - intros t Ht Hq. unfold qents. cbn [set_ql ql qg sec] in *. rewrite qents_app_snoc.
    destruct (Z.eq_dec (s_mb t + 6128) M) as [E|Hne].
    + assert (QE' : qent_ok Σ1 (M, s_n t)) by (right; exists t; split; [exact Ht|]; split; [exact Hq|]; split; [reflexivity | exact (eq_sym E)]).
      rewrite E, <- (hdr_unique Σ1 M n (s_n t) HW QE QE'). apply in_or_app. right. apply in_or_app. right. left. reflexivity.
    + pose proof (RC2 t Ht Hq Hne) as X. rewrite !in_app_iff in X |- *. cbn [In]. tauto.
Qed.

Theorem new_wfx_e : forall (Σ1 : rtsA) (cal : list Z) (jB : nat) M n, rt_wf0 Σ1 -> pend_e Σ1 M n -> ca Σ1 24 = cal ++ [Z.of_nat jB] ->
  rt_wfx (enq_new Σ1 cal jB M n) /\ rt_count (enq_new Σ1 cal jB M n).
Proof.
  intros Σ1 cal jB M n HW HP HCA. pose proof HP as (QE & FR & RC1 & RC2). pose proof (pe_n Σ1 M n HW QE) as Hnb. pose proof HW as HW0.
  destruct HW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  destruct W2 as (R1 & R2 & R3 & R4 & R5 & R6). destruct (R3 24 ltac:(lia)) as (C1 & C2 & C3). rewrite HCA in C1, C2, C3.
  assert (HjB : nth_error (r_st (pr Σ1 24)) jB = Some CkIdle).
  { pose proof (proj1 (Forall_forall _ _) C3 (Z.of_nat jB) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & X). rewrite Nat2Z.id in X. exact X. }
  assert (HnotB : forall i', nth_error (r_st (pr Σ1 24)) i' = Some CkBatch -> i' <> jB) by (intros i' Hi' ->; rewrite HjB in Hi'; discriminate).
  assert (St : forall c' i' st, nth_error (r_st (pr (pop24 Σ1 cal jB) c')) i' = Some st ->
                 (c' = 24 /\ i' = jB /\ st = CkBatch) \/ ((c' <> 24 \/ i' <> jB) /\ nth_error (r_st (pr Σ1 c')) i' = Some st)).
  { intros c' i' st H. cbn [pr pop24 enq_new set_ql] in H. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|right; split; [left; exact Hcc | exact H]].
    unfold upd_reg in H. cbn [r_st] in H. rewrite nth_error_upd_ck in H. destruct (Nat.eqb_spec jB i') as [<-|Hii].
    - destruct (Nat.ltb_spec jB (length (r_st (pr Σ1 24)))); [injection H as <-; left; tauto | discriminate].
    - right. split; [right; intros E; exact (Hii (eq_sym E)) | exact H]. }
  assert (Hcl : 0 <= Z.of_nat jB < Z.of_nat (length (r_st (pr Σ1 24)))) by (exact (proj1 (proj1 (Forall_forall _ _) C3 (Z.of_nat jB) ltac:(apply in_or_app; right; left; reflexivity)))).
  assert (Keep : forall c' i' st, nth_error (r_st (pr Σ1 c')) i' = Some (CkQuar st) -> nth_error (r_st (pr (pop24 Σ1 cal jB) c')) i' = Some (CkQuar st)).
  { intros c' i' st H. cbn [pr pop24]. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact H].
    unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec jB i') as [<-|_]; [rewrite HjB in H; discriminate | exact H]. }
  split.
  - split; [exact W1|]. split.
    {
      unfold regs_wf. cbn [pr ca ca_init pop24 enq_new set_ql]. split; [|split; [|split; [|split; [|split]]]].
      - intros c' Hc'. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact (R1 c' Hc')].
        pose proof (R1 24 ltac:(lia)) as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11).
        unfold upd_reg, reg_wf. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length.
        split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|].
        split; [exact V7|]. split; [exact V8|]. split; [|split; [|exact V11]].
        + apply Forall_forall. intros j Hj. destruct (proj1 (Forall_forall _ _) V9 j Hj) as (J1 & J2). split; [exact J1|].
          rewrite nth_error_upd_ck. destruct (Nat.eqb_spec jB (Z.to_nat j)) as [E|E]; [|exact J2].
          exfalso. apply NoDup_ListNoDup in C2. rewrite <- app_assoc in C2. apply (NoDup_remove_2 cal (r_fl (pr Σ1 24)) (Z.of_nat jB) C2).
          apply in_or_app. right. rewrite E, Z2Nat.id by lia. exact Hj.
        + apply Forall_forall. intros st Hst. apply (In_nth_error _ _) in Hst as (k & Hk). rewrite nth_error_upd_ck in Hk.
          destruct (Nat.eqb_spec jB k) as [E|E]; [destruct (Nat.ltb_spec k (length (r_st (pr Σ1 24)))); [injection Hk as <-; exact I | discriminate]|].
          exact (proj1 (Forall_forall _ _) V10 st (nth_error_In _ _ Hk)).
      - intros c' Hc'. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [lia | exact (R2 c' Hc')].
      - intros c' Hc'. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact (R3 c' Hc')].
        unfold upd_reg. cbn [r_st r_fl]. rewrite upd_length. rewrite length_app in C1. cbn [length] in C1.
        split; [lia|]. split.
        + apply NoDup_ListNoDup in C2. apply NoDup_ListNoDup. rewrite <- app_assoc in C2. cbn [app] in C2. exact (NoDup_remove_1 _ _ _ C2).
        + apply Forall_forall. intros j Hj. destruct (proj1 (Forall_forall _ _) C3 j ltac:(apply in_or_app; left; exact Hj)) as (J1 & J2).
          split; [exact J1|]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec jB (Z.to_nat j)) as [E|E]; [|exact J2].
          exfalso. apply NoDup_ListNoDup in C2. rewrite <- app_assoc in C2. apply (NoDup_remove_2 cal (r_fl (pr Σ1 24)) (Z.of_nat jB) C2).
          apply in_or_app. left. rewrite E, Z2Nat.id by lia. exact Hj.
      - intros Hci c'. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact (R4 Hci c')]. pose proof (R4 Hci 24) as X. rewrite HCA in X.
        exfalso. destruct cal; discriminate X.
      - intros c' i' Hc' Hi'. destruct (St c' i' CkIdle Hi') as [(_ & _ & E)|(Hne & Hi0)]; [discriminate E|].
        pose proof (R5 c' i' Hc' Hi0) as X. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact X].
        unfold upd_reg. cbn [r_fl]. rewrite HCA, <- app_assoc in X. apply in_app_or in X as [X|[X|X]]; [apply in_or_app; left; exact X| |apply in_or_app; right; exact X].
        exfalso. destruct Hne as [Hne|Hne]; [exact (Hne eq_refl)|]. apply Hne. apply Nat2Z.inj. exact (eq_sym X).
      - intros Hci c'. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact (R6 Hci c')]. unfold upd_reg. cbn [r_st]. rewrite (R6 Hci 24). reflexivity. }
    split.
    {
      destruct W3 as (V1 & V2 & V3 & V4 & V5). unfold live_wf. cbn [pr live lay sec pop24 enq_new set_ql].
      split; [exact V1|]. split; [exact V2|]. split; [|split; [|exact V5]].
      - intros p' n' Hin. destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & Ep)|X]; [left|right; exact X].
        exists c', i'. split; [exact Hc'|]. split; [|exact Ep]. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact Hn'].
        unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec jB i') as [<-|Hii]; [rewrite HjB in Hn'; discriminate | exact Hn'].
      - intros c' i' n' Hc' Hn'. destruct (St c' i' _ Hn') as [(_ & _ & E)|(_ & Hn0)]; [discriminate E | exact (V4 c' i' n' Hc' Hn0)]. }
    split; [exact W4|]. split.
    {
      destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). unfold quar_wfx. cbn [pop24 enq_new set_ql ql qg pr lay sec] in *.
      split; [|split; [exact Q2|split; [|split; [|split; [|split; [|split]]]]]].
      - rewrite <- !qbytes_eq in *. rewrite qbytes_app. cbn [R_quar_defs.qbytes fold_right snd bsum]. unfold bsum. cbn [fold_right snd].
        clear - Q1 Hnb. unfold QMAX_L in *. lia.
      - rewrite <- app_assoc. apply Forall_app. apply Forall_app in Q3 as (Q3a & Q3b). split.
        + eapply Forall_impl; [|exact Q3a]. intros b (j & Hj & Eb). exists j. split; [|exact Eb].
          destruct (Z.eqb_spec 24 24) as [_|X]; [|exfalso; apply X; reflexivity]. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
          destruct (Nat.eqb_spec jB j) as [<-|_]; [rewrite HjB in Hj; discriminate | exact Hj].
        + constructor.
          * exists jB. split; [|reflexivity]. destruct (Z.eqb_spec 24 24) as [_|X]; [|exfalso; apply X; reflexivity]. unfold upd_reg. cbn [r_st].
            rewrite nth_error_upd_ck, Nat.eqb_refl. rewrite (proj2 (Nat.ltb_lt jB (length (r_st (pr Σ1 24)))) ltac:(clear - Hcl; lia)). reflexivity.
          * eapply Forall_impl; [|exact Q3b]. intros b (j & Hj & Eb). exists j. split; [|exact Eb].
            destruct (Z.eqb_spec 24 24) as [_|X]; [|exfalso; apply X; reflexivity]. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
            destruct (Nat.eqb_spec jB j) as [<-|_]; [rewrite HjB in Hj; discriminate | exact Hj].
      - rewrite <- app_assoc, !map_app. cbn [map fst app]. rewrite map_app in Q4. apply nodup_insert; [exact Q4|].
        intros Hin. apply in_app_or in Hin as [Hin|Hin]; apply in_map_iff in Hin as (b & Eb & Hb);
          destruct (proj1 (Forall_forall _ _) Q3 b ltac:(apply in_or_app; first [left; exact Hb | right; exact Hb])) as (j & Hj & Eb');
          rewrite Eb' in Eb; pose proof (g_slot_apart Σ1 (conj W1 (conj (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 R6))))) (conj W4 W6)))
                                         24 j 24 jB CkBatch CkIdle ltac:(lia) ltac:(lia) Hj HjB ltac:(right; intros ->; rewrite HjB in Hj; discriminate)) as Y;
          change (ClassSize 24) with 8192 in Y; lia.
      - rewrite <- app_assoc. apply Forall_app. apply Forall_app in Q5 as (Q5a & Q5b). split; [exact Q5a|]. constructor; [cbn; lia | exact Q5b].
      - unfold qents in *. cbn [pop24 enq_new set_ql ql qg] in *. rewrite <- app_assoc, !flat_map_app. cbn [flat_map snd app].
        rewrite flat_map_app in Q6. apply Forall_app in Q6 as (Q6a & Q6b). apply Forall_app. split.
        + eapply Forall_impl; [|exact Q6a]. intros e [(c' & i' & Hc' & Hi' & Ee)|X]; [left|right; exact X]. exists c', i'. split; [exact Hc'|]. split; [|exact Ee].
          cbn [pr pop24 enq_new set_ql]. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact Hi']. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
          destruct (Nat.eqb_spec jB i') as [<-|_]; [rewrite HjB in Hi'; discriminate | exact Hi'].
        + constructor.
          * destruct QE as [(c & i & Hc & Hi & E)|X]; [left|right; exact X]. exists c, i. split; [exact Hc|]. split; [|exact E].
            cbn [pr pop24 enq_new set_ql]. destruct (Z.eqb_spec c 24) as [->|Hcc]; [|exact Hi]. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
            destruct (Nat.eqb_spec jB i) as [<-|_]; [rewrite HjB in Hi; discriminate | exact Hi].
          * eapply Forall_impl; [|exact Q6b]. intros e [(c' & i' & Hc' & Hi' & Ee)|X]; [left|right; exact X]. exists c', i'. split; [exact Hc'|]. split; [|exact Ee].
            cbn [pr pop24 enq_new set_ql]. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact Hi']. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
            destruct (Nat.eqb_spec jB i') as [<-|_]; [rewrite HjB in Hi'; discriminate | exact Hi'].
      - unfold qents in *. cbn [pop24 enq_new set_ql ql qg] in *. rewrite <- app_assoc, !flat_map_app. cbn [flat_map snd app].
        rewrite flat_map_app in Q7, FR. rewrite !map_app in Q7, FR |- *. cbn [map fst]. apply nodup_insert; [exact Q7 | exact FR].
      - intros c' i' Hc' Hi'. destruct (St c' i' CkBatch Hi') as [(-> & -> & _)|(_ & Hi0)].
        + split; [reflexivity|]. rewrite <- app_assoc, !map_app. cbn [map fst]. apply in_or_app. right. left. reflexivity.
        + destruct (Q8 c' i' Hc' Hi0) as (Ec & Hin). split; [exact Ec|]. rewrite <- app_assoc, !map_app. rewrite map_app in Hin. cbn [map fst].
          apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; right; exact Hin]. }
    split; [exact W6|]. split.
    { destruct W7 as (G1 & G2 & G3 & G4 & G5). unfold budget_wf. cbn [credit aw pop24 enq_new set_ql].
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [|exact G5].
      assert (E : rt_eager (enq_new Σ1 cal jB M n) = rt_eager Σ1).
      { unfold rt_eager, enq_new, set_ql, pop24. cbn [pr sec sec_nres].
        rewrite (sum_cls_ext _ (fun c0 => r_muser (pr Σ1 c0) + r_mfa (pr Σ1 c0))); [reflexivity|]. intros k _.
        destruct (Z.eqb_spec (Z.of_nat k) 24) as [Ek|Ek]; [rewrite Ek; unfold upd_reg; reflexivity | reflexivity]. }
      unfold enq_new, set_ql, pop24 in E. cbn [pr sec sec_nres] in E. rewrite E. exact G4. }
    split; [exact W8|]. split; [exact W9|]. split; [exact W10 | exact W11].
  -
    split.
    + intros c' i' n' Hc' Hi'. unfold qents. cbn [pop24 enq_new set_ql ql qg lay] in *. rewrite <- app_assoc, flat_map_app. cbn [flat_map snd app].
      destruct (St c' i' _ Hi') as [(_ & _ & E)|(_ & Hi0)]; [discriminate E|].
      destruct (Z.eq_dec (p_abeg (l_SB (lay Σ1)) c' i' + rz_size n' - 16) M) as [E|Hne].
      * assert (QE' : qent_ok Σ1 (M, n')) by (left; exists c', i'; split; [exact Hc'|]; split; [exact Hi0 | exact (eq_sym E)]).
        rewrite E, <- (hdr_unique Σ1 M n n' HW0 QE QE'). apply in_or_app. right. left. reflexivity.
      * pose proof (RC1 c' i' n' Hc' Hi0 Hne) as X. unfold qents in X. rewrite flat_map_app in X.
        apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
    + intros t Ht Hq. unfold qents. cbn [pop24 enq_new set_ql ql qg sec] in *. rewrite <- app_assoc, flat_map_app. cbn [flat_map snd app].
      destruct (Z.eq_dec (s_mb t + 6128) M) as [E|Hne].
      * assert (QE' : qent_ok Σ1 (M, s_n t)) by (right; exists t; split; [exact Ht|]; split; [exact Hq|]; split; [reflexivity | exact (eq_sym E)]).
        rewrite E, <- (hdr_unique Σ1 M n (s_n t) HW0 QE QE'). apply in_or_app. right. left. reflexivity.
      * pose proof (RC2 t Ht Hq Hne) as X. unfold qents in X. rewrite flat_map_app in X.
        apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
Qed.

End GWIN.
