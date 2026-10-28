(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pop24 (Σ : rtsA) (cal : list Z) (jB : nat) : rtsA :=
  mkRtsA (lay Σ) (fun c' => if c' =? 24 then upd_reg (pr Σ 24) jB CkBatch else pr Σ c') (fun c' => if c' =? 24 then cal else ca Σ c')
    (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ) (fs0 Σ) (fs2 Σ) (fs1 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).
Definition enq_new (Σ : rtsA) (cal : list Z) (jB : nat) (M n : Z) : rtsA :=
  set_ql (pop24 Σ cal jB) (ql Σ ++ [(p_abeg (l_SB (lay Σ)) 24 jB, [(M, n)])]).

(* [comment removed for export] *)
Definition pend_ok (Σ : rtsA) (c : Z) (i : nat) (n : Z) : Prop :=
  1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkQuar n)
  /\ ~ In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) (map fst (qents Σ))
  /\ (forall c' i' n', 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some (CkQuar n') -> (c' <> c \/ i' <> i) ->
        In (p_abeg (l_SB (lay Σ)) c' i' + rz_size n' - 16, n') (qents Σ))
  /\ (forall s, In s (sec Σ) -> s_quar s = true -> In (s_mb s + 6128, s_n s) (qents Σ)).

Lemma pend_free_p : forall Σ m c i n p D', ART_A Σ m -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  pend_ok (free_p Σ c i n p D') c i n.
Proof.
  intros Σ m c i n p D' HA Hc Hn. pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (RC1 & RC2)).
  split; [exact Hc|]. split.
  { cbn [pr free_p]. destruct (Z.eqb_spec c c) as [_|X]; [|exfalso; apply X; reflexivity]. unfold upd_reg. cbn [r_st].
    rewrite nth_error_upd_ck, Nat.eqb_refl. rewrite (proj2 (Nat.ltb_lt _ _) (proj1 (nth_error_Some _ _) ltac:(rewrite Hn; discriminate))). reflexivity. }
  split; [exact (new_ent_fresh Σ m c i n HA Hc Hn)|]. split.
  - intros c' i' n' Hc' Hi' Hne. cbn [pr free_p lay qents] in *. destruct (fp_st Σ c i n Hc c' i' _ Hi') as [(-> & -> & _)|(_ & Hi0)].
    + destruct Hne as [X|X]; exfalso; apply X; reflexivity.
    + exact (RC1 c' i' n' Hc' Hi0).
  - intros s Hs Hq. exact (RC2 s Hs Hq).
Qed.



(* [comment removed for export] *)
Theorem new_wfx : forall (Σ1 : rtsA) (cal : list Z) (jB : nat) c i n, rt_wf0 Σ1 -> pend_ok Σ1 c i n -> ca Σ1 24 = cal ++ [Z.of_nat jB] ->
  rt_wfx (enq_new Σ1 cal jB (p_abeg (l_SB (lay Σ1)) c i + rz_size n - 16) n)
  /\ rt_count (enq_new Σ1 cal jB (p_abeg (l_SB (lay Σ1)) c i + rz_size n - 16) n).
Proof.
  intros Σ1 cal jB c i n HW HP HCA. pose proof HP as (Hc & Hn & FR & RC1 & RC2).
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
  split.
  - split; [exact W1|]. split.
    { (* [comment removed for export] *)
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
    { (* [comment removed for export] *)
      destruct W3 as (V1 & V2 & V3 & V4 & V5). unfold live_wf. cbn [pr live lay sec pop24 enq_new set_ql].
      split; [exact V1|]. split; [exact V2|]. split; [|split; [|exact V5]].
      - intros p' n' Hin. destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & Ep)|X]; [left|right; exact X].
        exists c', i'. split; [exact Hc'|]. split; [|exact Ep]. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|exact Hn'].
        unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec jB i') as [<-|Hii]; [rewrite HjB in Hn'; discriminate | exact Hn'].
      - intros c' i' n' Hc' Hn'. destruct (St c' i' _ Hn') as [(_ & _ & E)|(_ & Hn0)]; [discriminate E | exact (V4 c' i' n' Hc' Hn0)]. }
    split; [exact W4|]. split.
    { (* [comment removed for export] *)
      destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). unfold quar_wfx. cbn [pop24 enq_new set_ql ql qg pr lay sec] in *.
      split; [|split; [exact Q2|split; [|split; [|split; [|split; [|split]]]]]].
      - rewrite <- !qbytes_eq in *. rewrite qbytes_app. cbn [R_quar_defs.qbytes fold_right snd bsum]. unfold bsum. cbn [fold_right snd].
        destruct (R1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & V10 & _).
        pose proof (proj1 (Forall_forall _ _) V10 _ (nth_error_In _ _ Hn)) as (X & X1 & _). cbv beta iota in X, X1.
        pose proof (ClassSize_range c Hc) as (X2 & _). pose proof (rz_facts n) as (_ & X3). clear - Q1 X X1 X2 X3. unfold QMAX_L in *. lia.
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
          * left. exists c, i. split; [exact Hc|]. split; [|reflexivity]. cbn [snd pr pop24 enq_new set_ql]. destruct (Z.eqb_spec c 24) as [->|Hcc]; [|exact Hn].
            unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec jB i) as [<-|_]; [rewrite HjB in Hn; discriminate | exact Hn].
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
      assert (E : rt_eager (enq_new Σ1 cal jB (p_abeg (l_SB (lay Σ1)) c i + rz_size n - 16) n) = rt_eager Σ1).
      { unfold rt_eager, enq_new, set_ql, pop24. cbn [pr sec sec_nres].
        rewrite (sum_cls_ext _ (fun c0 => r_muser (pr Σ1 c0) + r_mfa (pr Σ1 c0))); [reflexivity|]. intros k _.
        destruct (Z.eqb_spec (Z.of_nat k) 24) as [Ek|Ek]; [rewrite Ek; unfold upd_reg; reflexivity | reflexivity]. }
      unfold enq_new, set_ql, pop24 in E. cbn [pr sec sec_nres] in E. rewrite E. exact G4. }
    split; [exact W8|]. split; [exact W9|]. split; [exact W10 | exact W11].
  - (* [comment removed for export] *)
    split.
    + intros c' i' n' Hc' Hi'. unfold qents. cbn [pop24 enq_new set_ql ql qg lay] in *. rewrite <- app_assoc, flat_map_app. cbn [flat_map snd app].
      destruct (St c' i' _ Hi') as [(_ & _ & E)|(_ & Hi0)]; [discriminate E|].
      destruct (Z.eq_dec c' c) as [->|Hcc]; [destruct (Nat.eq_dec i' i) as [->|Hii]|].
      * rewrite Hn in Hi0. injection Hi0 as <-. apply in_or_app. right. left. reflexivity.
      * pose proof (RC1 c i' n' Hc' Hi0 (or_intror Hii)) as X. unfold qents in X. rewrite flat_map_app in X.
        apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
      * pose proof (RC1 c' i' n' Hc' Hi0 (or_introl Hcc)) as X. unfold qents in X. rewrite flat_map_app in X.
        apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
    + intros s Hs Hq. unfold qents. cbn [pop24 enq_new set_ql ql qg sec] in *. rewrite <- app_assoc, flat_map_app. cbn [flat_map snd app].
      pose proof (RC2 s Hs Hq) as X. unfold qents in X. rewrite flat_map_app in X.
      apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X | right; right; exact X].
Qed.
