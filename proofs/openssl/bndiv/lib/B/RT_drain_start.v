(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface R_sizeclass R_cache_defs R_prim_defs R_depot_defs R_fs_defs R_glue_defs R_quar_defs R_qrec_defs R_qrecycle RT_state RT_rep RT_freestmt RT_drain_defs RT_drain_pure RT_drain_led.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition QMIN : Z := 0xE666661.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma qbytes_eq : forall bs, RT_state.qbytes bs = R_quar_defs.qbytes bs.
Proof.
  intros bs. unfold RT_state.qbytes, R_quar_defs.qbytes, qsum, qn, bsum. induction bs as [|b bs IH]; [reflexivity|].
  cbn [fold_right length]. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma merge_walk_ents : forall rest cur,
  flat_map snd (fst (merge_walk cur rest)) = flat_map snd (cur :: rest) /\ flat_map snd (snd (merge_walk cur rest)) = [].
Proof.
  induction rest as [|nxt rest IH]; intros [b e]; [cbn; rewrite app_nil_r; split; reflexivity|].
  cbn [merge_walk fst snd]. destruct (_ <=? _).
  - cbn [fst snd]. destruct (IH (b, e ++ snd nxt)) as (A & B). split.
    + rewrite A. cbn [flat_map snd]. rewrite <- app_assoc. reflexivity.
    + cbn [flat_map snd app]. exact B.
  - cbn [fst snd flat_map]. destruct (IH nxt) as (A & B). split; [rewrite A; reflexivity | exact B].
Qed.

Lemma rec_merge_ents : forall gl, flat_map snd (fst (rec_merge gl)) = flat_map snd gl /\ flat_map snd (snd (rec_merge gl)) = [].
Proof.
  intros gl. unfold rec_merge. destruct (merge_cond gl); [|split; reflexivity].
  destruct gl as [|cur rest]; [split; reflexivity|]. exact (merge_walk_ents rest cur).
Qed.

Lemma rec_merge_perm : forall gl, Permutation (map fst (snd (rec_merge gl) ++ fst (rec_merge gl))) (map fst gl).
Proof.
  intros gl. unfold rec_merge. destruct (merge_cond gl); [apply merge_all_perm|]. cbn [fst snd app]. apply Permutation_refl.
Qed.

Lemma merge_walk_len : forall rest cur, (length (snd cur) <= 1021)%nat -> Forall (fun b => (length (snd b) <= 1021)%nat) rest ->
  Forall (fun b => (length (snd b) <= 1021)%nat) (fst (merge_walk cur rest) ++ snd (merge_walk cur rest)).
Proof.
  induction rest as [|nxt rest IH]; intros [b e] Hc Hr; [cbn; constructor; [exact Hc | constructor]|].
  inversion Hr as [|? ? Hn Hr']; subst. cbn [merge_walk fst snd] in *. destruct (_ <=? _) eqn:L.
  - apply Z.leb_le in L. cbn [fst snd]. pose proof (IH (b, e ++ snd nxt) ltac:(cbn [snd] in *; rewrite length_app; lia) Hr') as X.
    apply Forall_app in X as [X1 X2]. apply Forall_app. split; [exact X1|]. constructor; [cbn; lia | exact X2].
  - cbn [fst snd app]. constructor; [exact Hc|]. exact (IH nxt Hn Hr').
Qed.

Lemma rec_merge_len : forall gl, Forall (fun b => (length (snd b) <= 1021)%nat) gl ->
  Forall (fun b => (length (snd b) <= 1021)%nat) (fst (rec_merge gl) ++ snd (rec_merge gl)).
Proof.
  intros gl H. unfold rec_merge. destruct (merge_cond gl); [|cbn [fst snd]; rewrite app_nil_r; exact H].
  destruct gl as [|cur rest]; [constructor|]. inversion H; subst. apply merge_walk_len; assumption.
Qed.

(* [comment removed for export] *)
Lemma deq_rest_bytes : forall bs min, 0 <= min -> R_quar_defs.qbytes (snd (deq bs (R_quar_defs.qbytes bs) min)) <= min.
Proof.
  induction bs as [|b bs IH]; intros min Hm; [cbn; lia|]. cbn [deq].
  destruct (Z.leb_spec (R_quar_defs.qbytes (b :: bs)) min) as [L|L]; [exact L|].
  cbn [snd]. replace (R_quar_defs.qbytes (b :: bs) - (8192 + bsum (snd b))) with (R_quar_defs.qbytes bs) by (cbn [R_quar_defs.qbytes fold_right]; unfold R_quar_defs.qbytes; lia).
  apply IH. exact Hm.
Qed.

Lemma rec_parts : forall gl min,
  Permutation (map fst (rec_r gl min ++ rec_x gl min)) (map fst gl)
  /\ Permutation (flat_map snd (rec_r gl min ++ rec_x gl min)) (flat_map snd gl)
  /\ R_quar_defs.qbytes (rec_r gl min) + R_quar_defs.qbytes (rec_x gl min) = R_quar_defs.qbytes gl
  /\ (Forall (fun b => (length (snd b) <= 1021)%nat) gl -> Forall (fun b => (length (snd b) <= 1021)%nat) (rec_r gl min ++ rec_x gl min)).
Proof.
  intros gl min. unfold rec_r, rec_x.
  set (M := rec_merge gl). set (K := fst M). set (D := deq K (R_quar_defs.qbytes K) min).
  pose proof (deq_app K (R_quar_defs.qbytes K) min) as EK. fold D in EK.
  assert (P1 : Permutation (snd D ++ snd M ++ fst D) (snd M ++ K)).
  { rewrite <- EK. eapply perm_trans; [apply Permutation_app_comm|]. rewrite <- app_assoc. apply Permutation_refl. }
  split; [eapply perm_trans; [apply Permutation_map; exact P1 | apply rec_merge_perm]|].
  split.
  { eapply perm_trans; [apply Permutation_flat_map; exact P1|]. rewrite flat_map_app. destruct (rec_merge_ents gl) as (A & B).
    fold M in A, B. fold K in A. rewrite B, A. apply Permutation_refl. }
  split.
  { rewrite qbytes_app. pose proof (qbytes_app (fst D) (snd D)) as X. rewrite EK in X. pose proof (rec_merge_bytes gl) as Y. fold M K in Y. lia. }
  intros HL. pose proof (rec_merge_len gl HL) as X. fold M K in X.
  apply (Permutation_Forall (Permutation_sym P1)). apply Forall_app in X as [X1 X2]. apply Forall_app. split; [exact X2 | exact X1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_q_fields : forall Σ l g, lay (set_q Σ l g) = lay Σ /\ pr (set_q Σ l g) = pr Σ /\ ca (set_q Σ l g) = ca Σ
  /\ ca_init (set_q Σ l g) = ca_init Σ /\ sec (set_q Σ l g) = sec Σ /\ sec_nres (set_q Σ l g) = sec_nres Σ /\ aw (set_q Σ l g) = aw Σ
  /\ ql (set_q Σ l g) = l /\ qg (set_q Σ l g) = g /\ dep (set_q Σ l g) = dep Σ /\ credit (set_q Σ l g) = credit Σ
  /\ live (set_q Σ l g) = live Σ /\ frames (set_q Σ l g) = frames Σ.
Proof. intros. repeat split; reflexivity. Qed.

Lemma qent_ok_same : forall Σ Σ' e, lay Σ' = lay Σ -> pr Σ' = pr Σ -> sec Σ' = sec Σ -> qent_ok Σ e -> qent_ok Σ' e.
Proof. intros Σ Σ' e E1 E2 E3 H. unfold qent_ok. rewrite E1, E2, E3. exact H. Qed.

Lemma Forall_fst_perm : forall (P : Z -> Prop) (l1 l2 : list batch), Forall (fun b => P (fst b)) l1 ->
  Permutation (map fst l2) (map fst l1) -> Forall (fun b => P (fst b)) l2.
Proof.
  intros P l1 l2 H E. apply Forall_map. apply (Permutation_Forall (Permutation_sym E)). apply Forall_map. exact H.
Qed.

(* [comment removed for export] *)
Theorem rt_wfP_start : forall Σ, rt_wfx Σ -> rt_count Σ ->
  rt_wfP (set_q Σ [] (rec_r (qg Σ ++ ql Σ) QMIN)) (rec_x (qg Σ ++ ql Σ) QMIN).
Proof.
  intros Σ (H1 & HR & HV & HS & HQ & H6 & HB & H8 & H9 & H10 & H11) (K1 & K2).
  destruct HQ as (Q1 & Q2 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  set (G := qg Σ ++ ql Σ). pose proof (set_q_fields Σ [] (rec_r G QMIN)) as (El & Epr & Eca & Eci & Es & En & Ea & Eql & Eqg & Ed & Ec & Elv & Efr).
  destruct (rec_parts G QMIN) as (PF & PE & PB & PL).
  assert (GQ : Permutation (ql Σ ++ qg Σ) G) by apply Permutation_app_comm.
  assert (EA : qallP (set_q Σ [] (rec_r G QMIN)) (rec_x G QMIN) = rec_r G QMIN ++ rec_x G QMIN) by (unfold qallP; rewrite Eql, Eqg; reflexivity).
  assert (PF' : Permutation (map fst (qallP (set_q Σ [] (rec_r G QMIN)) (rec_x G QMIN))) (map fst (ql Σ ++ qg Σ))).
  { rewrite EA. eapply perm_trans; [exact PF|]. apply Permutation_map. apply Permutation_sym. exact GQ. }
  assert (PE' : Permutation (qentsP (set_q Σ [] (rec_r G QMIN)) (rec_x G QMIN)) (qents Σ)).
  { unfold qentsP, qents. rewrite EA. eapply perm_trans; [exact PE|]. apply Permutation_flat_map. apply Permutation_sym. exact GQ. }
  assert (Hpos : forall e, In e (flat_map snd (rec_r G QMIN ++ rec_x G QMIN)) -> 0 <= snd e).
  { intros e He. assert (Hq : In e (qents Σ)) by (apply (Permutation_in _ PE'); unfold qentsP; rewrite EA; exact He).
    pose proof (qent_n_pos Σ e HR HS (proj1 (Forall_forall _ _) Q7 e Hq)). lia. }
  assert (Hr0 : 0 <= RT_state.qbytes (rec_r G QMIN)).
  { apply qbytes_nonneg'. apply Forall_forall. intros x Hx. apply Hpos. rewrite flat_map_app. apply in_or_app. left. exact Hx. }
  assert (HG : R_quar_defs.qbytes G <= QMAX_L + 2 ^ 27 + 0x20000 + (QMAX_G + 0x10000)) by (unfold G; rewrite qbytes_app, <- !qbytes_eq; lia).
  split; [rewrite El; exact H1|]. split; [unfold regs_wf; rewrite Epr, Eca, Eci; exact HR|].
  split; [unfold live_wf; rewrite Elv, Epr, El, Es; exact HV|]. split; [unfold sec_wf; rewrite Es, En, El, Ea; exact HS|].
  split.
  { unfold quar_wfP. rewrite Eql, Eqg, El, Epr.
    split; [change (RT_state.qbytes []) with 0; unfold QMAX_L; lia|].
    split; [rewrite qbytes_eq; pose proof (deq_rest_bytes (fst (rec_merge G)) QMIN ltac:(unfold QMIN; lia)) as X; unfold rec_r; unfold QMIN, QMAX_G in *; lia|].
    split; [rewrite qbytes_eq in Hr0 |- *; unfold QMAX_L, QMAX_G in HG; lia|].
    split; [apply (Forall_fst_perm (fun x => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ x = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ)); [exact Q4 | exact PF']|].
    split; [apply NoDup_ListNoDup; apply (Permutation_NoDup (Permutation_sym PF')); apply NoDup_ListNoDup; exact Q5|].
    split; [rewrite EA; apply PL; apply (Permutation_Forall GQ); exact Q6|].
    split; [apply Forall_forall; intros e He; apply (qent_ok_same Σ); [exact El | exact Epr | exact Es |];
            exact (proj1 (Forall_forall _ _) Q7 e (Permutation_in _ PE' He))|].
    split; [apply NoDup_ListNoDup; apply (Permutation_NoDup (Permutation_map fst (Permutation_sym PE'))); apply NoDup_ListNoDup; exact Q8|].
    intros c i Hc Hi. destruct (Q9 c i Hc Hi) as (E24 & Hin). split; [exact E24|]. exact (Permutation_in _ (Permutation_sym PF') Hin). }
  split; [exact H6|]. split; [exact HB|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|].
  unfold rt_countP. rewrite El, Epr, Es. split.
  - intros c i n Hc Hi. exact (Permutation_in _ (Permutation_sym PE') (K1 c i n Hc Hi)).
  - intros s Hs Hq. exact (Permutation_in _ (Permutation_sym PE') (K2 s Hs Hq)).
Qed.

(* [comment removed for export] *)
Theorem rt_wf_transfer : forall Σ, rt_wfx Σ -> rt_count Σ -> RT_state.qbytes (qg Σ ++ ql Σ) <= QMAX_G ->
  rt_wf (set_q Σ [] (qg Σ ++ ql Σ)).
Proof.
  intros Σ HW HC HBY. apply rt_wfP_nil.
  pose proof (rt_wfP_start Σ HW HC) as _.
  destruct HW as (H1 & HR & HV & HS & HQ & H6 & HB & H8 & H9 & H10 & H11). destruct HC as (K1 & K2).
  destruct HQ as (Q1 & Q2 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  set (G := qg Σ ++ ql Σ). pose proof (set_q_fields Σ [] G) as (El & Epr & Eca & Eci & Es & En & Ea & Eql & Eqg & Ed & Ec & Elv & Efr).
  assert (GQ : Permutation (ql Σ ++ qg Σ) G) by apply Permutation_app_comm.
  assert (EA : qallP (set_q Σ [] G) [] = G) by (unfold qallP; rewrite Eql, Eqg, app_nil_r; reflexivity).
  assert (PF' : Permutation (map fst (qallP (set_q Σ [] G) [])) (map fst (ql Σ ++ qg Σ))) by (rewrite EA; apply Permutation_map; apply Permutation_sym; exact GQ).
  assert (PE' : Permutation (qentsP (set_q Σ [] G) []) (qents Σ)) by (unfold qentsP, qents; rewrite EA; apply Permutation_flat_map; apply Permutation_sym; exact GQ).
  split; [rewrite El; exact H1|]. split; [unfold regs_wf; rewrite Epr, Eca, Eci; exact HR|].
  split; [unfold live_wf; rewrite Elv, Epr, El, Es; exact HV|]. split; [unfold sec_wf; rewrite Es, En, El, Ea; exact HS|].
  split.
  { unfold quar_wfP. rewrite Eql, Eqg, El, Epr.
    split; [change (RT_state.qbytes []) with 0; unfold QMAX_L; lia|]. split; [eapply Z.le_trans; [exact HBY | unfold QMAX_G; lia]|]. split; [change (RT_state.qbytes []) with 0; lia|].
    split; [apply (Forall_fst_perm (fun x => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ x = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ)); [exact Q4 | exact PF']|].
    split; [apply NoDup_ListNoDup; apply (Permutation_NoDup (Permutation_sym PF')); apply NoDup_ListNoDup; exact Q5|].
    split; [rewrite EA; apply (Permutation_Forall GQ); exact Q6|].
    split; [apply Forall_forall; intros e He; apply (qent_ok_same Σ); [exact El | exact Epr | exact Es |];
            exact (proj1 (Forall_forall _ _) Q7 e (Permutation_in _ PE' He))|].
    split; [apply NoDup_ListNoDup; apply (Permutation_NoDup (Permutation_map fst (Permutation_sym PE'))); apply NoDup_ListNoDup; exact Q8|].
    intros c i Hc Hi. destruct (Q9 c i Hc Hi) as (E24 & Hin). split; [exact E24|]. exact (Permutation_in _ (Permutation_sym PF') Hin). }
  split; [exact H6|]. split; [exact HB|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|].
  unfold rt_countP. rewrite El, Epr, Es. split.
  - intros c i n Hc Hi. exact (Permutation_in _ (Permutation_sym PE') (K1 c i n Hc Hi)).
  - intros s Hs Hq. exact (Permutation_in _ (Permutation_sym PE') (K2 s Hs Hq)).
Qed.
