(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VAbs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition same_shape (A A' : vstate) : Prop :=
  vs_regs A' = vs_regs A /\ vs_slots A' = vs_slots A /\ vs_globs A' = vs_globs A /\
  vs_nul A' = vs_nul A /\ vs_pc A' = vs_pc A /\ vs_ctx A' = vs_ctx A /\ vs_ghosts A' = vs_ghosts A.

Definition aext (A A' : vstate) (nu nu' : val) : Prop :=
  ext (vs_next A) nu nu' /\ (vs_next A <= vs_next A')%positive /\ same_shape A A'.

Lemma same_shape_refl A : same_shape A A.
Proof. repeat split; reflexivity. Qed.

Lemma same_shape_trans A B C : same_shape A B -> same_shape B C -> same_shape A C.
Proof. unfold same_shape. intros (H1&H2&H3&H4&H5&H6&H7) (G1&G2&G3&G4&G5&G6&G7). repeat split; congruence. Qed.

Lemma aext_refl A nu : aext A A nu nu.
Proof. split; [apply ext_refl|split; [lia|apply same_shape_refl]]. Qed.

Lemma aext_trans A B C nu1 nu2 nu3 : aext A B nu1 nu2 -> aext B C nu2 nu3 -> aext A C nu1 nu3.
Proof.
  intros (E1&L1&S1) (E2&L2&S2). split; [|split; [lia|eapply same_shape_trans; eauto]].
  eapply ext_trans; eauto.
Qed.

(* [comment removed for export] *)
Lemma same_shape_set_store A S : same_shape A (set_store A S).
Proof. repeat split; reflexivity. Qed.
Lemma same_shape_set_next A n : same_shape A (set_next A n).
Proof. repeat split; reflexivity. Qed.
Lemma same_shape_set_conddef A m : same_shape A (set_conddef A m).
Proof. repeat split; reflexivity. Qed.
Lemma same_shape_set_moddef A m : same_shape A (set_moddef A m).
Proof. repeat split; reflexivity. Qed.
Lemma same_shape_set_valset A m : same_shape A (set_valset A m).
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma aext_keep A A' nu : vs_next A' = vs_next A -> same_shape A A' -> aext A A' nu nu.
Proof. intros Hn Hs. split; [apply ext_refl|split; [rewrite Hn; lia|exact Hs]]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lg_sat A nu : lgamma A nu -> sat nu (vs_store A).
Proof. intros H; exact (proj1 H). Qed.
Lemma lg_below A nu : lgamma A nu -> state_below A.
Proof. intros (_&_&_&_&H); exact H. Qed.
Lemma lg_store_below A nu : lgamma A nu -> store_below (vs_store A) (vs_next A) = true.
Proof. intros H. apply lg_below in H. exact (proj1 (proj2 H)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bnd_sound A nu e : lgamma A nu -> in_itv (eval nu e) (bnd A e).
Proof.
  intros H. unfold bnd. destruct (lin_is_const e) eqn:E.
  - rewrite (eval_is_const nu e E). apply in_itv_const.
  - apply lp_bounds_sound. now apply lg_sat.
Qed.

Lemma bnd_v_sound A nu v x :
  lgamma A nu -> match v with Some e => eval nu e = x | None => True end -> in_itv x (bnd_v A v).
Proof.
  intros H. destruct v as [e|]; simpl; [intros <-; now apply bnd_sound|intros _; apply in_itv_top].
Qed.

Lemma qle_sound A nu e c : lgamma A nu -> qle A e c = true -> eval nu e <= c.
Proof.
  intros H. unfold qle. destruct (lin_is_const e) eqn:E.
  - rewrite (eval_is_const nu e E). intros X; apply Z.leb_le in X; lia.
  - intros X. eapply check_hi_sound; eauto. now apply lg_sat.
Qed.

Lemma qge_sound A nu e c : lgamma A nu -> qge A e c = true -> c <= eval nu e.
Proof.
  intros H. unfold qge. destruct (lin_is_const e) eqn:E.
  - rewrite (eval_is_const nu e E). intros X; apply Z.leb_le in X; lia.
  - intros X. eapply check_lo_sound; eauto. now apply lg_sat.
Qed.

Lemma qwithin_sound A nu e lo hi : lgamma A nu -> qwithin A e lo hi = true -> lo <= eval nu e <= hi.
Proof.
  intros H X. unfold qwithin in X. rewrite if_andb in X. apply andb_prop in X as [X1 X2].
  split; [eapply qge_sound|eapply qle_sound]; eauto.
Qed.

Lemma inU_sound A nu e : lgamma A nu -> inU A e = true -> 0 <= eval nu e < 2 ^ 64.
Proof. intros H X. apply (qwithin_sound A nu e 0 M64 H) in X. unfold M64 in X. lia. Qed.

Lemma inS_sound A nu e : lgamma A nu -> inS A e = true -> - 2 ^ 63 <= eval nu e < 2 ^ 63.
Proof. intros H X. apply (qwithin_sound A nu e _ _ H) in X. unfold TWO63 in X. lia. Qed.

Lemma bnd_dead_sound A nu e : lgamma A nu -> bnd_dead A e = false.
Proof.
  intros H. unfold bnd_dead. destruct (lin_is_const e); auto.
  apply (lp_bounds_not_empty nu). now apply lg_sat.
Qed.

Lemma lp_bounds_not_empty' A nu e : lgamma A nu -> itv_empty (lp_bounds (vs_store A) e) = false.
Proof. intros H. apply (lp_bounds_not_empty nu). now apply lg_sat. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma norm_terms_sound nu B l : forall acc,
  in_box nu B -> eval nu (norm_terms B l acc) = eval nu acc + eval_terms nu l.
Proof.
  induction l as [|[s k] t IH]; intros acc HB; cbn [norm_terms eval_terms]; [lia|].
  assert (Ek : eval nu (laxpy acc k (lsym s)) = eval nu acc + k * nu s)
    by (rewrite eval_laxpy, eval_lsym; lia).
  destruct (is_fixed s && negb (Pos.eqb s SIZE)).
  - rewrite IH; auto. lia.
  - pose proof (in_box_get nu B s HB) as Hs.
    destruct (box_get B s) as [[lo|] [hi|]]; try (rewrite IH; auto; lia).
    destruct (Z.eqb_spec lo hi); [|rewrite IH; auto; lia].
    subst. destruct Hs as [H1 H2]; simpl in *. assert (nu s = hi) by lia.
    rewrite IH, eval_laddc; auto. subst. lia.
Qed.

Lemma anorm_sound A nu e : lgamma A nu -> eval nu (anorm A e) = eval nu e.
Proof.
  intros H. unfold anorm. rewrite norm_terms_sound; [|apply sat_box; now apply lg_sat].
  rewrite eval_lconst. unfold eval. lia.
Qed.

(* [comment removed for export] *)
Lemma map_fst_terms_scale k l : map fst (terms_scale k l) = map fst l.
Proof. induction l as [|[s c] t IH]; simpl; congruence. Qed.

Lemma terms_axpy_syms k l1 : forall l2 s,
  In s (map fst (terms_axpy k l1 l2)) -> In s (map fst l1) \/ In s (map fst l2).
Proof.
  induction l1 as [|[s1 c1] t1 IH1]; intros l2 s.
  - simpl. rewrite map_fst_terms_scale. auto.
  - induction l2 as [|[s2 c2] t2 IH2].
    + simpl. intros [X|X]; auto.
    + simpl. destruct (Pos.compare_spec s1 s2).
      * subst. destruct (Z.eqb (c1 + k * c2) 0).
        -- intros X. destruct (IH1 t2 s X); simpl; tauto.
        -- simpl. intros [X|X]; [tauto|]. destruct (IH1 t2 s X); simpl; tauto.
      * simpl. intros [X|X]; [tauto|]. destruct (IH1 ((s2, c2) :: t2) s X); simpl in *; tauto.
      * simpl. intros [X|X]; [tauto|]. simpl in IH2. destruct (IH2 X); tauto.
Qed.

Lemma lsyms_laxpy_sub a k b s : In s (lsyms (laxpy a k b)) -> In s (lsyms a) \/ In s (lsyms b).
Proof.
  unfold laxpy, lsyms. destruct (Z.eqb k 0); simpl; [auto|]. apply terms_axpy_syms.
Qed.

Lemma lin_below_laxpy a k b n :
  lin_below a n = true -> lin_below b n = true -> lin_below (laxpy a k b) n = true.
Proof.
  intros Ha Hb. apply (proj2 (lin_below_iff _ _)). intros s Hs.
  destruct (lsyms_laxpy_sub a k b s Hs); [apply (proj1 (lin_below_iff a n))|apply (proj1 (lin_below_iff b n))]; auto.
Qed.

Lemma lin_below_lsym s n : (s < n)%positive -> lin_below (lsym s) n = true.
Proof. intros. unfold lin_below, lsym; simpl. rewrite (proj2 (Pos.ltb_lt s n)); auto. Qed.

Lemma lin_below_lconst c n : lin_below (lconst c) n = true.
Proof. reflexivity. Qed.

Lemma lin_below_laddc a c n : lin_below a n = true -> lin_below (laddc a c) n = true.
Proof. unfold lin_below, laddc; simpl; auto. Qed.

Lemma lin_below_ladd a b n : lin_below a n = true -> lin_below b n = true -> lin_below (ladd a b) n = true.
Proof.
  intros Ha Hb. apply (proj2 (lin_below_iff _ _)). intros s Hs. unfold ladd, lsyms in Hs. simpl in Hs.
  destruct (terms_axpy_syms 1 (lt a) (lt b) s Hs);
    [apply (proj1 (lin_below_iff a n))|apply (proj1 (lin_below_iff b n))]; auto.
Qed.

Lemma lin_below_lsub a b n : lin_below a n = true -> lin_below b n = true -> lin_below (lsub a b) n = true.
Proof.
  intros Ha Hb. apply (proj2 (lin_below_iff _ _)). intros s Hs. unfold lsub, lsyms in Hs. simpl in Hs.
  destruct (terms_axpy_syms (-1) (lt a) (lt b) s Hs);
    [apply (proj1 (lin_below_iff a n))|apply (proj1 (lin_below_iff b n))]; auto.
Qed.

Lemma lin_below_lscale k a n : lin_below a n = true -> lin_below (lscale k a) n = true.
Proof.
  intros H. unfold lscale. destruct (Z.eqb k 0); [reflexivity|]. destruct (Z.eqb k 1); auto.
  apply (proj2 (lin_below_iff _ _)). intros s. unfold lsyms; simpl. rewrite map_fst_terms_scale.
  apply (proj1 (lin_below_iff a n) H).
Qed.

Lemma lin_below_lneg a n : lin_below a n = true -> lin_below (lneg a) n = true.
Proof.
  intros H. apply (proj2 (lin_below_iff _ _)). intros s. unfold lsyms, lneg; simpl. rewrite map_fst_terms_scale.
  apply (proj1 (lin_below_iff a n) H).
Qed.

Lemma norm_terms_below B l n : forall acc,
  lin_below acc n = true -> (forall s, In s (map fst l) -> (s < n)%positive) ->
  lin_below (norm_terms B l acc) n = true.
Proof.
  induction l as [|[s k] t IH]; intros acc Hacc Hl; cbn [norm_terms]; auto.
  assert (Hk : lin_below (laxpy acc k (lsym s)) n = true).
  { apply lin_below_laxpy; auto. apply lin_below_lsym. apply Hl. simpl; auto. }
  assert (Hl' : forall s0, In s0 (map fst t) -> (s0 < n)%positive) by (intros; apply Hl; simpl; auto).
  destruct (is_fixed s && negb (Pos.eqb s SIZE)); auto.
  destruct (box_get B s) as [[lo|] [hi|]]; auto.
  destruct (Z.eqb lo hi); [apply IH; auto; now apply lin_below_laddc|auto].
Qed.

Lemma anorm_below A e n : lin_below e n = true -> lin_below (anorm A e) n = true.
Proof.
  intros H. unfold anorm. apply norm_terms_below; [reflexivity|].
  apply (proj1 (lin_below_iff e n) H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lgamma_set_store A nu S' :
  lgamma A nu -> sat nu S' -> store_below S' (vs_next A) = true -> lgamma (set_store A S') nu.
Proof.
  intros (HS&HC&HM&HV&HB) HS' Hb. destruct HB as (B0&B1&B2&B3&B4&B5).
  split; [exact HS'|]. split; [exact HC|]. split; [exact HM|]. split; [exact HV|].
  split; [exact B0|]. split; [exact Hb|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|exact B5].
Qed.

(* [comment removed for export] *)
Lemma aassume_sound A nu e :
  lgamma A nu -> eval nu e <= 0 -> lin_below e (vs_next A) = true ->
  fst (aassume A e) = true /\ lgamma (snd (aassume A e)) nu /\ aext A (snd (aassume A e)) nu nu.
Proof.
  intros H He Hb. unfold aassume.
  destruct (sat_add_constraint nu (vs_store A) e (lg_sat _ _ H) He) as [S' [E HS']]. rewrite E. simpl.
  split; [reflexivity|]. split.
  - apply lgamma_set_store; auto. eapply store_below_add_constraint; eauto. eapply lg_store_below; eauto.
  - apply aext_keep; [reflexivity|apply same_shape_set_store].
Qed.

Lemma aassume_next A e : vs_next (snd (aassume A e)) = vs_next A.
Proof. unfold aassume. destruct (add_constraint _ _); reflexivity. Qed.

Lemma aassume2_sound A nu e1 e2 :
  lgamma A nu -> eval nu e1 <= 0 -> eval nu e2 <= 0 ->
  lin_below e1 (vs_next A) = true -> lin_below e2 (vs_next A) = true ->
  fst (aassume2 A e1 e2) = true /\ lgamma (snd (aassume2 A e1 e2)) nu /\ aext A (snd (aassume2 A e1 e2)) nu nu.
Proof.
  intros H H1 H2 B1 B2. unfold aassume2.
  pose proof (aassume_sound A nu e1 H H1 B1) as (F1&L1&X1).
  pose proof (aassume_next A e1) as N1.
  destruct (aassume A e1) as [ok1 A1]. simpl in *. subst.
  pose proof (aassume_sound A1 nu e2 L1 H2 ltac:(rewrite N1; exact B2)) as (F2&L2&X2).
  destruct (aassume A1 e2) as [ok2 A2]. simpl in *. subst. simpl.
  split; [reflexivity|]. split; [exact L2|]. eapply aext_trans; eauto.
Qed.

Lemma aassume2_next A e1 e2 : vs_next (snd (aassume2 A e1 e2)) = vs_next A.
Proof.
  unfold aassume2. pose proof (aassume_next A e1). destruct (aassume A e1) as [o1 A1]. simpl in *.
  pose proof (aassume_next A1 e2). destruct (aassume A1 e2) as [o2 A2]. simpl in *. congruence.
Qed.

(* [comment removed for export] *)

Lemma ameet_cong_sound A nu s m r :
  lgamma A nu -> (m | nu s - r) -> (s < vs_next A)%positive ->
  fst (ameet_cong A s m r) = true /\ lgamma (snd (ameet_cong A s m r)) nu /\ aext A (snd (ameet_cong A s m r)) nu nu.
Proof.
  intros H Hd Hs. unfold ameet_cong.
  destruct (sat_add_cong nu (vs_store A) s m r (lg_sat _ _ H) Hd) as [S' [E HS']]. rewrite E. simpl.
  split; [reflexivity|]. split.
  - apply lgamma_set_store; auto. eapply store_below_add_cong; eauto. eapply lg_store_below; eauto.
  - apply aext_keep; [reflexivity|apply same_shape_set_store].
Qed.

Lemma ameet_cong_next A s m r : vs_next (snd (ameet_cong A s m r)) = vs_next A.
Proof. unfold ameet_cong. destruct (store_add_cong _ _ _ _); reflexivity. Qed.

Lemma asetbox_sound A nu s b :
  lgamma A nu -> in_itv (nu s) b -> (s < vs_next A)%positive ->
  lgamma (asetbox A s b) nu /\ aext A (asetbox A s b) nu nu.
Proof.
  intros H Hb Hs. unfold asetbox. split.
  - apply lgamma_set_store; auto.
    + apply sat_set_box; auto. now apply lg_sat.
    + apply store_below_set_box; auto. eapply lg_store_below; eauto.
  - apply aext_keep; [reflexivity|apply same_shape_set_store].
Qed.

Lemma agetbox_sound A nu s : lgamma A nu -> in_itv (nu s) (agetbox A s).
Proof. intros H. unfold agetbox, store_get_box. apply in_box_get. apply sat_box. now apply lg_sat. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lgamma_fresh A nu x b :
  lgamma A nu -> in_itv x b ->
  let s := vs_next A in
  lgamma (set_next (set_store A (store_set_box (vs_store A) s b)) (Pos.succ s)) (vupd nu s x)
  /\ lgamma (set_next A (Pos.succ s)) (vupd nu s x).
Proof.
  intros (HS&HC&HM&HV&HB) Hx. cbn.
  destruct HB as (B0&B1&B2&B3&B4&(C1&C2&C3)).
  set (s := vs_next A) in *.
  assert (Es : s = vs_next A) by reflexivity. clearbody s.
  assert (Hext : ext s nu (vupd nu s x)).
  { intros s' Hs'. apply vupd_other. lia. }
  assert (HC' : forall A', vs_conddef A' = vs_conddef A -> gamma_conddef (vupd nu s x) A').
  { intros A' EA b0 k x0 y0 Hg. rewrite EA in Hg. destruct (C1 _ _ _ _ Hg) as (Hb&Hx0&Hy0).
    rewrite vupd_other by lia. rewrite !(eval_ext_below s nu (vupd nu s x)) by auto. now apply HC. }
  assert (HM' : forall A', vs_moddef A' = vs_moddef A -> gamma_moddef (vupd nu s x) A').
  { intros A' EA r x0 m Hg. rewrite EA in Hg. destruct (C2 _ _ _ Hg) as (Hr&Hx0).
    rewrite vupd_other by lia. rewrite !(eval_ext_below s nu (vupd nu s x)) by auto. now apply HM. }
  assert (HV' : forall A', vs_valset A' = vs_valset A -> gamma_valset (vupd nu s x) A').
  { intros A' EA s0 vs Hg. rewrite EA in Hg. pose proof (C3 _ _ Hg). rewrite vupd_other by lia. now apply HV. }
  assert (SB : forall A', vs_conddef A' = vs_conddef A -> vs_moddef A' = vs_moddef A -> vs_valset A' = vs_valset A ->
               vs_next A' = Pos.succ s -> side_below A').
  { intros A' E1 E2 E3 EN. split; [|split].
    - intros b0 k x0 y0 Hg. rewrite E1 in Hg. destruct (C1 _ _ _ _ Hg) as (Hb&Hx0&Hy0). rewrite EN.
      split; [lia|]. split; eapply lin_below_mono; eauto; lia.
    - intros r x0 m Hg. rewrite E2 in Hg. destruct (C2 _ _ _ Hg) as (Hr&Hx0). rewrite EN.
      split; [lia|]. eapply lin_below_mono; eauto; lia.
    - intros s0 vs Hg. rewrite E3 in Hg. pose proof (C3 _ _ Hg) as X. rewrite EN. lia. }
  split.
  - split; [|split; [apply HC'; reflexivity|split; [apply HM'; reflexivity|split; [apply HV'; reflexivity|]]]].
    + simpl. apply (sat_fresh nu (vs_store A) s s b x B1 ltac:(lia) HS Hx).
    + split; [simpl; lia|]. split; [|split; [|split; [|split]]]; simpl.
      * apply store_below_set_box; [eapply store_below_mono; eauto; lia|lia].
      * intros r e Hg. cbn in *. eapply lin_below_mono; [|eapply B2; eauto]. lia.
      * intros k w e Hin. cbn in *. eapply lin_below_mono; [|eapply B3; eauto]. lia.
      * intros k w e Hin. cbn in *. eapply lin_below_mono; [|eapply B4; eauto]. lia.
      * apply SB; reflexivity.
  - split; [|split; [apply HC'; reflexivity|split; [apply HM'; reflexivity|split; [apply HV'; reflexivity|]]]].
    + simpl. apply (sat_fresh_top nu (vs_store A) s s x B1 ltac:(lia) HS).
    + split; [simpl; lia|]. split; [|split; [|split; [|split]]]; simpl.
      * eapply store_below_mono; eauto; lia.
      * intros r e Hg. cbn in *. eapply lin_below_mono; [|eapply B2; eauto]. lia.
      * intros k w e Hin. cbn in *. eapply lin_below_mono; [|eapply B3; eauto]. lia.
      * intros k w e Hin. cbn in *. eapply lin_below_mono; [|eapply B4; eauto]. lia.
      * apply SB; reflexivity.
Qed.

Lemma fresh_lin_sound A nu b x :
  lgamma A nu -> in_itv x b ->
  let '(e, A') := fresh_lin A b in
  exists nu', aext A A' nu nu' /\ lgamma A' nu' /\ eval nu' e = x /\ lin_below e (vs_next A') = true.
Proof.
  intros H Hx. pose proof (lgamma_fresh A nu x b H Hx) as [L1 L2].
  assert (X1 : aext A (set_next (set_store A (store_set_box (vs_store A) (vs_next A) b)) (Pos.succ (vs_next A)))
                    nu (vupd nu (vs_next A) x)).
  { split; [intros s' Hs'; apply vupd_other; lia|]. split; [simpl; lia|repeat split; reflexivity]. }
  assert (X2 : aext A (set_next A (Pos.succ (vs_next A))) nu (vupd nu (vs_next A) x)).
  { split; [intros s' Hs'; apply vupd_other; lia|]. split; [simpl; lia|repeat split; reflexivity]. }
  assert (Es : eval (vupd nu (vs_next A) x) (lsym (vs_next A)) = x) by (rewrite eval_lsym; apply vupd_same).
  assert (Bs : lin_below (lsym (vs_next A)) (Pos.succ (vs_next A)) = true) by (apply lin_below_lsym; lia).
  unfold fresh_lin. destruct b as [[lo|] [hi|]].
  - destruct (Z.eqb_spec lo hi).
    + subst. exists nu. split; [apply aext_refl|]. split; [exact H|]. split; [|reflexivity].
      rewrite eval_lconst. destruct Hx as [H1 H2]; simpl in *; lia.
    + exists (vupd nu (vs_next A) x). eauto.
  - exists (vupd nu (vs_next A) x). eauto.
  - exists (vupd nu (vs_next A) x). eauto.
  - exists (vupd nu (vs_next A) x). eauto.
Qed.

Lemma afresh_sound A nu b x :
  lgamma A nu -> in_itv x b ->
  let '(v, A') := afresh A b in
  exists nu', aext A A' nu nu' /\ lgamma A' nu' /\
    match v with Some e => eval nu' e = x /\ lin_below e (vs_next A') = true | None => False end.
Proof.
  intros H Hx. unfold afresh. pose proof (fresh_lin_sound A nu b x H Hx) as X.
  destruct (fresh_lin A b) as [e A']. destruct X as [nu' (X1&X2&X3&X4)]. exists nu'.
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|exact X4].
Qed.

(* [comment removed for export] *)
Lemma fresh_sym_box_sound A nu b x :
  lgamma A nu -> in_itv x b ->
  let '(s, A1) := fresh_sym A in
  let A2 := asetbox A1 s b in
  aext A A2 nu (vupd nu s x) /\ lgamma A2 (vupd nu s x) /\ vupd nu s x s = x /\ (s < vs_next A2)%positive
  /\ vs_next A2 = Pos.succ (vs_next A).
Proof.
  intros H Hx. unfold fresh_sym, asetbox. cbn.
  pose proof (lgamma_fresh A nu x b H Hx) as [L1 _].
  split; [|split; [|split; [apply vupd_same|split; [simpl; lia|reflexivity]]]].
  - split; [intros s' Hs'; apply vupd_other; lia|]. split; [simpl; lia|repeat split; reflexivity].
  - (* [comment removed for export] *)
    unfold set_store, set_next in *. simpl in *. exact L1.
Qed.

Lemma fresh_sym_top_sound A nu x :
  lgamma A nu ->
  let '(s, A1) := fresh_sym A in
  aext A A1 nu (vupd nu s x) /\ lgamma A1 (vupd nu s x) /\ vupd nu s x s = x /\ (s < vs_next A1)%positive
  /\ vs_next A1 = Pos.succ (vs_next A).
Proof.
  intros H. unfold fresh_sym. cbn.
  pose proof (lgamma_fresh A nu x itv_top H (in_itv_top x)) as [_ L2].
  split; [|split; [exact L2|split; [apply vupd_same|split; [simpl; lia|reflexivity]]]].
  split; [intros s' Hs'; apply vupd_other; lia|]. split; [simpl; lia|repeat split; reflexivity].
Qed.
