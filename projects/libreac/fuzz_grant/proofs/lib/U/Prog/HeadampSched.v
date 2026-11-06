From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel NextModel NextLemmas
  SlotNeeds_c reac_headamp_tx_arm_scene_c reac_headamp_tx_set_resweep_c HeadampI1 GrantSlotPlan SegSetModel.
Import ListNotations.
Open Scope Z_scope.

Lemma sched_S : forall k T t ws us, sched T t ws us (S k) =
  match sched T t ws us k with
  | (T1, us1) => match next_model T1 t with (r, e, T') => (T', us_step ws us1 r e) end
  end.
Proof.
  induction k as [|k IH]; intros T t ws us.
  - change (sched T t ws us 1) with
      (match next_model T t with (r, e, T') => sched T' t ws (us_step ws us r e) 0 end).
    change (sched T t ws us 0) with (T, us). cbv beta iota.
    destruct (next_model T t) as [[r e] T']. reflexivity.
  - change (sched T t ws us (S (S k))) with
      (match next_model T t with (r, e, T') => sched T' t ws (us_step ws us r e) (S k) end).
    change (sched T t ws us (S k)) with
      (match next_model T t with (r, e, T') => sched T' t ws (us_step ws us r e) k end).
    destruct (next_model T t) as [[r e] T']. apply IH.
Qed.

Lemma fold_437 : forall cs s, Forall cell_ok cs -> length (fst (fst s)) = 460%nat -> tb (fst (fst s)) 437 = 0 ->
  length (fst (fst (fold_left set_step cs s))) = 460%nat /\ tb (fst (fst (fold_left set_step cs s))) 437 = 0.
Proof.
  induction cs as [|x cs IH]; intros s Hok HL H; [split; assumption|].
  inversion Hok as [|? ? Hx Hcs]; subst. cbn [fold_left].
  destruct s as [[T ws] st]. destruct x as [[c q] v]. destruct Hx as (Hc & Hq & Hv).
  rewrite set_step_cell. destruct ((c <? 48) && legalb q v) eqn:E; [|apply IH; assumption].
  apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1.
  pose proof (legal_bound q v (legalb_legal q v ltac:(lia) ltac:(lia) E2)) as (Bq & Bv).
  cbn [fst] in HL, H. apply IH; [exact Hcs | cbn [fst]; apply len_set_T; [exact HL | lia | lia] |].
  cbn [fst]. rewrite tb_set_T by lia. dec. cbn [andb]. exact H.
Qed.

Lemma T_end_437 : forall pl, tb (T_end pl) 437 = 0.
Proof.
  intros pl. unfold T_end, tables_end, tables_at, after_sets, cells_upto.
  apply (fold_437 _ (T0, Z144, Z144)); [apply cells_ok | reflexivity | apply tb_repeat0].
Qed.

Lemma sched_rd_range : forall pl, match sched_rd pl with (sb, sw, _, _, _) => 0 <= sb < 256 /\ 0 <= sw < 256 end.
Proof.
  intros pl. unfold sched_rd.
  pose proof (rd8_range pl (pos_raw pl)) as R1. destruct (rd8 pl (pos_raw pl)) as [sb p1]. cbv beta iota zeta.
  pose proof (rd8_range pl p1) as R2. destruct (rd8 pl p1) as [sw p2]. cbv beta iota zeta.
  destruct (rd32 pl p2) as [per p3]. cbv beta iota zeta. destruct (rd16 pl p3) as [fr p4].
  cbn [fst] in R1, R2. split; assumption.
Qed.

Definition sbw (pl : list byte) : Z * Z := match sched_rd pl with (sb, sw, _, _, _) => (sb, sw) end.

Definition Done (k : Z) (T : list byte) : Prop :=
  ~ complete T \/ (forall j, s32 T 440 <= j < 3 * tb T 437 -> ~ (j mod 3 = k mod 3 /\ tb T 436 + j / 3 = k / 3)).

Definition sinv (pl T us : list byte) : Prop :=
  length T = 460%nat /\ I1 T /\ lowsame (T_end pl) T /\ length us = 144%nat /\
  (complete T -> snd (sbw pl) <> 0 /\ fst (sbw pl) < 48 /\ tb T 436 = fst (sbw pl) /\ tb T 437 <= snd (sbw pl)) /\
  (forall k, 0 <= k < 144 -> tb (ws_end pl) k = 0 -> tb us k = 0 \/ (tb us k = 1 /\ Done k T)).

Lemma complete_dec : forall T, complete T \/ ~ complete T.
Proof.
  intros T. unfold complete. destruct (Z.eq_dec (tb T 437) 0); destruct (Z.eq_dec (tb T 448) 0); [right | right | left | right]; tauto.
Qed.

Lemma Done_mono : forall k T T', phase_le T T' -> Done k T -> Done k T'.
Proof.
  intros k T T' Hp [D|D]; destruct (complete_dec T') as [C|C]; try (left; exact C).
  - destruct (Hp C) as (C0 & _). contradiction.
  - right. destruct (Hp C) as (_ & E6 & E7 & Ex). intros j Hj. rewrite E6. apply D. lia.
Qed.

Lemma lowsame_trans : forall A B C, lowsame A B -> lowsame B C -> lowsame A C.
Proof. intros A B C H1 H2 i Hi. rewrite H2, H1 by lia. reflexivity. Qed.

Lemma sinv_0 : forall pl, sinv pl (T_sched0 pl) Z144.
Proof.
  intros pl. destruct (tables_end_inv pl) as (HL & Hw & Hs & HI & HH). pose proof (T_end_437 pl) as H437.
  pose proof (sched_rd_range pl) as Rg.
  unfold sinv, T_sched0, sbw. destruct (sched_rd pl) as [[[[sb sw] per] fr] p4]. destruct Rg as (Rsb & Rsw).
  cbn [fst snd].
  assert (U0 : forall k, 0 <= k < 144 -> tb (ws_end pl) k = 0 -> tb Z144 k = 0 \/ (tb Z144 k = 1 /\ Done k (T_end pl)))
    by (intros k Hk Hz; left; apply tb_repeat0).
  destruct ((sw =? 0) || (48 <=? sb)) eqn:Ea.
  - destruct (I1_set_resweep_T (T_end pl) per HI HL) as (I2 & L2 & Lw2 & E6 & E7 & E8).
    split; [exact L2|]. split; [exact I2|]. split; [exact Lw2|]. split; [reflexivity|].
    split; [intros (C & _); rewrite E7 in C; contradiction|].
    intros k Hk Hz. left. apply tb_repeat0.
  - apply orb_false_iff in Ea as [Ea1 Ea2]. apply Z.eqb_neq in Ea1. apply Z.leb_gt in Ea2.
    destruct (I1_arm_T (T_end pl) sb sw HI HL ltac:(lia) ltac:(lia)) as (I1a & L1a & Lw1 & A6 & A7 & A8 & AX).
    destruct (I1_set_resweep_T (arm_T (T_end pl) sb sw) per I1a L1a) as (I2 & L2 & Lw2 & E6 & E7 & E8).
    pose proof (arm_w_range sb sw ltac:(lia) ltac:(lia)) as Aw.
    split; [exact L2|]. split; [exact I2|]. split; [exact (lowsame_trans _ _ _ Lw1 Lw2)|]. split; [reflexivity|].
    split; [intros _; rewrite E6, E7, A6, A7; lia|].
    intros k Hk Hz. left. apply tb_repeat0.
Qed.

Lemma us_step_0 : forall ws us e, us_step ws us 0 e = us.
Proof. intros ws us [[c q] v]. reflexivity. Qed.

Lemma sinv_step : forall pl t T us, sinv pl T us ->
  match next_model T t with (r, e, T') => sinv pl T' (us_step (ws_end pl) us r e) end.
Proof.
  intros pl t T us (HL & HI & Hlow & Hus & K1 & U).
  pose proof (next_props T t HI HL) as F. destruct (tables_end_inv pl) as (HLe & Hwe & Hse & HIe & HH).
  destruct (next_model T t) as [[r [[c p] v]] T'] eqn:En.
  destruct F as (Hok & Hs' & Hp' & Hr & Hf). pose proof Hok as (HL' & Hl' & _ & _).
  assert (HI' : I1 T') by exact (I1_step T T' HI Hok Hs').
  assert (K1' : complete T' -> snd (sbw pl) <> 0 /\ fst (sbw pl) < 48 /\ tb T' 436 = fst (sbw pl) /\
                tb T' 437 <= snd (sbw pl)).
  { intros C. destruct (Hp' C) as (C0 & E6 & E7 & _). rewrite E6, E7. exact (K1 C0). }
  assert (Lw' : lowsame (T_end pl) T') by exact (lowsame_trans _ _ _ Hlow Hl').
  assert (Ukeep : forall us', length us' = 144%nat ->
            (forall k, 0 <= k < 144 -> tb (ws_end pl) k = 0 -> tb us' k = tb us k) -> sinv pl T' us').
  { intros us' Hl2 Hk. split; [exact HL'|]. split; [exact HI'|]. split; [exact Lw'|]. split; [exact Hl2|].
    split; [exact K1'|]. intros k Hk1 Hz. rewrite (Hk k Hk1 Hz).
    destruct (U k Hk1 Hz) as [U0|(U1 & D)]; [left; exact U0 | right; split; [exact U1 | exact (Done_mono k T T' Hp' D)]]. }
  destruct Hr as [-> | ->].
  { rewrite us_step_0. apply Ukeep; [exact Hus | intros; reflexivity]. }
  destruct (Hf eq_refl) as (Hc & Hp & _ & _ & _).
  unfold us_step. rewrite (proj2 (Z.ltb_lt c 48)), (proj2 (Z.ltb_lt p 3)) by lia. cbn [Z.eqb andb Pos.eqb].
  destruct (Z.eqb_spec (tb (ws_end pl) (3 * c + p)) 0) as [Wz|Wnz]; cbn [andb].
  - assert (Hz : tb T (144 + 3 * c + p) = 0).
    { rewrite (Hlow (144 + 3 * c + p)) by lia. destruct (HH c p Hc Hp) as (Hw1 & _). rewrite <- Hw1. exact Wz. }
    destruct (next_unset_emit T t c p v T' HI HL En Hz) as (C & Ec & Ep & HXw & HX' & _ & _).
    assert (U0 : tb us (3 * c + p) = 0).
    { destruct (U (3 * c + p) ltac:(lia) Wz) as [U0|(_ & [D|D])]; [exact U0 | contradiction |].
      exfalso. apply (D (s32 T 440)); [pose proof (I1_scal T HI) as (_ & _ & (Q7 & _) & _); lia|].
      split; [rewrite Ep; Z.div_mod_to_equations; lia | rewrite Ec; Z.div_mod_to_equations; lia]. }
    rewrite U0. split; [exact HL'|]. split; [exact HI'|]. split; [exact Lw'|].
    split; [apply len_ws_put; [exact Hus | lia | lia]|]. split; [exact K1'|].
    intros k Hk1 Hzk. rewrite tb_ws_put by (try exact Hus; lia).
    destruct (Z.eqb_spec k (3 * c + p)) as [Ek|Ek].
    + right. split; [reflexivity|]. destruct (complete_dec T') as [C'|C']; [|left; exact C'].
      right. destruct (Hp' C') as (_ & E6 & E7 & _). intros j Hj (Hm & Hd).
      rewrite HX' in Hj. rewrite E6 in Hd. subst k. rewrite Ec, Ep in Hm, Hd. Z.div_mod_to_equations. lia.
    + destruct (U k Hk1 Hzk) as [U1|(U1 & D)]; [left; exact U1|]. right. split; [exact U1 | exact (Done_mono k T T' Hp' D)].
  - apply Ukeep; [exact Hus | intros; reflexivity].
Qed.

Lemma sinv_at : forall pl t i, sinv pl (fst (sched_at pl t i)) (snd (sched_at pl t i)).
Proof.
  intros pl t i. induction i as [|i IH]; [exact (sinv_0 pl)|].
  unfold sched_at in *. rewrite sched_S.
  destruct (sched (T_sched0 pl) t (ws_end pl) Z144 i) as [T us]. cbn [fst snd] in IH.
  pose proof (sinv_step pl t T us IH) as H. destruct (next_model T t) as [[r e] T']. exact H.
Qed.

Lemma sched0_ok : forall pl, I1 (T_sched0 pl) /\ length (T_sched0 pl) = 460%nat.
Proof. intros pl. destruct (sinv_0 pl) as (HL & HI & _). split; assumption. Qed.

Theorem phase_unset_once_holds : phase_unset_once.
Proof.
  unfold phase_unset_once. intros pl t i c q Hc Hq Hz.
  destruct (sinv_at pl t i) as (_ & _ & _ & _ & _ & U).
  destruct (U (3 * c + q) ltac:(lia) Hz) as [U0|(U1 & _)]; lia.
Qed.

Lemma frame_ok : forall pl t i, 0 < t ->
  let '(sb, sw, _, _, _) := sched_rd pl in
  let '(T, us) := sched_at pl t i in
  match NextModel.next_model T t with
  | (r, (c, p, v), T') =>
    length T = 460%nat /\ length us = 144%nat /\ 0 <= NextModel.s32 T 440 /\ length T' = 460%nat /\ I1 T' /\
    sched_at pl t (S i) = (T', us_step (ws_end pl) us r (c, p, v)) /\ (r = 0 \/ r = 1) /\
    (r = 1 -> 0 <= c < 48 /\ 0 <= p < 3 /\ legal p v /\ v = eff T' t c p /\
       (tb (ws_end pl) (3 * c + p) <> 0 -> v = tb (st_end pl) (3 * c + p)) /\
       (tb (ws_end pl) (3 * c + p) = 0 -> v = dflt p /\ sw <> 0 /\ sb < 48 /\ sb <= c < sb + sw /\
          tb us (3 * c + p) = 0))
  end.
Proof.
  intros pl t i Ht. pose proof (sinv_at pl t i) as SI.
  assert (ES : sched_at pl t (S i) =
    match sched_at pl t i with
    | (T1, us1) => match next_model T1 t with (r, e, T') => (T', us_step (ws_end pl) us1 r e) end
    end) by (unfold sched_at; apply sched_S).
  destruct (tables_end_inv pl) as (HLe & Hwe & Hse & HIe & HH).
  unfold sinv, sbw in SI.
  destruct (sched_rd pl) as [[[[sb sw] per] fr] p4].
  destruct (sched_at pl t i) as [T us]. cbn [fst snd] in SI.
  destruct SI as (HL & HI & Hlow & Hus & K1 & U). cbn [fst snd] in K1.
  pose proof (next_props T t HI HL) as F.
  destruct (next_model T t) as [[r [[c p] v]] T'] eqn:En.
  destruct F as (Hok & Hs' & Hp' & Hr & Hf). pose proof Hok as (HL' & Hl' & _ & _).
  split; [exact HL|]. split; [exact Hus|]. split; [exact (proj1 (proj1 (proj2 (proj2 (I1_scal T HI)))))|].
  split; [exact HL'|]. split; [exact (I1_step T T' HI Hok Hs')|]. split; [exact ES|]. split; [exact Hr|].
  intros E1. destruct (Hf E1) as (Hc & Hp & Hlg & Hv & Hrest). pose proof (Hv ltac:(lia)) as Hv'.
  split; [exact Hc|]. split; [exact Hp|]. split; [exact Hlg|].
  split; [rewrite (eff_lowsame T T') by assumption; exact Hv'|].
  destruct (HH c p Hc Hp) as (Hw1 & Hs1).
  assert (Eset : tb T (144 + 3 * c + p) = tb (ws_end pl) (3 * c + p)).
  { rewrite (Hlow (144 + 3 * c + p)) by lia. rewrite Hw1. reflexivity. }
  split.
  - intros Wnz. rewrite Hv'. rewrite eff_cell by lia.
    pose proof (proj1 (proj1 HIe (3 * c + p) ltac:(lia))) as B. pose proof (tb_range (T_end pl) (144 + (3 * c + p))).
    rewrite Eset. rewrite (proj2 (Z.eqb_neq _ 0) Wnz). rewrite (Hlow (3 * c + p)) by lia. symmetry. exact Hs1.
  - intros Wz. assert (Hz : tb T (144 + 3 * c + p) = 0) by (rewrite Eset; exact Wz).
    subst r. destruct (next_unset_emit T t c p v T' HI HL En Hz) as (C & Ec & Ep & HXw & HX' & _ & _).
    split; [rewrite Hv'; rewrite eff_cell by lia; rewrite Hz; reflexivity|].
    destruct (K1 C) as (Ksw & Ksb & K6 & K7).
    split; [exact Ksw|]. split; [exact Ksb|].
    split; [rewrite Ec; pose proof (I1_scal T HI) as (_ & _ & (Q7 & _) & _); split; [pose proof (Z.div_pos (s32 T 440) 3 Q7 ltac:(lia)); lia|]; Z.div_mod_to_equations; lia|].
    destruct (U (3 * c + p) ltac:(lia) Wz) as [U0|(_ & [D|D])]; [exact U0 | contradiction |].
    exfalso. apply (D (s32 T 440)); [pose proof (I1_scal T HI) as (_ & _ & (Q7 & _) & _); lia|].
    split; [rewrite Ep; Z.div_mod_to_equations; lia | rewrite Ec; Z.div_mod_to_equations; lia].
Qed.

Ltac dec2 := repeat match goal with
  | |- context [?a =? ?b] => first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
  | |- context [?a <=? ?b] => first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
  | |- context [?a <? ?b] => first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  end; cbn [andb orb].

Ltac decall := repeat (first [ progress dec2 | progress (cbv beta iota) ]).

Lemma eff_set_T_same : forall T c q v t, length T = 460%nat -> 0 <= c < 48 -> 0 <= q < 3 -> 0 <= v < 256 -> t <> 0 ->
  eff (reac_headamp_tx_set_c.set_T T c q v) t c q = v.
Proof.
  intros T c q v t HL Hc Hq Hv Ht. rewrite eff_cell by lia.
  rewrite !tb_set_T by lia. decall. reflexivity.
Qed.

Lemma eff_set_T_other : forall T c q v t c' q', length T = 460%nat -> 0 <= c < 48 -> 0 <= q < 3 -> 0 <= v < 256 ->
  0 <= c' -> 0 <= q' -> (c' <> c \/ q' <> q) ->
  eff (reac_headamp_tx_set_c.set_T T c q v) t c' q' = eff T t c' q'.
Proof.
  intros T c q v t c' q' HL Hc Hq Hv Hc' Hq' Hne.
  destruct (Z_lt_le_dec q' 3) as [Q3|Q3]; [|rewrite !eff_p3 by lia; reflexivity].
  destruct (Z.eq_dec t 0) as [->|Ht]; [rewrite !eff_t0 by lia; reflexivity|].
  destruct (Z_lt_le_dec c' 48) as [C48|C48]; [|rewrite !eff_ch by lia; reflexivity].
  rewrite !eff_cell by lia. rewrite !tb_set_T by lia.
  assert (N : 3 * c' + q' <> 3 * c + q) by lia.
  decall. reflexivity.
Qed.
