(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition bytes_ok (p : list Z) : Prop := Forall (fun b => 0 <= b < 256) p.

Lemma blen_nonneg p : 0 <= blen p. Proof. unfold blen. lia. Qed.

Lemma be_val_bound : forall l acc, Forall (fun b => 0 <= b < 256) l -> 0 <= acc ->
  0 <= be_val l acc < (acc + 1) * 256 ^ Z.of_nat (length l).
Proof.
  induction l as [|b l IH]; intros acc Hl Hacc; cbn [be_val length].
  - cbn. lia.
  - inversion Hl as [|? ? Hb Hl']; subst.
    specialize (IH (acc * 256 + b) Hl' ltac:(lia)).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma Forall_firstn {A} (P : A -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof. revert l. induction n; intros [|a l] H; cbn; try constructor; inversion H; subst; auto. Qed.
Lemma Forall_skipn {A} (P : A -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof. revert l. induction n; intros [|a l] H; cbn; auto. inversion H; subst; auto. Qed.

Lemma rd_be_bound p i k : bytes_ok p -> 0 <= k -> 0 <= rd_be p i k < 256 ^ k.
Proof.
  intros Hp Hk. unfold rd_be.
  pose proof (be_val_bound (slice p i k) 0 (Forall_firstn _ _ _ (Forall_skipn _ _ _ Hp)) ltac:(lia)) as B.
  assert (L : Z.of_nat (length (slice p i k)) <= k) by (unfold slice; rewrite length_firstn; lia).
  assert (256 ^ Z.of_nat (length (slice p i k)) <= 256 ^ k) by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Lemma int_width_cases t : int_width t = 0 \/ int_width t = 1 \/ int_width t = 2 \/ int_width t = 4 \/ int_width t = 8.
Proof. unfold int_width. repeat (destruct (_ =? _); [tauto|]). tauto. Qed.

Lemma sgn_nonneg k v : (k = 1 \/ k = 2 \/ k = 4 \/ k = 8) -> 0 <= v < 256 ^ k -> 0 <= sgn k v -> sgn k v < 2 ^ 63.
Proof.
  intros Hk Hv. unfold sgn.
  destruct Hk as [Hk|[Hk|[Hk|Hk]]]; subst k; cbn in *; destruct (v <? _) eqn:E; try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Lemma get_length_some p pos n pos1 : bytes_ok p -> 0 <= pos ->
  get_length p pos = Some (n, pos1) -> 0 <= n < 2 ^ 63 /\ pos + 2 <= pos1 <= blen p /\ pos1 <= pos + 9.
Proof.
  intros Hp Hpos. unfold get_length.
  destruct (blen p <=? pos) eqn:E1; [discriminate|].
  destruct (int_width (bat p pos) =? 0) eqn:E2; [discriminate|].
  destruct (blen p <? pos + 1 + int_width (bat p pos)) eqn:E3; [discriminate|].
  apply Z.eqb_neq in E2. apply Z.ltb_ge in E3. apply Z.leb_gt in E1.
  pose proof (int_width_cases (bat p pos)) as W.
  assert (Wk : int_width (bat p pos) = 1 \/ int_width (bat p pos) = 2 \/ int_width (bat p pos) = 4 \/ int_width (bat p pos) = 8) by tauto.
  assert (W0 : 0 <= int_width (bat p pos)) by (destruct Wk as [Wk|[Wk|[Wk|Wk]]]; rewrite Wk; lia).
  pose proof (rd_be_bound p (pos + 1) (int_width (bat p pos)) Hp W0) as RB.
  destruct (bat p pos =? 85) eqn:E4.
  -
    apply Z.eqb_eq in E4. assert (int_width (bat p pos) = 1) as W1 by (rewrite E4; reflexivity). rewrite W1 in *.
    destruct (rd_be p (pos + 1) 1 <? 0) eqn:E5; [discriminate|]. intros H. injection H as <- <-. change (256 ^ 1) with 256 in RB. change (2 ^ 63) with 9223372036854775808. lia.
  - destruct (sgn (int_width (bat p pos)) (rd_be p (pos + 1) (int_width (bat p pos))) <? 0) eqn:E5; [discriminate|].
    apply Z.ltb_ge in E5. intros H. injection H as <- <-.
    pose proof (sgn_nonneg _ _ Wk RB E5). lia.
Qed.

Ltac simp_st := cbn [s_stk s_pos s_more s_done s_halt s_depth s_ec s_estk s_edepth s_lo s_hi s_bad
                     w_stk w_pos w_more w_done w_halt w_depth w_ec w_estk w_edepth w_out w_bad] in *.

Ltac zb := repeat match goal with
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

Definition ei_ok (e : eitem) : Prop := 0 <= ei_len e <= MAX_ITEMS /\ 0 <= ei_cnt e < TWO64 /\ 0 <= ei_kind e <= 3.

Lemma pl_size_pos n : 2 <= pl_size n <= 9.
Proof. unfold pl_size. repeat destruct (_ <=? _); lia. Qed.

Definition container_mode (m : pmode) : bool := match m with Mroot | Maccept => false | _ => true end.
Definition counted_mode (m : pmode) : bool := match m with Marray | Mtarray | Mkey | Mval | Mtkey | Mtval => true | _ => false end.
Definition ps_ok (t : pstate) : Prop :=
  0 <= ps_idx t /\ 0 <= ps_len t <= MAX_ITEMS /\
  (if counted_mode (ps_mode t) then ps_idx t <= ps_len t else ps_len t = 0 /\ ps_idx t <= MAX_ITEMS)
  /\ 0 <= ps_type t < 256.
Lemma bat_range p i : bytes_ok p -> 0 <= bat p i < 256.
Proof.
  intros Hp. unfold bat. destruct (nth_in_or_default (Z.to_nat i) p 0) as [IN| ->]; [|lia].
  exact (proj1 (Forall_forall _ _) Hp _ IN).
Qed.

Definition fmode (m : pmode) : Z := match m with Mval | Mtval | Mival => 1 | _ => 0 end.
Definition alive_eff (s s' : st) : Prop :=
  (s_stk s' = s_stk s /\ s_depth s' = s_depth s /\ s_edepth s' = s_edepth s /\ length (s_estk s') = length (s_estk s))
  \/ (exists c, s_stk s' = c :: s_stk s /\ container_mode (ps_mode c) = true /\ fmode (ps_mode c) = 0 /\ ps_ok c /\ ps_idx c = 0
        /\ s_depth s' = s_depth s + 1 /\ s_depth s' <= MAX_DEPTH /\ s_edepth s' = s_edepth s + 1
        /\ length (s_estk s') = S (length (s_estk s))
        /\ (counted_mode (ps_mode c) = true -> s_pos s + 1 <= s_pos s')).

Definition eff (p : list Z) (s s' : st) : Prop :=
  s_bad s' = false /\ s_done s' = s_done s /\ s_halt s' = s_halt s
  /\ s_pos s <= s_pos s' <= blen p
  /\ s_lo s <= s_lo s' /\ s_lo s' <= s_hi s'
  /\ s_hi s' - s_lo s' <= (s_hi s - s_lo s) + (s_pos s' - s_pos s)
  /\ Forall ei_ok (s_estk s')
  /\ ((s_more s' = false \/ s_ec s' = true)
      \/ (s_more s' = true /\ s_ec s' = false /\ s_ec s = false /\ alive_eff s s')).

Definition pre (p : list Z) (s : st) : Prop :=
  bytes_ok p /\ 0 <= s_pos s <= blen p /\ s_lo s <= s_hi s /\ s_bad s = false /\ s_edepth s = s_depth s /\ Forall ei_ok (s_estk s).

Lemma Forall_ei_bump e r : Forall ei_ok (e :: r) -> Forall ei_ok (EI (ei_kind e) (ei_len e) ((ei_cnt e + 1) mod TWO64) :: r).
Proof.
  intros H. inversion H as [|? ? [A [B C]] D]; subst. constructor; [| exact D].
  unfold ei_ok; cbn. pose proof (Z.mod_pos_bound (ei_cnt e + 1) TWO64 ltac:(unfold TWO64; lia)). lia.
Qed.

Lemma eev_stk s : s_stk (e_end_value s) = s_stk s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_pos s : s_pos (e_end_value s) = s_pos s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_more s : s_more (e_end_value s) = s_more s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_done s : s_done (e_end_value s) = s_done s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_halt s : s_halt (e_end_value s) = s_halt s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_depth s : s_depth (e_end_value s) = s_depth s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_ec s : s_ec (e_end_value s) = s_ec s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_edepth s : s_edepth (e_end_value s) = s_edepth s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_lo s : s_lo (e_end_value s) = s_lo s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_hi s : s_hi (e_end_value s) = s_hi s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_bad s : s_bad (e_end_value s) = s_bad s. Proof. unfold e_end_value; destruct (s_estk s); reflexivity. Qed.
Lemma eev_len s : length (s_estk (e_end_value s)) = length (s_estk s).
Proof. unfold e_end_value; destruct (s_estk s) eqn:E; simp_st; rewrite ?E; reflexivity. Qed.
Lemma eev_ok s : Forall ei_ok (s_estk s) -> Forall ei_ok (s_estk (e_end_value s)).
Proof. unfold e_end_value; destruct (s_estk s) eqn:E; simp_st; rewrite ?E; intros H; [exact H | apply Forall_ei_bump; exact H]. Qed.
#[global] Opaque e_end_value.
Ltac eev := rewrite ?eev_stk, ?eev_pos, ?eev_more, ?eev_done, ?eev_halt, ?eev_depth, ?eev_ec, ?eev_edepth, ?eev_lo, ?eev_hi, ?eev_bad, ?eev_len in *.

Lemma e_put_length_ok n s : n <= INT64_MAX -> e_put_length n s = w_out (pl_size n) (pl_size n) s.
Proof. intros H. unfold e_put_length. destruct (INT64_MAX <? n) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. Qed.

Ltac norm := zb; repeat progress (simp_st; eev; repeat match goal with H : s_ec ?x = _ |- context [s_ec ?x] => rewrite H end).
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac dying := left; first [left; reflexivity | right; reflexivity | left; assumption | right; assumption].

Lemma r_num_eff p k lo hi s : pre p s -> 0 <= k -> 0 <= lo <= hi -> hi - lo <= k -> eff p s (r_num p k lo hi s).
Proof.
  intros (Hp & Hpos & Hlh & Hbad & Hed & Hes) Hk Hlo Hsp. unfold r_num, r_fail, e_scalar, eff.
  destruct (blen p <? s_pos s + k) eqn:E1; norm; splits; try first [reflexivity | assumption | lia | (apply eev_ok; assumption) | dying].
  destruct (s_ec s) eqn:EC; [left; right; reflexivity|].
  right. splits; try reflexivity. left. norm. splits; reflexivity.
Qed.

Lemma INT64_MAX_val : INT64_MAX = 2 ^ 63 - 1. Proof. reflexivity. Qed.

Lemma r_key_eff p s : pre p s -> eff p s (r_key p s).
Proof.
  intros (Hp & Hpos & Hlh & Hbad & Hed & Hes). unfold r_key, r_fail, e_key, eff.
  destruct (get_length p (s_pos s)) as [[n pos1]|] eqn:G.
  2:{ norm; splits; try first [reflexivity | assumption | lia | dying]. }
  destruct (get_length_some p (s_pos s) n pos1 Hp (proj1 Hpos) G) as (Hn & Hp1 & _).
  pose proof (pl_size_pos n) as PL.
  destruct (s_ec s) eqn:EC.
  { norm; splits; try first [reflexivity | assumption | lia | dying]. }
  destruct (blen p <? pos1 + n) eqn:E1.
  { norm; splits; try first [reflexivity | assumption | lia | dying]. }
  destruct (utf8_valid (slice p pos1 n)) eqn:V.
  2:{ norm; splits; try first [reflexivity | assumption | lia | dying]. }
  rewrite e_put_length_ok by (rewrite INT64_MAX_val; lia).
  norm; splits; try first [reflexivity | assumption | lia].
  right. splits; try first [reflexivity | assumption]. left. norm. splits; reflexivity.
Qed.

Lemma MAX_ITEMS_val : MAX_ITEMS = 16777216. Proof. reflexivity. Qed.
Lemma MAX_DEPTH_val : MAX_DEPTH = 1024. Proof. reflexivity. Qed.

Lemma r_begin_eff p obj s : pre p s -> eff p s (r_begin p obj s).
Proof.
  intros (Hp & Hpos & Hlh & Hbad & Hed & Hes). unfold r_begin, eff. simp_st.
  destruct (MAX_DEPTH <? s_depth s + 1) eqn:D1.
  { unfold r_fail. norm; splits; try first [reflexivity | assumption | lia | dying]. }
  destruct (blen p <=? s_pos s) eqn:E0.
  { unfold r_fail. norm; splits; try first [reflexivity | assumption | lia | dying]. }
  assert (CNT : forall mode ty kind k, counted_mode mode = true -> container_mode mode = true -> fmode mode = 0 -> 0 <= kind <= 3 -> 1 <= k -> s_pos s + k <= blen p -> 0 <= ty < 256 ->
            let s1 := w_pos (s_pos s + k) (w_depth (s_depth s + 1) s) in
            let s' := r_counted p mode ty kind s1 in
            s_bad s' = false /\ s_done s' = s_done s /\ s_halt s' = s_halt s /\ s_pos s <= s_pos s' <= blen p /\
            s_lo s <= s_lo s' /\ s_lo s' <= s_hi s' /\ s_hi s' - s_lo s' <= s_hi s - s_lo s + (s_pos s' - s_pos s) /\
            Forall ei_ok (s_estk s') /\
            (s_more s' = false \/ s_ec s' = true \/ s_more s' = true /\ s_ec s' = false /\ s_ec s = false /\ alive_eff s s')).
  { intros mode ty kind k Hcm Hct Hfm Hkind Hk Hkb Hty s1 s'. subst s1 s'. unfold r_counted, r_fail. simp_st. zb.
    destruct (get_length p (s_pos s + k)) as [[n pos1]|] eqn:G.
    2:{ norm; splits; try first [reflexivity | assumption | lia | (left; reflexivity)]. }
    destruct (get_length_some p (s_pos s + k) n pos1 Hp ltac:(lia) G) as (Hn & Hp1 & _).
    pose proof (pl_size_pos n) as PL.
    destruct (s_ec s) eqn:EC.
    { norm; splits; try first [reflexivity | assumption | lia | (right; left; reflexivity)]. }
    destruct (MAX_ITEMS <? n) eqn:E1.
    { norm; splits; try first [reflexivity | assumption | lia | (left; reflexivity)]. }
    unfold e_begin_len. simp_st. rewrite Hed.
    replace (MAX_DEPTH <? s_depth s + 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite e_put_length_ok by (rewrite INT64_MAX_val; lia).
    norm; splits; try first [reflexivity | assumption | lia].
    - constructor; [unfold ei_ok; cbn; rewrite MAX_ITEMS_val in *; unfold TWO64; lia | exact Hes].
    - right. right. splits; try reflexivity. right. exists (PS mode n ty 0). norm. cbn [ps_mode ps_idx]. rewrite ?Hcm.
      splits; try first [reflexivity | assumption | lia]. unfold ps_ok; cbn [ps_mode ps_idx ps_len ps_type]. rewrite Hcm. lia. }
  destruct (bat p (s_pos s) =? 36) eqn:C1.
  { destruct (blen p <=? s_pos s + 1) eqn:E1.
    { unfold r_fail. norm; splits; try first [reflexivity | assumption | lia | dying]. }
    destruct (blen p <=? s_pos s + 2) eqn:E2.
    { unfold r_fail. norm; splits; try first [reflexivity | assumption | lia | dying]. }
    destruct (bat p (s_pos s + 2) =? 35) eqn:C2.
    2:{ unfold r_fail. norm; splits; try first [reflexivity | assumption | lia | dying]. }
    zb.
    pose proof (CNT (if obj then Mtkey else Mtarray) (bat p (s_pos s + 1)) (if obj then 0 else 2) 3
                  ltac:(destruct obj; reflexivity) ltac:(destruct obj; reflexivity) ltac:(destruct obj; reflexivity) ltac:(destruct obj; lia) ltac:(lia) ltac:(lia) (bat_range p _ Hp)) as H.
    cbv zeta in H. destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 _)))))))).
    destruct A9 as [A9|[A9|A9]]; [left; left; exact A9 | left; right; exact A9 | right; exact A9]. }
  destruct (bat p (s_pos s) =? 35) eqn:C2.
  { zb.
    pose proof (CNT (if obj then Mkey else Marray) 0 (if obj then 0 else 2) 1
                  ltac:(destruct obj; reflexivity) ltac:(destruct obj; reflexivity) ltac:(destruct obj; reflexivity) ltac:(destruct obj; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H.
    cbv zeta in H. destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 _)))))))).
    destruct A9 as [A9|[A9|A9]]; [left; left; exact A9 | left; right; exact A9 | right; exact A9]. }

  unfold e_begin_indef. simp_st. rewrite Hed.
  replace (MAX_DEPTH <? s_depth s + 1) with false by (symmetry; apply Z.ltb_ge; zb; lia).
  norm; splits; try first [reflexivity | assumption | lia].
  - constructor; [unfold ei_ok; cbn; rewrite MAX_ITEMS_val; unfold TWO64; destruct obj; lia | exact Hes].
  - destruct (s_ec s) eqn:EC; [left; right; reflexivity|].
    right. splits; try reflexivity. right. exists (PS (if obj then Mikey else Miarray) 0 0 0). norm.
    splits; try first [reflexivity | assumption | lia | (destruct obj; reflexivity)].
    all: try (unfold ps_ok; destruct obj; cbn; rewrite ?MAX_ITEMS_val; lia).
Qed.

Lemma eff_fin p s s' : eff p s s' -> eff p s (if s_ec s' then w_more false s' else s').
Proof.
  intros H. destruct (s_ec s') eqn:EC; [| exact H].
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  unfold eff. simp_st. refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 _)))))))). left. left. reflexivity.
Qed.
Lemma eff_fin_more p s s' : eff p s s' -> eff p s (if s_more s' then (if s_ec s' then w_more false s' else s') else s').
Proof. intros H. destruct (s_more s'); [apply eff_fin; exact H | exact H]. Qed.

Lemma eff_shift p s k s' : 0 <= k -> 0 <= s_pos s -> s_lo s <= s_hi s -> eff p (w_pos (s_pos s + k) s) s' -> eff p s s' /\ s_pos s + k <= s_pos s'.
Proof.
  intros Hk Hpos Hlh (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold eff, alive_eff in *. simp_st. split; [|lia].
  splits; try first [assumption | lia].
  destruct A9 as [A9|(B1 & B2 & B3 & B4)]; [left; exact A9|]. right. splits; try assumption.
  destruct B4 as [B4|(c & C1 & C2 & C2f & C3 & C4 & C5 & C6 & C7 & C8 & C9)]; [left; exact B4|].
  right. exists c. splits; try assumption. intros Hc. specialize (C9 Hc). lia.
Qed.

Definition pre_run (p : list Z) (s : st) : Prop := pre p s /\ s_more s = true.

Lemma pre_w_pos p s k : pre p s -> 0 <= k -> s_pos s + k <= blen p -> pre p (w_pos (s_pos s + k) s).
Proof. intros (Hp & Hpos & Hlh & Hbad & Hed & Hes) Hk Hb. unfold pre. simp_st. splits; try assumption; lia. Qed.

Lemma eff_refl_dying p s : pre p s -> forall s', s_bad s' = false -> s_done s' = s_done s -> s_halt s' = s_halt s -> s_pos s' = s_pos s ->
  s_lo s' = s_lo s -> s_hi s' = s_hi s -> s_estk s' = s_estk s -> (s_more s' = false \/ s_ec s' = true) -> eff p s s'.
Proof.
  intros (Hp & Hpos & Hlh & Hbad & Hed & Hes) s' B1 B2 B3 B4 B5 B6 B7 B8. unfold eff. rewrite B4, B5, B6, B7.
  splits; try first [assumption | lia]. left. exact B8.
Qed.

Lemma r_value_eff p t s : pre_run p s -> eff p s (r_value p t s).
Proof.
  intros [PRE Hmore]. pose proof PRE as (Hp & Hpos & Hlh & Hbad & Hed & Hes). unfold r_value.
  destruct ((t =? 90) || (t =? 84) || (t =? 70)).
  {   unfold e_scalar, eff. destruct (s_ec s) eqn:EC; norm; splits; try first [reflexivity | assumption | lia | (apply eev_ok; assumption) | dying].
    right. splits; try reflexivity. left. norm. splits; reflexivity. }
  destruct (t =? 78).
  {   unfold eff. destruct (s_ec s) eqn:EC; norm; splits; try first [reflexivity | assumption | lia | dying].
    right. splits; try first [reflexivity | assumption]. left. splits; reflexivity. }
  destruct (t =? 105). { apply eff_fin_more, r_num_eff; [exact PRE | lia | lia | lia]. }
  destruct (t =? 85). { apply eff_fin_more, r_num_eff; [exact PRE | lia | lia | lia]. }
  destruct (t =? 73). { apply eff_fin_more, r_num_eff; [exact PRE | lia | lia | lia]. }
  destruct (t =? 108). { apply eff_fin_more, r_num_eff; [exact PRE | lia | lia | lia]. }
  destruct (t =? 76). { apply eff_fin_more, r_num_eff; [exact PRE | lia | lia | lia]. }
  destruct (t =? 100). { apply eff_fin_more, r_num_eff; [exact PRE | lia | lia | lia]. }
  destruct (t =? 68). { apply eff_fin_more, r_num_eff; [exact PRE | lia | lia | lia]. }
  destruct (t =? 67).
  {
    destruct (blen p <? s_pos s + 1) eqn:E1.
    { unfold r_fail. apply (eff_refl_dying p s PRE); norm; try reflexivity; try assumption. left; reflexivity. }
    destruct (utf8_valid (slice p (s_pos s) 1)) eqn:V.
    2:{ unfold r_fail, eff. norm; splits; try first [reflexivity | assumption | lia | dying]. }
    unfold e_string. rewrite e_put_length_ok by (rewrite INT64_MAX_val; lia). change (pl_size 1) with 2.
    unfold eff. destruct (s_ec s) eqn:EC; norm; splits; try first [reflexivity | assumption | lia | (apply eev_ok; assumption) | dying].
    right. splits; try reflexivity. left. norm. splits; reflexivity. }
  destruct ((t =? 83) || (t =? 72)).
  {
    destruct (get_length p (s_pos s)) as [[n pos1]|] eqn:G.
    2:{ unfold r_fail. apply (eff_refl_dying p s PRE); norm; try reflexivity; try assumption. left; reflexivity. }
    destruct (get_length_some p (s_pos s) n pos1 Hp (proj1 Hpos) G) as (Hn & Hp1 & _).
    pose proof (pl_size_pos n) as PL.
    destruct (s_ec s) eqn:EC.
    { unfold eff. norm; splits; try first [reflexivity | assumption | lia | dying]. }
    destruct (blen p <? pos1 + n) eqn:E1.
    { unfold r_fail. apply (eff_refl_dying p s PRE); norm; try reflexivity; try assumption. left; reflexivity. }
    destruct ((t =? 83) && negb (utf8_valid (slice p pos1 n))).
    { unfold r_fail. apply (eff_refl_dying p s PRE); norm; try reflexivity; try assumption. left; reflexivity. }
    unfold e_string. destruct (utf8_valid (slice p pos1 n)).
    - rewrite e_put_length_ok by (rewrite INT64_MAX_val; lia).
      unfold eff. norm; splits; try first [reflexivity | assumption | lia | (apply eev_ok; assumption)].
      right. splits; try first [reflexivity | assumption]. left. norm. splits; reflexivity.
    - unfold eff. norm; splits; try first [reflexivity | assumption | lia | dying]. }
  destruct (t =? 91). { apply eff_fin, r_begin_eff; exact PRE. }
  destruct (t =? 123). { apply eff_fin, r_begin_eff; exact PRE. }
  unfold eff. norm; splits; try first [reflexivity | assumption | lia | dying].
Qed.

Lemma r_tv_eff p s : pre_run p s -> eff p s (r_tv p s) /\ (s_more (r_tv p s) = true -> s_ec (r_tv p s) = false -> s_pos s + 1 <= s_pos (r_tv p s)).
Proof.
  intros [PRE Hmore]. pose proof PRE as (Hp & Hpos & Hlh & Hbad & Hed & Hes). unfold r_tv.
  destruct (blen p <=? s_pos s) eqn:E0.
  { split; [unfold r_fail; apply (eff_refl_dying p s PRE); norm; try reflexivity; try assumption; left; reflexivity|].
    unfold r_fail. norm. discriminate. }
  zb.
  assert (P1 : pre_run p (w_pos (s_pos s + 1) s)) by (split; [apply pre_w_pos; [exact PRE | lia | lia] | exact Hmore]).
  pose proof (r_value_eff p (bat p (s_pos s)) _ P1) as H.
  destruct (eff_shift p s 1 _ ltac:(lia) (proj1 Hpos) Hlh H) as [H1 H2]. split; [exact H1 | intros _ _; exact H2].
Qed.

Lemma r_key_pos p s : pre p s -> s_more (r_key p s) = true -> s_ec (r_key p s) = false -> s_pos s + 2 <= s_pos (r_key p s).
Proof.
  intros (Hp & Hpos & Hlh & Hbad & Hed & Hes). unfold r_key, r_fail, e_key.
  destruct (get_length p (s_pos s)) as [[n pos1]|] eqn:G; [| norm; discriminate].
  destruct (get_length_some p (s_pos s) n pos1 Hp (proj1 Hpos) G) as (Hn & Hp1 & _).
  destruct (s_ec s) eqn:EC; [norm; discriminate|].
  destruct (blen p <? pos1 + n) eqn:E1; [norm; discriminate|].
  destruct (utf8_valid (slice p pos1 n)); [| norm; discriminate].
  rewrite e_put_length_ok by (rewrite INT64_MAX_val; lia). norm. intros _ _. lia.
Qed.

Fixpoint stk_shape (stk : list pstate) : Prop :=
  match stk with
  | [] => False
  | t :: r => match r with
              | [] => container_mode (ps_mode t) = false
              | _ => container_mode (ps_mode t) = true /\ stk_shape r
              end
  end.

Record rinv (s : st) : Prop := RINV {
  ri_shape : stk_shape (s_stk s);
  ri_ps : Forall ps_ok (s_stk s);
  ri_depth : s_depth s = Z.of_nat (length (s_stk s)) - 1;
  ri_dmax : s_depth s <= MAX_DEPTH;
  ri_edepth : s_edepth s = s_depth s;
  ri_estk : (length (s_stk s) <= S (length (s_estk s)))%nat;
  ri_estk_max : Z.of_nat (length (s_estk s)) <= MAX_DEPTH;
  ri_sync : s_ec s = false -> Z.of_nat (length (s_estk s)) = s_depth s
}.

Record ginv (p : list Z) (s : st) : Prop := GINV {
  gi_pos : 0 <= s_pos s <= blen p;
  gi_lo : 0 <= s_lo s <= s_hi s;
  gi_spread : s_hi s - s_lo s <= s_pos s;
  gi_bad : s_bad s = false;
  gi_eok : Forall ei_ok (s_estk s);
  gi_run : halted s = false -> rinv s
}.

Fixpoint wsum (stk : list pstate) : Z :=
  match stk with [] => 0 | t :: r => (if counted_mode (ps_mode t) then ps_len t - ps_idx t else 0) + wsum r end.
Fixpoint fsum (stk : list pstate) : Z :=
  match stk with [] => 0 | t :: r => fmode (ps_mode t) + fsum r end.
Definition mu (p : list Z) (s : st) : Z :=
  if halted s then 0
  else (blen p - s_pos s) * 2 ^ 27 + 4 * wsum (s_stk s) + 2 * fsum (s_stk s) + Z.of_nat (length (s_stk s)) + 1.

Lemma wsum_nonneg stk : Forall ps_ok stk -> 0 <= wsum stk.
Proof.
  induction 1 as [|t r [A [B C]] _ IH]; cbn [wsum]; [lia|]. destruct (counted_mode (ps_mode t)); lia.
Qed.
Lemma fsum_nonneg stk : 0 <= fsum stk.
Proof. induction stk as [|t r IH]; cbn [fsum]; [lia|]. unfold fmode. destruct (ps_mode t); lia. Qed.

Lemma halted_false s : halted s = false -> s_halt s = false /\ s_done s = false /\ s_more s = true.
Proof. unfold halted. destruct (s_halt s), (s_done s), (s_more s); cbn; intros H; try discriminate; auto. Qed.
Lemma halted_intro s : s_halt s = false -> s_done s = false -> s_more s = true -> halted s = false.
Proof. unfold halted. intros -> -> ->. reflexivity. Qed.

Lemma mu_pos p s : halted s = false -> ginv p s -> 0 < mu p s.
Proof.
  intros H G. unfold mu. rewrite H. pose proof (gi_pos p s G). pose proof (wsum_nonneg _ (ri_ps s (gi_run p s G H))). pose proof (fsum_nonneg (s_stk s)). nia.
Qed.

Lemma ret_if_ec_halted s' : (s_more s' = false \/ s_ec s' = true) -> halted (ret_if_ec s') = true.
Proof.
  intros [H|H]; unfold ret_if_ec, halted; destruct (s_ec s') eqn:E; simp_st; rewrite ?H; try discriminate;
    try reflexivity; destruct (s_halt s'), (s_done s'); reflexivity.
Qed.

Lemma ginv_num_of_eff p s s' : ginv p s -> eff p s s' ->
  0 <= s_pos s' <= blen p /\ 0 <= s_lo s' <= s_hi s' /\ s_hi s' - s_lo s' <= s_pos s' /\ s_bad s' = false /\ Forall ei_ok (s_estk s') /\ s_lo s <= s_lo s'.
Proof.
  intros G (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof (gi_pos p s G). pose proof (gi_lo p s G). pose proof (gi_spread p s G).
  repeat split; try assumption; lia.
Qed.

Lemma top_upd_fields f s t r : s_stk s = t :: r ->
  top_upd f s = w_stk (f t :: r) s.
Proof. intros H. unfold top_upd. rewrite H. reflexivity. Qed.

Lemma stk_shape_upd t t' r : container_mode (ps_mode t') = container_mode (ps_mode t) -> stk_shape (t :: r) -> stk_shape (t' :: r).
Proof. intros E H. cbn [stk_shape] in *. destruct r; rewrite E; exact H. Qed.

Lemma rinv_upd s t r t' : s_stk s = t :: r -> container_mode (ps_mode t') = container_mode (ps_mode t) -> ps_ok t' ->
  rinv s -> rinv (w_stk (t' :: r) s).
Proof.
  intros HS HC HP [A1 A2 A3 A4 A5 A6 A7 A8]. rewrite HS in *. constructor; simp_st; try assumption.
  - exact (stk_shape_upd t t' r HC A1).
  - inversion A2; subst. constructor; assumption.
Qed.

Lemma ginv_upd p s t r t' : s_stk s = t :: r -> container_mode (ps_mode t') = container_mode (ps_mode t) -> ps_ok t' ->
  halted s = false -> ginv p s -> ginv p (w_stk (t' :: r) s) /\ halted (w_stk (t' :: r) s) = false /\ rinv (w_stk (t' :: r) s).
Proof.
  intros HS HC HP HH [B1 B2 B3 B4 B5 B6]. pose proof (rinv_upd s t r t' HS HC HP (B6 HH)) as R.
  split; [|split; [exact HH | exact R]]. constructor; simp_st; try assumption. intros _. exact R.
Qed.

Lemma pre_of_ginv p s : bytes_ok p -> ginv p s -> halted s = false -> pre_run p s.
Proof.
  intros Hp [B1 B2 B3 B4 B5 B6] HH. destruct (halted_false s HH) as (_ & _ & HM).
  split; [|exact HM]. unfold pre. pose proof (ri_edepth s (B6 HH)). repeat split; try assumption; lia.
Qed.

Lemma after_value p s0 s' : bytes_ok p -> ginv p s0 -> halted s0 = false -> eff p s0 s' ->
  ginv p (ret_if_ec s') /\ s_lo s0 <= s_lo (ret_if_ec s') /\
  (halted (ret_if_ec s') = false ->
     ret_if_ec s' = s' /\ s_pos s0 <= s_pos s' /\
     (s_stk s' = s_stk s0 \/
      exists c, s_stk s' = c :: s_stk s0 /\ fmode (ps_mode c) = 0 /\ ps_ok c /\ ps_idx c = 0 /\ (counted_mode (ps_mode c) = true -> s_pos s0 + 1 <= s_pos s'))).
Proof.
  intros Hp G HH E. destruct (ginv_num_of_eff p s0 s' G E) as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct E as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  destruct (halted_false s0 HH) as (H1 & H2 & H3). pose proof (gi_run p s0 G HH) as [R1 R2 R3 R4 R5 R6 R7 R8].
  destruct A9 as [D|(B1 & B2 & B3 & B4)].
  -
    pose proof (ret_if_ec_halted s' D) as HD. split; [|split].
    + assert (GX : forall x, halted x = true -> s_pos x = s_pos s' -> s_lo x = s_lo s' -> s_hi x = s_hi s' -> s_bad x = s_bad s' -> s_estk x = s_estk s' -> ginv p x).
      { intros x X0 X1 X2 X3 X4 X5. constructor; rewrite ?X1, ?X2, ?X3, ?X4, ?X5; try assumption. intros HX. rewrite HX in X0. discriminate. }
      apply GX; [exact HD | | | | |]; unfold ret_if_ec; destruct (s_ec s'); reflexivity.
    + unfold ret_if_ec. destruct (s_ec s'); simp_st; exact N6.
    + intros HX. rewrite HX in HD. discriminate.
  -
    assert (RE : ret_if_ec s' = s') by (unfold ret_if_ec; rewrite B2; reflexivity). rewrite RE.
    assert (HA : halted s' = false) by (apply halted_intro; congruence).
    split; [|split; [exact N6|]].
    + constructor; try assumption. intros _.
      destruct B4 as [(C1 & C2 & C3 & C4)|(c & C1 & C2 & C2f & C3 & C4 & C5 & C6 & C7 & C8 & C9)].
      * constructor; rewrite ?C1, ?C2, ?C3, ?C4; try assumption. intros _. apply R8. exact B3.
      * constructor; rewrite ?C1, ?C5, ?C7, ?C8; try assumption.
        -- cbn [stk_shape]. destruct (s_stk s0) eqn:ES; [exact (False_ind _ R1)|]. split; [exact C2 | exact R1].
        -- constructor; assumption.
        -- cbn [length]. rewrite R3. lia.
        -- rewrite <- C5. exact C6.
        -- rewrite R5. reflexivity.
        -- cbn [length]. lia.
        -- rewrite Nat2Z.inj_succ. pose proof (R8 B3). lia.
        -- intros _. rewrite Nat2Z.inj_succ. pose proof (R8 B3). lia.
    + intros _. split; [reflexivity|]. split; [lia|].
      destruct B4 as [(C1 & C2 & C3 & C4)|(c & C1 & C2 & C2f & C3 & C4 & C5 & C6 & C7 & C8 & C9)]; [left; exact C1|].
      right. exists c. split; [exact C1|]. split; [exact C2f|]. split; [exact C3|]. split; [exact C4 | exact C9].
Qed.

Lemma ginv_w_pos p s k : ginv p s -> 0 <= k -> s_pos s + k <= blen p -> ginv p (w_pos (s_pos s + k) s).
Proof.
  intros [B1 B2 B3 B4 B5 B6] Hk Hb. constructor; simp_st; try assumption; try lia.
  intros HX. assert (HH : halted s = false) by exact HX. destruct (B6 HH) as [R1 R2 R3 R4 R5 R6 R7 R8]. constructor; simp_st; assumption.
Qed.

Lemma r_end_ok p s t r : ginv p s -> halted s = false -> s_stk s = t :: r -> container_mode (ps_mode t) = true ->
  let s' := r_end s in
  ginv p s' /\ halted s' = false /\ s_stk s' = r /\ s_pos s' = s_pos s /\ s_lo s <= s_lo s'.
Proof.
  intros G HH HS HC. destruct (halted_false s HH) as (H1 & H2 & H3).
  pose proof G as [B1 B2 B3 B4 B5 B6]. pose proof (B6 HH) as [R1 R2 R3 R4 R5 R6 R7 R8].
  rewrite HS in *. cbn [stk_shape] in R1. destruct r as [|t2 r2]; [rewrite HC in R1; discriminate|]. destruct R1 as [_ R1].
  cbn [length] in R3, R6.
  destruct (s_estk s) as [|e er] eqn:ES; [cbn [length] in R6; lia|].
  pose proof (Forall_inv B5) as Ee. pose proof (Forall_inv_tail B5) as Eer.
  cbv zeta. unfold r_end, e_end. simp_st. rewrite ES. simp_st.
  assert (RR : forall x, s_stk x = t2 :: r2 -> s_depth x = s_depth s - 1 -> s_edepth x = s_edepth s - 1 ->
                 (s_estk x = e :: er /\ s_ec x = true \/ (length (s_estk x) = length er /\ s_ec x = s_ec s)) -> rinv x).
  { intros x X1 X2 X3 X4. constructor; rewrite ?X1, ?X2, ?X3; try assumption.
    - inversion R2; assumption.
    - cbn [length]. lia.
    - lia.
    - lia.
    - destruct X4 as [[X4 _]|[X4 _]]; rewrite X4; cbn [length] in *; lia.
    - destruct X4 as [[X4 _]|[X4 _]]; rewrite X4; cbn [length] in *; lia.
    - intros EC. destruct X4 as [[_ X4]|[X4 X5]]; [congruence|]. rewrite X5 in EC. pose proof (R8 EC) as Q. cbn [length] in Q. rewrite X4. lia. }
  assert (HS' : s_stk s = t :: t2 :: r2) by exact HS.
  destruct (ei_indef e) eqn:EI.
  { norm. rewrite !HS'. cbn [tl]. splits; try first [reflexivity | lia | (apply halted_intro; norm; first [assumption | reflexivity])].
    constructor; norm; try first [assumption | lia]. { apply eev_ok. simp_st. exact Eer. }
    intros _. apply RR; norm; try reflexivity. right. split; [rewrite ?eev_len; simp_st; reflexivity | reflexivity]. }
  destruct (ei_cnt e <? ei_len e) eqn:E1.
  { norm. rewrite !HS'. cbn [tl]. splits; try first [reflexivity | lia | (apply halted_intro; norm; first [assumption | reflexivity])].
    constructor; norm; try first [assumption | lia]. { rewrite ?ES. exact B5. }
    intros _. apply RR; norm; try reflexivity. left. split; [exact ES | reflexivity]. }
  destruct (ei_len e <? ei_cnt e) eqn:E2.
  { norm. rewrite !HS'. cbn [tl]. splits; try first [reflexivity | lia | (apply halted_intro; norm; first [assumption | reflexivity])].
    constructor; norm; try first [assumption | lia]. { rewrite ?ES. exact B5. }
    intros _. apply RR; norm; try reflexivity. left. split; [exact ES | reflexivity]. }
  norm. rewrite !HS'. cbn [tl]. splits; try first [reflexivity | lia | (apply halted_intro; norm; first [assumption | reflexivity])].
  constructor; norm; try first [assumption | lia]. { apply eev_ok. simp_st. exact Eer. }
  intros _. apply RR; norm; try reflexivity. right. split; [rewrite ?eev_len; simp_st; reflexivity | reflexivity].
Qed.

Definition lw (t : pstate) : Z := 4 * (if counted_mode (ps_mode t) then ps_len t - ps_idx t else 0) + 2 * fmode (ps_mode t).
Lemma lw_nonneg t : ps_ok t -> 0 <= lw t.
Proof. intros (A & B & C). unfold lw, fmode. destruct (counted_mode (ps_mode t)); destruct (ps_mode t); lia. Qed.
Lemma mu_running p s : halted s = false ->
  mu p s = (blen p - s_pos s) * 2 ^ 27 + 4 * wsum (s_stk s) + 2 * fsum (s_stk s) + Z.of_nat (length (s_stk s)) + 1.
Proof. intros H. unfold mu. rewrite H. reflexivity. Qed.
Lemma wf_cons t r : 4 * wsum (t :: r) + 2 * fsum (t :: r) = lw t + (4 * wsum r + 2 * fsum r).
Proof. unfold lw. cbn [wsum fsum]. lia. Qed.

Lemma mu_dec p s s' t t' r :
  halted s = false -> halted s' = false -> s_pos s <= s_pos s' -> s_stk s = t :: r ->
  (s_stk s' = t' :: r \/
   exists c, s_stk s' = c :: t' :: r /\ fmode (ps_mode c) = 0 /\ ps_ok c /\ ps_idx c = 0 /\ (counted_mode (ps_mode c) = true -> s_pos s + 1 <= s_pos s')) ->
  (lw t' + 2 <= lw t \/ (s_pos s + 1 <= s_pos s' /\ lw t' <= lw t + 2)) ->
  mu p s' < mu p s.
Proof.
  intros H H' HP HS HS' HL. rewrite (mu_running p s H), (mu_running p s' H'). rewrite HS.
  change (2 ^ 27) with 134217728.
  destruct HS' as [HS'|(c & HS' & C1 & (C2 & C3 & C4) & C5 & C6)]; rewrite HS'.
  - cbn [length]. pose proof (wf_cons t r). pose proof (wf_cons t' r). lia.
  - cbn [length]. pose proof (wf_cons t r). pose proof (wf_cons c (t' :: r)). pose proof (wf_cons t' r).
    assert (LC : lw c = 0 \/ (lw c <= 4 * MAX_ITEMS /\ s_pos s + 1 <= s_pos s')).
    { unfold lw. rewrite C1. destruct (counted_mode (ps_mode c)); [right; split; [lia | apply C6; reflexivity] | left; lia]. }
    rewrite MAX_ITEMS_val in LC. lia.
Qed.

Lemma mu_dec_pop p s s' t r :
  halted s = false -> halted s' = false -> s_pos s <= s_pos s' -> s_stk s = t :: r -> ps_ok t -> s_stk s' = r -> mu p s' < mu p s.
Proof.
  intros H H' HP HS HT HS'. rewrite (mu_running p s H), (mu_running p s' H'). rewrite HS, HS'.
  change (2 ^ 27) with 134217728. cbn [length]. pose proof (wf_cons t r). pose proof (lw_nonneg t HT). lia.
Qed.

Lemma halted_ret_if_ec_false s' : halted (ret_if_ec s') = false -> s_ec s' = false /\ s_more s' = true /\ halted s' = false.
Proof.
  unfold ret_if_ec. destruct (s_ec s') eqn:E; intros H.
  - unfold halted in H. simp_st. discriminate.
  - destruct (halted_false s' H) as (A & B & C). auto.
Qed.

Lemma step_value p s t r t' (op : st -> st) :
  bytes_ok p -> ginv p s -> halted s = false -> s_stk s = t :: r ->
  container_mode (ps_mode t') = container_mode (ps_mode t) -> ps_ok t' ->
  (forall s0, pre_run p s0 -> eff p s0 (op s0)) ->
  (lw t' + 2 <= lw t \/
   ((forall s0, pre_run p s0 -> s_more (op s0) = true -> s_ec (op s0) = false -> s_pos s0 + 1 <= s_pos (op s0)) /\ lw t' <= lw t + 2)) ->
  let s'' := ret_if_ec (op (w_stk (t' :: r) s)) in
  ginv p s'' /\ s_lo s <= s_lo s'' /\ mu p s'' < mu p s.
Proof.
  intros Hp G HH HS HC HT Heff HL. cbv zeta.
  destruct (ginv_upd p s t r t' HS HC HT HH G) as (G0 & HH0 & R0).
  set (s0 := w_stk (t' :: r) s) in *.
  pose proof (pre_of_ginv p s0 Hp G0 HH0) as PRE0.
  destruct (after_value p s0 (op s0) Hp G0 HH0 (Heff s0 PRE0)) as (G' & LO & AL).
  split; [exact G'|]. split; [exact LO|].
  destruct (halted (ret_if_ec (op s0))) eqn:HX.
  - unfold mu at 1. rewrite HX. exact (mu_pos p s HH G).
  - destruct (AL eq_refl) as (RE & POS & STK). destruct (halted_ret_if_ec_false _ HX) as (X1 & X2 & X3).
    rewrite RE. apply (mu_dec p s (op s0) t t' r HH X3 POS HS).
    + destruct STK as [STK|(c & C1 & C2 & C3 & C4 & C5)]; [left; exact STK|]. right. exists c.
      split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4 | exact C5].
    + destruct HL as [HL|[HL1 HL2]]; [left; exact HL|]. right. split; [|exact HL2]. exact (HL1 s0 PRE0 X2 X1).
Qed.

Lemma r_key_comm p x s : r_key p (w_stk x s) = w_stk x (r_key p s).
Proof.
  unfold r_key, r_fail, e_key, e_put_length. simp_st.
  destruct (get_length p (s_pos s)) as [[n pos1]|]; [|reflexivity].
  destruct (s_ec s); [reflexivity|]. destruct (blen p <? pos1 + n); [reflexivity|].
  destruct (utf8_valid (slice p pos1 n)); [|reflexivity]. simp_st. destruct (INT64_MAX <? n); reflexivity.
Qed.

Lemma ginv_halted_stk p x y : halted x = true -> ginv p x -> ginv p (w_stk y x).
Proof.
  intros H [B1 B2 B3 B4 B5 B6]. constructor; simp_st; try assumption.
  intros HX. assert (halted x = false) by exact HX. congruence.
Qed.

Lemma step_key p s t r (M : pmode) :
  bytes_ok p -> ginv p s -> halted s = false -> s_stk s = t :: r ->
  let t'' := ps_mode_set M (ps_inc t) in
  container_mode (ps_mode t'') = container_mode (ps_mode t) -> ps_ok t'' ->
  (lw t'' + 2 <= lw t \/ lw t'' <= lw t + 2) ->
  let s' := r_key p (top_upd ps_inc s) in
  let R := if s_ec s' then w_halt true s' else top_upd (ps_mode_set M) s' in
  ginv p R /\ s_lo s <= s_lo R /\ mu p R < mu p s.
Proof.
  intros Hp G HH HS t'' HC HT HL s' R.
  pose proof (step_value p s t r t'' (r_key p) Hp G HH HS HC HT (fun s0 P => r_key_eff p s0 (proj1 P))
                ltac:(destruct HL as [HL|HL]; [left; exact HL | right; split; [|exact HL]; intros s0 P A B; pose proof (r_key_pos p s0 (proj1 P) A B); lia])) as (G' & LO & MU).
  cbv zeta in G', LO, MU. set (X := ret_if_ec (r_key p (w_stk (t'' :: r) s))) in *.
  assert (S' : s' = w_stk (ps_inc t :: r) (r_key p s)).
  { subst s'. rewrite (top_upd_fields ps_inc s t r HS). apply r_key_comm. }
  assert (XE : X = ret_if_ec (w_stk (t'' :: r) (r_key p s))) by (subst X; rewrite r_key_comm; reflexivity).
  assert (EC : s_ec s' = s_ec (r_key p s)) by (rewrite S'; reflexivity).
  destruct (s_ec (r_key p s)) eqn:EK.
  -
    assert (RX : R = w_stk (ps_inc t :: r) X).
    { subst R. rewrite EC. rewrite XE. unfold ret_if_ec. simp_st. rewrite EK. rewrite S'. reflexivity. }
    assert (HXh : halted X = true) by (rewrite XE; apply ret_if_ec_halted; right; simp_st; exact EK).
    rewrite RX. split; [apply ginv_halted_stk; assumption|]. split; [simp_st; exact LO|].
    unfold mu at 1. replace (halted (w_stk (ps_inc t :: r) X)) with true by (symmetry; exact HXh). exact (mu_pos p s HH G).
  - assert (RX : R = X).
    { subst R. rewrite EC. rewrite XE. unfold ret_if_ec. simp_st. rewrite EK. rewrite S'. unfold top_upd. simp_st. reflexivity. }
    rewrite RX. auto.
Qed.

Ltac side EM := unfold ps_ok, lw, ps_inc, ps_mode_set in *; cbn [ps_mode ps_len ps_idx ps_type] in *; rewrite ?EM in *;
                cbn [counted_mode container_mode fmode] in *; rewrite ?MAX_ITEMS_val in *; zb; try reflexivity; try lia.

Lemma ginv_halt_set p s : ginv p s -> ginv p (w_halt true s).
Proof.
  intros [B1 B2 B3 B4 B5 B6]. constructor; simp_st; try assumption. intros HX. unfold halted in HX. simp_st. discriminate.
Qed.

Lemma step_end p s t r : bytes_ok p -> ginv p s -> halted s = false -> s_stk s = t :: r -> container_mode (ps_mode t) = true ->
  ginv p (r_end s) /\ s_lo s <= s_lo (r_end s) /\ mu p (r_end s) < mu p s.
Proof.
  intros Hp G HH HS HC. destruct (r_end_ok p s t r G HH HS HC) as (G' & H' & S' & P' & L').
  split; [exact G'|]. split; [exact L'|].
  pose proof (ri_ps s (gi_run p s G HH)) as PS. rewrite HS in PS.
  apply (mu_dec_pop p s (r_end s) t r HH H' ltac:(lia) HS (Forall_inv PS) S').
Qed.

Lemma step_end_marker p s t r : bytes_ok p -> ginv p s -> halted s = false -> s_stk s = t :: r -> container_mode (ps_mode t) = true ->
  s_pos s + 1 <= blen p ->
  let R := ret_if_ec (r_end (w_pos (s_pos s + 1) s)) in
  ginv p R /\ s_lo s <= s_lo R /\ mu p R < mu p s.
Proof.
  intros Hp G HH HS HC HB R.
  pose proof (ginv_w_pos p s 1 G ltac:(lia) HB) as G1.
  assert (HH1 : halted (w_pos (s_pos s + 1) s) = false) by exact HH.
  destruct (r_end_ok p _ t r G1 HH1 HS HC) as (G' & H' & S' & P' & L'). simp_st.
  subst R. unfold ret_if_ec. destruct (s_ec (r_end (w_pos (s_pos s + 1) s))) eqn:EC.
  - split; [apply ginv_halt_set; exact G'|]. split; [simp_st; exact L'|].
    unfold mu at 1. replace (halted (w_halt true (r_end (w_pos (s_pos s + 1) s)))) with true by (unfold halted; simp_st; reflexivity).
    exact (mu_pos p s HH G).
  - split; [exact G'|]. split; [exact L'|].
    pose proof (ri_ps s (gi_run p s G HH)) as PS. rewrite HS in PS.
    apply (mu_dec_pop p s _ t r HH H' ltac:(lia) HS (Forall_inv PS) S').
Qed.

Lemma step_fail_halt p s x : ginv p s -> halted s = false -> s_pos x = s_pos s -> s_lo x = s_lo s -> s_hi x = s_hi s -> s_bad x = s_bad s -> s_estk x = s_estk s ->
  halted x = true -> ginv p x /\ s_lo s <= s_lo x /\ mu p x < mu p s.
Proof.
  intros G HH X1 X2 X3 X4 X5 HX. pose proof G as [B1 B2 B3 B4 B5 B6].
  split; [constructor; rewrite ?X1, ?X2, ?X3, ?X4, ?X5; try assumption; intros HY; congruence|].
  split; [lia|]. unfold mu at 1. rewrite HX. exact (mu_pos p s HH G).
Qed.

Theorem step_ok p s : bytes_ok p -> ginv p s ->
  ginv p (step p s) /\ s_lo s <= s_lo (step p s) /\ (halted s = false -> mu p (step p s) < mu p s).
Proof.
  intros Hp G. unfold step. destruct (halted s) eqn:HH.
  { split; [apply ginv_halt_set; exact G|]. split; [simp_st; lia | discriminate]. }
  pose proof (gi_run p s G HH) as RI. pose proof (ri_shape s RI) as SH. pose proof (ri_ps s RI) as PS.
  destruct (s_stk s) as [|t r] eqn:HS; [exact (False_ind _ SH)|].
  pose proof (Forall_inv PS) as PT.
  assert (E3 : forall A B C : Prop, A /\ B /\ C -> A /\ B /\ (false = false -> C)) by tauto. apply E3. clear E3.
  assert (TV : forall s0, pre_run p s0 -> eff p s0 (r_tv p s0)) by (intros s0 P; exact (proj1 (r_tv_eff p s0 P))).
  assert (TVP : forall s0, pre_run p s0 -> s_more (r_tv p s0) = true -> s_ec (r_tv p s0) = false -> s_pos s0 + 1 <= s_pos (r_tv p s0))
    by (intros s0 P; exact (proj2 (r_tv_eff p s0 P))).
  destruct (ps_mode t) eqn:EM.
  -   rewrite (top_upd_fields _ s t r HS).
    apply (step_value p s t r (ps_mode_set Maccept t) (r_tv p) Hp G HH HS); [side EM | side EM | exact TV |].
    right. split; [exact TVP | side EM].
  -
    destruct r as [|t2 r2].
    + apply step_fail_halt; simp_st; try reflexivity; try assumption. unfold halted; simp_st. rewrite orb_true_r. reflexivity.
    + cbn [stk_shape] in SH. rewrite EM in SH. cbn in SH. destruct SH; discriminate.
  -
    destruct (ps_idx t <? ps_len t) eqn:E1.
    + rewrite (top_upd_fields _ s t r HS).
      apply (step_value p s t r (ps_inc t) (r_tv p) Hp G HH HS); [side EM | side EM | exact TV |]. left. side EM.
    + apply (step_end p s t r Hp G HH HS). rewrite EM. reflexivity.
  -
    destruct (blen p <=? s_pos s) eqn:E0.
    { apply step_fail_halt; unfold r_fail; simp_st; try reflexivity; try assumption. }
    destruct (bat p (s_pos s) =? 93) eqn:E1.
    { zb. apply (step_end_marker p s t r Hp G HH HS); [rewrite EM; reflexivity | lia]. }
    destruct (MAX_ITEMS <? ps_idx t + 1) eqn:E2.
    { rewrite (top_upd_fields _ s t r HS). apply step_fail_halt; unfold r_fail; simp_st; try reflexivity; try assumption. }
    rewrite (top_upd_fields _ s t r HS).
    apply (step_value p s t r (ps_inc t) (r_tv p) Hp G HH HS); [side EM | side EM | exact TV |].
    right. split; [exact TVP | side EM].
  -
    destruct (ps_idx t <? ps_len t) eqn:E1.
    + rewrite (top_upd_fields _ s t r HS).
      apply (step_value p s t r (ps_inc t) (r_value p (ps_type t)) Hp G HH HS); [side EM | side EM | intros s0 P; apply r_value_eff; exact P |]. left. side EM.
    + apply (step_end p s t r Hp G HH HS). rewrite EM. reflexivity.
  -
    destruct (ps_idx t <? ps_len t) eqn:E1.
    + apply (step_key p s t r Mval Hp G HH HS); [side EM | side EM | left; side EM].
    + apply (step_end p s t r Hp G HH HS). rewrite EM. reflexivity.
  -   rewrite (top_upd_fields _ s t r HS).
    apply (step_value p s t r (ps_mode_set Mkey t) (r_tv p) Hp G HH HS); [side EM | side EM | exact TV |]. left. side EM.
  -
    destruct (ps_idx t <? ps_len t) eqn:E1.
    + apply (step_key p s t r Mtval Hp G HH HS); [side EM | side EM | left; side EM].
    + apply (step_end p s t r Hp G HH HS). rewrite EM. reflexivity.
  -   rewrite (top_upd_fields _ s t r HS).
    apply (step_value p s t r (ps_mode_set Mtkey t) (r_value p (ps_type t)) Hp G HH HS); [side EM | side EM | intros s0 P; apply r_value_eff; exact P |]. left. side EM.
  -
    destruct (blen p <=? s_pos s) eqn:E0.
    { apply step_fail_halt; unfold r_fail; simp_st; try reflexivity; try assumption. }
    destruct (bat p (s_pos s) =? 125) eqn:E1.
    { zb. apply (step_end_marker p s t r Hp G HH HS); [rewrite EM; reflexivity | lia]. }
    destruct (MAX_ITEMS <? ps_idx t + 1) eqn:E2.
    { rewrite (top_upd_fields _ s t r HS). apply step_fail_halt; unfold r_fail; simp_st; try reflexivity; try assumption. }
    apply (step_key p s t r Mival Hp G HH HS); [side EM | side EM | right; side EM].
  -   rewrite (top_upd_fields _ s t r HS).
    apply (step_value p s t r (ps_mode_set Mikey t) (r_tv p) Hp G HH HS); [side EM | side EM | exact TV |]. left. side EM.
Qed.

Lemma ginv_init p : ginv p init.
Proof.
  pose proof (blen_nonneg p) as BL.
  constructor.
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
  - reflexivity.
  - constructor.
  - intros _. constructor.
    + cbn. reflexivity.
    + constructor; [unfold ps_ok; cbn; rewrite MAX_ITEMS_val; lia | constructor].
    + cbn. reflexivity.
    + cbn. rewrite MAX_DEPTH_val. lia.
    + cbn. reflexivity.
    + cbn. lia.
    + cbn. rewrite MAX_DEPTH_val. lia.
    + intros _. cbn. reflexivity.
Qed.

Lemma run_S n p s : run (S n) p s = run n p (step p s). Proof. reflexivity. Qed.
Lemma run_add n m p s : run (n + m) p s = run m p (run n p s).
Proof. revert s. induction n as [|n IH]; intros s; [reflexivity|]. cbn [Nat.add run]. apply IH. Qed.

Lemma run_ginv p : bytes_ok p -> forall n s, ginv p s -> ginv p (run n p s).
Proof. intros Hp. induction n as [|n IH]; intros s G; [exact G|]. cbn [run]. apply IH. exact (proj1 (step_ok p s Hp G)). Qed.

Lemma run_lo_mono p : bytes_ok p -> forall n s, ginv p s -> s_lo s <= s_lo (run n p s).
Proof.
  intros Hp. induction n as [|n IH]; intros s G; [cbn; lia|]. cbn [run].
  destruct (step_ok p s Hp G) as (G' & L & _). specialize (IH _ G'). lia.
Qed.

Lemma step_halted p s : halted s = true -> step p s = w_halt true s.
Proof. intros H. unfold step. rewrite H. reflexivity. Qed.
Lemma run_halted p n s : halted s = true ->
  halted (run n p s) = true /\ s_lo (run n p s) = s_lo s /\ s_hi (run n p s) = s_hi s /\ s_pos (run n p s) = s_pos s /\ s_ec (run n p s) = s_ec s.
Proof.
  revert s. induction n as [|n IH]; intros s H; [cbn; auto|]. cbn [run]. rewrite (step_halted p s H).
  assert (H' : halted (w_halt true s) = true) by reflexivity.
  destruct (IH _ H') as (A & B & C & D & E). repeat split; assumption.
Qed.

Lemma run_halts p : bytes_ok p -> forall n s, ginv p s -> mu p s <= Z.of_nat n -> halted (run n p s) = true.
Proof.
  intros Hp. induction n as [|n IH]; intros s G M.
  - cbn [run]. destruct (halted s) eqn:H; [reflexivity|]. pose proof (mu_pos p s H G). lia.
  - cbn [run]. destruct (halted s) eqn:H.
    + rewrite (step_halted p s H). exact (proj1 (run_halted p n (w_halt true s) eq_refl)).
    + destruct (step_ok p s Hp G) as (G' & _ & D). specialize (D H). apply IH; [exact G' | lia].
Qed.

Definition fuel (p : list Z) : nat := Z.to_nat (blen p * 2 ^ 27 + 2).
Definition final (p : list Z) : st := run (fuel p) p init.

Definition F (p : list Z) : Z := s_lo (final p).

Lemma mu_init p : mu p init = blen p * 2 ^ 27 + 2.
Proof. unfold mu. cbn. lia. Qed.

Theorem final_halted p : bytes_ok p -> halted (final p) = true.
Proof.
  intros Hp. apply (run_halts p Hp); [apply ginv_init|]. rewrite mu_init. unfold fuel. pose proof (blen_nonneg p). lia.
Qed.

Theorem halted_is_final p n : bytes_ok p -> halted (run n p init) = true ->
  s_lo (run n p init) = F p /\ s_hi (run n p init) = s_hi (final p) /\ s_ec (run n p init) = s_ec (final p).
Proof.
  intros Hp H. unfold F, final. destruct (Nat.le_ge_cases n (fuel p)) as [L|L].
  - replace (fuel p) with (n + (fuel p - n))%nat by lia. rewrite run_add.
    destruct (run_halted p (fuel p - n) _ H) as (_ & A & B & _ & C). rewrite A, B, C. auto.
  - pose proof (final_halted p Hp) as HF. unfold final in HF.
    replace n with (fuel p + (n - fuel p))%nat by lia. rewrite run_add.
    destruct (run_halted p (n - fuel p) _ HF) as (_ & A & B & _ & C). rewrite A, B, C. auto.
Qed.

Theorem run_lo_le_F p n : bytes_ok p -> s_lo (run n p init) <= F p.
Proof.
  intros Hp. unfold F, final. destruct (Nat.le_ge_cases n (fuel p)) as [L|L].
  - replace (fuel p) with (n + (fuel p - n))%nat by lia. rewrite run_add.
    apply (run_lo_mono p Hp). apply (run_ginv p Hp). apply ginv_init.
  - pose proof (final_halted p Hp) as HF. unfold final in HF.
    replace n with (fuel p + (n - fuel p))%nat by lia. rewrite run_add.
    destruct (run_halted p (n - fuel p) _ HF) as (_ & A & _). rewrite A. lia.
Qed.

Theorem run_hi_le p n : bytes_ok p -> s_hi (run n p init) <= F p + blen p.
Proof.
  intros Hp. pose proof (run_ginv p Hp n init (ginv_init p)) as [B1 B2 B3 B4 B5 B6].
  pose proof (run_lo_le_F p n Hp). lia.
Qed.

Theorem run_not_bad p n : bytes_ok p -> s_bad (run n p init) = false.
Proof. intros Hp. exact (gi_bad p _ (run_ginv p Hp n init (ginv_init p))). Qed.

Theorem run_rinv p n : bytes_ok p -> halted (run n p init) = false -> rinv (run n p init).
Proof. intros Hp. exact (gi_run p _ (run_ginv p Hp n init (ginv_init p))). Qed.

Theorem F_nonneg p : bytes_ok p -> 0 <= F p.
Proof. intros Hp. pose proof (gi_lo p _ (run_ginv p Hp (fuel p) init (ginv_init p))). unfold F, final. lia. Qed.
