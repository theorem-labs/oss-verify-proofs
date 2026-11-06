(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim SoftFloat FmtFp FmtFpPre.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_of_u32 f128_of_i32.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma pad_loop_eq : forall c fuel s, pad_loop c fuel s = wloop (fun s => 256 <=? fst s) (pad_loop_body c) fuel s.
Proof. induction fuel; intros [l o]; cbn - [pad_loop_body Z.leb]; [reflexivity|]. destruct (256 <=? l); auto. Qed.
Lemma fmt_u_loop_eq : forall fuel st, fmt_u_loop fuel st = wloop (fun st => let '(y, _, _) := st in negb (y =? 0)) fmt_u_loop_body fuel st.
Proof. induction fuel; intros [[y s] b]; cbn - [fmt_u_loop_body Z.eqb]; [reflexivity|]. destruct (negb (y =? 0)); auto. Qed.
Lemma fmt_fp_up_inner_eq : forall sh fuel a s, fmt_fp_up_inner sh fuel a s = wloop (fun s => let '(_, d, _) := s in a <=? d) (fmt_fp_up_inner_body sh) fuel s.
Proof. induction fuel; intros a [[big d] c]; cbn - [fmt_fp_up_inner_body Z.leb]; [reflexivity|]. destruct (a <=? d); auto. Qed.
Lemma fmt_fp_strip_eq : forall fuel big a z, fmt_fp_strip fuel big a z = wloop (fun z => (a <? z) && (znth big (z - 1) =? 0)) fmt_fp_strip_body fuel z.
Proof. induction fuel; intros big a z; cbn - [fmt_fp_strip_body Z.ltb Z.eqb znth]; [reflexivity|]. destruct (_ && _); auto. Qed.
Lemma fmt_fp_up_eq : forall fuel s, fmt_fp_up fuel s = owloop (fun s => let '(_, _, _, e2) := s in 0 <? e2) fmt_fp_up_body fuel s.
Proof. induction fuel; intros [[[big a] z] e2]; cbn - [fmt_fp_up_body Z.ltb]; [reflexivity|]. destruct (0 <? e2); [|reflexivity]. destruct (fmt_fp_up_body _); auto. Qed.
Lemma fmt_fp_dn_inner_eq : forall sh fuel z s, fmt_fp_dn_inner sh fuel z s = wloop (fun s => let '(_, d, _) := s in d <? z) (fmt_fp_dn_inner_body sh) fuel s.
Proof. induction fuel; intros z [[big d] c]; cbn - [fmt_fp_dn_inner_body Z.ltb]; [reflexivity|]. destruct (d <? z); auto. Qed.
Lemma fmt_fp_dn_eq : forall fuel p t r s, fmt_fp_dn fuel p t r s = owloop (fun s => let '(_, _, _, e2) := s in e2 <? 0) (fmt_fp_dn_body p t r) fuel s.
Proof. induction fuel; intros p t r [[[big a] z] e2]; cbn - [fmt_fp_dn_body Z.ltb]; [reflexivity|]. destruct (e2 <? 0); [|reflexivity]. destruct (fmt_fp_dn_body _ _ _ _); auto. Qed.
Lemma fmt_fp_cnt_eq : forall fuel v s, fmt_fp_cnt fuel v s = wloop (fun s => fst s <=? v) fmt_fp_cnt_body fuel s.
Proof. induction fuel; intros v [i e]; cbn - [fmt_fp_cnt_body Z.leb]; [reflexivity|]. destruct (i <=? v); auto. Qed.
Lemma fmt_fp_powi_eq : forall fuel s, fmt_fp_powi fuel s = wloop (fun s => snd s <? 9) fmt_fp_powi_body fuel s.
Proof. induction fuel; intros [i j]; cbn - [fmt_fp_powi_body Z.ltb]; [reflexivity|]. destruct (j <? 9); auto. Qed.
Lemma fmt_fp_carry_eq : forall fuel s, fmt_fp_carry fuel s = wloop (fun s => let '(big, d, _) := s in 999999999 <? znth big d) fmt_fp_carry_body fuel s.
Proof. induction fuel; intros [[big d] a]; cbn - [fmt_fp_carry_body Z.ltb znth]; [reflexivity|]. destruct (999999999 <? znth big d); auto. Qed.
Lemma fmt_fp_tz_eq : forall fuel v s, fmt_fp_tz fuel v s = wloop (fun s => v mod fst s =? 0) fmt_fp_tz_body fuel s.
Proof. induction fuel; intros v [i j]; cbn - [fmt_fp_tz_body Z.eqb Z.modulo]; [reflexivity|]. destruct (v mod i =? 0); auto. Qed.
Lemma fmt_fp_epad_eq : forall fuel s, fmt_fp_epad fuel s = wloop (fun s => 12 - fst s <? 2) fmt_fp_epad_body fuel s.
Proof. induction fuel; intros [e b]; cbn - [fmt_fp_epad_body Z.ltb Z.sub]; [reflexivity|]. destruct (12 - e <? 2); auto. Qed.
Lemma fmt_fp_zfill_eq : forall fuel st, fmt_fp_zfill fuel st = wloop (fun st => 0 <? fst st) fmt_fp_zfill_body fuel st.
Proof. induction fuel; intros [s b]; cbn - [fmt_fp_zfill_body Z.ltb]; [reflexivity|]. destruct (0 <? s); auto. Qed.
Lemma fmt_fp_fint_eq : forall fuel big a r st,
  fmt_fp_fint fuel big a r st = owloop (fun st => fst st <=? r) (fmt_fp_fint_body big a) fuel st.
Proof. induction fuel; intros big a r [d o]; cbn - [fmt_fp_fint_body Z.leb]; [reflexivity|]. destruct (d <=? r); [|reflexivity]. destruct (fmt_fp_fint_body _ _ _); auto. Qed.
Lemma fmt_fp_ffrac_eq : forall fuel big z st,
  fmt_fp_ffrac fuel big z st = owloop (fun st => let '(d, p, _) := st in (d <? z) && (0 <? p)) (fmt_fp_ffrac_body big) fuel st.
Proof. induction fuel; intros big z [[d p] o]; cbn - [fmt_fp_ffrac_body Z.ltb andb]; [reflexivity|]. destruct (_ && _); [|reflexivity]. destruct (fmt_fp_ffrac_body _ _); auto. Qed.
Lemma fmt_fp_eloop_eq : forall fuel big a z fl st,
  fmt_fp_eloop fuel big a z fl st = owloop (fun st => let '(d, p, _) := st in (d <? z) && (0 <=? p)) (fmt_fp_eloop_body big a fl) fuel st.
Proof. induction fuel; intros big a z fl [[d p] o]; cbn - [fmt_fp_eloop_body Z.ltb Z.leb andb]; [reflexivity|]. destruct (_ && _); [|reflexivity]. destruct (fmt_fp_eloop_body _ _ _ _); auto. Qed.

Definition okb (b : Z) : Prop := 0 <= b < 256 /\ b <> 120 /\ b <> 88.
Definition OKL (l : list Z) : Prop := forall i, okb (znth l i).

Lemma okb_0 : okb 0. Proof. unfold okb. lia. Qed.
Lemma OKL_nil : OKL [].
Proof. intros i. unfold znth. destruct (i <? 0); [apply okb_0|]. destruct (Z.to_nat i); apply okb_0. Qed.
Lemma OKL_Forall : forall l, OKL l <-> Forall okb l.
Proof.
  intros l. split.
  - intros H. apply Forall_forall. intros x I. apply In_nth with (d := 0) in I. destruct I as [n [Hn <-]].
    specialize (H (Z.of_nat n)). unfold znth in H. destruct (Z.ltb_spec (Z.of_nat n) 0); [lia|]. rewrite Nat2Z.id in H. exact H.
  - intros F i. destruct (znth_In_or l i) as [->|I]; [apply okb_0|]. rewrite Forall_forall in F. apply F. exact I.
Qed.
Lemma OKL_app : forall l1 l2, OKL l1 -> OKL l2 -> OKL (l1 ++ l2).
Proof. intros l1 l2 H1 H2. apply OKL_Forall. apply Forall_app. split; apply OKL_Forall; assumption. Qed.
Lemma OKL_zupd : forall l i v, OKL l -> okb v -> OKL (zupd l i v).
Proof.
  intros l i v H Hv j. destruct (Z.eq_dec i j).
  - subst. destruct (Z.lt_ge_cases j 0). { rewrite znth_neg by lia. apply okb_0. }
    destruct (Z.lt_ge_cases j (zlength l)). { rewrite znth_zupd_eq by lia. exact Hv. }
    rewrite znth_ge. { apply okb_0. } rewrite zlength_zupd. lia.
  - rewrite znth_zupd_neq by lia. apply H.
Qed.
Lemma OKL_zrepeat : forall v n, okb v -> OKL (zrepeat v n).
Proof. intros v n Hv i. rewrite znth_zrepeat. destruct (_ && _); [exact Hv| apply okb_0]. Qed.
Lemma OKL_firstn : forall n l, OKL l -> OKL (firstn n l).
Proof.
  intros n l H. apply OKL_Forall. apply OKL_Forall in H. revert n. induction H; intros [|n]; cbn; try constructor; auto.
Qed.
Lemma OKL_skipn : forall n l, OKL l -> OKL (skipn n l).
Proof.
  intros n l H. apply OKL_Forall. apply OKL_Forall in H. revert n. induction H; intros [|n]; cbn; try constructor; auto.
Qed.
Lemma OKL_zsub : forall l i n, OKL l -> OKL (zsub l i n).
Proof. intros. unfold zsub. apply OKL_firstn, OKL_skipn. assumption. Qed.
Lemma OKL_out : forall o b, OKL o -> OKL b -> OKL (out o b).
Proof. intros. unfold out. apply OKL_app; assumption. Qed.
Lemma okb_digit : forall y, okb (CHR_0 + y mod 10).
Proof. intros. unfold okb, CHR_0. pose proof (Z.mod_pos_bound y 10 ltac:(lia)). lia. Qed.
Lemma okb_chr0 : okb CHR_0. Proof. unfold okb, CHR_0; lia. Qed.
Lemma okb_sp : okb CHR_sp. Proof. unfold okb, CHR_sp; lia. Qed.
Lemma okb_dot : okb CHR_dot. Proof. unfold okb, CHR_dot; lia. Qed.

Lemma pad_total : forall o c w l fl, OKL o -> okb c -> w - l < 256 * 64 ->
  exists o', pad o c w l fl = Some o' /\ OKL o'.
Proof.
  intros o c w l fl Ho Hc Hw. unfold pad.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l)) eqn:C. { eexists. split; [reflexivity| exact Ho]. }
  apply orb_false_elim in C. destruct C as [_ C]. apply Z.leb_gt in C.
  rewrite pad_loop_eq.
  destruct (wloop_total (fun s : Z * list Z => 256 <=? fst s) (pad_loop_body c) (fun s => OKL (snd s)) (fun s => fst s / 256))
    with (fuel := PAD_FUEL) (s := (w - l, o)) as [[l' o'] (E & OK & _)].
  - intros [l1 o1] H1 C1. cbn [fst snd] in *. apply Z.leb_le in C1. unfold pad_loop_body. cbn [fst snd].
    split. { apply OKL_out; [exact H1| apply OKL_zrepeat; exact Hc]. }
    replace (l1 - 256) with (l1 + (-1) * 256) by lia. rewrite Z.div_add by lia.
    assert (1 <= l1 / 256) by (apply Z.div_le_lower_bound; lia). lia.
  - exact Ho.
  - cbn [fst]. unfold PAD_FUEL. change (Z.of_nat 64) with 64. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
  - rewrite E. eexists. split; [reflexivity|]. apply OKL_out; [exact OK| apply OKL_zrepeat; exact Hc].
Qed.

Lemma fmt_u_loop_total : forall k fuel y s b, 0 <= y < 10 ^ Z.of_nat k -> (k < fuel)%nat -> OKL b ->
  exists y' s' b', fmt_u_loop fuel (y, s, b) = Some (y', s', b') /\ OKL b' /\ s - Z.of_nat k <= s' <= s /\ zlength b' = zlength b.
Proof.
  induction k as [|k IH]; intros fuel y s b Hy Hf Hb.
  - destruct fuel as [|fuel]; [lia|]. cbn [fmt_u_loop]. change (10 ^ Z.of_nat 0) with 1 in Hy.
    replace (y =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn. eexists _, _, _. split; [reflexivity|]. split; [exact Hb|]. split; [lia| reflexivity].
  - destruct fuel as [|fuel]; [lia|]. cbn [fmt_u_loop].
    destruct (Z.eqb_spec y 0) as [->|NZ]; cbn [negb].
    + eexists _, _, _. split; [reflexivity|]. split; [exact Hb|]. split; [lia| reflexivity].
    + unfold fmt_u_loop_body.
      destruct (IH fuel (y / 10) (s - 1) (zupd b (s - 1) (CHR_0 + y mod 10))) as [y' [s' [b' (E & OK & R & L)]]].
      * rewrite Nat2Z.inj_succ in Hy. rewrite Z.pow_succ_r in Hy by lia.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
      * lia.
      * apply OKL_zupd; [exact Hb| apply okb_digit].
      * rewrite E. eexists _, _, _. split; [reflexivity|]. split; [exact OK|]. split; [rewrite Nat2Z.inj_succ in *; lia| rewrite L; apply zlength_zupd].
Qed.

Lemma fmt_u_total : forall x b s, 0 <= x < 2^64 -> OKL b ->
  exists s' b', fmt_u x b s = Some (s', b') /\ OKL b' /\ s - 20 <= s' <= s /\ zlength b' = zlength b.
Proof.
  intros x b s Hx Hb. unfold fmt_u.
  destruct (fmt_u_loop_total 20 FMT_U_FUEL x s b) as [y' [s' [b' (E & OK & R & L)]]].
  { change (10 ^ Z.of_nat 20) with (10 ^ 20). assert (2^64 <= 10^20) by (cbv; discriminate || lia). lia. }
  { unfold FMT_U_FUEL. lia. } { exact Hb. }
  rewrite E. eexists _, _. split; [reflexivity|]. split; [exact OK|]. split; [cbn in R; lia| exact L].
Qed.

Lemma fmt_u_total_small : forall x b s, 0 <= x < 2^32 -> OKL b ->
  exists s' b', fmt_u x b s = Some (s', b') /\ OKL b' /\ s - 10 <= s' <= s /\ zlength b' = zlength b.
Proof.
  intros x b s Hx Hb. unfold fmt_u.
  destruct (fmt_u_loop_total 10 FMT_U_FUEL x s b) as [y' [s' [b' (E & OK & R & L)]]].
  { change (10 ^ Z.of_nat 10) with (10 ^ 10). lia. }
  { unfold FMT_U_FUEL. lia. } { exact Hb. }
  rewrite E. eexists _, _. split; [reflexivity|]. split; [exact OK|]. split; [cbn in R; lia| exact L].
Qed.

Lemma fmt_fp_zfill_total : forall s buf, s <= 11 -> OKL buf ->
  exists s' buf', fmt_fp_zfill ZFILL_FUEL (s, buf) = Some (s', buf') /\ OKL buf' /\ s' <= 0.
Proof.
  intros s buf Hs Hb. rewrite fmt_fp_zfill_eq.
  destruct (wloop_total (fun st : Z * list Z => 0 <? fst st) fmt_fp_zfill_body (fun st => OKL (snd st) /\ fst st <= 11) (fun st => Z.max 0 (fst st)))
    with (fuel := ZFILL_FUEL) (s := (s, buf)) as [[s' b'] (E & [OK R] & C)].
  - intros [s1 b1] [H1 R1] C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. unfold fmt_fp_zfill_body. cbn [fst snd].
    split; [split; [apply OKL_zupd; [exact H1| apply okb_chr0]| lia]| lia].
  - cbn [fst snd]. auto.
  - cbn [fst]. unfold ZFILL_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. eexists _, _. split; [reflexivity|]. cbn [fst snd] in *. split; [exact OK|]. apply Z.ltb_ge in C. lia.
Qed.

Lemma fmt_fp_epad_total : forall estr eb, estr <= 12 -> OKL eb ->
  exists estr' eb', fmt_fp_epad EPAD_FUEL (estr, eb) = Some (estr', eb') /\ OKL eb' /\ estr' <= 10 /\ estr - 2 <= estr' /\ zlength eb' = zlength eb.
Proof.
  intros estr eb He Hb. rewrite fmt_fp_epad_eq.
  destruct (wloop_total (fun st : Z * list Z => 12 - fst st <? 2) fmt_fp_epad_body
             (fun st => OKL (snd st) /\ fst st <= 12 /\ estr - 2 <= fst st /\ (fst st < estr -> fst st >= 10 \/ True) /\ zlength (snd st) = zlength eb)
             (fun st => Z.max 0 (fst st - 10)))
    with (fuel := EPAD_FUEL) (s := (estr, eb)) as [[e' b'] (E & (OK & R1 & R2 & _ & L) & C)].
  - intros [e1 b1] (H1 & Q1 & Q2 & _ & L1) C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. unfold fmt_fp_epad_body. cbn [fst snd].
    split; [| lia]. split; [apply OKL_zupd; [exact H1| apply okb_chr0]|]. split; [lia|]. split; [lia|]. split; [auto| rewrite zlength_zupd; exact L1].
  - cbn [fst snd]. split; [exact Hb|]. split; [lia|]. split; [lia|]. split; [auto| reflexivity].
  - cbn [fst]. unfold EPAD_FUEL. change (Z.of_nat 4) with 4. lia.
  - rewrite E. eexists _, _. split; [reflexivity|]. cbn [fst snd] in *. split; [exact OK|]. apply Z.ltb_ge in C. split; [lia|]. split; [lia| exact L].
Qed.

Lemma pow10_succ : forall k, 0 <= k -> 10 ^ (k + 1) = 10 * 10 ^ k.
Proof. intros. rewrite <- Z.pow_succ_r by lia. reflexivity. Qed.

Lemma fmt_fp_cnt_total : forall v e0, 0 <= v < 2^32 ->
  exists i e, fmt_fp_cnt TEN_FUEL v (10, e0) = Some (i, e) /\ e0 <= e <= e0 + 9.
Proof.
  intros v e0 Hv. rewrite fmt_fp_cnt_eq.
  destruct (wloop_total (fun s : Z * Z => fst s <=? v) fmt_fp_cnt_body
             (fun s => exists k, 1 <= k <= 10 /\ fst s = 10 ^ k /\ snd s = e0 + k - 1)
             (fun s => 11 - (snd s - e0))) with (fuel := TEN_FUEL) (s := (10, e0)) as [[i e] (E & [k (Hk & Hi & He)] & C)].
  - intros [i e] [k (Hk & Hi & He)] C1. cbn [fst snd] in *. subst i. apply Z.leb_le in C1.
    assert (k <= 9). { destruct (Z.le_gt_cases k 9); [assumption|]. exfalso.
      assert (10 ^ 10 <= 10 ^ k) by (apply Z.pow_le_mono_r; lia). change (10^10) with 10000000000 in H0. lia. }
    unfold fmt_fp_cnt_body. cbn [fst snd]. split; [| lia]. exists (k + 1). split; [lia|]. split; [rewrite pow10_succ by lia; lia| lia].
  - exists 1. cbn. repeat split; lia.
  - cbn [snd]. unfold TEN_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. eexists _, _. split; [reflexivity|]. cbn [fst snd] in *. lia.
Qed.

Lemma fmt_fp_powi_total : forall j0, 0 <= j0 ->
  exists i j, fmt_fp_powi TEN_FUEL (10, j0) = Some (i, j) /\ (exists k, 1 <= k <= 10 /\ i = 10 ^ k).
Proof.
  intros j0 Hj. rewrite fmt_fp_powi_eq.
  destruct (wloop_total (fun s : Z * Z => snd s <? 9) fmt_fp_powi_body
             (fun s => exists k, 1 <= k /\ fst s = 10 ^ k /\ snd s = j0 + k - 1 /\ (1 < k -> j0 + k - 2 < 9))
             (fun s => Z.max 0 (10 - snd s))) with (fuel := TEN_FUEL) (s := (10, j0)) as [[i j] (E & [k (Hk & Hi & Hj' & Hb)] & C)].
  - intros [i j] [k (Hk & Hi & Hj2 & Hb)] C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. subst i j.
    unfold fmt_fp_powi_body. cbn [fst snd]. split; [|lia]. exists (k + 1). split; [lia|]. split; [rewrite pow10_succ by lia; lia|]. split; [lia|]. intros; lia.
  - exists 1. cbn [fst snd]. repeat split; try lia.
  - cbn [snd]. unfold TEN_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. eexists _, _. split; [reflexivity|]. exists k. cbn [fst snd] in *. apply Z.ltb_ge in C. split; [| exact Hi]. lia.
Qed.

Lemma fmt_fp_tz_total : forall v, 0 < v < 2^32 ->
  exists i j, fmt_fp_tz TEN_FUEL v (10, 0) = Some (i, j).
Proof.
  intros v Hv. rewrite fmt_fp_tz_eq.
  destruct (wloop_total (fun s : Z * Z => v mod fst s =? 0) fmt_fp_tz_body
             (fun s => exists k, 1 <= k <= 10 /\ fst s = 10 ^ k /\ snd s = k - 1)
             (fun s => 11 - snd s)) with (fuel := TEN_FUEL) (s := (10, 0)) as [[i j] (E & _ & _)].
  - intros [i j] [k (Hk & Hi & Hj)] C1. cbn [fst snd] in *. subst i j. apply Z.eqb_eq in C1.
    assert (k <= 9). { destruct (Z.le_gt_cases k 9); [assumption|]. exfalso.
      apply Z.mod_divide in C1; [|pose proof (Z.pow_pos_nonneg 10 k); lia]. destruct C1 as [q Hq].
      assert (10 ^ 10 <= 10 ^ k) by (apply Z.pow_le_mono_r; lia). change (10^10) with 10000000000 in H0.
      pose proof (Z.pow_pos_nonneg 10 k). assert (1 <= q) by nia. nia. }
    unfold fmt_fp_tz_body. cbn [fst snd]. split; [|lia]. exists (k + 1). split; [lia|]. split; [rewrite pow10_succ by lia; lia| lia].
  - exists 1. cbn. repeat split; lia.
  - cbn [snd]. unfold TEN_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. eexists _, _. reflexivity.
Qed.

Definition W32L (x : list Z) : Prop := forall i, 0 <= znth x i < 2^32.
Lemma W32L_zupd : forall x i v, W32L x -> 0 <= v < 2^32 -> W32L (zupd x i v).
Proof. exact W32_zupd. Qed.

Lemma fmt_fp_carry_total : forall big d a, W32L big -> a <= d <= a + 100 ->
  exists big' d' a', fmt_fp_carry BIG_FUEL (big, d, a) = Some (big', d', a') /\ W32L big' /\ a - 1 <= a' <= a /\ zlength big' = zlength big.
Proof.
  intros big d a WB Had.
  rewrite fmt_fp_carry_eq.
  destruct (wloop_total (fun s : list Z * Z * Z => let '(big0, d0, _) := s in 999999999 <? znth big0 d0) fmt_fp_carry_body
             (fun s => let '(b, d1, a1) := s in W32L b /\ zlength b = zlength big /\
                        ((a1 = a /\ a <= d1 <= d) \/ (a1 = a - 1 /\ znth b d1 <= 999999999)))
             (fun s => let '(b, d1, a1) := s in if a1 =? a then d1 - a + 2 else 0))
    with (fuel := BIG_FUEL) (s := (big, d, a)) as [[[b' d'] a'] (E & (W' & L' & R') & _)].
  - intros [[b d1] a1] (W1 & L1 & D1) C1. apply Z.ltb_lt in C1.
    destruct D1 as [[-> R1]|[-> R1]]; [|lia].
    rewrite Z.eqb_refl.
    unfold fmt_fp_carry_body.
    destruct (Z.ltb_spec (d1 - 1) a).
    +
      assert (d1 = a) by lia. subst d1.
      set (b2 := zupd (zupd b a 0) (a - 1) 0).
      assert (L2 : zlength b2 = zlength b) by (subst b2; now rewrite !zlength_zupd).
      assert (X1 : znth (zupd b2 (a - 1) (u32 (znth b2 (a - 1) + 1))) (a - 1) <= 999999999).
      { destruct (Z.lt_ge_cases (a - 1) 0). { rewrite znth_neg by lia. lia. }
        destruct (Z.lt_ge_cases (a - 1) (zlength b)). 2:{ rewrite znth_ge; [lia|]. rewrite zlength_zupd, L2. lia. }
        rewrite znth_zupd_eq by (rewrite L2; lia). subst b2. rewrite znth_zupd_eq by (rewrite zlength_zupd; lia). cbv. discriminate. }
      split.
      * split; [apply W32L_zupd; [subst b2; apply W32L_zupd; [apply W32L_zupd; [exact W1|lia]|lia]| apply u32_range]|].
        split; [rewrite zlength_zupd, L2; exact L1|]. right. split; [reflexivity| exact X1].
      * replace (a - 1 =? a) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    + split.
      * split; [apply W32L_zupd; [apply W32L_zupd; [exact W1| lia]| apply u32_range]|]. split; [rewrite !zlength_zupd; exact L1|]. left; lia.
      * rewrite Z.eqb_refl. lia.
  - split; [exact WB|]. split; [reflexivity|]. left; lia.
  - rewrite Z.eqb_refl. unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. eexists _, _, _. split; [reflexivity|]. split; [exact W'|]. split; [| exact L']. destruct R' as [[-> _]|[-> _]]; lia.
Qed.

Lemma okb_u8_101 : okb (u8 101). Proof. unfold okb, u8. cbn. lia. Qed.
Lemma okb_sign : forall e, okb (if e <? 0 then CHR_minus else CHR_plus).
Proof. intros. unfold okb, CHR_minus, CHR_plus. destruct (e <? 0); lia. Qed.

Lemma fmt_fp_len_total : forall t l e, (t = 101 \/ t = 102) -> 0 <= l <= 1000 -> -2000 <= e <= 2000 ->
  exists r, fmt_fp_len t l e = Some r /\
    match r with Ret _ => True | Cont (l', ebuf0, estr) => OKL ebuf0 /\ 0 <= l' <= 4000 end.
Proof.
  intros t l e Ht Hl He. unfold fmt_fp_len.
  destruct Ht as [-> | ->].
  - change (Z.lor 101 32 =? CHR_f) with false. cbn iota.
    destruct (fmt_u_total (if e <? 0 then - e else e) (zrepeat 0 12) 12) as [s' [b' (E1 & OK1 & R1 & L1)]].
    { destruct (Z.ltb_spec e 0); lia. } { apply OKL_zrepeat. apply okb_0. }
    rewrite E1.
    destruct (fmt_fp_epad_total s' b' ltac:(lia) OK1) as [es [eb (E2 & OK2 & R2 & R3 & L2)]]. rewrite E2.
    destruct (INT_MAX - l <? 12 - (es - 1 - 1)). { eexists. split; [reflexivity|]. exact I. }
    eexists. split; [reflexivity|]. split.
    + apply OKL_zupd; [apply OKL_zupd; [exact OK2| apply okb_sign]| apply okb_u8_101].
    + lia.
  - change (Z.lor 102 32 =? CHR_f) with true. cbn iota.
    destruct (INT_MAX - l <? e). { eexists. split; [reflexivity|]. exact I. }
    eexists. split; [reflexivity|]. cbn iota. split; [apply OKL_zrepeat; apply okb_0|]. destruct (Z.ltb_spec 0 e); lia.
Qed.

Lemma fmt_fp_fint_body_total : forall big a d o, W32L big -> OKL o ->
  exists o', fmt_fp_fint_body big a (d, o) = Some (d + 1, o') /\ OKL o'.
Proof.
  intros big a d o WB Ho. unfold fmt_fp_fint_body.
  destruct (fmt_u_total_small (znth big d) (zrepeat 0 37) 9 (WB d)) as [s' [b' (E1 & OK1 & R1 & L1)]]. { apply OKL_zrepeat, okb_0. }
  rewrite E1.
  match goal with |- exists o', (match ?m with Some _ => _ | None => None end) = _ /\ _ =>
    assert (M : exists s2 b2, m = Some (s2, b2) /\ OKL b2) end.
  { destruct (negb (d =? a)).
    - destruct (fmt_fp_zfill_total s' b' ltac:(lia) OK1) as [s2 [b2 (E2 & OK2 & _)]]. rewrite E2. eexists _, _. split; [reflexivity| exact OK2].
    - destruct (s' =? 9); eexists _, _; (split; [reflexivity|]); [apply OKL_zupd; [exact OK1| apply okb_chr0]| exact OK1]. }
  destruct M as [s2 [b2 (-> & OK2)]].
  eexists. split; [reflexivity|]. apply OKL_out; [exact Ho| apply OKL_zsub; exact OK2].
Qed.

Lemma fmt_fp_fint_total : forall big a r d o, W32L big -> OKL o -> r - d <= 128 ->
  exists d' o', fmt_fp_fint BIG_FUEL big a r (d, o) = Some (d', o') /\ OKL o'.
Proof.
  intros big a r d o WB Ho Hd. rewrite fmt_fp_fint_eq.
  destruct (owloop_total (fun st : Z * list Z => fst st <=? r) (fmt_fp_fint_body big a) (fun st => OKL (snd st) /\ r - fst st <= 128)
             (fun st => Z.max 0 (r - fst st + 1))) with (fuel := BIG_FUEL) (s := (d, o)) as [[d' o'] (E & [OK _] & _)].
  - intros [d1 o1] [H1 R1] C1. cbn [fst snd] in *. apply Z.leb_le in C1.
    destruct (fmt_fp_fint_body_total big a d1 o1 WB H1) as [o2 [E2 OK2]]. rewrite E2.
    eexists. split; [reflexivity|]. cbn [fst snd]. split; [split; [exact OK2| lia]| lia].
  - cbn. auto.
  - cbn [fst]. unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. eexists _, _. split; [reflexivity| exact OK].
Qed.

Lemma fmt_fp_ffrac_total : forall big z d p o, W32L big -> OKL o -> p <= 1000 ->
  exists d' p' o', fmt_fp_ffrac BIG_FUEL big z (d, p, o) = Some (d', p', o') /\ OKL o' /\ p' <= p.
Proof.
  intros big z d p o WB Ho Hp. rewrite fmt_fp_ffrac_eq.
  destruct (owloop_total (fun st : Z * Z * list Z => let '(d0, p0, _) := st in (d0 <? z) && (0 <? p0)) (fmt_fp_ffrac_body big)
             (fun st => let '(_, p0, o0) := st in OKL o0 /\ p0 <= p)
             (fun st => let '(_, p0, _) := st in Z.max 0 ((p0 + 8) / 9))) with (fuel := BIG_FUEL) (s := (d, p, o)) as [[[d' p'] o'] (E & [OK P] & _)].
  - intros [[d1 p1] o1] [H1 P1] C1. apply andb_prop in C1. destruct C1 as [_ C1]. apply Z.ltb_lt in C1.
    unfold fmt_fp_ffrac_body.
    destruct (fmt_u_total_small (znth big d1) (zrepeat 0 37) 9 (WB d1)) as [s' [b' (E1 & OK1 & R1 & L1)]]. { apply OKL_zrepeat, okb_0. }
    rewrite E1.
    destruct (fmt_fp_zfill_total s' b' ltac:(lia) OK1) as [s2 [b2 (E2 & OK2 & _)]]. rewrite E2.
    eexists. split; [reflexivity|]. split. { split; [apply OKL_out; [exact H1| apply OKL_zsub; exact OK2]| lia]. }
    replace (p1 - 9 + 8) with ((p1 + 8) + (-1) * 9) by lia. rewrite Z.div_add by lia.
    assert (1 <= (p1 + 8) / 9) by (apply Z.div_le_lower_bound; lia). lia.
  - split; [exact Ho| lia].
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. assert ((p + 8) / 9 <= 112) by (apply Z.div_le_upper_bound; lia). lia.
  - rewrite E. eexists _, _, _. split; [reflexivity|]. auto.
Qed.

Lemma fmt_fp_eloop_body_total : forall big a fl d p o, W32L big -> OKL o ->
  exists p' o', fmt_fp_eloop_body big a fl (d, p, o) = Some (d + 1, p', o') /\ OKL o' /\ p' <= p.
Proof.
  intros big a fl d p o WB Ho. unfold fmt_fp_eloop_body.
  destruct (fmt_u_total_small (znth big d) (zrepeat 0 37) 9 (WB d)) as [s' [b' (E1 & OK1 & R1 & L1)]]. { apply OKL_zrepeat, okb_0. }
  rewrite E1.
  set (sb := if s' =? 9 then (s' - 1, zupd b' (s' - 1) CHR_0) else (s', b')).
  assert (SB : exists s2 b2, sb = (s2, b2) /\ OKL b2 /\ s2 <= 8).
  { subst sb. destruct (Z.eqb_spec s' 9); eexists _, _; (split; [reflexivity|]).
    - split; [apply OKL_zupd; [exact OK1| apply okb_chr0]| lia].
    - split; [exact OK1| lia]. }
  destruct SB as [s2 [b2 (-> & OK2 & S2)]].
  match goal with |- exists p' o', (match ?m with Some _ => _ | None => None end) = _ /\ _ =>
    assert (M : exists s3 b3 o3, m = Some (s3, b3, o3) /\ OKL b3 /\ OKL o3 /\ s3 <= 9) end.
  { destruct (negb (d =? a)).
    - destruct (fmt_fp_zfill_total s2 b2 ltac:(lia) OK2) as [s3 [b3 (E3 & OK3 & S3)]]. rewrite E3. eexists _, _, _. split; [reflexivity|]. split; [exact OK3|]. split; [exact Ho| lia].
    - assert (OD : OKL [CHR_dot]). { intros i; unfold znth; destruct (i <? 0); [apply okb_0|]; destruct (Z.to_nat i) as [|[|n]]; cbn; try apply okb_dot; apply okb_0. }
      assert (H : OKL (out o (zsub b2 s2 1))) by (apply OKL_out; [exact Ho| apply OKL_zsub; exact OK2]).
      destruct ((0 <? p) || negb (Z.land fl ALT_FORM =? 0)); eexists _, _, _; (split; [reflexivity|]); (split; [exact OK2|]); (split; [| lia]).
      + apply OKL_out; [exact H| exact OD].
      + exact H. }
  destruct M as [s3 [b3 [o3 (-> & OK3 & OKo3 & S3)]]].
  eexists _, _. split; [reflexivity|]. split; [apply OKL_out; [exact OKo3| apply OKL_zsub; exact OK3]| lia].
Qed.

Lemma fmt_fp_eloop_total : forall big a z fl d p o, W32L big -> OKL o -> z - d <= 129 ->
  exists d' p' o', fmt_fp_eloop BIG_FUEL big a z fl (d, p, o) = Some (d', p', o') /\ OKL o' /\ p' <= p.
Proof.
  intros big a z fl d p o WB Ho Hz. rewrite fmt_fp_eloop_eq.
  destruct (owloop_total (fun st : Z * Z * list Z => let '(d0, p0, _) := st in (d0 <? z) && (0 <=? p0)) (fmt_fp_eloop_body big a fl)
             (fun st => let '(d0, p0, o0) := st in OKL o0 /\ p0 <= p /\ z - d0 <= 129)
             (fun st => let '(d0, _, _) := st in Z.max 0 (z - d0))) with (fuel := BIG_FUEL) (s := (d, p, o)) as [[[d' p'] o'] (E & (OK & P & _) & _)].
  - intros [[d1 p1] o1] (H1 & P1 & Z1) C1. apply andb_prop in C1. destruct C1 as [C1 _]. apply Z.ltb_lt in C1.
    destruct (fmt_fp_eloop_body_total big a fl d1 p1 o1 WB H1) as [p2 [o2 (E2 & OK2 & P2)]].
    rewrite E2. eexists. split; [reflexivity|]. split; [split; [exact OK2| lia]| lia].
  - split; [exact Ho| lia].
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. eexists _, _, _. split; [reflexivity|]. auto.
Qed.

Lemma fmt_fp_emit_f_total : forall o big a r z p fl, W32L big -> OKL o -> r - 128 <= a -> 0 <= p <= 1000 ->
  exists o', fmt_fp_emit_f o big a r z p fl = Some o' /\ OKL o'.
Proof.
  intros o big a r z p fl WB Ho Ha Hp. unfold fmt_fp_emit_f.
  destruct (fmt_fp_fint_total big (if r <? a then r else a) r (if r <? a then r else a) o WB Ho) as [d1 [o1 [E1 OK1]]].
  { destruct (r <? a); lia. }
  rewrite E1.
  set (o2 := if negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0) then out o1 [CHR_dot] else o1).
  assert (OK2 : OKL o2).
  { subst o2. destruct (_ || _); [| exact OK1]. apply OKL_out; [exact OK1|].
    intros i; unfold znth; destruct (i <? 0); [apply okb_0|]; destruct (Z.to_nat i) as [|[|n]]; cbn; try apply okb_dot; apply okb_0. }
  destruct (fmt_fp_ffrac_total big z d1 p o2 WB OK2 ltac:(lia)) as [d3 [p3 [o3 (E3 & OK3 & P3)]]]. rewrite E3.
  apply pad_total; [exact OK3| apply okb_chr0| lia].
Qed.

Lemma fmt_fp_emit_e_total : forall o big a z p fl ebuf0 estr, W32L big -> OKL o -> OKL ebuf0 -> z - a <= 129 -> p <= 1000 ->
  exists o', fmt_fp_emit_e o big a z p fl ebuf0 estr = Some o' /\ OKL o'.
Proof.
  intros o big a z p fl ebuf0 estr WB Ho He Hz Hp. unfold fmt_fp_emit_e.
  destruct (fmt_fp_eloop_total big a (if z <=? a then a + 1 else z) fl a p o WB Ho) as [d1 [p1 [o1 (E1 & OK1 & P1)]]].
  { destruct (z <=? a); lia. }
  rewrite E1.
  destruct (pad_total o1 CHR_0 (p1 + 18) 18 0 OK1 okb_chr0 ltac:(lia)) as [o2 [E2 OK2]]. rewrite E2.
  eexists. split; [reflexivity|]. apply OKL_out; [exact OK2| apply OKL_zsub; exact He].
Qed.
