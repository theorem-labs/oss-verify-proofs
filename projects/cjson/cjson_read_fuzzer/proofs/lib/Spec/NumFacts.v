(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Bool.
From Stdlib Require List.
From Stdlib Require Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
Module FmtFpProps.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_of_u32 f128_of_i32.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pow10_succ : forall k, 0 <= k -> 10 ^ (k + 1) = 10 * 10 ^ k.
Proof. intros. rewrite <- Z.pow_succ_r by lia. reflexivity. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
    + (* [comment removed for export] *)
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
End FmtFpProps.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloatProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFpDig.
Module FmtFpRun.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps FmtFpProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_of_u32 f128_of_i32.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

Definition NB : Z := 1000000000.

(* [comment removed for export] *)
Definition W9 (b : list Z) : Prop := forall i, 0 <= znth b i < NB.
Definition zeros_below (b : list Z) (a : Z) : Prop := forall k, k < a -> znth b k = 0.
Definition zeros_from (b : list Z) (z : Z) : Prop := forall k, z <= k -> znth b k = 0.

Lemma W9_W32 : forall b, W9 b -> W32L b.
Proof. intros b H i. pose proof (H i). unfold NB in *. lia. Qed.
Lemma W9_zupd : forall b i v, W9 b -> 0 <= v < NB -> W9 (zupd b i v).
Proof.
  intros b i v H Hv j. destruct (Z.eq_dec i j) as [->|].
  - destruct (Z.lt_ge_cases j 0). { rewrite znth_neg by lia. unfold NB; lia. }
    destruct (Z.lt_ge_cases j (zlength b)). { rewrite znth_zupd_eq by lia. lia. }
    rewrite znth_ge by (rewrite zlength_zupd; lia). unfold NB; lia.
  - rewrite znth_zupd_neq by lia. apply H.
Qed.
Lemma W9_zrepeat : forall n, W9 (zrepeat 0 n).
Proof. intros n i. rewrite znth_zrepeat. unfold NB. destruct (_ && _); lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma strip_spec : forall big a z, z - a <= 129 -> a < z -> znth big a <> 0 ->
  exists z', fmt_fp_strip BIG_FUEL big a z = Some z' /\ a < z' <= z /\
    (forall i, z' <= i < z -> znth big i = 0) /\ znth big (z' - 1) <> 0.
Proof.
  intros big a z Hz Haz NZ. rewrite fmt_fp_strip_eq.
  destruct (wloop_total (fun z0 => (a <? z0) && (znth big (z0 - 1) =? 0)) fmt_fp_strip_body
             (fun z' => a < z' <= z /\ forall i, z' <= i < z -> znth big i = 0) (fun z' => Z.max 0 (z' - a)))
    with (fuel := BIG_FUEL) (s := z) as [z' (E & [Q1 Q2] & C)].
  - intros z1 [R1 R2] C1. apply andb_prop in C1. destruct C1 as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2. unfold fmt_fp_strip_body.
    assert (z1 - 1 <> a) by (intros X; rewrite X in C2; exact (NZ C2)).
    split; [|lia]. split; [lia|]. intros i Hi. destruct (Z.eq_dec i (z1 - 1)) as [->|]; [exact C2|]. apply R2. lia.
  - split; [lia|]. intros; lia.
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - exists z'. split; [exact E|]. split; [exact Q1|]. split; [exact Q2|].
    apply Bool.andb_false_iff in C. destruct C as [C|C]. { apply Z.ltb_ge in C. lia. } apply Z.eqb_neq in C. exact C.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma up_inner_spec : forall sh a big z, 1 <= sh <= 29 -> a < z -> z - a <= 128 -> W9 big -> zlength big = 128 -> 0 <= a < 128 ->
  exists big' d' c', fmt_fp_up_inner sh BIG_FUEL a (big, z - 1, 0) = Some (big', d', c') /\
    W9 big' /\ 0 <= c' < NB /\ zlength big' = 128 /\ d' = a - 1 /\
    (forall i, (i < a \/ z <= i) -> znth big' i = znth big i) /\
    exists cin, 0 <= cin < NB /\ let x := znth big a * 2 ^ sh + cin in
      c' = x / NB /\ znth big' a = x mod NB.
Proof.
  intros sh a big z Hsh Haz Hza WB LB Ha. rewrite fmt_fp_up_inner_eq.
  assert (P2 : 2 <= 2 ^ sh <= 2^29). { split. { change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. } apply Z.pow_le_mono_r; lia. }
  destruct (wloop_total (fun s : list Z * Z * Z => let '(_, d0, _) := s in a <=? d0) (fmt_fp_up_inner_body sh)
             (fun s => let '(b, d1, c1) := s in W9 b /\ 0 <= c1 < NB /\ zlength b = 128 /\ a - 1 <= d1 <= z - 1 /\
                 (forall i, (i <= d1 \/ z <= i) -> znth b i = znth big i) /\
                 (d1 < a -> exists cin, 0 <= cin < NB /\ let x := znth big a * 2 ^ sh + cin in
                      c1 = x / NB /\ znth b a = x mod NB))
             (fun s => let '(_, d1, _) := s in Z.max 0 (d1 - a + 1)))
    with (fuel := BIG_FUEL) (s := (big, z - 1, 0)) as [[[b' d'] c'] (E & (W' & C' & L' & D' & U' & X') & CND)].
  - intros [[b d1] c1] (W1 & C1 & L1 & D1 & U1 & _) CC. apply Z.leb_le in CC. unfold fmt_fp_up_inner_body.
    pose proof (W1 d1) as Wd. rewrite Z.shiftl_mul_pow2 by lia.
    set (x := znth b d1 * 2 ^ sh + c1).
    assert (XR : 0 <= x <= (NB - 1) * 2^29 + NB) by (subst x; unfold NB in *; nia).
    assert (XD : 0 <= x / NB < NB). { unfold NB in *. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    change 1000000000 with NB.
    split; [| lia]. split. { apply W9_zupd; [exact W1|]. pose proof (Z.mod_pos_bound x NB ltac:(unfold NB; lia)). lia. }
    split; [rewrite u32_id by (unfold NB in *; lia); lia|]. split; [now rewrite zlength_zupd|]. split; [lia|].
    split. { intros i Hi. rewrite znth_zupd_neq by lia. apply U1. lia. }
    intros LT. assert (d1 = a) by lia. subst d1. exists c1. split; [lia|]. cbv zeta.
    rewrite u32_id by (unfold NB in *; lia). subst x. rewrite <- (U1 a ltac:(lia)).
    split; [reflexivity|]. apply znth_zupd_eq. rewrite L1. lia.
  - split; [exact WB|]. split; [unfold NB; lia|]. split; [exact LB|]. split; [lia|]. split; [intros; reflexivity| intros; lia].
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. apply Z.leb_gt in CND. eexists _, _, _. split; [reflexivity|]. split; [exact W'|]. split; [exact C'|]. split; [exact L'|].
    split; [lia|]. split. { intros i Hi. apply U'. lia. } apply X'. lia.
Qed.

Definition upm (e2 : Z) : Z := Z.max 0 ((e2 + 28) / 29).
Lemma upm_pos : forall e2, 0 < e2 -> 1 <= upm e2.
Proof. intros. unfold upm. assert (1 <= (e2 + 28) / 29) by (apply Z.div_le_lower_bound; lia). lia. Qed.
Lemma upm_step : forall e2, 0 < e2 -> upm (e2 - Z.min 29 e2) = upm e2 - 1.
Proof.
  intros e2 H. unfold upm. destruct (Z.le_gt_cases 29 e2).
  - rewrite Z.min_l by lia. replace (e2 - 29 + 28) with ((e2 + 28) + (-1) * 29) by lia. rewrite Z.div_add by lia.
    assert (1 <= (e2 + 28) / 29) by (apply Z.div_le_lower_bound; lia). lia.
  - rewrite Z.min_r by lia. replace (e2 - e2 + 28) with 28 by lia. change (28 / 29) with 0.
    assert ((e2 + 28) / 29 = 1). { symmetry. apply Z.div_unique with (r := e2 - 1); lia. } lia.
Qed.

(* [comment removed for export] *)
Definition UPI (z0 : Z) (s : list Z * Z * Z * Z) : Prop :=
  let '(big, a, z, e2) := s in
  W9 big /\ zlength big = 128 /\ 0 <= a < z /\ z <= z0 /\ a <= 122 /\ 122 - a + upm e2 <= 36 /\ 0 <= e2 <= 1024 /\
  znth big a <> 0 /\ zeros_below big a /\ zeros_from big z.

Lemma up_body_spec : forall z0 big a z e2, z0 <= 126 -> UPI z0 (big, a, z, e2) -> 0 < e2 ->
  exists s', fmt_fp_up_body (big, a, z, e2) = Some s' /\ UPI z0 s' /\
    (let '(_, _, _, e2') := s' in e2' = e2 - Z.min 29 e2).
Proof.
  intros z0 big a z e2 HZ0 (WB & LB & AZ & ZZ & AR & RA & E2 & NZ & ZB & ZF) C1.
  pose proof (upm_pos e2 C1) as UP1. pose proof (upm_step e2 C1) as UPS.
  unfold fmt_fp_up_body.
  destruct (up_inner_spec (Z.min 29 e2) a big z ltac:(lia) ltac:(lia) ltac:(lia) WB LB ltac:(lia)) as [b1 [d1 [c1 (E1 & W1 & C1r & L1 & D1 & U1 & [cin (Hcin & X1 & X2)])]]].
  rewrite E1.
  assert (P2 : 2 <= 2 ^ Z.min 29 e2). { change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. }
  pose proof (WB a) as Wa.
  set (ab := if negb (c1 =? 0) then (a - 1, zupd b1 (a - 1) c1) else (a, b1)).
  assert (AB : exists a2 b2, ab = (a2, b2) /\ W9 b2 /\ zlength b2 = 128 /\ a - 1 <= a2 <= a /\ 0 <= a2 /\ znth b2 a2 <> 0 /\
               zeros_below b2 a2 /\ zeros_from b2 z).
  { subst ab. destruct (Z.eqb_spec c1 0) as [C0|C0]; cbn [negb].
    - eexists _, _. split; [reflexivity|]. split; [exact W1|]. split; [exact L1|]. split; [lia|]. split; [lia|].
      split. { rewrite X2. rewrite C0 in X1. symmetry in X1.
        assert (znth big a * 2 ^ Z.min 29 e2 + cin < NB). { apply Z.div_small_iff in X1; unfold NB in *; lia. }
        rewrite Z.mod_small by lia. (* [comment removed for export] *) assert (0 < znth big a * 2 ^ Z.min 29 e2) by (apply Z.mul_pos_pos; lia). lia. }
      split. { intros k Hk. rewrite U1 by lia. apply ZB. lia. }
      intros k Hk. rewrite U1 by lia. apply ZF. lia.
    - assert (1 <= a). { destruct (Z.eq_dec a 0) as [A0|]; [|lia]. exfalso.
        (* [comment removed for export] *) lia. }
      eexists _, _. split; [reflexivity|]. split; [apply W9_zupd; [exact W1| lia]|]. split; [now rewrite zlength_zupd|]. split; [lia|]. split; [lia|].
      split. { rewrite znth_zupd_eq by (rewrite L1; lia). exact C0. }
      split. { intros k Hk. rewrite znth_zupd_neq by lia. rewrite U1 by lia. apply ZB. lia. }
      intros k Hk. rewrite znth_zupd_neq by lia. rewrite U1 by lia. apply ZF. lia. }
  destruct AB as [a2 [b2 (-> & W2 & L2 & A2 & A2p & N2 & ZB2 & ZF2)]].
  destruct (strip_spec b2 a2 z ltac:(lia) ltac:(lia) N2) as [z2 (Es & Z2 & Z2z & _)]. rewrite Es.
  eexists. split; [reflexivity|]. split.
  + unfold UPI. split; [exact W2|]. split; [exact L2|]. split; [lia|]. split; [lia|]. split; [lia|]. rewrite UPS. split; [lia|]. split; [lia|].
    split; [exact N2|]. split; [exact ZB2|].
    intros k Hk. destruct (Z.lt_ge_cases k z); [apply Z2z; lia| apply ZF2; lia].
  + reflexivity.
Qed.

Lemma up_spec : forall z0 s, z0 <= 126 -> UPI z0 s ->
  exists s', fmt_fp_up UP_FUEL s = Some s' /\ UPI z0 s' /\ (let '(_, _, _, e2) := s' in e2 = 0).
Proof.
  intros z0 s HZ0 HI. rewrite fmt_fp_up_eq.
  destruct (owloop_total (fun s : list Z * Z * Z * Z => let '(_, _, _, e2) := s in 0 <? e2) fmt_fp_up_body (UPI z0)
             (fun s => let '(_, _, _, e2) := s in upm e2)) with (fuel := UP_FUEL) (s := s) as [s' (E & HI' & C)].
  - intros [[[big a] z] e2] HI1 C1. apply Z.ltb_lt in C1.
    destruct (up_body_spec z0 big a z e2 HZ0 HI1 C1) as [s' (E & HI2 & He)].
    exists s'. split; [exact E|]. split; [exact HI2|]. destruct s' as [[[? ?] ?] e2']. rewrite He, upm_step by lia.
    destruct HI1 as (_ & _ & _ & _ & _ & RA & _). pose proof (upm_pos e2 C1). lia.
  - exact HI.
  - destruct s as [[[big a] z] e2]. destruct HI as (_ & _ & _ & _ & _ & RA & E2 & _). unfold upm in *. unfold UP_FUEL. change (Z.of_nat 40) with 40.
    assert ((e2 + 28) / 29 <= 37) by (apply Z.div_le_upper_bound; lia). lia.
  - exists s'. split; [exact E|]. split; [exact HI'|]. destruct s' as [[[? ?] ?] e2']. apply Z.ltb_ge in C.
    destruct HI' as (_ & _ & _ & _ & _ & _ & E2 & _). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dn_word_bound : forall sh w rm, 1 <= sh <= 9 -> 0 <= w < NB -> 0 <= rm < 2^sh ->
  0 <= Z.shiftr w sh + Z.shiftr NB sh * rm < NB.
Proof.
  intros sh w rm Hsh Hw Hrm. rewrite !Z.shiftr_div_pow2 by lia. unfold NB in *.
  assert (C : sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7 \/ sh = 8 \/ sh = 9) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]; cbn -[Z.add Z.mul Z.div Z.le Z.lt] in *; dnia.
Qed.

Lemma sh_ones : forall sh, 0 <= sh -> Z.shiftl 1 sh - 1 = Z.ones sh.
Proof. intros. unfold Z.ones. rewrite Z.shiftl_1_l. lia. Qed.

Section DnInner.
  Variables (sh a z : Z) (big : list Z).
  Let v := znth big a.
  Hypothesis Hsh : 1 <= sh <= 9.
  Hypothesis Haz : 0 <= a < z.
  Hypothesis Hz : z <= 128.
  Hypothesis WB : W9 big.
  Hypothesis HL : zlength big = 128.
  Hypothesis Hv : v <> 0.

  Definition DNK (s : list Z * Z * Z) : Prop :=
    let '(b, d, c) := s in
    W9 b /\ zlength b = 128 /\ (exists rm, 0 <= rm < 2^sh /\ c = Z.shiftr NB sh * rm) /\ a <= d /\
    (forall i, (i < a \/ d <= i) -> znth b i = znth big i) /\
    (d = a -> c = 0) /\
    (a < d -> znth b a = Z.shiftr v sh /\
              (Z.shiftr v sh = 0 -> (d = a + 1 -> 1 <= c) /\ (a + 1 < d -> 1 <= znth b (a + 1)))).

  Lemma dn_inner_spec :
    exists b c, fmt_fp_dn_inner sh BIG_FUEL z (big, a, 0) = Some (b, z, c) /\ DNK (b, z, c).
  Proof.
    assert (P2 : 2 <= 2 ^ sh <= 512). { split. { change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. } change 512 with (2^9). apply Z.pow_le_mono_r; lia. }
    assert (Q1 : 1 <= Z.shiftr NB sh). { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_le_lower_bound; unfold NB; lia. }
    rewrite fmt_fp_dn_inner_eq.
    destruct (wloop_total (fun s : list Z * Z * Z => let '(_, d, _) := s in d <? z) (fmt_fp_dn_inner_body sh)
               (fun s => DNK s /\ (let '(_, d, _) := s in d <= z))
               (fun s => let '(_, d, _) := s in z - d)) with (fuel := BIG_FUEL) (s := (big, a, 0)) as [[[b d] c] (E & [HI Dz] & C)].
    - intros [[b d] c] [(W1 & L1 & [rm0 [Hrm0 Hc]] & AD & U1 & D0 & D1) Dz] CC. apply Z.ltb_lt in CC.
      unfold fmt_fp_dn_inner_body.
      pose proof (W1 d) as Wd.
      rewrite sh_ones, Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (znth b d) (2^sh) ltac:(lia)) as RR.
      pose proof (dn_word_bound sh (znth b d) rm0 Hsh Wd Hrm0) as NB1. rewrite <- Hc in NB1.
      rewrite (u32_id (Z.shiftr (znth b d) sh + c)) by (unfold NB in *; lia).
      pose proof (dn_word_bound sh 0 (znth b d mod 2^sh) Hsh ltac:(unfold NB; lia) RR) as NB2.
      rewrite Z.shiftr_0_l, Z.add_0_l in NB2.
      change 1000000000 with NB. rewrite (u32_id _) by (unfold NB in *; lia).
      split; [| lia]. split; [| lia].
      unfold DNK. split; [apply W9_zupd; [exact W1| lia]|]. split; [now rewrite zlength_zupd|].
      split; [exists (znth b d mod 2^sh); split; [lia| reflexivity]|]. split; [lia|].
      split. { intros i Hi. rewrite znth_zupd_neq by lia. apply U1. lia. }
      split; [intros; lia|]. intros _.
      assert (SR : 0 <= Z.shiftr (znth b d) sh <= znth b d). { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|].
        (* [comment removed for export] *) pose proof (Z.pow_pos_nonneg 2 sh ltac:(lia) ltac:(lia)) as PP. assert (znth b d * 1 <= znth b d * 2 ^ sh) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
      destruct (Z.eq_dec d a) as [->|NE].
      + rewrite (D0 eq_refl). rewrite Z.add_0_r.
        split. { rewrite znth_zupd_eq by (rewrite L1; lia). subst v. rewrite (U1 a) by lia. reflexivity. }
        intros VS. split; [| intros; lia]. intros _.
        subst v. rewrite <- (U1 a) in VS, Hv by lia.
        rewrite Z.shiftr_div_pow2 in VS by lia. apply Z.div_small_iff in VS; [| lia].
        rewrite Z.mod_small by lia. nia.
      + destruct (D1 ltac:(lia)) as [BA BS]. split. { rewrite znth_zupd_neq by lia. exact BA. }
        intros VS. destruct (BS VS) as [B1 B2]. split; [intros; lia|]. intros LT.
        destruct (Z.eq_dec d (a + 1)) as [->|NE2].
        * rewrite znth_zupd_eq by (rewrite L1; lia). specialize (B1 eq_refl). lia.
        * rewrite znth_zupd_neq by lia. apply B2. lia.
    - split; [| lia]. unfold DNK. split; [exact WB|]. split; [exact HL|]. split; [exists 0; split; [lia|lia]|]. split; [lia|].
      split; [intros; reflexivity|]. split; [auto| intros; lia].
    - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
    - exists b, c. apply Z.ltb_ge in C. assert (d = z) by lia. subst d. split; [exact E| exact HI].
  Qed.
End DnInner.

Definition dnm (e2 : Z) : Z := Z.max 0 ((- e2 + 8) / 9).
Lemma dnm_pos : forall e2, e2 < 0 -> 1 <= dnm e2.
Proof. intros. unfold dnm. assert (1 <= (- e2 + 8) / 9) by (apply Z.div_le_lower_bound; lia). lia. Qed.
Lemma dnm_step : forall e2, e2 < 0 -> dnm (e2 + Z.min 9 (- e2)) = dnm e2 - 1.
Proof.
  intros e2 H. unfold dnm. destruct (Z.le_gt_cases 9 (- e2)).
  - rewrite Z.min_l by lia. replace (- (e2 + 9) + 8) with ((- e2 + 8) + (-1) * 9) by lia. rewrite Z.div_add by lia.
    assert (1 <= (- e2 + 8) / 9) by (apply Z.div_le_lower_bound; lia). lia.
  - rewrite Z.min_r by lia. replace (- (e2 + - e2) + 8) with 8 by lia. change (8 / 9) with 0.
    assert ((- e2 + 8) / 9 = 1). { symmetry. apply Z.div_unique with (r := - e2 - 1); lia. } lia.
Qed.

(* [comment removed for export] *)
Definition DNI (s : list Z * Z * Z * Z) : Prop :=
  let '(big, a, z, e2) := s in
  W9 big /\ zlength big = 128 /\ 0 <= a < z /\ znth big a <> 0 /\ zeros_below big a /\
  z + dnm e2 <= 127 /\ -1102 <= e2 <= 0 /\ znth big 0 < 2^29.

Lemma dn_body_spec : forall p t big a z e2, 0 <= p -> Z.lor t 32 <> CHR_f -> DNI (big, a, z, e2) -> e2 < 0 ->
  exists s', fmt_fp_dn_body p t 0 (big, a, z, e2) = Some s' /\ DNI s' /\
    (let '(_, _, _, e2') := s' in e2' = e2 + Z.min 9 (- e2)).
Proof.
  intros p t big a z e2 Hp Ht (WB & LB & AZ & NZ & ZB & ZM & E2 & B0) C1.
  pose proof (dnm_pos e2 C1) as DP. pose proof (dnm_step e2 C1) as DS.
  unfold fmt_fp_dn_body.
  set (sh := Z.min 9 (- e2)). assert (Hsh : 1 <= sh <= 9) by (subst sh; lia).
  change LDBL_MANT_DIG with 113. change (113 / 3) with 37.
  pose proof (u32_range (p + 37 + 8)) as UR.
  set (need := 1 + u32 (p + 37 + 8) / 9).
  assert (Hneed : 1 <= need) by (subst need; pose proof (Z.div_pos (u32 (p + 37 + 8)) 9); lia).
  destruct (dn_inner_spec sh a z big Hsh AZ ltac:(lia) WB LB NZ) as [b [c (E1 & (W1 & L1 & [rm [Hrm Hc]] & AD & U1 & D0 & D1))]].
  rewrite E1.
  destruct (D1 ltac:(lia)) as [BA BS].
  replace (Z.lor t 32 =? CHR_f) with false by (symmetry; apply Z.eqb_neq; exact Ht).
  assert (P2 : 2 <= 2 ^ sh). { change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. }
  assert (Hc2 : 0 <= c < NB). { pose proof (dn_word_bound sh 0 rm Hsh ltac:(unfold NB; lia) Hrm) as X. rewrite Z.shiftr_0_l in X. lia. }
  assert (B0' : znth b 0 < 2^29).
  { destruct (Z.eq_dec a 0) as [A0|A0].
    - rewrite A0 in BA. rewrite BA. rewrite Z.shiftr_div_pow2 by lia.
      pose proof (WB 0). apply Z.div_lt_upper_bound; [lia|]. (* [comment removed for export] *) assert (2 * 2 ^ 29 <= 2 ^ sh * 2 ^ 29) by (apply Z.mul_le_mono_nonneg_r; lia). unfold NB in *. lia.
    - rewrite U1 by lia. exact B0. }
  set (a' := if znth b a =? 0 then a + 1 else a).
  assert (A' : (znth b a <> 0 /\ a' = a) \/ (znth b a = 0 /\ a' = a + 1)).
  { subst a'. destruct (Z.eqb_spec (znth b a) 0); [right| left]; auto. }
  clearbody a'.
  assert (ZB' : zeros_below b a').
  { intros k Hk. destruct A' as [[N ->]|[Zr ->]].
    - rewrite U1 by lia. apply ZB. lia.
    - destruct (Z.eq_dec k a) as [->|]; [exact Zr|]. rewrite U1 by lia. apply ZB. lia. }
  set (bz := if negb (c =? 0) then (zupd b z c, z + 1) else (b, z)).
  assert (BZ : exists b1 z1, bz = (b1, z1) /\ W9 b1 /\ zlength b1 = 128 /\ z <= z1 <= z + 1 /\
               a' < z1 /\ znth b1 a' <> 0 /\ a <= a' <= a + 1 /\ zeros_below b1 a' /\ znth b1 0 < 2^29).
  { subst bz. destruct (Z.eqb_spec c 0) as [C0|C0]; cbn [negb].
    - eexists _, _. split; [reflexivity|]. split; [exact W1|]. split; [exact L1|]. split; [lia|].
      destruct A' as [[N ->]|[Zr ->]]. { split; [lia|]. split; [exact N|]. split; [lia|]. split; [exact ZB'| exact B0']. }
      rewrite BA in Zr. destruct (BS Zr) as [B1 B2].
      destruct (Z.eq_dec z (a + 1)) as [E|NE]. { exfalso. specialize (B1 E). lia. }
      split; [lia|]. split; [specialize (B2 ltac:(lia)); lia|]. split; [lia|]. split; [exact ZB'| exact B0'].
    - eexists _, _. split; [reflexivity|]. split; [apply W9_zupd; [exact W1| lia]|]. split; [rewrite zlength_zupd; exact L1|]. split; [lia|].
      destruct A' as [[N ->]|[Zr ->]].
      { split; [lia|]. split; [rewrite znth_zupd_neq by lia; exact N|]. split; [lia|].
        split; [intros k Hk; rewrite znth_zupd_neq by lia; apply ZB'; lia|]. rewrite znth_zupd_neq by lia. exact B0'. }
      rewrite BA in Zr. destruct (BS Zr) as [B1 B2].
      split; [lia|]. split.
      { destruct (Z.eq_dec z (a + 1)) as [->|NE].
        - rewrite znth_zupd_eq by (rewrite L1; lia). exact C0.
        - rewrite znth_zupd_neq by lia. specialize (B2 ltac:(lia)). lia. }
      split; [lia|]. split; [intros k Hk; rewrite znth_zupd_neq by lia; apply ZB'; lia|]. rewrite znth_zupd_neq by lia. exact B0'. }
  destruct BZ as [b1 [z1 (-> & W2 & L2 & Z1 & AZ1 & N1 & AA & ZB1 & B01)]].
  eexists. split; [reflexivity|]. split; [| reflexivity].
  unfold DNI. split; [exact W2|]. split; [exact L2|]. split.
  { destruct (need <? z1 - a'); lia. }
  split; [exact N1|]. split; [exact ZB1|]. split.
  { replace (e2 + sh) with (e2 + Z.min 9 (- e2)) by reflexivity. rewrite DS. destruct (need <? z1 - a') eqn:CN; [apply Z.ltb_lt in CN|]; lia. }
  split; [lia| exact B01].
Qed.

(* [comment removed for export] *)
Fixpoint dn_iter (n : nat) (p t r : Z) (s : list Z * Z * Z * Z) {struct n} : option (list Z * Z * Z * Z) :=
  match n with
  | O => Some s
  | S n' => let '(big, a, z, e2) := s in
            if e2 <? 0 then match fmt_fp_dn_body p t r s with Some s' => dn_iter n' p t r s' | None => None end
            else None
  end.

Lemma dn_iter_DNI : forall p t n s s', 0 <= p -> Z.lor t 32 <> CHR_f -> DNI s -> dn_iter n p t 0 s = Some s' -> DNI s'.
Proof.
  intros p t n. induction n as [|n IH]; intros s s' Hp Ht HI E.
  - cbn in E. inversion E. subst. exact HI.
  - cbn [dn_iter] in E. destruct s as [[[big a] z] e2]. destruct (Z.ltb_spec e2 0); [|discriminate E].
    destruct (dn_body_spec p t big a z e2 Hp Ht HI ltac:(lia)) as [s1 (E1 & HI1 & _)]. rewrite E1 in E.
    eapply IH; eauto.
Qed.

Lemma dn_spec : forall p t s, 0 <= p -> Z.lor t 32 <> CHR_f -> DNI s ->
  exists s', fmt_fp_dn DN_FUEL p t 0 s = Some s' /\ DNI s' /\ (let '(_, _, _, e2) := s' in e2 = 0).
Proof.
  intros p t s Hp Ht HI. rewrite fmt_fp_dn_eq.
  destruct (owloop_total (fun s : list Z * Z * Z * Z => let '(_, _, _, e2) := s in e2 <? 0) (fmt_fp_dn_body p t 0) DNI
             (fun s => let '(_, _, _, e2) := s in dnm e2)) with (fuel := DN_FUEL) (s := s) as [s' (E & HI' & C)].
  - intros [[[big a] z] e2] HI1 C1. apply Z.ltb_lt in C1.
    destruct (dn_body_spec p t big a z e2 Hp Ht HI1 C1) as [s1 (E1 & HI2 & He)].
    exists s1. split; [exact E1|]. split; [exact HI2|]. destruct s1 as [[[? ?] ?] e2']. rewrite He, dnm_step by lia.
    pose proof (dnm_pos e2 C1). unfold dnm in *. lia.
  - exact HI.
  - destruct s as [[[big a] z] e2]. destruct HI as (_ & _ & AZ & _ & _ & ZM & E2 & _). unfold dnm in *. unfold DN_FUEL. change (Z.of_nat 130) with 130.
    assert ((- e2 + 8) / 9 <= 124) by (apply Z.div_le_upper_bound; lia). lia.
  - exists s'. split; [exact E|]. split; [exact HI'|]. destruct s' as [[[? ?] ?] e2']. apply Z.ltb_ge in C.
    destruct HI' as (_ & _ & _ & _ & _ & _ & E2 & _). lia.
Qed.

Lemma upd_nat_same : forall l i, upd_nat l i (nth i l 0) = l.
Proof. induction l as [|h l IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma zupd_same : forall l i, zupd l i (znth l i) = l.
Proof.
  intros l i. unfold zupd, znth. destruct (Z.ltb_spec i 0); [reflexivity|]. apply upd_nat_same.
Qed.

(* [comment removed for export] *)
Definition POST (r0 : Z) (big : list Z) (a z : Z) : Prop :=
  W9 big /\ zlength big = 128 /\ 0 <= a < z /\ z <= 127 /\ znth big a <> 0 /\ zeros_below big a /\
  ((r0 = 0 /\ znth big 0 < 2^29) \/ (r0 = 122 /\ 86 <= a <= 122 /\ zeros_from big z)).


Theorem fmt_loops : forall d p t, dfin d -> 0 <= p -> Z.lor t 32 <> CHR_f ->
  let y1 := strip_sign (f128_of_d d) in
  exists (nz : bool) fr e0 y2,
    1 < fpclassifyl y1 /\ frexpl FREXPL_FUEL y1 0 = Some (fr, e0) /\ f128_mul fr (f128_of_i32 2) = y2 /\
    negb (f128_le y2 F128_ZERO =? 0) = nz /\
    let e1 := if nz then e0 - 1 else e0 in
    let y := if nz then f128_mul y2 (f128_of_d D_0x1p28) else y2 in
    let e2 := if nz then e1 - 28 else e1 in
    let r0 := if e2 <? 0 then 0 else 122 in
    -1102 <= e2 <= 995 /\
    exists big z, fmt_fp_dig DIG_FUEL (zrepeat 0 128, r0, y) = Some (big, z, f128_pack 0 0 0) /\ r0 + 1 <= z <= r0 + 4 /\
      W9 big /\ zlength big = 128 /\ (forall i, ~ (r0 <= i < z) -> znth big i = 0) /\
      (nz = true -> 2^28 <= znth big r0 < 2^29) /\
      (nz = false -> e2 = 0 /\ z = 123 /\ big = zrepeat 0 128) /\
      exists s1, fmt_fp_up UP_FUEL (big, r0, z, e2) = Some s1 /\
        (e2 <= 0 -> s1 = (big, r0, z, e2)) /\ (nz = true -> e2 < 0 -> DNI s1) /\
        (0 <= e2 -> exists b1 a1 z1, s1 = (b1, a1, z1, 0)) /\
        exists big2 a2 z2, fmt_fp_dn DN_FUEL p t r0 s1 = Some (big2, a2, z2, 0) /\
          (nz = true -> POST r0 big2 a2 z2) /\ (nz = false -> big2 = zrepeat 0 128 /\ a2 = 122 /\ z2 = 123).
Proof.
  intros d p t Hfin Hp Ht.
  destruct (prologue_ok_finite d Hfin) as [nz [fr [e0 [N0 (C1 & C2 & C3 & C4 & C5 & DIG)]]]].
  cbv zeta in C3, C4, C5. cbv zeta.
  exists nz, fr, e0, (f128_mul fr (f128_of_i32 2)).
  split; [exact C1|]. split; [exact C2|]. split; [reflexivity|]. split; [exact C3|].
  destruct nz.
  - (* [comment removed for export] *)
    destruct (C5 eq_refl) as (He0 & HN0 & EY). rewrite EY.
    set (e2 := e0 - 1 - 28).
    assert (He2 : -1102 <= e2 <= 995) by (subst e2; lia).
    split; [exact He2|].
    set (r0 := if e2 <? 0 then 0 else 122).
    assert (Hr0 : (e2 < 0 /\ r0 = 0) \/ (0 <= e2 /\ r0 = 122)). { subst r0. destruct (Z.ltb_spec e2 0); lia. }
    destruct (DIG DIG_FUEL r0 (zrepeat 0 128)) as [big [z (E & HL & Hz & _ & W0 & Ws & Oth)]].
    { unfold DIG_FUEL. lia. } { lia. } { rewrite zlength_zrepeat; lia. }
    rewrite E. exists big, z. split; [reflexivity|]. split; [exact Hz|].
    assert (WB : W9 big). { intros i. destruct (Z.lt_ge_cases i r0); [|destruct (Z.lt_ge_cases i z)].
      - rewrite Oth by lia. rewrite znth_zrepeat. unfold NB. destruct (_ && _); lia.
      - unfold NB. apply Ws. lia.
      - rewrite Oth by lia. rewrite znth_zrepeat. unfold NB. destruct (_ && _); lia. }
    assert (LB : zlength big = 128). { unfold zlength. rewrite HL. pose proof (zlength_zrepeat 0 128). unfold zlength in H. lia. }
    assert (ZO : forall i, ~ (r0 <= i < z) -> znth big i = 0). { intros i Hi. rewrite Oth by lia. rewrite znth_zrepeat. destruct (_ && _); reflexivity. }
    destruct (W0 eq_refl) as [W0a W0b].
    split; [exact WB|]. split; [exact LB|]. split; [exact ZO|]. split; [intros _; exact W0b|]. split; [intros X; discriminate X|].
    destruct Hr0 as [[Hneg ->]|[Hnn ->]].
    + (* [comment removed for export] *)
      exists (big, 0, z, e2). rewrite fmt_fp_up_eq. unfold UP_FUEL. cbn [owloop].
      replace (0 <? e2) with false by (symmetry; apply Z.ltb_ge; lia).
      split; [reflexivity|]. split; [intros _; reflexivity|].
      assert (HD : DNI (big, 0, z, e2)).
      { unfold DNI. split; [exact WB|]. split; [exact LB|]. split; [lia|]. split; [lia|].
        split; [intros k Hk; apply ZO; lia|]. split; [| lia].
        unfold dnm. assert ((- e2 + 8) / 9 <= 123) by dlia. lia. }
      split; [intros _ _; exact HD|]. split; [intros X; lia|].
      destruct (dn_spec p t (big, 0, z, e2) Hp Ht HD) as [[[[big2 a2] z2] e2'] (E2 & HI2 & He2')]. subst e2'.
      rewrite E2. exists big2, a2, z2. split; [reflexivity|]. split; [| intros X; discriminate X]. intros _.
      destruct HI2 as (W2 & L2 & AZ2 & NZ2 & ZB2 & ZM2 & _ & B02). unfold POST.
      split; [exact W2|]. split; [exact L2|]. split; [exact AZ2|]. split; [unfold dnm in ZM2; change ((- 0 + 8) / 9) with 0 in ZM2; lia|].
      split; [exact NZ2|]. split; [exact ZB2|]. left. split; [reflexivity| exact B02].
    + (* [comment removed for export] *)
      assert (HU : UPI z (big, 122, z, e2)).
      { unfold UPI. split; [exact WB|]. split; [exact LB|]. split; [lia|]. split; [lia|]. split; [lia|].
        split. { unfold upm. assert ((e2 + 28) / 29 <= 35) by dlia. lia. }
        split; [lia|]. split; [lia|]. split; [intros k Hk; apply ZO; lia| intros k Hk; apply ZO; lia]. }
      destruct (up_spec z (big, 122, z, e2) ltac:(lia) HU) as [[[[big1 a1] z1] e21] (E1 & HI1 & He21)]. subst e21.
      rewrite E1. exists (big1, a1, z1, 0). split; [reflexivity|]. split.
      { intros Hle. assert (e2 = 0) by lia. rewrite fmt_fp_up_eq in E1. unfold UP_FUEL in E1. cbn [owloop] in E1.
        replace (0 <? e2) with false in E1 by (symmetry; apply Z.ltb_ge; lia). inversion E1; subst. reflexivity. }
      split; [intros _ X; lia|]. split; [intros _; eexists _, _, _; reflexivity|].
      rewrite fmt_fp_dn_eq. unfold DN_FUEL. cbn [owloop]. change (0 <? 0) with false. cbv iota.
      exists big1, a1, z1. split; [reflexivity|]. split; [| intros X; discriminate X]. intros _.
      destruct HI1 as (W1 & L1 & AZ1 & ZZ1 & AR1 & RA1 & _ & NZ1 & ZB1 & ZF1). unfold POST.
      split; [exact W1|]. split; [exact L1|]. split; [exact AZ1|]. split; [lia|]. split; [exact NZ1|]. split; [exact ZB1|].
      right. split; [reflexivity|]. split; [unfold upm in RA1; change ((0 + 28) / 29) with 0 in RA1; lia| exact ZF1].
  - (* [comment removed for export] *)
    destruct (C4 eq_refl) as [-> EY2]. rewrite EY2.
    change (0 <? 0) with false. cbv iota. change (0 - 28 <? 0) with true. cbv iota.
    split; [lia|].
    rewrite (dig_zero DIG_FUEL (zrepeat 0 128) 122) by (try rewrite zlength_zrepeat; unfold DIG_FUEL; lia).
    replace (zupd (zrepeat 0 128) 122 0) with (zrepeat 0 128).
    2:{ symmetry. etransitivity; [| apply (zupd_same (zrepeat 0 128) 122)]. rewrite znth_zrepeat. reflexivity. }
    exists (zrepeat 0 128), 123. split; [reflexivity|]. split; [lia|]. split; [apply W9_zrepeat|]. split; [apply zlength_zrepeat; lia|].
    split; [intros i _; rewrite znth_zrepeat; destruct (_ && _); reflexivity|]. split; [intros X; discriminate X|]. split; [intros _; repeat split; reflexivity|].
    exists (zrepeat 0 128, 122, 123, 0). rewrite fmt_fp_up_eq. unfold UP_FUEL. cbn [owloop]. change (0 <? 0) with false. cbv iota.
    split; [reflexivity|]. split; [intros _; reflexivity|]. split; [intros X; discriminate X|].
    split; [intros _; eexists _, _, _; reflexivity|].
    rewrite fmt_fp_dn_eq. unfold DN_FUEL. cbn [owloop]. change (0 <? 0) with false. cbv iota.
    exists (zrepeat 0 128), 122, 123. split; [reflexivity|]. split; [intros X; discriminate X|]. intros _. repeat split; reflexivity.
Qed.
End FmtFpRun.

(* [comment removed for export] *)
Module FmtFpTail.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps FmtFpProps FmtFpRun.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_of_u32 f128_of_i32.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.
Local Ltac dnia := Z.div_mod_to_equations; nia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition isdig (c : Z) : Prop := 48 <= c <= 57.
(* [comment removed for export] *)
Definition gch (c : Z) : Prop := (48 <= c <= 57) \/ c = 43 \/ c = 45 \/ c = 46 \/ c = 69 \/ c = 101.
Lemma gch_dig : forall c, isdig c -> gch c. Proof. intros c H. left. exact H. Qed.

Lemma zsub_length : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l -> length (zsub l i n) = Z.to_nat n.
Proof.
  intros l i n Hi Hn H. unfold zsub. rewrite length_firstn, length_skipn. unfold zlength in H. lia.
Qed.

Lemma zsub_Forall : forall (P : Z -> Prop) l i n, 0 <= i -> 0 <= n -> i + n <= zlength l ->
  (forall k, i <= k < i + n -> P (znth l k)) -> Forall P (zsub l i n).
Proof.
  intros P l i n Hi Hn H HP. apply Forall_nth. intros j d Hj.
  rewrite (nth_indep _ d 0) by exact Hj.
  rewrite zsub_length in Hj by lia.
  unfold zsub. rewrite nth_firstn. replace (j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. specialize (HP (i + Z.of_nat j) ltac:(lia)). unfold znth in HP.
  destruct (Z.ltb_spec (i + Z.of_nat j) 0); [lia|]. replace (Z.to_nat i + j)%nat with (Z.to_nat (i + Z.of_nat j)) by lia. exact HP.
Qed.

Lemma zlength_app : forall (l1 l2 : list Z), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_zsub : forall l i n, 0 <= i -> 0 <= n -> i + n <= zlength l -> zlength (zsub l i n) = n.
Proof. intros. unfold zlength. rewrite zsub_length by lia. lia. Qed.

(* [comment removed for export] *)
Definition DIGk (x k : Z) : Prop := (x = 0 /\ k = 0) \/ (1 <= k /\ 10^(k-1) <= x < 10^k).

Lemma DIGk_exists : forall x n, 0 <= x < 10^n -> 0 <= n -> exists k, DIGk x k /\ 0 <= k <= n.
Proof.
  intros x n Hx Hn. destruct (Z.eq_dec x 0) as [->|NZ]. { exists 0. split; [left; lia| lia]. }
  revert x Hx NZ. pattern n. apply (Wf_Z.natlike_ind); [| | lia].
  - intros x Hx NZ. change (10^0) with 1 in Hx. lia.
  - intros m Hm IH x Hx NZ. destruct (Z.lt_ge_cases x (10^m)).
    + destruct (IH x ltac:(lia) NZ) as [k [Hk Hkn]]. exists k. split; [exact Hk| lia].
    + exists (Z.succ m). split; [| lia]. right. split; [lia|]. replace (Z.succ m - 1) with m by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pow10_pos : forall k, 0 <= k -> 0 < 10^k. Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma fmt_u_loop_spec : forall k fuel y s b, DIGk y k -> 0 <= y -> (Z.to_nat k < fuel)%nat -> k <= s <= zlength b ->
  exists b', fmt_u_loop fuel (y, s, b) = Some (0, s - k, b') /\ zlength b' = zlength b /\
    (forall i, s - k <= i < s -> isdig (znth b' i)) /\ (forall i, ~ (s - k <= i < s) -> znth b' i = znth b i).
Proof.
  intros k. destruct (Z.lt_ge_cases k 0) as [Hneg|Hk0].
  { intros fuel y s b [[_ K]|[K _]]; lia. }
  generalize Hk0. pattern k. apply Wf_Z.natlike_ind; [ | | exact Hk0].
  - intros _ fuel y s b D Hy Hf Hs. destruct D as [[-> _]|[? _]]; [|lia].
    destruct fuel as [|fuel]; [lia|]. cbn [fmt_u_loop Z.eqb negb]. exists b. rewrite Z.sub_0_r.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; lia| intros; reflexivity].
  - intros m Hm IH _ fuel y s b D Hy Hf Hs. destruct D as [[-> K]|[K R]]; [lia|].
    pose proof (pow10_pos m Hm) as P0.
    assert (E1 : 10 ^ Z.succ m = 10 * 10 ^ m) by (rewrite Z.pow_succ_r; lia).
    destruct fuel as [|fuel]; [lia|]. cbn [fmt_u_loop].
    replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. unfold fmt_u_loop_body.
    destruct (IH ltac:(lia) fuel (y / 10) (s - 1) (zupd b (s - 1) (CHR_0 + y mod 10))) as [b' (E & L & D1 & D2)].
    + destruct (Z.eq_dec m 0) as [->|M0].
      * left. split; [|reflexivity]. change (10^0) with 1 in R. change (10 ^ Z.succ 0) with 10 in R. dlia.
      * right. split; [lia|].
        assert (E2 : 10 ^ m = 10 * 10 ^ (m - 1)) by (replace m with (Z.succ (m - 1)) at 1 by lia; rewrite Z.pow_succ_r; lia).
        replace (Z.succ m - 1) with m in R by lia. pose proof (pow10_pos (m - 1) ltac:(lia)). dlia.
    + dlia.
    + lia.
    + rewrite zlength_zupd. lia.
    + rewrite E. exists b'. replace (s - 1 - m) with (s - Z.succ m) by lia.
      split; [reflexivity|]. split; [rewrite L; apply zlength_zupd|]. split.
      * intros i Hi. destruct (Z.eq_dec i (s - 1)) as [->|NE].
        -- rewrite D2 by lia. rewrite znth_zupd_eq by lia. unfold isdig, CHR_0. pose proof (Z.mod_pos_bound y 10 ltac:(lia)). lia.
        -- apply D1. lia.
      * intros i Hi. rewrite D2 by lia. apply znth_zupd_neq. lia.
Qed.

Lemma fmt_u_spec : forall x b s k, 0 <= x -> DIGk x k -> k <= 20 -> k <= s <= zlength b ->
  exists b', fmt_u x b s = Some (s - k, b') /\ zlength b' = zlength b /\
    (forall i, s - k <= i < s -> isdig (znth b' i)) /\ (forall i, ~ (s - k <= i < s) -> znth b' i = znth b i).
Proof.
  intros x b s k Hx D Hk Hs. unfold fmt_u.
  destruct (fmt_u_loop_spec k FMT_U_FUEL x s b D Hx ltac:(unfold FMT_U_FUEL; lia) Hs) as [b' (E & L & D1 & D2)].
  rewrite E. exists b'. auto.
Qed.

Lemma zfill_spec : forall s buf, 0 <= s <= 11 -> s <= zlength buf ->
  exists buf', fmt_fp_zfill ZFILL_FUEL (s, buf) = Some (0, buf') /\ zlength buf' = zlength buf /\
    (forall i, 0 <= i < s -> znth buf' i = CHR_0) /\ (forall i, ~ (0 <= i < s) -> znth buf' i = znth buf i).
Proof.
  intros s buf Hs Hl. rewrite fmt_fp_zfill_eq.
  destruct (wloop_total (fun st : Z * list Z => 0 <? fst st) fmt_fp_zfill_body
             (fun st => 0 <= fst st <= s /\ zlength (snd st) = zlength buf /\
                        (forall i, fst st <= i < s -> znth (snd st) i = CHR_0) /\
                        (forall i, ~ (fst st <= i < s) -> znth (snd st) i = znth buf i))
             (fun st => fst st))
    with (fuel := ZFILL_FUEL) (s := (s, buf)) as [[s' b'] (E & (R & L & F1 & F2) & C)].
  - intros [s1 b1] (R1 & L1 & G1 & G2) C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. unfold fmt_fp_zfill_body. cbn [fst snd].
    split; [| lia]. split; [lia|]. split; [now rewrite zlength_zupd|]. split.
    + intros i Hi. destruct (Z.eq_dec i (s1 - 1)) as [->|]; [apply znth_zupd_eq; lia|]. rewrite znth_zupd_neq by lia. apply G1. lia.
    + intros i Hi. rewrite znth_zupd_neq by lia. apply G2. lia.
  - cbn [fst snd]. split; [lia|]. split; [reflexivity|]. split; [intros; lia| intros; reflexivity].
  - cbn [fst]. unfold ZFILL_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. cbn [fst snd] in *. apply Z.ltb_ge in C. assert (s' = 0) by lia. subst s'.
    exists b'. split; [reflexivity|]. split; [exact L|]. split; [intros i Hi; apply F1; lia| intros i Hi; apply F2; lia].
Qed.

Lemma epad_spec : forall estr eb, 8 <= estr <= 12 -> zlength eb = 12 ->
  exists eb', fmt_fp_epad EPAD_FUEL (estr, eb) = Some (Z.min estr 10, eb') /\ zlength eb' = 12 /\
    (forall i, Z.min estr 10 <= i < estr -> znth eb' i = CHR_0) /\ (forall i, ~ (Z.min estr 10 <= i < estr) -> znth eb' i = znth eb i).
Proof.
  intros estr eb He Hl. rewrite fmt_fp_epad_eq.
  destruct (wloop_total (fun st : Z * list Z => 12 - fst st <? 2) fmt_fp_epad_body
             (fun st => Z.min estr 10 <= fst st <= estr /\ zlength (snd st) = 12 /\
                        (forall i, fst st <= i < estr -> znth (snd st) i = CHR_0) /\
                        (forall i, ~ (fst st <= i < estr) -> znth (snd st) i = znth eb i))
             (fun st => fst st - Z.min estr 10))
    with (fuel := EPAD_FUEL) (s := (estr, eb)) as [[e' b'] (E & (R & L & F1 & F2) & C)].
  - intros [e1 b1] (R1 & L1 & G1 & G2) C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. unfold fmt_fp_epad_body. cbn [fst snd].
    split; [| lia]. split; [lia|]. split; [now rewrite zlength_zupd|]. split.
    + intros i Hi. destruct (Z.eq_dec i (e1 - 1)) as [->|]; [apply znth_zupd_eq; lia|]. rewrite znth_zupd_neq by lia. apply G1. lia.
    + intros i Hi. rewrite znth_zupd_neq by lia. apply G2. lia.
  - cbn [fst snd]. split; [lia|]. split; [exact Hl|]. split; [intros; lia| intros; reflexivity].
  - cbn [fst]. unfold EPAD_FUEL. change (Z.of_nat 4) with 4. lia.
  - rewrite E. cbn [fst snd] in *. apply Z.ltb_ge in C. assert (e' = Z.min estr 10) by lia. subst e'.
    exists b'. split; [reflexivity|]. split; [exact L|]. split; [exact F1| exact F2].
Qed.

Lemma cnt_spec : forall v e0, 0 <= v < NB ->
  exists k, fmt_fp_cnt TEN_FUEL v (10, e0) = Some (10^k, e0 + k - 1) /\ 1 <= k <= 9 /\ v < 10^k /\ (v <> 0 -> 10^(k-1) <= v).
Proof.
  intros v e0 Hv. rewrite fmt_fp_cnt_eq.
  destruct (wloop_total (fun s : Z * Z => fst s <=? v) fmt_fp_cnt_body
             (fun s => exists k, 1 <= k <= 10 /\ fst s = 10 ^ k /\ snd s = e0 + k - 1 /\ (k = 1 \/ 10^(k-1) <= v))
             (fun s => 11 - (snd s - e0))) with (fuel := TEN_FUEL) (s := (10, e0)) as [[i e] (E & [k (Hk & Hi & He & Hlow)] & C)].
  - intros [i e] [k (Hk & Hi & He & Hlow)] C1. cbn [fst snd] in *. subst i. apply Z.leb_le in C1.
    assert (k <= 9). { destruct (Z.le_gt_cases k 9); [assumption|]. exfalso.
      assert (10 ^ 10 <= 10 ^ k) by (apply Z.pow_le_mono_r; lia). change (10^10) with 10000000000 in *. unfold NB in Hv. lia. }
    unfold fmt_fp_cnt_body. cbn [fst snd]. split; [| lia]. exists (k + 1). split; [lia|]. split; [rewrite pow10_succ by lia; lia|].
    split; [lia|]. right. replace (k + 1 - 1) with k by lia. exact C1.
  - exists 1. cbn. repeat split; lia.
  - cbn [snd]. unfold TEN_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. cbn [fst snd] in *. apply Z.leb_gt in C. subst i e. exists k. split; [reflexivity|].
    assert (k <= 9). { destruct (Z.le_gt_cases k 9); [assumption|]. exfalso. destruct Hlow as [->|Hlow]; [lia|].
      assert (10 ^ 9 <= 10 ^ (k-1)) by (apply Z.pow_le_mono_r; lia). change (10^9) with 1000000000 in *. unfold NB in Hv. lia. }
    split; [lia|]. split; [exact C|]. intros NZ. destruct Hlow as [->|Hlow]; [change (10^(1-1)) with 1; lia| exact Hlow].
Qed.

Lemma powi_spec : forall j2, 0 <= j2 <= 8 -> fmt_fp_powi TEN_FUEL (10, j2 + 1) = Some (10^(9 - j2), 9).
Proof.
  intros j2 Hj. rewrite fmt_fp_powi_eq.
  destruct (wloop_total (fun s : Z * Z => snd s <? 9) fmt_fp_powi_body
             (fun s => fst s = 10 ^ (snd s - j2) /\ j2 + 1 <= snd s <= 9)
             (fun s => 9 - snd s)) with (fuel := TEN_FUEL) (s := (10, j2 + 1)) as [[i j] (E & [Hi Hj'] & C)].
  - intros [i j] [Hi Hj2] C1. cbn [fst snd] in *. apply Z.ltb_lt in C1. subst i.
    unfold fmt_fp_powi_body. cbn [fst snd]. split; [|lia]. split; [|lia].
    replace (j + 1 - j2) with ((j - j2) + 1) by lia. rewrite pow10_succ by lia. lia.
  - cbn [fst snd]. split; [|lia]. replace (j2 + 1 - j2) with 1 by lia. reflexivity.
  - cbn [snd]. unfold TEN_FUEL. change (Z.of_nat 12) with 12. lia.
  - rewrite E. cbn [fst snd] in *. apply Z.ltb_ge in C. assert (j = 9) by lia. subst j i. reflexivity.
Qed.

Lemma carry_spec : forall big d a,
  zlength big = 128 -> 0 <= a <= d -> d < 128 ->
  (forall i, i <> d -> 0 <= znth big i < NB) -> 1 <= znth big d <= NB ->
  (a = 0 -> a < d /\ znth big 0 < NB - 1) ->
  exists big' d' a', fmt_fp_carry BIG_FUEL (big, d, a) = Some (big', d', a') /\
    zlength big' = 128 /\ W9 big' /\ 0 <= a' /\ (a' = a \/ (a' = a - 1 /\ d' = a' /\ znth big' a' = 1)) /\ a' <= d' <= d /\
    1 <= znth big' d' /\
    (forall i, i < a' -> znth big' i = znth big i) /\
    (forall i, a' <= i < d' -> znth big' i = znth big i) /\
    (forall i, d' < i <= d -> znth big' i = 0) /\
    (forall i, d < i -> znth big' i = znth big i) /\
    (d' = d -> big' = big).
Proof.
  intros big d a HL Had Hd128 Hoth Hd Ha0.
  rewrite fmt_fp_carry_eq.
  destruct (wloop_total (fun s : list Z * Z * Z => let '(b0, d0, _) := s in 999999999 <? znth b0 d0) fmt_fp_carry_body
    (fun s => let '(b, d1, a1) := s in
       zlength b = 128 /\
       ((a1 = a /\ a <= d1 <= d /\ 0 <= znth b d1 <= NB /\ (d1 < d -> znth b d1 = znth big d1 + 1) /\ (d1 = d -> b = big)) \/
        (a1 = a - 1 /\ 1 <= a /\ d1 = a1 /\ znth b d1 = 1)) /\
       (forall i, i <> d1 -> 0 <= znth b i < NB) /\
       (forall i, i < a1 -> znth b i = znth big i) /\
       (forall i, a1 <= i < d1 -> znth b i = znth big i) /\
       (forall i, d1 < i <= d -> znth b i = 0) /\
       (forall i, d < i -> znth b i = znth big i))
    (fun s => let '(b, d1, a1) := s in d1 - a + 2))
    with (fuel := BIG_FUEL) (s := (big, d, a)) as [[[b' d'] a'] (E & (L' & M' & O' & B' & U' & Z' & T') & C)].
  - intros [[b d1] a1] (L1 & M1 & O1 & B1 & U1 & Z1 & T1) C1. apply Z.ltb_lt in C1.
    destruct M1 as [(-> & R1 & V1 & PL & _)|(-> & A1 & -> & V1)]; [| rewrite V1 in C1; lia].
    unfold fmt_fp_carry_body.
    assert (VD : znth b d1 = NB) by (unfold NB in *; lia).
    assert (D1p : 1 <= d1).
    { destruct (Z.eq_dec d1 0) as [D0|]; [|lia]. exfalso. assert (a = 0) by lia.
      destruct (Ha0 ltac:(lia)) as [AD B0]. rewrite D0 in *. specialize (PL ltac:(lia)). unfold NB in *. lia. }
    destruct (Z.ltb_spec (d1 - 1) a) as [LT|GE].
    + (* [comment removed for export] *)
      assert (d1 = a) by lia. subst d1.
      split; [| lia]. split; [now rewrite !zlength_zupd|].
      assert (Vn : znth (zupd (zupd b a 0) (a - 1) 0) (a - 1) = 0) by (apply znth_zupd_eq; rewrite zlength_zupd; lia).
      rewrite Vn. change (u32 (0 + 1)) with 1.
      split. { right. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. apply znth_zupd_eq. rewrite !zlength_zupd. lia. }
      split. { intros i Hi. destruct (Z.eq_dec i a) as [->|].
               - rewrite znth_zupd_neq, znth_zupd_neq, znth_zupd_eq by lia. unfold NB; lia.
               - rewrite !znth_zupd_neq by lia. apply O1. lia. }
      split. { intros i Hi. rewrite !znth_zupd_neq by lia. apply B1. lia. }
      split. { intros i Hi. lia. }
      split. { intros i Hi. destruct (Z.eq_dec i a) as [->|].
               - rewrite znth_zupd_neq, znth_zupd_neq, znth_zupd_eq by lia. reflexivity.
               - rewrite !znth_zupd_neq by lia. apply Z1. lia. }
      intros i Hi. rewrite !znth_zupd_neq by lia. apply T1. lia.
    + (* [comment removed for export] *)
      split; [| lia]. split; [now rewrite !zlength_zupd|].
      assert (Wp : 0 <= znth b (d1 - 1) < NB) by (apply O1; lia).
      rewrite (znth_zupd_neq b d1 (d1 - 1)) by lia.
      rewrite u32_id by (unfold NB in *; lia).
      split. { left. split; [reflexivity|]. split; [lia|].
               rewrite znth_zupd_eq by (rewrite zlength_zupd; lia).
               split; [lia|]. split; [| intros; lia]. intros _. rewrite U1 by lia. reflexivity. }
      split. { intros i Hi. destruct (Z.eq_dec i d1) as [->|].
               - rewrite znth_zupd_neq, znth_zupd_eq by lia. unfold NB; lia.
               - rewrite !znth_zupd_neq by lia. apply O1. lia. }
      split. { intros i Hi. rewrite !znth_zupd_neq by lia. apply B1. lia. }
      split. { intros i Hi. rewrite !znth_zupd_neq by lia. apply U1. lia. }
      split. { intros i Hi. destruct (Z.eq_dec i d1) as [->|].
               - rewrite znth_zupd_neq, znth_zupd_eq by lia. reflexivity.
               - rewrite !znth_zupd_neq by lia. apply Z1. lia. }
      intros i Hi. rewrite !znth_zupd_neq by lia. apply T1. lia.
  - split; [exact HL|]. split. { left. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [intros; lia| intros; reflexivity]. }
    split; [exact Hoth|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; lia| intros; reflexivity].
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. apply Z.ltb_ge in C. exists b', d', a'. split; [reflexivity|]. split; [exact L'|].
    assert (Vd : 0 <= znth b' d' < NB) by (destruct M' as [(_ & _ & V & _)|(_ & _ & _ & V)]; unfold NB in *; lia).
    split. { intros i. destruct (Z.eq_dec i d') as [->|]; [exact Vd| apply O'; lia]. }
    destruct M' as [(-> & R1 & V1 & PL & EQ)|(-> & A1 & -> & V1)].
    + split; [lia|]. split; [left; reflexivity|]. split; [lia|].
      split. { destruct (Z.eq_dec d' d) as [->|]. - rewrite (EQ eq_refl). lia. - rewrite PL by lia. pose proof (Hoth d' ltac:(lia)). lia. }
      split; [exact B'|]. split; [exact U'|]. split; [exact Z'|]. split; [exact T'| exact EQ].
    + split; [lia|]. split; [right; repeat split; lia|]. split; [lia|]. split; [lia|].
      split; [exact B'|]. split; [intros; lia|]. split; [exact Z'|]. split; [exact T'| intros; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation "'let?' x ':=' e 'in' k" :=
  (match e with Some x => k | None => None end)
  (at level 200, x pattern, e at level 100, k at level 200, only parsing).

Definition g_e (big : list Z) (a r z : Z) : option Z :=
  if a <? z
  then (let? (i, e) := fmt_fp_cnt TEN_FUEL (znth big a) (10, 9 * (r - a)) in Some e)
  else Some 0.
Definition g_j (t p e : Z) : Z :=
  p - (if negb (Z.lor t 32 =? CHR_f) then 1 else 0) * e
    - (if (Z.lor t 32 =? CHR_g) && negb (p =? 0) then 1 else 0).

(* [comment removed for export] *)
Definition g_R (t p prefix pl : Z) (big : list Z) (a r z e j : Z) : option (list Z * Z * Z * Z) :=
    if j <? 9 * (z - r - 1) then
      let d := r + 1 + (Z.quot (j + 9 * LDBL_MAX_EXP) 9 - LDBL_MAX_EXP) in
      let j := j + 9 * LDBL_MAX_EXP in
      let j := Z.rem j 9 in
      let? (i, j) := fmt_fp_powi TEN_FUEL (10, j + 1) in
      let x := (znth big d) mod i in
      let? (big, a, d, e) :=
        if negb (x =? 0) || negb (d + 1 =? z) then
          let round := f128_div (f128_of_i32 2) K_LDBL_EPSILON in
          let round :=
            if negb (Z.land (znth big d / i) 1 =? 0)
               || ((i =? 1000000000) && (a <? d) && negb (Z.land (znth big (d - 1)) 1 =? 0))
            then f128_add round (f128_of_i32 2)
            else round in
          let small :=
            if x <? Z.quot i 2 then f128_of_d D_0_5
            else if (x =? Z.quot i 2) && (d + 1 =? z) then f128_of_d D_1_0
            else f128_of_d D_1_5 in
          let '(round, small) :=
            if negb (pl =? 0) && (znth PREFIX_STR prefix =? CHR_minus) then
              let m1 := f128_of_i32 (-1) in
              let round := f128_mul round m1 in
              let small := f128_mul small m1 in
              (round, small)
            else (round, small) in
          let big := zupd big d (znth big d - x) in
          if negb (f128_le (f128_add round small) round =? 0) then
            let big := zupd big d (u32 (znth big d + i)) in
            let? (big, d, a) := fmt_fp_carry BIG_FUEL (big, d, a) in
            let? (i, e) := fmt_fp_cnt TEN_FUEL (znth big a) (10, 9 * (r - a)) in
            Some (big, a, d, e)
          else Some (big, a, d, e)
        else Some (big, a, d, e) in
      let z := if d + 1 <? z then d + 1 else z in
      Some (big, a, z, e)
    else Some (big, a, z, e).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TS (r0 : Z) (big : list Z) (a z e : Z) : Prop :=
  W9 big /\ zlength big = 128 /\ 0 <= a < z /\ z <= 127 /\ zeros_below big a /\
  (r0 = 0 \/ (r0 = 122 /\ 85 <= a <= 122)) /\
  exists k, 1 <= k <= 9 /\ 10^(k-1) <= znth big a < 10^k /\ e = 9 * (r0 - a) + k - 1.

Lemma TS_e_bound : forall r0 big a z e, TS r0 big a z e -> -1143 <= e <= 341.
Proof. intros r0 big a z e (_ & _ & AZ & Z7 & _ & R & [k (Hk & _ & ->)]). lia. Qed.

Lemma g_e_spec : forall r0 big a z, POST r0 big a z -> exists e, g_e big a r0 z = Some e /\ TS r0 big a z e.
Proof.
  intros r0 big a z (WB & LB & AZ & Z7 & NZ & ZB & R).
  unfold g_e. replace (a <? z) with true by (symmetry; apply Z.ltb_lt; lia).
  pose proof (WB a) as Wa.
  destruct (cnt_spec (znth big a) (9 * (r0 - a)) Wa) as [k (E & Hk & Hhi & Hlo)]. rewrite E.
  eexists. split; [reflexivity|]. unfold TS.
  split; [exact WB|]. split; [exact LB|]. split; [exact AZ|]. split; [exact Z7|]. split; [exact ZB|].
  split; [destruct R as [[-> _]|(-> & ? & _)]; [left; reflexivity| right; lia]|].
  exists k. split; [exact Hk|]. split; [| lia]. split; [apply Hlo; exact NZ| exact Hhi].
Qed.

Lemma pow10_le_NB : forall k, 0 <= k <= 9 -> 1 <= 10^k <= NB.
Proof.
  intros k Hk. unfold NB. change 1000000000 with (10^9). split; [pose proof (pow10_pos k); lia| apply Z.pow_le_mono_r; lia].
Qed.

Lemma NB_multiple : forall k, 0 <= k <= 9 -> NB = 10^k * 10^(9 - k).
Proof. intros. unfold NB. change 1000000000 with (10^9). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma R_spec : forall p1 prefix pl r0 big a z e,
  TS r0 big a z e -> znth big a <> 0 -> (r0 = 0 -> znth big 0 < 2^29) -> (r0 = 122 -> 86 <= a) -> 9 <= p1 <= 26 ->
  exists bigR aR zR eR, g_R CHR_g p1 prefix pl big a r0 z e (g_j CHR_g p1 e) = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z.
Proof.
  intros p1 prefix pl r0 big a z e HT NZ B0 A86 Hp.
  pose proof HT as (WB & LB & AZ & Z7 & ZB & R & [k (Hk & Hka & He)]).
  unfold g_j. change (Z.lor CHR_g 32 =? CHR_f) with false. change (Z.lor CHR_g 32 =? CHR_g) with true.
  replace (p1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
  set (j := p1 - 1 * e - 1).
  unfold g_R.
  destruct (Z.ltb_spec j (9 * (z - r0 - 1))) as [JL|JG].
  2:{ eexists _, _, _, _. split; [reflexivity|]. split; [exact HT|]. split; [exact NZ|]. split; [left; reflexivity| lia]. }
  change LDBL_MAX_EXP with 16384.
  assert (Hj : -1200 <= j <= 1200) by (subst j; lia).
  rewrite Z.quot_div_nonneg by lia. rewrite Z.rem_mod_nonneg by lia.
  set (q := (j + 9 * 16384) / 9 - 16384). set (j2 := (j + 9 * 16384) mod 9).
  assert (Hq : j = 9 * q + j2 /\ 0 <= j2 <= 8) by (subst q j2; dlia).
  assert (Hd : a + 1 <= r0 + 1 + q < z).
  { subst j. destruct Hq as [Hq _]. split; [| nia]. (* [comment removed for export] *) nia. }
  set (d := r0 + 1 + q) in *.
  rewrite (powi_spec j2) by lia.
  set (i := 10 ^ (9 - j2)).
  assert (Hi : 10 <= i <= NB /\ NB = i * 10^j2).
  { subst i. pose proof (pow10_le_NB (9 - j2) ltac:(lia)). pose proof (pow10_le_NB j2 ltac:(lia)).
    split; [| rewrite (NB_multiple (9 - j2)) by lia; f_equal; f_equal; lia].
    split; [| lia]. change 10 with (10^1). apply Z.pow_le_mono_r; lia. }
  clearbody i. destruct Hi as [Hi NBi].
  pose proof (WB d) as Wd.
  pose proof (Z.mod_pos_bound (znth big d) i ltac:(lia)) as Xr.
  pose proof (Z.div_mod (znth big d) i ltac:(lia)) as Xd.
  set (x := znth big d mod i) in *.
  destruct (negb (x =? 0) || negb (d + 1 =? z)) eqn:CX.
  2:{ (* [comment removed for export] *)
      eexists _, _, _, _. split; [reflexivity|].
      replace (if d + 1 <? z then d + 1 else z) with z by (destruct (Z.ltb_spec (d + 1) z); lia).
      split; [exact HT|]. split; [exact NZ|]. split; [left; reflexivity| lia]. }
  cbv zeta.
  (* [comment removed for export] *)
  assert (DOWN : exists bigR aR zR eR,
    match Some (zupd big d (znth big d - x), a, d, e) with
    | Some (big0, a0, d0, e0) => Some (big0, a0, if d0 + 1 <? z then d0 + 1 else z, e0)
    | None => None end = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z).
  { eexists _, _, _, _. split; [reflexivity|].
    assert (ZR : a + 1 < (if d + 1 <? z then d + 1 else z) <= z) by (destruct (Z.ltb_spec (d + 1) z); lia).
    split; [| split; [rewrite znth_zupd_neq by lia; exact NZ| split; [left; reflexivity| lia]]].
    unfold TS. split; [apply W9_zupd; [exact WB| lia]|]. split; [rewrite zlength_zupd; exact LB|].
    split; [lia|]. split; [lia|]. split; [intros kk Hkk; rewrite znth_zupd_neq by lia; apply ZB; lia|].
    split; [exact R|]. exists k. rewrite znth_zupd_neq by lia. split; [exact Hk|]. split; [exact Hka| exact He]. }
  assert (UP : exists bigR aR zR eR,
    match (match fmt_fp_carry BIG_FUEL
             (zupd (zupd big d (znth big d - x)) d (u32 (znth (zupd big d (znth big d - x)) d + i)), d, a) with
           | Some (big0, d0, a0) =>
             match fmt_fp_cnt TEN_FUEL (znth big0 a0) (10, 9 * (r0 - a0)) with
             | Some (_, e0) => Some (big0, a0, d0, e0)
             | None => None
             end
           | None => None end) with
    | Some (big0, a0, d0, e0) => Some (big0, a0, if d0 + 1 <? z then d0 + 1 else z, e0)
    | None => None end = Some (bigR, aR, zR, eR) /\
    TS r0 bigR aR zR eR /\ znth bigR aR <> 0 /\ (aR = a \/ aR = a - 1) /\ zR <= z).
  { rewrite znth_zupd_eq by lia.
    assert (XI : 0 <= znth big d - x /\ znth big d - x + i <= NB).
    { split; [lia|].
      (* [comment removed for export] *)
      assert (QL : znth big d / i < 10 ^ j2) by (apply Z.div_lt_upper_bound; lia).
      assert (i * (znth big d / i + 1) <= i * 10 ^ j2) by (apply Z.mul_le_mono_nonneg_l; lia).
      lia. }
    rewrite (u32_id (znth big d - x + i)) by (unfold NB in *; lia).
    set (big2 := zupd (zupd big d (znth big d - x)) d (znth big d - x + i)).
    assert (L2 : zlength big2 = 128) by (subst big2; rewrite !zlength_zupd; exact LB).
    destruct (carry_spec big2 d a L2 ltac:(lia) ltac:(lia)) as [bigC [dC [aC (EC & LC & WC & AC0 & ACa & DC & VdC & BC & UC & ZC & TC & EQC)]]].
    { intros ii Hii. subst big2. rewrite !znth_zupd_neq by lia. apply WB. }
    { subst big2. rewrite znth_zupd_eq by (rewrite zlength_zupd; lia). lia. }
    { intros A0. split; [lia|]. subst big2. rewrite !znth_zupd_neq by lia. destruct R as [R0|[_ ?]]; [| lia]. specialize (B0 R0). unfold NB. lia. }
    rewrite EC.
    assert (NZC : znth bigC aC <> 0).
    { destruct ACa as [->|(-> & -> & V1)]; [| rewrite V1; lia].
      destruct (Z.eq_dec dC a) as [->|]; [lia|]. rewrite UC by lia. subst big2. rewrite !znth_zupd_neq by lia. exact NZ. }
    pose proof (WC aC) as WaC.
    destruct (cnt_spec (znth bigC aC) (9 * (r0 - aC)) WaC) as [kC (ECn & HkC & HhiC & HloC)]. rewrite ECn.
    eexists _, _, _, _. split; [reflexivity|].
    assert (ZR : aC < (if dC + 1 <? z then dC + 1 else z) <= z) by (destruct (Z.ltb_spec (dC + 1) z); lia).
    split; [| split; [exact NZC| split; [destruct ACa as [->|(-> & _)]; [left|right]; reflexivity| lia]]].
    unfold TS. split; [exact WC|]. split; [exact LC|]. split; [lia|]. split; [lia|].
    split. { intros kk Hkk. rewrite BC by lia. subst big2. rewrite !znth_zupd_neq by lia. apply ZB. destruct ACa as [->|(-> & _)]; lia. }
    split. { destruct R as [R0|(R1 & R2)]; [left; exact R0| right]. split; [exact R1|]. specialize (A86 R1). destruct ACa as [->|(-> & _)]; lia. }
    exists kC. split; [exact HkC|]. split; [| lia]. split; [apply HloC; exact NZC| exact HhiC]. }
  destruct (negb (pl =? 0) && (znth PREFIX_STR prefix =? CHR_minus)); cbv beta iota;
  match goal with |- context [negb (f128_le ?A ?B =? 0)] => destruct (negb (f128_le A B =? 0)) end;
  first [exact DOWN | exact UP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zrepeat_nil : forall c n, n <= 0 -> zrepeat c n = [].
Proof. intros. Local Transparent zrepeat. unfold zrepeat. replace (Z.to_nat n) with 0%nat by lia. reflexivity. Qed.
Local Opaque zrepeat.

Lemma pad_exact : forall o c w l, w - l < 256 ->
  pad o c w l 0 = Some (o ++ zrepeat c (w - l)).
Proof.
  intros o c w l Hw. unfold pad. change (negb (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)) with false. cbn [orb].
  destruct (Z.leb_spec w l).
  - rewrite zrepeat_nil by lia. rewrite app_nil_r. reflexivity.
  - rewrite pad_loop_eq. unfold PAD_FUEL. cbn [wloop]. cbn [fst].
    replace (256 <=? w - l) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma zlength_zrepeat' : forall c n, zlength (zrepeat c n) = Z.max 0 n.
Proof. intros. Local Transparent zrepeat. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.

Lemma Forall_zrepeat : forall (P : Z -> Prop) c n, P c -> Forall P (zrepeat c n).
Proof. intros P c n Hc. Local Transparent zrepeat. unfold zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. exact Hc. Qed.
Local Opaque zrepeat.

Lemma isdig_0 : isdig CHR_0. Proof. unfold isdig, CHR_0. lia. Qed.

Lemma W9_DIGk : forall big i, W9 big -> exists k, DIGk (znth big i) k /\ 0 <= k <= 9.
Proof.
  intros big i WB. pose proof (WB i). apply (DIGk_exists (znth big i) 9); [| lia]. unfold NB in H. change (10^9) with 1000000000. lia.
Qed.

(* [comment removed for export] *)
Lemma fint_body_spec : forall big a0 d o k, W9 big -> DIGk (znth big d) k -> 0 <= k <= 9 ->
  exists txt, fmt_fp_fint_body big a0 (d, o) = Some (d + 1, o ++ txt) /\ Forall isdig txt /\
    zlength txt = (if d =? a0 then Z.max k 1 else 9).
Proof.
  intros big a0 d o k WB D Hk. pose proof (WB d) as Hv. unfold fmt_fp_fint_body.
  destruct (fmt_u_spec (znth big d) (zrepeat 0 37) 9 k ltac:(lia) D ltac:(lia)) as [b1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  destruct (Z.eqb_spec d a0) as [->|NE].
  - cbn [negb]. destruct (Z.eqb_spec (9 - k) 9) as [K0|K0].
    + assert (k = 0) by lia. subst k. eexists. split; [reflexivity|]. unfold out. split.
      * apply zsub_Forall; try (rewrite ?zlength_zupd; lia). intros i Hi. replace i with 8 by lia. rewrite znth_zupd_eq by lia. apply isdig_0.
      * rewrite zlength_zsub by (rewrite ?zlength_zupd; lia). reflexivity.
    + eexists. split; [reflexivity|]. unfold out. split.
      * apply zsub_Forall; try lia. intros i Hi. apply D1. lia.
      * rewrite zlength_zsub by lia. lia.
  - cbn [negb]. destruct (zfill_spec (9 - k) b1 ltac:(lia) ltac:(lia)) as [b2 (E2 & L2 & F1 & F2)]. rewrite E2.
    eexists. split; [reflexivity|]. unfold out. split.
    + apply zsub_Forall; try lia. intros i Hi. destruct (Z.lt_ge_cases i (9 - k)).
      * rewrite F1 by lia. apply isdig_0.
      * rewrite F2 by lia. apply D1. lia.
    + rewrite zlength_zsub by lia. reflexivity.
Qed.

Lemma fint_spec : forall big a0 r o k, W9 big -> 0 <= a0 <= r -> r - a0 <= 128 -> DIGk (znth big a0) k -> 0 <= k <= 9 ->
  exists txt, fmt_fp_fint BIG_FUEL big a0 r (a0, o) = Some (r + 1, o ++ txt) /\ Forall isdig txt /\
    zlength txt = Z.max k 1 + 9 * (r - a0).
Proof.
  intros big a0 r o k WB Har Hw D Hk. rewrite fmt_fp_fint_eq.
  destruct (owloop_total (fun st : Z * list Z => fst st <=? r) (fmt_fp_fint_body big a0)
    (fun st => a0 <= fst st <= r + 1 /\ exists acc, snd st = o ++ acc /\ Forall isdig acc /\
               zlength acc = (if fst st =? a0 then 0 else Z.max k 1 + 9 * (fst st - a0 - 1)))
    (fun st => r + 1 - fst st)) with (fuel := BIG_FUEL) (s := (a0, o)) as [[d' o'] (E & (R' & [acc (Eo & Facc & Lacc)]) & C)].
  - intros [d o1] (R1 & [acc (Eo1 & F1 & L1)]) C1. cbn [fst snd] in *. subst o1. apply Z.leb_le in C1.
    destruct (W9_DIGk big d WB) as [kd [Dd Hkd]].
    assert (KD : d = a0 -> kd = k).
    { intros ->. destruct D as [[A1 A2]|[A1 A2]]; destruct Dd as [[B1 B2]|[B1 B2]]; try lia.
      destruct (Z.lt_trichotomy kd k) as [LT|[EQ|GT]]; [| exact EQ |].
      - exfalso. assert (10 ^ kd <= 10 ^ (k - 1)) by (apply Z.pow_le_mono_r; lia). lia.
      - exfalso. assert (10 ^ k <= 10 ^ (kd - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
    destruct (fint_body_spec big a0 d (o ++ acc) kd WB Dd Hkd) as [txt (Eb & Ft & Lt)].
    rewrite Eb. eexists. split; [reflexivity|]. cbn [fst snd]. split; [| lia]. split; [lia|].
    exists (acc ++ txt). split; [now rewrite app_assoc|]. split; [apply Forall_app; split; assumption|].
    rewrite zlength_app, L1, Lt. destruct (Z.eqb_spec d a0) as [->|NE].
    + rewrite (KD eq_refl). replace (a0 + 1 =? a0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
    + replace (d + 1 =? a0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - cbn [fst snd]. split; [lia|]. exists []. rewrite app_nil_r, Z.eqb_refl. repeat split; auto.
  - cbn [fst]. unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. cbn [fst snd] in *. subst o'. apply Z.leb_gt in C. assert (d' = r + 1) by lia. subst d'.
    exists acc. split; [reflexivity|]. split; [exact Facc|]. rewrite Lacc.
    replace (r + 1 =? a0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
Qed.

Lemma ffrac_spec : forall big z d p o, W9 big -> z - d <= 129 -> 0 <= p ->
  exists d' p' acc, fmt_fp_ffrac BIG_FUEL big z (d, p, o) = Some (d', p', o ++ acc) /\ Forall isdig acc /\
    zlength acc = p - Z.max p' 0 /\ p' <= p.
Proof.
  intros big z d p o WB Hw Hp. rewrite fmt_fp_ffrac_eq.
  destruct (owloop_total (fun st : Z * Z * list Z => let '(d0, p0, _) := st in (d0 <? z) && (0 <? p0)) (fmt_fp_ffrac_body big)
    (fun st => let '(d1, p1, o1) := st in z - d1 <= 129 /\ p1 <= p /\ exists acc, o1 = o ++ acc /\ Forall isdig acc /\ zlength acc = p - Z.max p1 0)
    (fun st => let '(d1, _, _) := st in Z.max 0 (z - d1))) with (fuel := BIG_FUEL) (s := (d, p, o)) as [[[d' p'] o'] (E & (R1 & R2 & [acc (-> & Facc & Lacc)]) & C)].
  - intros [[d1 p1] o1] (Q1 & Q2 & [acc (-> & F1 & L1)]) C1. apply andb_prop in C1. destruct C1 as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
    unfold fmt_fp_ffrac_body.
    destruct (W9_DIGk big d1 WB) as [kd [Dd Hkd]]. pose proof (WB d1) as Wd.
    destruct (fmt_u_spec (znth big d1) (zrepeat 0 37) 9 kd ltac:(lia) Dd ltac:(lia)) as [b1 (E1 & L1' & D1 & U1)].
    { rewrite zlength_zrepeat; lia. }
    rewrite E1. rewrite zlength_zrepeat in L1' by lia.
    destruct (zfill_spec (9 - kd) b1 ltac:(lia) ltac:(lia)) as [b2 (E2 & L2 & G1 & G2)]. rewrite E2.
    eexists. split; [reflexivity|]. split; [| lia]. split; [lia|]. split; [lia|].
    exists (acc ++ zsub b2 0 (Z.min 9 p1)). unfold out. split; [now rewrite app_assoc|]. split.
    + apply Forall_app. split; [exact F1|]. apply zsub_Forall; try lia. intros i Hi.
      destruct (Z.lt_ge_cases i (9 - kd)); [rewrite G1 by lia; apply isdig_0| rewrite G2 by lia; apply D1; lia].
    + rewrite zlength_app, L1, zlength_zsub by lia. lia.
  - split; [lia|]. split; [lia|]. exists []. rewrite app_nil_r. repeat split; auto. unfold zlength. cbn [length]. lia.
  - unfold BIG_FUEL. change (Z.of_nat 130) with 130. lia.
  - rewrite E. exists d', p', acc. split; [reflexivity|]. split; [exact Facc|]. split; [exact Lacc| exact R2].
Qed.


Definition isdigdot (c : Z) : Prop := isdig c \/ c = CHR_dot.

Lemma emit_f_spec : forall o big a r0 z p k, W9 big -> 0 <= r0 -> r0 - 128 < a -> a < z -> z <= 128 -> 0 <= a -> 0 <= p <= 40 ->
  (r0 < a -> znth big r0 = 0) -> DIGk (znth big a) k -> 1 <= k <= 9 ->
  exists txt, fmt_fp_emit_f o big a r0 z p 0 = Some (o ++ txt) /\ Forall isdigdot txt /\
    zlength txt = (if a <=? r0 then k + 9 * (r0 - a) else 1) + (if p =? 0 then 0 else 1) + p.
Proof.
  intros o big a r0 z p k WB Hr0 Har Haz Hz Ha Hp Hbelow D Hk. unfold fmt_fp_emit_f.
  set (a0 := if r0 <? a then r0 else a).
  assert (A0 : (a <= r0 /\ a0 = a) \/ (r0 < a /\ a0 = r0)) by (subst a0; destruct (Z.ltb_spec r0 a); lia).
  assert (K0 : exists k0, DIGk (znth big a0) k0 /\ 0 <= k0 <= 9 /\ Z.max k0 1 = (if a <=? r0 then k else 1)).
  { destruct A0 as [[H1 ->]|[H1 ->]].
    - exists k. split; [exact D|]. replace (a <=? r0) with true by (symmetry; apply Z.leb_le; lia). lia.
    - exists 0. rewrite (Hbelow H1). split; [left; lia|]. replace (a <=? r0) with false by (symmetry; apply Z.leb_gt; lia). lia. }
  destruct K0 as [k0 (D0 & Hk0 & MK)]. clearbody a0.
  destruct (fint_spec big a0 r0 o k0 WB ltac:(lia) ltac:(lia) D0 Hk0) as [t1 (E1 & F1 & L1)]. rewrite E1.
  change (Z.land 0 ALT_FORM =? 0) with true. cbn [negb orb].
  set (o2 := if negb (p =? 0) || false then out (o ++ t1) [CHR_dot] else o ++ t1).
  assert (O2 : exists t2, o2 = o ++ t2 /\ Forall isdigdot t2 /\ zlength t2 = zlength t1 + (if p =? 0 then 0 else 1)).
  { subst o2. destruct (Z.eqb_spec p 0); cbn [negb orb].
    - exists t1. split; [reflexivity|]. split; [| lia]. eapply Forall_impl; [| exact F1]. intros c Hc; left; exact Hc.
    - exists (t1 ++ [CHR_dot]). unfold out. rewrite app_assoc. split; [reflexivity|]. split.
      + apply Forall_app. split; [eapply Forall_impl; [| exact F1]; intros c Hc; left; exact Hc|]. constructor; [right; reflexivity| constructor].
      + rewrite zlength_app. unfold zlength. cbn [length]. lia. }
  destruct O2 as [t2 (-> & F2 & L2)]. 
  destruct (ffrac_spec big z (r0 + 1) p (o ++ t2) WB ltac:(lia) ltac:(lia)) as [d' [p' [t3 (E3 & F3 & L3 & P3)]]].
  rewrite E3. rewrite pad_exact by lia.
  exists (t2 ++ t3 ++ zrepeat CHR_0 (p' + 9 - 9)). unfold out. split; [rewrite <- !app_assoc; reflexivity|]. split.
  - apply Forall_app. split; [exact F2|]. apply Forall_app. split; [eapply Forall_impl; [| exact F3]; intros c Hc; left; exact Hc|].
    apply Forall_zrepeat. left. apply isdig_0.
  - rewrite !zlength_app, zlength_zrepeat', L2, L1, L3, MK. destruct A0 as [[H1 ->]|[H1 ->]].
    + replace (a <=? r0) with true by (symmetry; apply Z.leb_le; lia). lia.
    + replace (a <=? r0) with false by (symmetry; apply Z.leb_gt; lia). lia.
Qed.

Lemma owloop_S : forall {A} (c : A -> bool) (b : A -> option A) n s,
  owloop c b (S n) s = (if c s then match b s with Some s' => owloop c b n s' | None => None end else Some s).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma eloop_rest_spec : forall fuel big a z d p o, W9 big -> a < d -> (1 <= fuel)%nat -> z - d < Z.of_nat fuel ->
  exists d' p' acc, fmt_fp_eloop fuel big a z 0 (d, p, o) = Some (d', p', o ++ acc) /\ Forall isdig acc /\
    zlength acc = Z.max p 0 - Z.max p' 0 /\ p' <= p.
Proof.
  intros fuel big a z d p o WB Had Hf1 Hf. rewrite fmt_fp_eloop_eq.
  destruct (owloop_total (fun st : Z * Z * list Z => let '(d0, p0, _) := st in (d0 <? z) && (0 <=? p0)) (fmt_fp_eloop_body big a 0)
    (fun st => let '(d1, p1, o1) := st in a < d1 /\ p1 <= p /\ exists acc, o1 = o ++ acc /\ Forall isdig acc /\ zlength acc = Z.max p 0 - Z.max p1 0)
    (fun st => let '(d1, p1, _) := st in if (d1 <? z) && (0 <=? p1) then z - d1 else 0)) with (fuel := fuel) (s := (d, p, o))
    as [[[d' p'] o'] (E & (R1 & R2 & [acc (-> & Facc & Lacc)]) & C)].
  - intros [[d1 p1] o1] (Q1 & Q2 & [acc (-> & F1 & L1)]) C1. rewrite C1.
    apply andb_prop in C1. destruct C1 as [C1 C2]. apply Z.ltb_lt in C1. apply Z.leb_le in C2.
    unfold fmt_fp_eloop_body.
    destruct (W9_DIGk big d1 WB) as [kd [Dd Hkd]]. pose proof (WB d1) as Wd.
    destruct (fmt_u_spec (znth big d1) (zrepeat 0 37) 9 kd ltac:(lia) Dd ltac:(lia)) as [b1 (E1 & L1' & D1 & U1)].
    { rewrite zlength_zrepeat; lia. }
    rewrite E1. rewrite zlength_zrepeat in L1' by lia.
    replace (negb (d1 =? a)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; lia).
    set (sb := if 9 - kd =? 9 then (9 - kd - 1, zupd b1 (9 - kd - 1) CHR_0) else (9 - kd, b1)).
    assert (SB : exists s2 b2, sb = (s2, b2) /\ 0 <= s2 <= 8 /\ zlength b2 = 37 /\ forall i, s2 <= i < 9 -> isdig (znth b2 i)).
    { subst sb. destruct (Z.eqb_spec (9 - kd) 9).
      - eexists _, _. split; [reflexivity|]. split; [lia|]. split; [rewrite zlength_zupd; lia|].
        intros i Hi. replace i with 8 by lia. replace (9 - kd - 1) with 8 by lia. rewrite znth_zupd_eq by lia. apply isdig_0.
      - eexists _, _. split; [reflexivity|]. split; [lia|]. split; [lia|]. intros i Hi. apply D1. lia. }
    destruct SB as [s2 [b2 (-> & S2 & L2 & D2)]].
    destruct (zfill_spec s2 b2 ltac:(lia) ltac:(lia)) as [b3 (E3 & L3 & G1 & G2)]. rewrite E3.
    eexists. split; [reflexivity|]. split.
    + split; [lia|]. split; [lia|]. exists (acc ++ zsub b3 0 (Z.min (9 - 0) (p1))). unfold out. split; [now rewrite app_assoc|]. split.
      * apply Forall_app. split; [exact F1|]. apply zsub_Forall; try lia. intros i Hi.
        destruct (Z.lt_ge_cases i s2); [rewrite G1 by lia; apply isdig_0| rewrite G2 by lia; apply D2; lia].
      * rewrite zlength_app, L1, zlength_zsub by lia. lia.
    + destruct ((d1 + 1 <? z) && (0 <=? p1 - (9 - 0))) eqn:CC; [|lia].
      apply andb_prop in CC. destruct CC as [CC1 CC2]. apply Z.ltb_lt in CC1. lia.
  - split; [lia|]. split; [lia|]. exists []. rewrite app_nil_r. repeat split; auto. unfold zlength. cbn [length]. lia.
  - destruct ((d <? z) && (0 <=? p)) eqn:CC; [|lia]. apply andb_prop in CC. destruct CC as [CC1 CC2]. apply Z.ltb_lt in CC1. lia.
  - rewrite E. exists d', p', acc. split; [reflexivity|]. split; [exact Facc|]. split; [exact Lacc| exact R2].
Qed.

Lemma eloop_S : forall n big a z fl d p o,
  fmt_fp_eloop (S n) big a z fl (d, p, o) =
  (if (d <? z) && (0 <=? p) then match fmt_fp_eloop_body big a fl (d, p, o) with Some st => fmt_fp_eloop n big a z fl st | None => None end
   else Some (d, p, o)).
Proof. reflexivity. Qed.

Lemma emit_e_spec : forall o big a z p ebuf0 estr k, W9 big -> 0 <= a -> a < z -> z <= 128 -> 0 <= p <= 40 ->
  DIGk (znth big a) k -> 1 <= k <= 9 -> 0 <= estr <= 12 -> zlength ebuf0 = 12 ->
  exists txt, fmt_fp_emit_e o big a z p 0 ebuf0 estr = Some (o ++ txt ++ zsub ebuf0 estr (12 - estr)) /\ Forall isdigdot txt /\
    zlength txt = 1 + (if 0 <? p then 1 else 0) + p.
Proof.
  intros o big a z p ebuf0 estr k WB Ha Haz Hz Hp D Hk He HLe. unfold fmt_fp_emit_e.
  replace (z <=? a) with false by (symmetry; apply Z.leb_gt; lia).
  change BIG_FUEL with (S 129%nat). rewrite eloop_S.
  replace ((a <? z) && (0 <=? p)) with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Z.ltb_lt; lia| apply Z.leb_le; lia]. }
  unfold fmt_fp_eloop_body at 1.
  pose proof (WB a) as Wa.
  destruct (fmt_u_spec (znth big a) (zrepeat 0 37) 9 k ltac:(lia) D ltac:(lia)) as [b1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  replace (9 - k =? 9) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Z.eqb_refl. cbn [negb]. change (Z.land 0 ALT_FORM =? 0) with true. cbn [negb]. rewrite Bool.orb_false_r.
  set (o1 := out o (zsub b1 (9 - k) 1)).
  set (o2 := if 0 <? p then out o1 [CHR_dot] else o1).
  set (o3 := out o2 (zsub b1 (9 - k + 1) (Z.min (9 - (9 - k + 1)) p))).
  assert (O3 : exists t3, o3 = o ++ t3 /\ Forall isdigdot t3 /\ zlength t3 = 1 + (if 0 <? p then 1 else 0) + Z.min (k - 1) p).
  { subst o3 o2 o1. unfold out.
    assert (F0 : Forall isdigdot (zsub b1 (9 - k) 1)).
    { apply zsub_Forall; try lia. intros i Hi. left. apply D1. lia. }
    assert (F2 : Forall isdigdot (zsub b1 (9 - k + 1) (Z.min (9 - (9 - k + 1)) p))).
    { apply zsub_Forall; try lia. intros i Hi. left. apply D1. lia. }
    destruct (Z.ltb_spec 0 p).
    - eexists. rewrite <- !app_assoc. split; [reflexivity|]. split.
      + apply Forall_app. split; [exact F0|]. apply Forall_app. split; [constructor; [right; reflexivity| constructor]| exact F2].
      + rewrite !zlength_app, !zlength_zsub by lia. unfold zlength. cbn [length]. lia.
    - eexists. rewrite <- !app_assoc. split; [reflexivity|]. split.
      + apply Forall_app. split; [exact F0| exact F2].
      + rewrite !zlength_app, !zlength_zsub by lia. lia. }
  destruct O3 as [t3 (EO3 & F3 & L3)]. rewrite EO3.
  destruct (eloop_rest_spec 129%nat big a z (a + 1) (p - (9 - (9 - k + 1))) (o ++ t3) WB ltac:(lia) ltac:(lia) ltac:(lia)) as [d' [p' [t4 (E4 & F4 & L4 & P4)]]].
  rewrite E4. rewrite pad_exact by lia.
  exists (t3 ++ t4 ++ zrepeat CHR_0 (p' + 18 - 18)). unfold out. split; [rewrite <- !app_assoc; reflexivity|]. split.
  - apply Forall_app. split; [exact F3|]. apply Forall_app. split; [eapply Forall_impl; [| exact F4]; intros c Hc; left; exact Hc|].
    apply Forall_zrepeat. left. apply isdig_0.
  - rewrite !zlength_app, zlength_zrepeat', L3, L4. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition g_H (o : list Z) (w fl t p prefix pl : Z) (big : list Z) (a r z e : Z) : option (list Z * Z) :=
  let? z := fmt_fp_strip BIG_FUEL big a z in
  let? (p, t) :=
    if Z.lor t 32 =? CHR_g then
      let p := if p =? 0 then p + 1 else p in
      let '(t, p) := if (e <? p) && (-4 <=? e) then (t - 1, p - (e + 1)) else (t - 2, p - 1) in
      if Z.land fl ALT_FORM =? 0 then
        let? j := if (a <? z) && negb (znth big (z - 1) =? 0)
                  then (let? (i, j) := fmt_fp_tz TEN_FUEL (znth big (z - 1)) (10, 0) in Some j)
                  else Some 9 in
        let p := if Z.lor t 32 =? CHR_f
                 then Z.min p (Z.max 0 (9 * (z - r - 1) - j))
                 else Z.min p (Z.max 0 (9 * (z - r - 1) + e - j)) in
        Some (p, t)
      else Some (p, t)
    else Some (p, t) in
  let palt := if negb (p =? 0) || negb (Z.land fl ALT_FORM =? 0) then 1 else 0 in
  if INT_MAX - 1 - palt <? p then Some (o, -1) else
  let l := 1 + p + palt in
  let? len := fmt_fp_len t l e in
  match len with
  | Ret v => Some (o, v)
  | Cont (l, ebuf0, estr) =>
  if INT_MAX - pl <? l then Some (o, -1) else
  let? o := pad o CHR_sp w (pl + l) fl in
  let o := out o (zsub PREFIX_STR prefix pl) in
  let? o := pad o CHR_0 w (pl + l) (Z.lxor fl ZERO_PAD) in
  let? o := if Z.lor t 32 =? CHR_f
            then fmt_fp_emit_f o big a r z p fl
            else fmt_fp_emit_e o big a z p fl ebuf0 estr in
  let? o := pad o CHR_sp w (pl + l) (Z.lxor fl LEFT_ADJ) in
  Some (o, Z.max w (pl + l))
  end.

Lemma pad_flag : forall o c w l fl, Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) <> 0 -> pad o c w l fl = Some o.
Proof.
  intros o c w l fl H. unfold pad. replace (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) with false by (symmetry; apply Z.eqb_neq; exact H).
  reflexivity.
Qed.

Lemma gch_0 : gch CHR_0. Proof. left. unfold CHR_0. lia. Qed.
Lemma gch_isdigdot : forall c, isdigdot c -> gch c.
Proof. intros c [H| ->]; [left; exact H| unfold gch, CHR_dot; lia]. Qed.

Lemma len_f_spec : forall l e, 0 <= l <= 100 -> -2000 <= e <= 2000 ->
  fmt_fp_len 102 l e = Some (Cont ((if 0 <? e then l + e else l), zrepeat 0 12, 12)).
Proof.
  intros l e Hl He. unfold fmt_fp_len. change (Z.lor 102 32 =? CHR_f) with true. cbv iota.
  replace (INT_MAX - l <? e) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia). reflexivity.
Qed.

Lemma len_e_spec : forall l e, 0 <= l <= 100 -> -9999 <= e <= 9999 ->
  exists estr eb, fmt_fp_len 101 l e = Some (Cont (l + (12 - estr), eb, estr)) /\ 4 <= 12 - estr <= 6 /\ zlength eb = 12 /\
    forall i, estr <= i < 12 -> gch (znth eb i).
Proof.
  intros l e Hl He. unfold fmt_fp_len. change (Z.lor 101 32 =? CHR_f) with false. cbv iota.
  set (ea := if e <? 0 then - e else e).
  assert (Hea : 0 <= ea < 10^4) by (subst ea; destruct (Z.ltb_spec e 0); lia).
  destruct (DIGk_exists ea 4 Hea ltac:(lia)) as [ke [Dk Hke]].
  destruct (fmt_u_spec ea (zrepeat 0 12) 12 ke ltac:(lia) Dk ltac:(lia)) as [eb1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  destruct (epad_spec (12 - ke) eb1 ltac:(lia) L1) as [eb2 (E2 & L2 & G1 & G2)]. rewrite E2.
  replace (INT_MAX - l <? 12 - (Z.min (12 - ke) 10 - 1 - 1)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
  eexists _, _. split; [reflexivity|]. split; [lia|]. split; [rewrite !zlength_zupd; exact L2|].
  intros i Hi.
  destruct (Z.eq_dec i (Z.min (12 - ke) 10 - 1 - 1)) as [->|N1].
  { rewrite znth_zupd_eq by (rewrite zlength_zupd, L2; lia). unfold u8. change (101 mod 2^8) with 101. unfold gch. lia. }
  rewrite znth_zupd_neq by lia.
  destruct (Z.eq_dec i (Z.min (12 - ke) 10 - 1)) as [->|N2].
  { rewrite znth_zupd_eq by (rewrite L2; lia). unfold gch, CHR_minus, CHR_plus. destruct (e <? 0); lia. }
  rewrite znth_zupd_neq by lia.
  destruct (Z.lt_ge_cases i (12 - ke)).
  - rewrite G1 by lia. apply gch_0.
  - rewrite G2 by lia. apply gch_dig. apply D1. lia.
Qed.

Theorem H_spec : forall o p1 prefix pl r0 big a z e,
  TS r0 big a z e -> znth big a <> 0 -> 1 <= p1 <= 26 -> 0 <= pl -> 0 <= prefix -> prefix + pl <= 18 ->
  Forall gch (zsub PREFIX_STR prefix pl) ->
  exists txt l', g_H o 1 0 CHR_g p1 prefix pl big a r0 z e = Some (o ++ txt, pl + l') /\
    zlength txt = pl + l' /\ Forall gch txt /\ 1 <= l' <= p1 + 7.
Proof.
  intros o p1 prefix pl r0 big a z e HT NZ Hp Hpl Hpr Hpp Fpre.
  pose proof HT as (WB & LB & AZ & Z7 & ZB & R & [k (Hk & Hka & He)]).
  assert (Hr0 : 0 <= r0 <= 122) by (destruct R as [->|[-> _]]; lia).
  unfold g_H.
  destruct (strip_spec big a z ltac:(lia) ltac:(lia) NZ) as [z' (Es & Hz' & Zs & NZs)]. rewrite Es.
  change (Z.lor CHR_g 32 =? CHR_g) with true. cbv iota.
  replace (p1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (Z.land 0 ALT_FORM =? 0) with true.
  replace ((a <? z') && negb (znth big (z' - 1) =? 0)) with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Z.ltb_lt; lia| apply Bool.negb_true_iff, Z.eqb_neq; exact NZs]. }
  pose proof (WB (z' - 1)) as Wz.
  destruct (fmt_fp_tz_total (znth big (z' - 1)) ltac:(unfold NB in Wz; lia)) as [it [jt Et]]. rewrite Et.
  assert (PL : zlength (zsub PREFIX_STR prefix pl) = pl) by (apply zlength_zsub; [lia|lia| unfold PREFIX_STR, zlength; cbn [length]; lia]).
  destruct ((e <? p1) && (-4 <=? e)) eqn:CF.
  - (* [comment removed for export] *)
    apply andb_prop in CF. destruct CF as [CF1 CF2]. apply Z.ltb_lt in CF1. apply Z.leb_le in CF2.
    change (Z.lor (CHR_g - 1) 32 =? CHR_f) with true. cbv iota.
    set (p2 := Z.min (p1 - (e + 1)) (Z.max 0 (9 * (z' - r0 - 1) - jt))).
    assert (Hp2 : 0 <= p2 <= p1 - (e + 1)) by (subst p2; lia). clearbody p2.
    cbn [negb orb]. rewrite Bool.orb_false_r.
    set (palt := if negb (p2 =? 0) then 1 else 0).
    assert (Hpalt : palt = (if p2 =? 0 then 0 else 1) /\ 0 <= palt <= 1) by (subst palt; destruct (p2 =? 0); cbn; lia).
    destruct Hpalt as [Epalt Bpalt]. clearbody palt.
    replace (INT_MAX - 1 - palt <? p2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    change (CHR_g - 1) with 102. rewrite len_f_spec by lia.
    set (l2 := if 0 <? e then 1 + p2 + palt + e else 1 + p2 + palt).
    assert (Hl2 : l2 = 1 + p2 + palt + Z.max e 0 /\ 1 <= l2 <= p1 + 7) by (subst l2; destruct (Z.ltb_spec 0 e); lia).
    destruct Hl2 as [El2 Bl2]. clearbody l2.
    replace (INT_MAX - pl <? l2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
    rewrite pad_flag by (cbv; discriminate).
    change (Z.lor 102 32 =? CHR_f) with true. cbv iota.
    destruct (emit_f_spec (out o (zsub PREFIX_STR prefix pl)) big a r0 z' p2 k WB) as [txt (Ef & Ff & Lf)]; try lia.
    { intros Hra. apply ZB. lia. }
    { right. split; [lia| exact Hka]. }
    rewrite Ef. rewrite pad_flag by (cbv; discriminate).
    exists (zsub PREFIX_STR prefix pl ++ txt), l2. unfold out. rewrite <- app_assoc.
    split; [f_equal; f_equal; lia|]. split.
    + rewrite zlength_app, PL, Lf, El2, Epalt.
      destruct (Z.leb_spec a r0); destruct (Z.eqb_spec p2 0); lia.
    + split; [| exact Bl2]. apply Forall_app. split; [exact Fpre|]. eapply Forall_impl; [| exact Ff]. apply gch_isdigdot.
  - (* [comment removed for export] *)
    change (Z.lor (CHR_g - 2) 32 =? CHR_f) with false. cbv iota.
    set (p2 := Z.min (p1 - 1) (Z.max 0 (9 * (z' - r0 - 1) + e - jt))).
    assert (Hp2 : 0 <= p2 <= p1 - 1) by (subst p2; lia). clearbody p2.
    cbn [negb orb]. rewrite Bool.orb_false_r.
    set (palt := if negb (p2 =? 0) then 1 else 0).
    assert (Hpalt : palt = (if p2 =? 0 then 0 else 1) /\ 0 <= palt <= 1) by (subst palt; destruct (p2 =? 0); cbn; lia).
    destruct Hpalt as [Epalt Bpalt]. clearbody palt.
    replace (INT_MAX - 1 - palt <? p2) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    change (CHR_g - 2) with 101.
    pose proof (TS_e_bound _ _ _ _ _ HT) as EB.
    destruct (len_e_spec (1 + p2 + palt) e ltac:(lia) ltac:(lia)) as [estr [eb (El & Hest & Leb & Geb)]]. rewrite El.
    replace (INT_MAX - pl <? 1 + p2 + palt + (12 - estr)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
    rewrite pad_flag by (cbv; discriminate).
    change (Z.lor 101 32 =? CHR_f) with false. cbv iota.
    destruct (emit_e_spec (out o (zsub PREFIX_STR prefix pl)) big a z' p2 eb estr k WB) as [txt (Ee & Fe & Le)]; try lia.
    { right. split; [lia| exact Hka]. }
    rewrite Ee. rewrite pad_flag by (cbv; discriminate).
    exists (zsub PREFIX_STR prefix pl ++ txt ++ zsub eb estr (12 - estr)), (1 + p2 + palt + (12 - estr)). unfold out. rewrite <- !app_assoc.
    split; [f_equal; f_equal; lia|]. split.
    + rewrite !zlength_app, PL, Le, zlength_zsub by lia. rewrite Epalt.
      destruct (Z.ltb_spec 0 p2); destruct (Z.eqb_spec p2 0); lia.
    + split; [| lia]. apply Forall_app. split; [exact Fpre|]. apply Forall_app. split; [eapply Forall_impl; [| exact Fe]; apply gch_isdigdot|].
      apply zsub_Forall; try lia. intros kk Hkk. apply Geb. lia.
Qed.
End FmtFpTail.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan FloatScanProps SoftFloatProps FmtFpDig.
Import FmtFpProps.
Import FmtFpRun.
Import FmtFpTail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_splitR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_splitR.FmtFp_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
Open Scope Z_scope.
Local Opaque zrepeat.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ffp_e_eq : ffp_e = g_e. Proof. reflexivity. Qed.
Lemma ffp_j_eq : ffp_j = g_j. Proof. reflexivity. Qed.
Lemma ffp_R_eq : ffp_R = g_R. Proof. reflexivity. Qed.
Lemma ffp_H_eq : ffp_H = g_H. Proof. reflexivity. Qed.

Lemma ffp_sign_0 : forall y, ffp_sign y 0 = if negb (signbitl y =? 0) then (Z.lxor y F128_SIGNBIT, 0, 1) else (y, 1, 0).
Proof. intros. reflexivity. Qed.

Lemma gch_numch : forall c, gch c -> is_numch c = true.
Proof.
  intros c H. unfold is_numch. unfold gch in H.
  destruct H as [H|[->|[->|[->|[->| ->]]]]]; try reflexivity.
  replace (48 <=? c) with true by (symmetry; apply Z.leb_le; lia).
  replace (c <=? 57) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fmt_fp_g_total : forall d p1, dfin d -> (p1 = 15 \/ p1 = 17) ->
  exists txt pl l', fmt_fp [] (f128_of_d d) 1 p1 0 CHR_g = Some (txt, pl + l') /\
    zlength txt = pl + l' /\ Forall gch txt /\ 0 <= pl <= 1 /\ 1 <= l' <= p1 + 7.
Proof.
  intros d p1 Hfin Hp.
  destruct (fmt_loops d p1 CHR_g Hfin ltac:(lia) ltac:(cbv; discriminate))
    as [nz [fr [e0 [y2 (C1 & C2 & C3 & C4 & REST)]]]].
  cbv zeta in REST. destruct REST as (He2 & [big [z (ED & Hz & WB & LB & ZO & W0 & ZC & [s1 (EU & HS1 & DS1 & ZS1 & [big2 [a2 [z2 (EDN & PN & PZ)]]])])]]).
  rewrite fmt_fp_split, ffp_sign_0.
  set (sb := negb (signbitl (f128_of_d d) =? 0)).
  assert (Y1 : forall prefix pl, (if sb then (Z.lxor (f128_of_d d) F128_SIGNBIT, 0, 1) else (f128_of_d d, 1, 0)) = (strip_sign (f128_of_d d), prefix, pl) ->
     exists txt l', ffp_C [] 1 0 CHR_g (strip_sign (f128_of_d d)) p1 prefix pl = Some (txt, pl + l') /\
       zlength txt = pl + l' /\ Forall gch txt /\ 1 <= l' <= p1 + 7).
  2:{ assert (SS : strip_sign (f128_of_d d) = if sb then Z.lxor (f128_of_d d) F128_SIGNBIT else f128_of_d d) by reflexivity.
      destruct sb.
      - destruct (Y1 0 1) as [txt [l' (E & L & F & B)]]; [rewrite SS; reflexivity|].
        rewrite <- SS. replace (fpclassifyl _ <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite E. exists txt, 1, l'. repeat split; auto; lia.
      - destruct (Y1 1 0) as [txt [l' (E & L & F & B)]]; [rewrite SS; reflexivity|].
        rewrite <- SS. replace (fpclassifyl _ <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
        rewrite E. exists txt, 0, l'. repeat split; auto; lia. }
  intros prefix pl EQ.
  assert (PP : (prefix = 0 /\ pl = 1) \/ (prefix = 1 /\ pl = 0)) by (destruct sb; inversion EQ; lia).
  unfold ffp_C. rewrite C2. cbv zeta. rewrite C3. unfold ffp_C2. rewrite C4.
  replace (p1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct nz.
  - (* [comment removed for export] *)
    cbv iota in ED. cbv iota.
    set (e2 := e0 - 1 - 28) in *.
    unfold ffp_D. change (128 - 5 - 1) with 122.
    set (r0 := if e2 <? 0 then 0 else 122) in *.
    rewrite ED. unfold ffp_E. rewrite EU. unfold ffp_F.
    destruct s1 as [[[b1 a1] z1] e21]. rewrite EDN.
    rewrite ffp_G_eq, ffp_e_eq, ffp_j_eq, ffp_R_eq, ffp_H_eq.
    pose proof (PN eq_refl) as PO.
    destruct (g_e_spec r0 big2 a2 z2 PO) as [e (Ee & TSe)]. rewrite Ee.
    pose proof PO as (_ & _ & _ & _ & NZa & _ & Rr).
    destruct (R_spec p1 prefix pl r0 big2 a2 z2 e TSe NZa) as [bigR [aR [zR [eR (ER & TSR & NZR & AR & ZR)]]]]; [| | lia |].
    { intros R0. destruct Rr as [[_ B]|[R1 _]]; [exact B| lia]. }
    { intros R1. destruct Rr as [[R0 _]|(_ & B & _)]; [lia| lia]. }
    cbv zeta. rewrite ER.
    destruct (H_spec [] p1 prefix pl r0 bigR aR zR eR TSR NZR) as [txt [l' (EH & L & F & B)]]; try lia.
    { destruct PP as [[-> ->]|[-> ->]]; cbn; [constructor; [unfold gch; lia| constructor] | constructor]. }
    rewrite EH. exists txt, l'. cbn. repeat split; auto; lia.
  - (* [comment removed for export] *)
    destruct (ZC eq_refl) as (E2 & Ez & Ebig). cbv iota in ED. cbv iota.
    rewrite E2 in *. change (0 <? 0) with false in *. cbv iota in ED. cbv iota.
    unfold ffp_D. change (128 - 5 - 1) with 122. change (0 <? 0) with false. cbv iota.
    rewrite ED. unfold ffp_E. rewrite EU. rewrite (HS1 ltac:(lia)). unfold ffp_F.
    rewrite (HS1 ltac:(lia)) in EDN. rewrite EDN.
    destruct (PZ eq_refl) as (-> & -> & ->).
    assert (G15a : ffp_G [] 1 0 CHR_g 15 0 1 (zrepeat 0 128) 122 122 123 = Some ([45; 48], 2)) by (vm_compute; reflexivity).
    assert (G15b : ffp_G [] 1 0 CHR_g 15 1 0 (zrepeat 0 128) 122 122 123 = Some ([48], 1)) by (vm_compute; reflexivity).
    assert (G17a : ffp_G [] 1 0 CHR_g 17 0 1 (zrepeat 0 128) 122 122 123 = Some ([45; 48], 2)) by (vm_compute; reflexivity).
    assert (G17b : ffp_G [] 1 0 CHR_g 17 1 0 (zrepeat 0 128) 122 122 123 = Some ([48], 1)) by (vm_compute; reflexivity).
    destruct Hp as [-> | ->]; destruct PP as [[-> ->]|[-> ->]].
    + rewrite G15a. exists [45; 48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G15b. exists [48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G17a. exists [45; 48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
    + rewrite G17b. exists [48], 1. repeat split; try (cbn; lia). repeat constructor; unfold gch; lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_fp_g_some_dfin : forall o d w p fl t r, fmt_fp o (f128_of_d d) w p fl t = Some r -> dfin d.
Proof.
  intros o d w p fl t r H. unfold dfin. intros E.
  pose proof (fpclassifyl_infnan d E) as C.
  rewrite fmt_fp_split in H.
  assert (S1 : fst (fst (ffp_sign (f128_of_d d) fl)) = strip_sign (f128_of_d d)).
  { unfold ffp_sign, strip_sign. destruct (negb (signbitl (f128_of_d d) =? 0)); [reflexivity|].
    destruct (negb (Z.land fl MARK_POS =? 0)); [reflexivity|]. destruct (negb (Z.land fl PAD_POS =? 0)); reflexivity. }
  destruct (ffp_sign (f128_of_d d) fl) as [[y1 prefix] pl]. cbn [fst] in S1. subst y1.
  replace (fpclassifyl (strip_sign (f128_of_d d)) <=? 1) with true in H by (symmetry; apply Z.leb_le; exact C).
  discriminate H.
Qed.

Theorem fmt_g_total : forall d p1, dfin d -> (p1 = 15 \/ p1 = 17) ->
  exists txt, fmt_g d p1 = Some (txt, zlength txt) /\ Forall gch txt /\ zlength txt <= p1 + 8.
Proof.
  intros d p1 Hfin Hp. unfold fmt_g.
  destruct (fmt_fp_g_total d p1 Hfin Hp) as [txt [pl [l' (E & L & F & B1 & B2)]]]. rewrite E.
  replace (pl + l' <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  exists txt. split; [reflexivity|]. split; [exact F| lia].
Qed.

Lemma fmt_g_some_dfin : forall d p r, fmt_g d p = Some r -> dfin d.
Proof.
  intros d p r H. unfold fmt_g in H.
  destruct (fmt_fp [] (f128_of_d d) 1 p 0 CHR_g) as [[o l]|] eqn:E; [| discriminate H].
  eapply fmt_fp_g_some_dfin. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fmt_d_spec : forall x,
  exists o, fmt_d x = Some (o, zlength o) /\ Forall gch o /\ zlength o <= 22 /\
    (- 2^31 <= x < 2^31 -> zlength o <= 11).
Proof.
  intros x. unfold fmt_d.
  change (Z.land 0 MARK_POS =? 0) with true. change (Z.land 0 PAD_POS =? 0) with true. cbn [negb].
  pose proof (u64_range x) as U.
  set (ap := if INTMAX_MAX <? u64 x then (u64 (- u64 x), 0, 1) else (u64 x, 0, 0)).
  assert (AP : exists argi pl, ap = (argi, 0, pl) /\ 0 <= argi < 2^64 /\ 0 <= pl <= 1 /\
            (- 2^31 <= x < 2^31 -> argi <= 2^31)).
  { subst ap. unfold INTMAX_MAX. destruct (Z.ltb_spec 9223372036854775807 (u64 x)).
    - eexists _, _. split; [reflexivity|]. pose proof (u64_range (- u64 x)). split; [lia|]. split; [lia|].
      intros Hx. unfold u64 in *. dlia.
    - eexists _, _. split; [reflexivity|]. split; [lia|]. split; [lia|]. intros Hx. unfold u64 in *. dlia. }
  destruct AP as [argi [pl (-> & Ha & Hpl & Hsmall)]].
  destruct (DIGk_exists argi 20 ltac:(change (10^20) with 100000000000000000000; lia) ltac:(lia)) as [k [Dk Hk]].
  destruct (fmt_u_spec argi (zrepeat 0 24) 24 k ltac:(lia) Dk ltac:(lia)) as [b1 (E1 & L1 & D1 & U1)].
  { rewrite zlength_zrepeat; lia. }
  rewrite E1. rewrite zlength_zrepeat in L1 by lia.
  change (-1 =? 0) with false. rewrite Bool.andb_false_r.
  set (p0 := Z.max (-1) (24 - (24 - k) + (if argi =? 0 then 1 else 0))).
  assert (Hp0 : p0 = k + (if argi =? 0 then 1 else 0) /\ 1 <= p0 <= 21 /\ k <= p0).
  { subst p0. destruct (Z.eqb_spec argi 0).
    - destruct Dk as [[_ ->]|[? ?]]; [lia|]. subst argi. pose proof (pow10_pos (k-1)). lia.
    - destruct Dk as [[? _]|[? ?]]; [lia|]. lia. }
  destruct Hp0 as (Ep0 & Bp0 & Kp0). clearbody p0.
  replace (p0 <? 24 - (24 - k)) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (0 <? pl + p0) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite pad_exact by lia. rewrite zrepeat_nil by lia. rewrite app_nil_r.
  rewrite pad_flag by (cbv; discriminate).
  rewrite pad_exact by lia.
  rewrite pad_flag by (cbv; discriminate).
  set (pre := zsub PREFIX_D 0 pl).
  assert (PRE : zlength pre = pl /\ Forall gch pre).
  { subst pre. split; [apply zlength_zsub; [lia|lia| unfold PREFIX_D, zlength; cbn [length]; lia]|].
    apply zsub_Forall; [lia|lia| unfold PREFIX_D, zlength; cbn [length]; lia|].
    intros kk Hkk. replace kk with 0 by lia. change (znth PREFIX_D 0) with 45. unfold gch. lia. }
  destruct PRE as [Lpre Fpre]. clearbody pre.
  replace (FmtFp.INT_MAX - pl <? p0) with false by (symmetry; apply Z.ltb_ge; unfold FmtFp.INT_MAX; lia).
  replace (FmtFp.INT_MAX - 0 <? pl + p0) with false by (symmetry; apply Z.ltb_ge; unfold FmtFp.INT_MAX; lia).
  assert (LD : zlength (zsub b1 (24 - k) (24 - (24 - k))) = k) by (rewrite zlength_zsub by lia; lia).
  assert (FD : Forall gch (zsub b1 (24 - k) (24 - (24 - k)))).
  { apply zsub_Forall; try lia. intros i Hi. apply gch_dig. apply D1. lia. }
  exists (pre ++ zrepeat CHR_0 (p0 - (24 - (24 - k))) ++ zsub b1 (24 - k) (24 - (24 - k))). unfold out. cbn [app].
  split.
  { rewrite <- app_assoc. f_equal. f_equal. rewrite !zlength_app, zlength_zrepeat', Lpre, LD. lia. }
  split.
  { apply Forall_app. split; [exact Fpre|]. apply Forall_app. split; [apply Forall_zrepeat; apply gch_0| exact FD]. }
  rewrite !zlength_app, zlength_zrepeat', Lpre, LD. split; [lia|].
  intros Hx. specialize (Hsmall Hx).
  assert (k <= 10). { destruct Dk as [[? ->]|[? [LO ?]]]; [lia|]. destruct (Z.le_gt_cases k 10); [lia|]. exfalso.
    assert (10 ^ 10 <= 10 ^ (k - 1)) by (apply Z.pow_le_mono_r; lia). change (10^10) with 10000000000 in *. lia. }
  destruct (Z.eqb_spec argi 0).
  - destruct Dk as [[_ K0]|[K1 [LO _]]]; [lia|]. subst argi. pose proof (pow10_pos (k-1) ltac:(lia)). lia.
  - lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma is_numch_byte : forall c, is_numch c = true -> 0 <= c < 256.
Proof.
  intros c H. unfold is_numch in H.
  repeat (apply Bool.orb_true_iff in H; destruct H as [H|H]); try (apply Z.eqb_eq in H; lia).
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma is_numch_nox : forall c, is_numch c = true -> c <> 120 /\ c <> 88.
Proof.
  intros c H. unfold is_numch in H.
  repeat (apply Bool.orb_true_iff in H; destruct H as [H|H]); try (apply Z.eqb_eq in H; lia).
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* [comment removed for export] *)
Definition scan_strtod_total_stmt : Prop := forall l,
  (length l <= 63)%nat -> Forall (fun c => is_numch c = true) l ->
  scan_strtod (l ++ [0]) <> None.
Theorem scan_strtod_total_proof : scan_strtod_total_stmt.
Proof.
  intros l _ F.
  destruct (scan_strtod_total_gen l) as [vd [c [E _]]].
  - eapply Forall_impl; [|exact F]. intros a Ha. exact (is_numch_byte a Ha).
  - eapply Forall_impl; [|exact F]. intros a Ha. exact (is_numch_nox a Ha).
  - rewrite E. discriminate.
Qed.

(* [comment removed for export] *)
Definition is_nan_or_inf (d : word) : bool := 0x7FF0000000000000 <=? bv_unsigned (fabs_d d).

Lemma not_nan_inf_dfin : forall vd, is_nan_or_inf (Z_to_bv 64 vd) = false -> dfin vd.
Proof.
  intros vd H. unfold is_nan_or_inf, fabs_d in H. rewrite !Z_to_bv_unsigned in H.
  change (bv_wrap 64 vd) with (vd mod 2^64) in H.
  rewrite Z.land_ones in H by lia.
  match type of H with (_ <=? bv_wrap 64 ?v) = false => change (bv_wrap 64 v) with (v mod 2^64) in H end.
  apply Z.leb_gt in H.
  pose proof (Z.mod_pos_bound vd (2^64) ltac:(lia)) as B.
  rewrite (Z.mod_small ((vd mod 2^64) mod 2^63)) in H by (pose proof (Z.mod_pos_bound (vd mod 2^64) (2^63)); lia).
  unfold dfin, d_exp. intros E. dlia.
Qed.

Lemma gch_Forall_bytes : forall txt, Forall gch txt -> Forall (fun c => 0 <= c < 256) txt /\ Forall (fun c => c <> 120 /\ c <> 88) txt.
Proof.
  intros txt F. split; (eapply Forall_impl; [| exact F]); intros c Hc; unfold gch in Hc; lia.
Qed.

