(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BigModel BigFactsBase BigFactsOps BigDivLemmas L5Words L5Shl L5Norm L5DivSpecs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5OM1V.
Import L5W.

Definition A0 : Z := L5DivSpecs.L5DS.A0.
Definition A1 : Z := L5DivSpecs.L5DS.A1.
Lemma A0_val : A0 = 0x16af9c0daf145395. Proof. reflexivity. Qed.
Lemma A1_val : A1 = 0x2a9f3636273caaf2. Proof. reflexivity. Qed.
Lemma MM_val : W.M = 2 ^ 64. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma val2 x y : BigFactsBase.val [x; y] = x + 2 ^ 64 * y.
Proof. cbn [BigFactsBase.val]. rewrite MM_val. lia. Qed.
Lemma val3 x y z : BigFactsBase.val [x; y; z] = x + 2 ^ 64 * y + 2 ^ 128 * z.
Proof. cbn [BigFactsBase.val]. rewrite MM_val. lia. Qed.

Lemma words_ok_nth' ws j : words_ok ws -> 0 <= nth_w ws j < 2 ^ 64.
Proof. apply words_ok_nth. Qed.
Lemma words_ok_firstn' k ws : words_ok ws -> words_ok (firstn k ws).
Proof. revert k. induction ws as [|w ws IH]; intros [|k] W; cbn; try constructor. inversion W; subst. exact H1. apply IH. inversion W; subst. exact H2. Qed.

(* [comment removed for export] *)
Lemma val_skipn_zero ws k : (forall i, (k <= i < length ws)%nat -> nth_w ws i = 0) -> BigFactsBase.val (skipn k ws) = 0.
Proof.
  revert k. induction ws as [|w ws IH]; intros k Hz. rewrite skipn_nil. reflexivity.
  destruct k as [|k].
  - cbn [skipn]. cbn [BigFactsBase.val]. pose proof (Hz 0%nat ltac:(cbn; lia)) as H0. cbn in H0. rewrite H0. pose proof (IH 0%nat) as I0. change (skipn 0 ws) with ws in I0. rewrite I0. lia.
    intros i Hi. exact (Hz (S i) ltac:(cbn in Hi |- *; lia)).
  - cbn [skipn]. apply IH. intros i Hi. exact (Hz (S i) ltac:(cbn in Hi |- *; lia)).
Qed.
Lemma val_rlen ws : BigFactsBase.val ws = BigFactsBase.val (firstn (rlen ws) ws).
Proof.
  rewrite (BigFactsBase.val_firstn_skipn (rlen ws) ws) at 1. rewrite (val_skipn_zero ws (rlen ws)). lia.
  intros i Hi. apply rlen_zeros. exact Hi.
Qed.
Lemma val_lt_pow ws k : words_ok ws -> (length ws <= k)%nat -> BigFactsBase.val ws < 2 ^ (64 * Z.of_nat k).
Proof.
  intros W Hk. pose proof (BigFactsBase.val_bound ws ltac:(apply (proj1 (words_ok_BF ws)); exact W)) as [_ B]. rewrite MM_val in B.
  rewrite <- Z.pow_mul_r in B by lia. assert (2 ^ (64 * Z.of_nat (length ws)) <= 2 ^ (64 * Z.of_nat k)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
(* [comment removed for export] *)
Lemma rlen_ge_of_val ws k : words_ok ws -> 2 ^ (64 * Z.of_nat k) <= BigFactsBase.val ws -> (k < rlen ws)%nat.
Proof.
  intros W V. destruct (Nat.lt_ge_cases k (rlen ws)) as [H|H]. exact H. exfalso.
  rewrite val_rlen in V. pose proof (val_lt_pow (firstn (rlen ws) ws) k ltac:(apply words_ok_firstn'; exact W) ltac:(rewrite length_firstn; pose proof (rlen_le ws); lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma limbs3_of_val w0 w1 w2 P : 0 <= w0 < 2 ^ 64 -> 0 <= w1 < 2 ^ 64 -> 0 <= w2 < 2 ^ 64 ->
  w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 = P -> w0 = P mod 2 ^ 64 /\ w1 = (P / 2 ^ 64) mod 2 ^ 64 /\ w2 = (P / 2 ^ 128) mod 2 ^ 64.
Proof.
  intros H0 H1 H2 E. subst P.
  assert (E1: (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) / 2 ^ 64 = w1 + 2 ^ 64 * w2).
  { replace (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) with (w0 + (w1 + 2 ^ 64 * w2) * 2 ^ 64) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (E2: (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) / 2 ^ 128 = w2).
  { replace (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) with ((w0 + 2 ^ 64 * w1) + w2 * 2 ^ 128) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  rewrite E1, E2. split. { replace (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2) with (w0 + (w1 + 2 ^ 64 * w2) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry; apply Z.mod_small; lia. }
  split. { replace (w1 + 2 ^ 64 * w2) with (w1 + w2 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry; apply Z.mod_small; lia. }
  symmetry; apply Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
Lemma shl_words_1 x c : 0 <= x < 2 ^ 64 -> 0 < c < 64 -> x * 2 ^ c < 2 ^ 64 -> shl_words [x] c = [x * 2 ^ c; 0].
Proof.
  intros Hx Hc Hov. unfold shl_words. cbn [length seq map app].
  assert (W2: BigFactsBase.words_ok [x; 0]). { apply (proj1 (words_ok_BF _)). constructor. lia. constructor. lia. constructor. }
  pose proof (BigFactsOps.shlG_val c Hc [x; 0] 0 W2) as [E0 _]. pose proof (BigFactsOps.shlG_val c Hc [x; 0] 1 W2) as [E1 _].
  rewrite E0, E1. cbn [nth_w BigModel.nth_w nth Nat.ltb Nat.leb Nat.sub]. unfold W.shl, W.wrap. rewrite MM_val.
  rewrite Z.mod_small by lia. rewrite Z.mul_0_l, Z.mod_0_l by lia. rewrite Z.div_small. rewrite !Z.add_0_r. reflexivity.
  split. lia. replace 64 with ((64 - c) + c) in Hov by lia. rewrite Z.pow_add_r in Hov by lia. nia.
Qed.
Lemma shl_words_2 x y c : 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 < c < 64 -> y * 2 ^ c < 2 ^ 64 ->
  shl_words [x; y] c = [(x * 2 ^ c) mod 2 ^ 64; y * 2 ^ c + x / 2 ^ (64 - c); 0]
  /\ 0 <= x / 2 ^ (64 - c) < 2 ^ c /\ y * 2 ^ c + x / 2 ^ (64 - c) < 2 ^ 64.
Proof.
  intros Hx Hy Hc Hov.
  assert (Hy2: 0 <= y * 2 ^ c < 2 ^ 64). { pose proof (Z.pow_pos_nonneg 2 c). nia. }
  assert (Hyd: y / 2 ^ (64 - c) = 0).
  { apply Z.div_small. split. lia. replace 64 with ((64 - c) + c) in Hov by lia. rewrite Z.pow_add_r in Hov by lia. pose proof (Z.pow_pos_nonneg 2 c). nia. }
  unfold shl_words. cbn [length seq map app].
  assert (W3: BigFactsBase.words_ok [x; y; 0]). { apply (proj1 (words_ok_BF _)). constructor. lia. constructor. lia. constructor. lia. constructor. }
  pose proof (BigFactsOps.shlG_val c Hc [x; y; 0] 0 W3) as [E0 _]. pose proof (BigFactsOps.shlG_val c Hc [x; y; 0] 1 W3) as [E1 R1].
  pose proof (BigFactsOps.shlG_val c Hc [x; y; 0] 2 W3) as [E2 _].
  pose proof (BigFactsOps.shl_decomp c Hc x ltac:(unfold BigFactsBase.wordZ; rewrite MM_val; lia)) as (_ & _ & XR).
  rewrite E1 in R1.
  rewrite E0, E1, E2. clear E0 E1 E2. cbn [nth_w BigModel.nth_w nth Nat.ltb Nat.leb Nat.sub] in R1 |- *. unfold W.shl, W.wrap, BigFactsBase.wordZ in R1 |- *. rewrite MM_val in R1 |- *.
  rewrite (Z.mod_small (y * 2 ^ c)) in R1 |- * by exact Hy2. rewrite Z.mul_0_l, Z.mod_0_l by (clear; lia). rewrite Hyd.
  rewrite Z.add_0_r. split. reflexivity. split. exact XR. clear - R1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section O1.
Variables (nb : nat) (b0 b1 : Z) (wb : list Z).
Hypothesis NB : nb = 1%nat \/ nb = 2%nat.
Hypothesis WB : wb = firstn nb [b0; b1].
Hypothesis Rb0 : 0 <= b0 < 2 ^ 64.
Hypothesis Rb1 : 0 <= b1 < 2 ^ 64.
Hypothesis TOPNZ : nth_w wb (nb - 1) <> 0.
Hypothesis V1 : nb = 1%nat -> 2 ^ 32 <= b0.
Hypothesis V2 : nb = 2%nat -> BigFactsBase.val wb <= BigFactsBase.val [A0; A1].

Definition top : Z := nth_w wb (nb - 1).
Definition c : Z := L5NORM.clz_of top.
Definition D : list Z := L5SHL.shl_result wb c.
Definition sec : bool := L5NORM.second nb D.
Definition rwd : list Z := L5NORM.norm_words wb c sec.
Definition N : list Z := L5SHL.shl_result [A0; A1] c.
Definition rwn : list Z := L5NORM.norm_words [A0; A1] c sec.
Definition l1 : nat := rlen rwd.   (* [comment removed for export] *)
Definition n1 : nat := rlen rwn.   (* [comment removed for export] *)

Lemma top_range : 1 <= top < 2 ^ 64.
Proof.
  unfold top. pose proof TOPNZ as T. rewrite WB in T |- *. destruct NB as [E|E]; rewrite E in T |- *; cbn [firstn nth_w nth Nat.sub] in T |- *; lia.
Qed.
Lemma c_spec : 0 <= c <= 63 /\ 2 ^ 63 <= top * 2 ^ c < 2 ^ 64.
Proof. unfold c. apply L5NORM.clz_of_spec. apply top_range. Qed.
Lemma b1_small : nb = 2%nat -> b1 < 2 ^ 62.
Proof using nb b0 b1 wb NB WB Rb0 Rb1 V1 V2.
  intros H2. pose proof (V2 H2) as V. rewrite WB, H2 in V. cbn [firstn] in V. rewrite !val2 in V. rewrite A0_val, A1_val in V. lia.
Qed.
Lemma c_pos2 : nb = 2%nat -> 2 <= c.
Proof.
  intros H2. pose proof c_spec as [Hc Hp]. pose proof (b1_small H2) as B1. unfold top in Hp. rewrite WB, H2 in Hp. cbn [firstn nth_w nth Nat.sub] in Hp.
  destruct (Z_lt_le_dec c 2) as [L|L]; [|exact L]. exfalso.
  assert (2 ^ c <= 2) by (replace 2 with (2 ^ 1) at 2 by reflexivity; apply Z.pow_le_mono_r; lia). nia.
Qed.
Lemma c_small1 : nb = 1%nat -> c <= 31.
Proof.
  intros H1. pose proof c_spec as [Hc Hp]. pose proof (V1 H1) as B0. unfold top in Hp. rewrite WB, H1 in Hp. cbn [firstn nth_w nth Nat.sub] in Hp.
  destruct (Z_lt_le_dec 31 c) as [L|L]; [|exact L]. exfalso.
  assert (2 ^ 32 <= 2 ^ c) by (apply Z.pow_le_mono_r; lia). nia.
Qed.

(* [comment removed for export] *)
Lemma N_shape :
  (c = 0 /\ N = [A0; A1]) \/
  (1 <= c <= 63 /\ N = [(A0 * 2 ^ c) mod 2 ^ 64; A1 * 2 ^ c + A0 / 2 ^ (64 - c); 0] /\ 0 <= A0 / 2 ^ (64 - c) < 2 ^ c /\ A1 * 2 ^ c + A0 / 2 ^ (64 - c) < 2 ^ 64
   /\ A1 * 2 ^ c < 2 ^ 64) \/
  (1 <= c <= 63 /\ exists h, N = [(A0 * 2 ^ c) mod 2 ^ 64; (A1 * 2 ^ c) mod 2 ^ 64 + A0 / 2 ^ (64 - c); h] /\ 0 <= h < 2 ^ 64).
Proof.
  pose proof c_spec as [Hc _]. unfold N, L5SHL.shl_result. destruct (Z.eqb_spec c 0) as [E|NE]. left. split. exact E. reflexivity.
  right. right. split. lia.
  assert (W3: BigFactsBase.words_ok [A0; A1; 0]). { rewrite A0_val, A1_val. apply (proj1 (words_ok_BF _)). constructor. lia. constructor. lia. constructor. lia. constructor. }
  assert (Hc' : 0 < c < 64) by lia.
  pose proof (BigFactsOps.shlG_val c Hc' [A0; A1; 0] 0 W3) as [E0 _]. pose proof (BigFactsOps.shlG_val c Hc' [A0; A1; 0] 1 W3) as [E1 _].
  pose proof (BigFactsOps.shlG_val c Hc' [A0; A1; 0] 2 W3) as [E2 R2].
  exists (BigFactsOps.shlG c [A0; A1; 0] 2). unfold shl_words. cbn [length seq map app]. rewrite E0, E1.
  cbn [nth_w BigModel.nth_w nth Nat.ltb Nat.leb Nat.sub]. unfold W.shl, W.wrap. rewrite MM_val. rewrite Z.add_0_r. split. reflexivity.
  unfold BigFactsBase.wordZ in R2. rewrite MM_val in R2. exact R2.
Qed.
Lemma N_len : length N = (if (c =? 0)%Z then 2%nat else 3%nat).
Proof. unfold N, L5SHL.shl_result. destruct (c =? 0). reflexivity. rewrite shl_words_length. reflexivity. Qed.
Lemma N_ok : words_ok N.
Proof.
  pose proof c_spec as [Hc _]. unfold N, L5SHL.shl_result. destruct (Z.eqb_spec c 0). rewrite A0_val, A1_val. repeat constructor; lia.
  apply shl_words_ok. lia. rewrite A0_val, A1_val. repeat constructor; lia.
Qed.
Lemma N_val : BigFactsBase.val N = 2 ^ c * BigFactsBase.val [A0; A1].
Proof.
  pose proof c_spec as [Hc _]. unfold N, L5SHL.shl_result. destruct (Z.eqb_spec c 0) as [->|NE]. lia.
  apply shl_words_val. lia. rewrite A0_val, A1_val. repeat constructor; lia.
Qed.
Lemma N_rlen : (2 <= rlen N <= 3)%nat.
Proof.
  pose proof c_spec as [Hc _]. split.
  - assert (LT: (1 < rlen N)%nat). 2: lia.
    apply rlen_ge_of_val. apply N_ok. rewrite N_val, val2, A0_val, A1_val. assert (1 <= 2 ^ c) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) in Hc || pose proof (Z.pow_pos_nonneg 2 c); lia). nia.
  - pose proof (rlen_le N) as RL. rewrite N_len in RL. destruct (c =? 0); lia.
Qed.

(* [comment removed for export] *)
Lemma D_facts :
  (* [comment removed for export] *)
  (nb = 1%nat /\ sec = false /\ rwd = D /\ (length D <= 2)%nat /\ rlen D = 1%nat /\ nth_w D 0 = b0 * 2 ^ c /\ 2 ^ 63 <= b0 * 2 ^ c < 2 ^ 64)
  \/ (* [comment removed for export] *)
  (nb = 2%nat /\ sec = false /\ 2 <= c /\ rwd = D /\ length D = 3%nat /\ rlen D = 2%nat /\ 2 ^ 63 <= nth_w D 1 < 2 ^ 64)
  \/ (* [comment removed for export] *)
  (nb = 2%nat /\ sec = true /\ 2 <= c /\ length D = 3%nat /\ rlen D = 2%nat /\ 2 ^ 63 <= nth_w D 1 < 2 ^ 64 /\ 0 <= nth_w D 1 < nth_w D 0 /\ nth_w D 0 < 2 ^ 64
      /\ rwd = mulw_words [nth_w D 0; nth_w D 1] L5NORM.MAXW /\ length rwd = 3%nat /\ rlen rwd = 3%nat
      /\ nth_w rwd 0 = 2 ^ 64 - nth_w D 0 /\ nth_w rwd 1 = nth_w D 0 - nth_w D 1 - 1 /\ nth_w rwd 2 = nth_w D 1).
Proof.
  pose proof c_spec as [Hc Hp]. unfold top in Hp. pose proof WB as WB'.
  destruct NB as [H1|H2].
  - left. rewrite H1 in WB'. cbn [firstn] in WB'. rewrite WB', H1 in Hp. cbn [firstn nth_w nth Nat.sub] in Hp.
    assert (DD: D = (if c =? 0 then [b0] else [b0 * 2 ^ c; 0])).
    { unfold D, L5SHL.shl_result. rewrite WB'. destruct (Z.eqb_spec c 0). reflexivity. apply shl_words_1. exact Rb0. lia. lia. }
    assert (SEC: sec = false). { unfold sec, L5NORM.second. rewrite H1. reflexivity. }
    split. exact H1. split. exact SEC. split. { unfold rwd, L5NORM.norm_words. fold D. fold sec. rewrite SEC. reflexivity. }
    rewrite DD. destruct (Z.eqb_spec c 0) as [E|NE].
    + rewrite E in Hp |- *. rewrite Z.pow_0_r, Z.mul_1_r in Hp |- *. split. cbn; lia. split. apply rlen_charact. cbn; lia. intros i Hi; cbn in Hi; lia. right. cbn. lia.
      split. reflexivity. exact Hp.
    + split. cbn; lia. split. apply rlen_charact. cbn; lia. { intros i Hi. cbn in Hi. replace i with 1%nat by lia. reflexivity. } right. cbn [nth_w nth Nat.sub]. lia.
      split. reflexivity. exact Hp.
  - right. rewrite H2 in WB'. cbn [firstn] in WB'. pose proof (c_pos2 H2) as C2. rewrite WB', H2 in Hp. cbn [firstn nth_w nth Nat.sub] in Hp.
    destruct (shl_words_2 b0 b1 c Rb0 Rb1 ltac:(lia) ltac:(clear -Hp Rb1 Rb0 Hc; nia)) as (SW & XR & SUM).
    assert (DD: D = [(b0 * 2 ^ c) mod 2 ^ 64; b1 * 2 ^ c + b0 / 2 ^ (64 - c); 0]).
    { unfold D, L5SHL.shl_result. rewrite WB'. destruct (Z.eqb_spec c 0). exfalso; lia. exact SW. }
    clear SW.
    assert (D0r: 0 <= nth_w D 0 < 2 ^ 64). { rewrite DD. cbn [nth_w nth]. apply Z.mod_pos_bound. lia. }
    assert (D1r: 2 ^ 63 <= nth_w D 1 < 2 ^ 64). { rewrite DD. cbn [nth_w nth]. clear DD. lia. }
    assert (LD: length D = 3%nat). { rewrite DD. reflexivity. }
    assert (RD: rlen D = 2%nat). { apply rlen_charact. rewrite LD; lia. { intros i Hi. rewrite LD in Hi. replace i with 2%nat by lia. rewrite DD. reflexivity. } right. cbn [Nat.sub]. lia. }
    assert (F2: firstn 2 D = [nth_w D 0; nth_w D 1]). { rewrite DD. reflexivity. }
    assert (SEC: sec = (nth_w D 1 <? nth_w D 0)). { unfold sec, L5NORM.second. rewrite H2. reflexivity. }
    assert (RWD: rwd = if sec then mulw_words [nth_w D 0; nth_w D 1] L5NORM.MAXW else D).
    { unfold rwd, L5NORM.norm_words. cbv zeta. fold D. rewrite RD, F2. reflexivity. }
    clear XR SUM DD. revert SEC RWD. destruct sec; intros SEC RWD.
    + right. assert (LT: nth_w D 1 < nth_w D 0). { symmetry in SEC. apply Z.ltb_lt. exact SEC. } clear SEC.
      rewrite RWD. clear RWD. set (P := mulw_words [nth_w D 0; nth_w D 1] L5NORM.MAXW).
      assert (LP: length P = 3%nat). { subst P. rewrite mulw_words_length. reflexivity. }
      assert (OP: words_ok P). { subst P. apply mulw_words_ok. constructor. lia. constructor. lia. constructor. unfold L5NORM.MAXW; lia. }
      assert (VP: BigFactsBase.val P = (nth_w D 0 + nth_w D 1 * BDV.MM) * (BDV.MM - 1)). { subst P. rewrite mulw_words_val, val2. unfold L5NORM.MAXW, BDV.MM. lia. }
      destruct P as [|p0 [|p1 [|p2 [|? ?]]]]; try discriminate LP.
      pose proof (words_ok_nth' _ 0 OP) as R0. pose proof (words_ok_nth' _ 1 OP) as R1. pose proof (words_ok_nth' _ 2 OP) as R2'. cbn [nth_w nth] in R0, R1, R2'.
      rewrite val3 in VP.
      destruct (BDV.mul_max_word_2_limbs (nth_w D 0) (nth_w D 1) ltac:(clear -LT D1r; lia) ltac:(clear -D0r; unfold BDV.MM; lia)) as (M0 & M1 & M2 & _).
      destruct (limbs3_of_val p0 p1 p2 _ R0 R1 R2' VP) as (E0 & E1 & E2).
      unfold BDV.MM in M0, M1, M2, E0, E1, E2. replace ((2 ^ 64) ^ 2) with (2 ^ 128) in M2 by reflexivity. rewrite <- E0 in M0. rewrite <- E1 in M1. rewrite <- E2 in M2.
      clear E0 E1 E2 VP. cbn [nth_w nth length].
      assert (RP: rlen [p0; p1; p2] = 3%nat). { apply rlen_charact. cbn; lia. intros i Hi; cbn in Hi; lia. right. cbn [nth_w nth Nat.sub]. lia. }
      repeat split; try assumption; try reflexivity; lia.
    + left. repeat split; try assumption; try reflexivity; try lia.
Qed.

(* [comment removed for export] *)
Lemma rwn_facts :
  words_ok rwn /\ (length rwn <= 4)%nat /\ (2 <= n1 <= 4)%nat /\ (n1 <= length rwn)%nat
  /\ (sec = true -> (3 <= n1)%nat /\ (3 <= length rwn)%nat)
  /\ (sec = false -> rwn = N /\ (n1 <= 3)%nat)
  /\ (c = 0 -> sec = false /\ rwn = [A0; A1] /\ n1 = 2%nat)
  /\ (1 <= c -> (3 <= length rwn)%nat).
Proof.
  pose proof c_spec as [Hc _]. pose proof N_rlen as NR. pose proof N_ok as NO. pose proof N_len as NL.
  assert (SECc: c = 0 -> sec = false).
  { intros E. destruct D_facts as [(_ & S' & _)|[(_ & _ & C2 & _)|(_ & _ & C2 & _)]]. exact S'. exfalso; lia. exfalso; lia. }
  unfold rwn, n1, L5NORM.norm_words. fold N. unfold rwn, L5NORM.norm_words. fold N. destruct sec eqn:ES.
  - set (P := mulw_words (firstn (rlen N) N) L5NORM.MAXW).
    assert (LP: length P = S (rlen N)). { subst P. rewrite mulw_words_length, length_firstn. pose proof (rlen_le N). f_equal. lia. }
    assert (OP: words_ok P). { subst P. apply mulw_words_ok. apply words_ok_firstn'. exact NO. unfold L5NORM.MAXW; lia. }
    assert (RP: (3 <= rlen P)%nat).
    { assert (LT: (2 < rlen P)%nat). 2: lia. apply rlen_ge_of_val. exact OP. subst P. rewrite mulw_words_val, <- val_rlen, N_val, val2, A0_val, A1_val.
      assert (1 <= 2 ^ c) by (pose proof (Z.pow_pos_nonneg 2 c); lia). unfold L5NORM.MAXW. nia. }
    pose proof (rlen_le P) as RL.
    split. exact OP. split. lia. split. lia. split. lia. split. intros _; lia. split. intros F; discriminate F. split. intros E. pose proof (SECc E). congruence. intros _. lia.
  - split. exact NO. split. rewrite NL; destruct (c =? 0); lia. split. { pose proof (rlen_le N). rewrite NL in H. split. lia. destruct (c =? 0); lia. }
    split. apply rlen_le. split. intros F; discriminate F. split. { intros _. split. reflexivity. pose proof (rlen_le N). rewrite NL in H. destruct (c =? 0); lia. }
    split. { intros E. split. reflexivity. unfold N, L5SHL.shl_result. rewrite (proj2 (Z.eqb_eq c 0) E). split. reflexivity.
             apply rlen_charact. cbn; lia. intros i Hi; cbn in Hi; lia. right. rewrite A1_val. cbn. lia. }
    intros C1. rewrite NL. destruct (Z.eqb_spec c 0); lia.
Qed.

(* [comment removed for export] *)
Lemma norm_facts :
  (1 <= l1 <= 3)%nat /\ (2 <= n1 <= 4)%nat /\ (l1 <= n1)%nat /\ (n1 - l1 <= 2)%nat
  /\ (l1 <= length rwd)%nat /\ (length rwd <= 3)%nat /\ (n1 <= length rwn)%nat /\ (length rwn <= 4)%nat
  /\ 2 ^ 63 <= nth_w rwd (l1 - 1) < 2 ^ 64
  /\ (sec = true -> nb = 2%nat /\ l1 = 3%nat /\ (3 <= n1)%nat /\ length rwd = 3%nat /\ (3 <= length rwn)%nat)
  /\ (sec = false -> l1 = nb /\ (n1 <= 3)%nat)
  /\ ((3 <= length rwd)%nat <-> nb = 2%nat)
  /\ ((3 <= length rwn)%nat <-> 1 <= c)
  /\ (nb = 2%nat -> 1 <= c).
Proof.
  pose proof c_spec as [Hc _].
  destruct rwn_facts as (NO & NL4 & N24 & NLE & NSEC & NNSEC & NC0 & NC1).
  unfold l1. destruct D_facts as [(H1 & SEC & RW & LD & RD & D0 & DP)|[(H2 & SEC & C2 & RW & LD & RD & DP)|(H2 & SEC & C2 & LD & RD & DP & LT & D0R & RW & LRW & RRW & W0 & W1 & W2)]].
  all: pose proof (rlen_le D) as RLD; pose proof (rlen_le rwn) as RLN.
  all: assert (CL: (3 <= length rwn)%nat -> 1 <= c) by (intros L3; destruct (Z.eq_dec c 0) as [E|NE]; [destruct (NC0 E) as (_ & E2 & _); rewrite E2 in L3; cbn in L3; exfalso; lia | lia]).
  - rewrite RW, RD, SEC in *. destruct (NNSEC eq_refl) as [_ N3]. cbn [Nat.sub]. rewrite D0.
    repeat split; first [lia | (intros F; discriminate F) | exact CL | (intros; apply NC1; lia) | (intros; exfalso; lia)].
  - rewrite RW, RD, SEC in *. destruct (NNSEC eq_refl) as [_ N3]. cbn [Nat.sub].
    repeat split; first [lia | (intros F; discriminate F) | exact CL | (intros; apply NC1; lia) | (intros; exfalso; lia) | (intros; lia)].
  - rewrite SEC, RRW, LRW in *. destruct (NSEC eq_refl) as [N3 L3]. cbn [Nat.sub]. rewrite W2.
    repeat split; first [lia | (intros F; discriminate F) | exact CL | (intros; apply NC1; lia) | (intros; exfalso; lia) | (intros; lia)].
Qed.

End O1.
End L5OM1V.
