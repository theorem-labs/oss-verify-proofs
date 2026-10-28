(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats ZdHufX1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require FseNCountRT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section X2.
  Variables (ws rank : list Z) (tl T : Z).
  Hypothesis OK : huf_stats_ok ws rank tl.
  Hypothesis TT : tl <= T <= 12.

  Definition xs1 (w : Z) : Z := xsym rank w - Znth 0 rank.
  Definition rv0 (w : Z) : Z := 2^(T - tl) * xcur rank w.
  Definition rvc (c w : Z) : Z := rv0 w / 2^c.

  Let TLR : 1 <= tl <= 12. Proof. destruct OK as (H & _). exact H. Qed.

  (* [comment removed for export] *)
  Lemma xs1_1 : xs1 1 = 0.
  Proof. unfold xs1, xsym. change (Z.to_nat 1) with 1%nat. cbn [psum]. change (Z.of_nat 0) with 0. lia. Qed.
  Lemma xs1_step w : 1 <= w -> xs1 (w + 1) = xs1 w + Znth w rank.
  Proof. intros Hw. unfold xs1. rewrite (xsym_step rank w) by lia. lia. Qed.
  Lemma xs1_mono w w' : 1 <= w <= w' -> w' <= 13 -> xs1 w <= xs1 w'.
  Proof. intros H1 H2. unfold xs1. pose proof (xsym_mono ws rank tl OK w w' ltac:(lia) H2). lia. Qed.
  Lemma xs1_top : xs1 13 + Znth 0 rank = Zlength ws.
  Proof. unfold xs1. rewrite (xsym_total ws rank tl OK). lia. Qed.
  Lemma xs1_nonneg w : 1 <= w <= 13 -> 0 <= xs1 w.
  Proof. intros H. rewrite <- xs1_1. apply xs1_mono; lia. Qed.

  Lemma xs1_high maxW w : 1 <= maxW -> (forall v, maxW < v <= 12 -> Znth v rank = 0) -> maxW < w <= 13 -> xs1 w = xs1 (maxW + 1).
  Proof.
    intros HM HZ Hw.
    assert (G : forall k : nat, xs1 (maxW + 1 + Z.of_nat k) = xs1 (maxW + 1) \/ 13 < maxW + 1 + Z.of_nat k).
    { induction k as [|k IH]; [left; f_equal; lia|].
      destruct (Z_le_gt_dec (maxW + 1 + Z.of_nat (S k)) 13) as [LE|GT]; [|right; lia]. left.
      destruct IH as [IH|IH]; [|lia].
      replace (maxW + 1 + Z.of_nat (S k)) with (maxW + 1 + Z.of_nat k + 1) by lia.
      rewrite xs1_step by lia. rewrite HZ by lia. lia. }
    destruct (G (Z.to_nat (w - (maxW + 1)))) as [E|E]; [|lia]. rewrite <- E. f_equal. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma xs1_total maxW : 1 <= maxW <= 12 -> (forall v, maxW < v <= 12 -> Znth v rank = 0) -> xs1 (maxW + 1) + Znth 0 rank = Zlength ws.
  Proof.
    intros HM HZ. rewrite <- xs1_top. f_equal. destruct (Z.eq_dec maxW 12) as [->|NE]; [reflexivity|].
    symmetry. apply xs1_high; [lia | exact HZ | lia].
  Qed.

  (* [comment removed for export] *)
  Let P0 : 0 < 2^(T - tl). Proof. apply Z.pow_pos_nonneg; lia. Qed.

  Lemma rv0_1 : rv0 1 = 0.
  Proof. unfold rv0, xcur. change (Z.to_nat 1) with 1%nat. cbn [psum]. change (Z.of_nat 0) with 0. change (hw_cells 0) with 0. lia. Qed.
  (* [comment removed for export] *)
  Lemma cells1 w : 1 <= w -> 2^(T - tl) * hw_cells w = 2^(T - (tl + 1 - w)).
  Proof.
    intros Hw. unfold hw_cells. destruct (Z.eqb_spec w 0); [lia|]. rewrite <- Z.pow_add_r by lia. f_equal. lia.
  Qed.
  Lemma rv0_step w : 1 <= w -> rv0 (w + 1) = rv0 w + Znth w rank * 2^(T - (tl + 1 - w)).
  Proof. intros Hw. unfold rv0. rewrite (xcur_step rank w) by lia. rewrite <- (cells1 w Hw). ring. Qed.
  Lemma rv0_nonneg w : 0 <= w <= 13 -> 0 <= rv0 w.
  Proof. intros H. unfold rv0. pose proof (xcur_nonneg ws rank tl OK w H). nia. Qed.
  Lemma rv0_mono w w' : 0 <= w <= w' -> w' <= 13 -> rv0 w <= rv0 w'.
  Proof. intros H1 H2. unfold rv0. pose proof (xcur_mono ws rank tl OK w w' H1 H2). nia. Qed.
  Lemma rv0_end : rv0 (tl + 1) = 2^T.
  Proof. unfold rv0. rewrite (xcur_end ws rank tl OK). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
  (* [comment removed for export] *)
  Lemma rv0_high maxW w : 1 <= maxW -> (forall v, maxW < v <= 12 -> Znth v rank = 0) -> maxW < w <= 13 -> rv0 w = rv0 (maxW + 1).
  Proof.
    intros HM HZ Hw.
    assert (G : forall k : nat, rv0 (maxW + 1 + Z.of_nat k) = rv0 (maxW + 1) \/ 13 < maxW + 1 + Z.of_nat k).
    { induction k as [|k IH]; [left; f_equal; lia|].
      destruct (Z_le_gt_dec (maxW + 1 + Z.of_nat (S k)) 13) as [LE|GT]; [|right; lia]. left.
      destruct IH as [IH|IH]; [|lia].
      replace (maxW + 1 + Z.of_nat (S k)) with (maxW + 1 + Z.of_nat k + 1) by lia.
      rewrite rv0_step by lia. rewrite HZ by lia. lia. }
    destruct (G (Z.to_nat (w - (maxW + 1)))) as [E|E]; [|lia]. rewrite <- E. f_equal. lia.
  Qed.
  Lemma rv0_top maxW : 1 <= maxW <= tl -> (forall v, maxW < v <= 12 -> Znth v rank = 0) -> rv0 (maxW + 1) = 2^T.
  Proof.
    intros HM HZ. destruct (Z.eq_dec maxW tl) as [->|NE]; [apply rv0_end|].
    rewrite <- rv0_end. symmetry. apply rv0_high; [lia | exact HZ | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma some_weight : (forall v, 1 <= v <= tl -> Znth v rank = 0) -> False.
  Proof.
    intros HZ.
    assert (G : forall k : nat, Z.of_nat k <= tl -> rv0 (1 + Z.of_nat k) = 0).
    { induction k as [|k IH]; intros Hk; [exact rv0_1|].
      replace (1 + Z.of_nat (S k)) with (1 + Z.of_nat k + 1) by lia. rewrite rv0_step by lia. rewrite IH by lia. rewrite HZ by lia. lia. }
    specialize (G (Z.to_nat tl) ltac:(lia)). replace (1 + Z.of_nat (Z.to_nat tl)) with (tl + 1) in G by lia.
    rewrite rv0_end in G. pose proof (Z.pow_pos_nonneg 2 T ltac:(lia) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rvc_nonneg c w : 0 <= c -> 0 <= w <= 13 -> 0 <= rvc c w.
  Proof. intros Hc Hw. unfold rvc. apply Z.div_pos; [apply rv0_nonneg; exact Hw | apply Z.pow_pos_nonneg; lia]. Qed.
  Lemma rvc_1 c : 0 <= c -> rvc c 1 = 0.
  Proof. intros Hc. unfold rvc. rewrite rv0_1. apply Z.div_0_l. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) Hc). lia. Qed.
  (* [comment removed for export] *)
  Lemma rvc_step c w : 0 <= c -> 1 <= w -> c <= T - (tl + 1 - w) ->
    rvc c (w + 1) = rvc c w + Znth w rank * 2^(T - (tl + 1 - w) - c).
  Proof.
    intros Hc Hw Hd. unfold rvc. rewrite rv0_step by lia.
    replace (2^(T - (tl + 1 - w))) with (2^(T - (tl + 1 - w) - c) * 2^c) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Z.mul_assoc. rewrite Z.div_add by (pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) Hc); lia). reflexivity.
  Qed.
  Lemma rvc_top c maxW : 0 <= c <= T -> 1 <= maxW <= tl -> (forall v, maxW < v <= 12 -> Znth v rank = 0) -> rvc c (maxW + 1) = 2^(T - c).
  Proof.
    intros Hc HM HZ. unfold rvc. rewrite (rv0_top maxW HM HZ).
    replace (2^T) with (2^(T - c) * 2^c) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    apply Z.div_mul. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)). lia.
  Qed.
  Lemma rvc_mono c w w' : 0 <= c -> 0 <= w <= w' -> w' <= 13 -> rvc c w <= rvc c w'.
  Proof.
    intros Hc H1 H2. unfold rvc. apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia | apply rv0_mono; assumption].
  Qed.
End X2.

(* [comment removed for export] *)
Definition okw (v : Z) : Prop := 0 <= v mod 256 <= 12 /\ 1 <= (v / 256) mod 256 <= 2.
(* [comment removed for export] *)
Definition PREF2 (cur : Z) (cw : list Z) : Prop := forall i, 0 <= i < cur -> okw (Znth (2 * i + 1) cw).
(* [comment removed for export] *)
Definition cells_written (cw cw' : list Z) (pos n v : Z) : Prop :=
  Zlength cw' = Zlength cw /\
  (forall k, 0 <= k -> k < 2 * pos \/ 2 * (pos + n) <= k -> Znth k cw' = Znth k cw) /\
  (forall i, pos <= i < pos + n -> Znth (2 * i + 1) cw' = v).

Lemma okw_val nb len : 0 <= nb <= 12 -> 1 <= len <= 2 -> okw (nb + 256 * len).
Proof.
  intros Hn Hl. unfold okw. replace ((nb + 256 * len) mod 256) with nb by (Z.div_mod_to_equations; lia).
  replace ((nb + 256 * len) / 256) with len by (Z.div_mod_to_equations; lia). rewrite Z.mod_small by lia. lia.
Qed.

Lemma cells_written_refl cw pos v : cells_written cw cw pos 0 v.
Proof. split; [reflexivity|]. split; [reflexivity | intros i Hi; lia]. Qed.

Lemma cells_written_app cw cw1 cw2 pos n1 n2 v : 0 <= pos -> 0 <= n1 -> 0 <= n2 ->
  cells_written cw cw1 pos n1 v -> cells_written cw1 cw2 (pos + n1) n2 v -> cells_written cw cw2 pos (n1 + n2) v.
Proof.
  intros Hp H1 H2 (L1 & S1 & V1) (L2 & S2 & V2). split; [congruence|]. split.
  - intros k Hk HK. rewrite S2 by lia. apply S1; lia.
  - intros i Hi. destruct (Z.lt_ge_cases i (pos + n1)) as [L|G]; [|apply V2; lia].
    rewrite S2 by lia. apply V1. lia.
Qed.

(* [comment removed for export] *)
Lemma pref2_write cur cw cw' pos n v : PREF2 cur cw -> cells_written cw cw' pos n v -> okw v -> 0 <= pos <= cur -> 0 <= n ->
  PREF2 (Z.max cur (pos + n)) cw'.
Proof.
  intros PR (L & S & V) OKV Hp Hn i Hi.
  destruct (Z.lt_ge_cases i pos) as [A|A]; [rewrite S by lia; apply PR; lia|].
  destruct (Z.lt_ge_cases i (pos + n)) as [B|B]; [rewrite V by lia; exact OKV|].
  rewrite S by lia. apply PR. lia.
Qed.

(* [comment removed for export] *)
Lemma firstn_succ_Znth (ws : list Z) n : 0 <= n < Zlength ws -> firstn (Z.to_nat (n + 1)) ws = firstn (Z.to_nat n) ws ++ [Znth n ws].
Proof.
  intros Hn. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. unfold Znth. apply FseNCountRT.firstn_S_nth. unfold Zlength in Hn. lia.
Qed.
Lemma hcount_firstn_step ws n v : 0 <= n < Zlength ws ->
  hcount (firstn (Z.to_nat (n + 1)) ws) v = hcount (firstn (Z.to_nat n) ws) v + (if Z.eq_dec (Znth n ws) v then 1 else 0).
Proof. intros Hn. rewrite firstn_succ_Znth by exact Hn. rewrite hcount_app, hcount_one. reflexivity. Qed.
Lemma hcount_firstn_le ws k v : hcount (firstn k ws) v <= hcount ws v.
Proof.
  rewrite <- (firstn_skipn k ws) at 2. rewrite hcount_app. pose proof (hcount_nonneg (skipn k ws) v). lia.
Qed.
Lemma hcount_firstn_lt ws n : 0 <= n < Zlength ws -> hcount (firstn (Z.to_nat n) ws) (Znth n ws) + 1 <= hcount ws (Znth n ws).
Proof.
  intros Hn. pose proof (hcount_firstn_le ws (Z.to_nat (n + 1)) (Znth n ws)) as H.
  rewrite hcount_firstn_step in H by exact Hn. destruct (Z.eq_dec (Znth n ws) (Znth n ws)); [lia | congruence].
Qed.
Lemma hcount_firstn_all ws v : hcount (firstn (Z.to_nat (Zlength ws)) ws) v = hcount ws v.
Proof. unfold Zlength. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.
