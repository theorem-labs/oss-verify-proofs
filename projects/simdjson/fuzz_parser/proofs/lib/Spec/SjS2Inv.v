(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjStage1 SjInvPath.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition roundup (x m : Z) : Z := ((x + m - 1) / m) * m.

Lemma roundup_ge : forall x m, 0 < m -> x <= roundup x m.
Proof.
  intros x m Hm. unfold roundup.
  pose proof (Z.div_mod (x + m - 1) m ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (x + m - 1) m Hm) as B. nia.
Qed.

(* [comment removed for export] *)
Lemma bpath_quote_here : forall data len p q, bpath data len p q -> byte_at data p = 34 -> p = q.
Proof. intros data len p q H Hb. inversion H; subst; [reflexivity| |]; congruence. Qed.

Lemma bpath_inv_plain : forall data len p q, bpath data len p q -> byte_at data p <> 34 -> byte_at data p <> 92 -> bpath data len (p + 1) q.
Proof. intros data len p q H H34 H92. inversion H; subst; [congruence|congruence|assumption]. Qed.

Lemma bpath_inv_esc : forall data len p q, bpath data len p q -> byte_at data p = 92 -> bpath data len (p + 2) q.
Proof. intros data len p q H H92. inversion H; subst; [congruence|assumption|congruence]. Qed.

Lemma bpath_esc_next_lt : forall data len p q, bpath data len p q -> byte_at data p = 92 -> p + 2 <= q.
Proof. intros data len p q H H92. pose proof (bpath_bound _ _ _ _ (bpath_inv_esc data len p q H H92)). lia. Qed.

(* [comment removed for export] *)
Inductive hd : Type := HOB | HAB | HAV | HOF | HOC | HAC | HEND | HDE.

Record ast : Type := mkast { a_k : Z; a_d : Z; a_w : Z; a_sb : Z; a_e : Z }.

Section S2.
  Variables (data idxs : list Z) (n cap : Z).
  Notation len := (Z.of_nat (length data)).
  Definition dbyte (i : Z) : Z := byte_at data i.
  Definition idx (j : Z) : Z := nth (Z.to_nat j) idxs 0.

  (* [comment removed for export] *)
  Definition capt : Z := roundup (cap + 3) 64.                  (* [comment removed for export] *)
  Definition caps : Z := roundup (5 * (cap / 3) + 64) 64.       (* [comment removed for export] *)
  Definition MAXD : Z := 1024.                                 (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record s1out : Prop := {
    so_n : 1 <= n <= len;
    so_len : n + 3 <= Z.of_nat (length idxs);
    so_range : forall j, 0 <= j < n -> 0 <= idx j < len;
    so_incr : forall j, 0 <= j -> j + 1 < n -> idx j < idx (j + 1);
    so_sent : idx n = len /\ idx (n + 1) = len /\ idx (n + 2) = 0;
    so_str : forall j, 0 <= j < n -> dbyte (idx j) = 34 -> exists q, bpath data len (idx j + 1) q /\ q < idx (j + 1)
  }.

  Hypothesis S1 : s1out.
  Hypothesis CAP : 32 <= cap /\ len <= cap.

  Lemma len_nonneg : 0 <= len.
  Proof. lia. Qed.

  Lemma idx_last_lt : 0 <= n - 1 -> idx (n - 1) < idx n.
  Proof.
    intros H. destruct S1 as [Hn _ Hr _ [Hs _] _]. rewrite Hs.
    specialize (Hr (n - 1) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma idx_lt : forall a b, 0 <= a -> a < b -> b <= n -> idx a < idx b.
  Proof.
    intros a b Ha Hab Hb.
    assert (Step : forall x, 0 <= x -> x + 1 <= n -> idx x < idx (x + 1)).
    { intros x Hx Hx1. destruct (Z.eq_dec (x + 1) n) as [E|E].
      - replace x with (n - 1) by lia. replace (n - 1 + 1) with n by lia. apply idx_last_lt. lia.
      - apply (so_incr S1); lia. }
    assert (G : forall t, 0 <= t -> a + 1 + t <= n -> idx a < idx (a + 1 + t)).
    { intros t Ht. pattern t. apply natlike_ind; [| |lia].
      - intros _. replace (a + 1 + 0) with (a + 1) by lia. apply Step; lia.
      - intros x Hx IH H. specialize (IH ltac:(lia)).
        replace (a + 1 + Z.succ x) with ((a + 1 + x) + 1) by lia.
        pose proof (Step (a + 1 + x) ltac:(lia) ltac:(lia)). lia. }
    replace b with (a + 1 + (b - a - 1)) by lia. apply G; lia.
  Qed.

  Lemma idx_le : forall a b, 0 <= a -> a <= b -> b <= n -> idx a <= idx b.
  Proof. intros a b Ha Hab Hb. destruct (Z.eq_dec a b) as [->|N]; [lia|]. pose proof (idx_lt a b); lia. Qed.

  Lemma idx_bound : forall j, 0 <= j <= n -> 0 <= idx j <= len.
  Proof.
    intros j Hj. destruct (Z.eq_dec j n) as [->|N].
    - destruct S1 as [Hn _ _ _ [Hs _] _]. lia.
    - pose proof (so_range S1 j ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition value_head (h : hd) : bool := match h with HOB | HAB | HAV => true | _ => false end.

  Definition tape_ok (h : hd) (s : ast) : Prop :=
    1 <= a_w s /\
    match h with
    | HOB | HAB => a_w s <= a_k s
    | HAV | HOF | HEND => a_w s <= a_k s + 1
    | HOC | HAC | HDE => a_w s <= a_k s + 2
    end.

  Definition depth_ok (h : hd) (s : ast) : Prop :=
    match h with
    | HOB | HAB => 0 <= a_d s <= MAXD - 1
    | HDE => a_d s = 0
    | _ => 1 <= a_d s <= MAXD - 1
    end.

  Definition sbuf_ok (h : hd) (s : ast) : Prop :=
    0 <= a_sb s /\ 0 <= a_e s /\ 3 * a_sb s <= 5 * a_e s /\
    (if value_head h then a_e s <= idx (a_k s - 1) else a_e s <= idx (a_k s)).

  Definition winv (h : hd) (s : ast) (ti ia : Z -> Z) : Prop :=
    (match h with HOB | HAB | HAV | HOF => 1 <= a_k s | _ => 0 <= a_k s end) /\ a_k s <= n /\
    tape_ok h s /\ depth_ok h s /\ sbuf_ok h s /\
    (forall i, 0 <= i <= a_d s -> 0 <= ti i < a_w s) /\
    (forall i, 1 <= i <= a_d s -> ia i = 0 \/ ia i = 1).

  (* [comment removed for export] *)
  Definition rank (h : hd) : Z := match h with HAB | HEND => 1 | _ => 0 end.
  Definition mu (h : hd) (s : ast) : Z := 2 * (n + 2 - a_k s) + rank h.

  Lemma mu_nonneg : forall h s ti ia, winv h s ti ia -> 0 <= mu h s.
  Proof. intros h s ti ia (Hk & Hkn & _). unfold mu, rank. destruct h; lia. Qed.

  (* [comment removed for export] *)
  Definition upd (f : Z -> Z) (i v : Z) : Z -> Z := fun x => if Z.eq_dec x i then v else f x.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac s2simpl := unfold winv, tape_ok, depth_ok, sbuf_ok, value_head, mu, rank, MAXD in *; cbn [a_k a_d a_w a_sb a_e] in *.
  Ltac winv_destr H := destruct H as (Hk1 & Hkn & (Hw1 & Hw) & Hd & (Hsb & He & Hse & Hei) & Hti & Hia);
    s2simpl; match goal with Hk : a_k ?s <= n |- _ => pose proof (idx_bound (a_k s) ltac:(lia)) end.
  Ltac winv_split := split; [| split; [| split; [| split; [| split; [| split]]]]].
  Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
  Ltac idx_norm := repeat match goal with
    | |- context [idx (?a + ?c1 - ?c2)] => is_zlit c1; is_zlit c2; let c := eval vm_compute in (c1 - c2) in
        replace (a + c1 - c2) with (a + c) by lia
    end; rewrite ?Z.add_0_r.
  Ltac s2close Hti Hia :=
    winv_split; s2simpl; idx_norm;
    try lia;
    try (repeat split; lia);
    try (intros i Hi; unfold upd; destruct (Z.eq_dec i _); [lia| specialize (Hti i ltac:(lia)); lia]);
    try (intros i Hi; unfold upd; destruct (Z.eq_dec i _); [first [left; reflexivity | right; reflexivity] | apply Hia; lia]);
    try (intros i Hi; specialize (Hti i ltac:(lia)); lia);
    try (intros i Hi; apply Hia; lia).

  (* [comment removed for export] *)
  Lemma sbuf_step : forall s j q c, 1 <= j < n -> 3 * a_sb s <= 5 * a_e s -> a_e s <= idx (j - 1) -> 0 <= c ->
    idx j + 1 + c <= q -> 3 * (a_sb s + c + 5) <= 5 * (q + 1).
  Proof.
    intros s j q c Hj Hse Hei Hc Hq. pose proof (idx_lt (j - 1) j ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tr_AV_string : forall s ti ia q c, winv HAV s ti ia -> a_k s < n -> dbyte (idx (a_k s)) = 34 ->
    bpath data len (idx (a_k s) + 1) q -> q < idx (a_k s + 1) -> 0 <= c -> idx (a_k s) + 1 + c <= q ->
    winv HAC (mkast (a_k s + 1) (a_d s) (a_w s + 1) (a_sb s + c + 5) (q + 1)) ti ia /\
    mu HAC (mkast (a_k s + 1) (a_d s) (a_w s + 1) (a_sb s + c + 5) (q + 1)) < mu HAV s.
  Proof.
    intros s ti ia q c H Hkn' Hq HP Hqn Hc Hcq. winv_destr H. s2simpl.
    pose proof (sbuf_step s (a_k s) q c ltac:(lia) Hse Hei Hc Hcq).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  Lemma tr_AV_prim : forall s ti ia t, winv HAV s ti ia -> a_k s < n -> 1 <= t <= 2 ->
    winv HAC (mkast (a_k s + 1) (a_d s) (a_w s + t) (a_sb s) (a_e s)) ti ia /\
    mu HAC (mkast (a_k s + 1) (a_d s) (a_w s + t) (a_sb s) (a_e s)) < mu HAV s.
  Proof.
    intros s ti ia t H Hkn' Ht. winv_destr H. s2simpl.
    pose proof (idx_le (a_k s - 1) (a_k s + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  Lemma tr_AV_empty : forall s ti ia, winv HAV s ti ia -> a_k s + 1 < n ->
    winv HAC (mkast (a_k s + 2) (a_d s) (a_w s + 2) (a_sb s) (a_e s)) ti ia /\
    mu HAC (mkast (a_k s + 2) (a_d s) (a_w s + 2) (a_sb s) (a_e s)) < mu HAV s.
  Proof.
    intros s ti ia H Hkn'. winv_destr H. s2simpl.
    pose proof (idx_le (a_k s - 1) (a_k s + 2) ltac:(lia) ltac:(lia) ltac:(lia)).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  Lemma tr_AV_open : forall s ti ia h', winv HAV s ti ia -> a_k s < n -> h' = HAB \/ h' = HOB ->
    winv h' (mkast (a_k s + 1) (a_d s) (a_w s) (a_sb s) (a_e s)) ti ia /\
    mu h' (mkast (a_k s + 1) (a_d s) (a_w s) (a_sb s) (a_e s)) < mu HAV s.
  Proof.
    intros s ti ia h' H Hkn' Hh. destruct Hh as [->| ->]; winv_destr H;
      pose proof (idx_le (a_k s - 1) (a_k s) ltac:(lia) ltac:(lia) ltac:(lia));
      (split; [|unfold mu, rank; s2simpl; lia]); s2close Hti Hia.
  Qed.

  (* [comment removed for export] *)
  Lemma tr_AB : forall s ti ia, winv HAB s ti ia -> a_d s + 1 <= MAXD - 1 ->
    winv HAV (mkast (a_k s) (a_d s + 1) (a_w s + 1) (a_sb s) (a_e s)) (upd ti (a_d s + 1) (a_w s)) (upd ia (a_d s + 1) 1) /\
    mu HAV (mkast (a_k s) (a_d s + 1) (a_w s + 1) (a_sb s) (a_e s)) < mu HAB s.
  Proof.
    intros s ti ia H Hdm. winv_destr H. s2simpl.
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  (* [comment removed for export] *)
  Lemma tr_OB_key : forall s ti ia q c, winv HOB s ti ia -> a_d s + 1 <= MAXD - 1 -> a_k s < n -> dbyte (idx (a_k s)) = 34 ->
    bpath data len (idx (a_k s) + 1) q -> q < idx (a_k s + 1) -> 0 <= c -> idx (a_k s) + 1 + c <= q ->
    winv HOF (mkast (a_k s + 1) (a_d s + 1) (a_w s + 2) (a_sb s + c + 5) (q + 1)) (upd ti (a_d s + 1) (a_w s)) (upd ia (a_d s + 1) 0) /\
    mu HOF (mkast (a_k s + 1) (a_d s + 1) (a_w s + 2) (a_sb s + c + 5) (q + 1)) < mu HOB s.
  Proof.
    intros s ti ia q c H Hdm Hkn' Hq HP Hqn Hc Hcq. winv_destr H. s2simpl.
    pose proof (sbuf_step s (a_k s) q c ltac:(lia) Hse Hei Hc Hcq).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  (* [comment removed for export] *)
  Lemma tr_OF_string : forall s ti ia q c, winv HOF s ti ia -> a_k s + 1 < n -> dbyte (idx (a_k s + 1)) = 34 ->
    bpath data len (idx (a_k s + 1) + 1) q -> q < idx (a_k s + 2) -> 0 <= c -> idx (a_k s + 1) + 1 + c <= q ->
    winv HOC (mkast (a_k s + 2) (a_d s) (a_w s + 1) (a_sb s + c + 5) (q + 1)) ti ia /\
    mu HOC (mkast (a_k s + 2) (a_d s) (a_w s + 1) (a_sb s + c + 5) (q + 1)) < mu HOF s.
  Proof.
    intros s ti ia q c H Hkn' Hq HP Hqn Hc Hcq. winv_destr H. s2simpl.
    pose proof (sbuf_step s (a_k s + 1) q c ltac:(lia) Hse ltac:(replace (a_k s + 1 - 1) with (a_k s) by lia; exact Hei) Hc Hcq).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  Lemma tr_OF_prim : forall s ti ia t, winv HOF s ti ia -> a_k s + 1 < n -> 1 <= t <= 2 ->
    winv HOC (mkast (a_k s + 2) (a_d s) (a_w s + t) (a_sb s) (a_e s)) ti ia /\
    mu HOC (mkast (a_k s + 2) (a_d s) (a_w s + t) (a_sb s) (a_e s)) < mu HOF s.
  Proof.
    intros s ti ia t H Hkn' Ht. winv_destr H. s2simpl.
    pose proof (idx_le (a_k s) (a_k s + 2) ltac:(lia) ltac:(lia) ltac:(lia)).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  Lemma tr_OF_empty : forall s ti ia, winv HOF s ti ia -> a_k s + 2 < n ->
    winv HOC (mkast (a_k s + 3) (a_d s) (a_w s + 2) (a_sb s) (a_e s)) ti ia /\
    mu HOC (mkast (a_k s + 3) (a_d s) (a_w s + 2) (a_sb s) (a_e s)) < mu HOF s.
  Proof.
    intros s ti ia H Hkn'. winv_destr H. s2simpl.
    pose proof (idx_le (a_k s) (a_k s + 3) ltac:(lia) ltac:(lia) ltac:(lia)).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  Lemma tr_OF_open : forall s ti ia h', winv HOF s ti ia -> a_k s + 1 < n -> h' = HAB \/ h' = HOB ->
    winv h' (mkast (a_k s + 2) (a_d s) (a_w s) (a_sb s) (a_e s)) ti ia /\
    mu h' (mkast (a_k s + 2) (a_d s) (a_w s) (a_sb s) (a_e s)) < mu HOF s.
  Proof.
    intros s ti ia h' H Hkn' Hh. destruct Hh as [->| ->]; winv_destr H;
      pose proof (idx_le (a_k s) (a_k s + 1) ltac:(lia) ltac:(lia) ltac:(lia));
      (split; [|unfold mu, rank; s2simpl; lia]); s2close Hti Hia.
  Qed.

  (* [comment removed for export] *)
  Lemma tr_OC_close : forall s ti ia, winv HOC s ti ia -> a_k s < n -> a_w s <= a_k s + 1 \/ True ->
    winv HEND (mkast (a_k s + 1) (a_d s) (a_w s) (a_sb s) (a_e s)) ti ia /\
    mu HEND (mkast (a_k s + 1) (a_d s) (a_w s) (a_sb s) (a_e s)) < mu HOC s.
  Proof.
    intros s ti ia H Hkn' _. winv_destr H. s2simpl.
    pose proof (idx_le (a_k s) (a_k s + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  Lemma tr_OC_key : forall s ti ia q c, winv HOC s ti ia -> a_k s + 1 < n -> dbyte (idx (a_k s + 1)) = 34 ->
    bpath data len (idx (a_k s + 1) + 1) q -> q < idx (a_k s + 2) -> 0 <= c -> idx (a_k s + 1) + 1 + c <= q ->
    winv HOF (mkast (a_k s + 2) (a_d s) (a_w s + 1) (a_sb s + c + 5) (q + 1)) ti ia /\
    mu HOF (mkast (a_k s + 2) (a_d s) (a_w s + 1) (a_sb s + c + 5) (q + 1)) < mu HOC s.
  Proof.
    intros s ti ia q c H Hkn' Hq HP Hqn Hc Hcq. winv_destr H. s2simpl.
    pose proof (sbuf_step s (a_k s + 1) q c ltac:(lia) Hse ltac:(replace (a_k s + 1 - 1) with (a_k s) by lia; exact Hei) Hc Hcq).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  (* [comment removed for export] *)
  Lemma tr_AC_close : forall s ti ia, winv HAC s ti ia -> a_k s < n ->
    winv HEND (mkast (a_k s + 1) (a_d s) (a_w s) (a_sb s) (a_e s)) ti ia /\
    mu HEND (mkast (a_k s + 1) (a_d s) (a_w s) (a_sb s) (a_e s)) < mu HAC s.
  Proof.
    intros s ti ia H Hkn'. winv_destr H. s2simpl.
    pose proof (idx_le (a_k s) (a_k s + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  Lemma tr_AC_comma : forall s ti ia, winv HAC s ti ia -> a_k s < n ->
    winv HAV (mkast (a_k s + 1) (a_d s) (a_w s) (a_sb s) (a_e s)) ti ia /\
    mu HAV (mkast (a_k s + 1) (a_d s) (a_w s) (a_sb s) (a_e s)) < mu HAC s.
  Proof.
    intros s ti ia H Hkn'. winv_destr H. s2simpl.
    split; [|unfold mu, rank; s2simpl; lia].
    s2close Hti Hia.
  Qed.

  (* [comment removed for export] *)
  Lemma tr_END : forall s ti ia h', winv HEND s ti ia ->
    (a_d s = 1 /\ h' = HDE) \/ (2 <= a_d s /\ (h' = HOC \/ h' = HAC)) ->
    winv h' (mkast (a_k s) (a_d s - 1) (a_w s + 1) (a_sb s) (a_e s)) ti ia /\
    mu h' (mkast (a_k s) (a_d s - 1) (a_w s + 1) (a_sb s) (a_e s)) < mu HEND s.
  Proof.
    intros s ti ia h' H Hh. destruct Hh as [[Hd1 ->]|[Hd2 [-> | ->]]]; winv_destr H;
      (split; [|unfold mu, rank; s2simpl; lia]); s2close Hti Hia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma capt_ge : cap + 3 <= capt.
  Proof. unfold capt. apply roundup_ge. lia. Qed.

  Lemma caps_ge : 5 * (cap / 3) + 64 <= caps.
  Proof. unfold caps. apply roundup_ge. lia. Qed.

  (* [comment removed for export] *)
  Lemma tape_value_AV : forall s ti ia, winv HAV s ti ia -> a_k s < n -> a_w s + 1 < capt.
  Proof. intros s ti ia H Hk. winv_destr H. pose proof capt_ge. pose proof (so_n S1). lia. Qed.
  Lemma tape_value_OF : forall s ti ia, winv HOF s ti ia -> a_k s + 1 < n -> a_w s + 1 < capt.
  Proof. intros s ti ia H Hk. winv_destr H. pose proof capt_ge. pose proof (so_n S1). lia. Qed.
  (* [comment removed for export] *)
  Lemma tape_value_OB : forall s ti ia, winv HOB s ti ia -> a_w s + 1 < capt.
  Proof. intros s ti ia H. winv_destr H. pose proof capt_ge. pose proof (so_n S1). lia. Qed.
  (* [comment removed for export] *)
  Lemma tape_value_OC : forall s ti ia, winv HOC s ti ia -> a_k s < n -> a_w s < capt.
  Proof. intros s ti ia H Hk. winv_destr H. pose proof capt_ge. pose proof (so_n S1). lia. Qed.
  (* [comment removed for export] *)
  Lemma tape_END : forall s ti ia, winv HEND s ti ia -> a_w s < capt /\ 0 <= ti (a_d s) < capt.
  Proof.
    intros s ti ia H. winv_destr H. pose proof capt_ge. pose proof (so_n S1). s2simpl.
    specialize (Hti (a_d s) ltac:(lia)). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma tape_DE : forall s ti ia, winv HDE s ti ia -> a_w s < capt.
  Proof. intros s ti ia H. winv_destr H. pose proof capt_ge. pose proof (so_n S1). lia. Qed.

  (* [comment removed for export] *)
  Lemma sbuf_room : forall sbv ev j q, 0 <= j < n -> 0 <= sbv -> 3 * sbv <= 5 * ev ->
    (1 <= j -> ev <= idx (j - 1)) -> (j = 0 -> sbv = 0) -> q < idx (j + 1) ->
    sbv + 4 + (q - idx j - 1) + 4 <= caps.
  Proof.
    intros sbv ev j q Hj Hsb Hse Hsep H0 Hq. pose proof caps_ge.
    pose proof (idx_bound (j + 1) ltac:(lia)). pose proof (idx_bound j ltac:(lia)).
    pose proof (Z.mul_div_le cap 3 ltac:(lia)). pose proof (Z.mod_pos_bound cap 3 ltac:(lia)).
    pose proof (Z.div_mod cap 3 ltac:(lia)).
    destruct (Z.eq_dec j 0) as [->|Nj].
    - specialize (H0 eq_refl). pose proof (idx_bound 0 ltac:(lia)). lia.
    - specialize (Hsep ltac:(lia)). pose proof (idx_lt (j - 1) j ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oc_index_ok : forall dd, 0 <= dd <= MAXD - 1 -> 0 <= 8 * dd /\ 8 * dd + 8 <= 8 * MAXD /\ dd < MAXD.
  Proof. unfold MAXD. lia. Qed.

  (* [comment removed for export] *)
  Lemma idx_read_ok : forall j, 0 <= j <= n -> 4 * j + 4 <= 4 * Z.of_nat (length idxs).
  Proof. intros j Hj. pose proof (so_len S1). lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma byte_sentinel : dbyte (idx n) = 0.
  Proof. unfold dbyte. destruct S1 as [_ _ _ _ [Hs _] _]. rewrite Hs. apply byte_at_past. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition str_inv (p0 q p o : Z) : Prop := bpath data len p q /\ p0 <= p /\ 0 <= o <= p - p0.

  Lemma str_start : forall p0 q, bpath data len p0 q -> str_inv p0 q p0 0.
  Proof. intros p0 q H. repeat split; try lia. exact H. Qed.

  Lemma str_exit : forall p0 q p o, str_inv p0 q p o -> dbyte p = 34 -> p = q /\ o <= q - p0.
  Proof. intros p0 q p o (H & Hp & Ho) Hb. pose proof (bpath_quote_here data len p q H Hb). lia. Qed.

  Lemma str_plain : forall p0 q p o, str_inv p0 q p o -> dbyte p <> 34 -> dbyte p <> 92 ->
    str_inv p0 q (p + 1) (o + 1) /\ q - (p + 1) < q - p.
  Proof.
    intros p0 q p o (H & Hp & Ho) H34 H92. pose proof (bpath_inv_plain data len p q H H34 H92) as H'.
    pose proof (bpath_bound _ _ _ _ H'). repeat split; try lia. exact H'.
  Qed.

  Lemma str_simple_esc : forall p0 q p o, str_inv p0 q p o -> dbyte p = 92 ->
    str_inv p0 q (p + 2) (o + 1) /\ q - (p + 2) < q - p /\ p + 1 < len.
  Proof.
    intros p0 q p o (H & Hp & Ho) H92. pose proof (bpath_inv_esc data len p q H H92) as H'.
    pose proof (bpath_bound _ _ _ _ H'). repeat split; try lia. exact H'.
  Qed.

  Definition is_hex (c : Z) : Prop := (48 <= c <= 57) \/ (65 <= c <= 70) \/ (97 <= c <= 102).

  Lemma hex_not_special : forall c, is_hex c -> c <> 34 /\ c <> 92.
  Proof. unfold is_hex. lia. Qed.

  (* [comment removed for export] *)
  Lemma bpath_over_hex4 : forall a q, bpath data len a q ->
    is_hex (dbyte a) -> is_hex (dbyte (a + 1)) -> is_hex (dbyte (a + 2)) -> is_hex (dbyte (a + 3)) -> bpath data len (a + 4) q.
  Proof.
    intros a q H h0 h1 h2 h3.
    destruct (hex_not_special _ h0) as [n0 m0], (hex_not_special _ h1) as [n1 m1],
             (hex_not_special _ h2) as [n2 m2], (hex_not_special _ h3) as [n3 m3].
    pose proof (bpath_inv_plain _ _ _ _ H n0 m0) as P1.
    pose proof (bpath_inv_plain _ _ _ _ P1 n1 m1) as P2. replace (a + 1 + 1) with (a + 2) in P2 by lia.
    pose proof (bpath_inv_plain _ _ _ _ P2 n2 m2) as P3. replace (a + 2 + 1) with (a + 3) in P3 by lia.
    pose proof (bpath_inv_plain _ _ _ _ P3 n3 m3) as H4. replace (a + 3 + 1) with (a + 4) in H4 by lia.
    exact H4.
  Qed.

  (* [comment removed for export] *)
  Lemma str_u : forall p0 q p o ob, str_inv p0 q p o -> dbyte p = 92 ->
    is_hex (dbyte (p + 2)) -> is_hex (dbyte (p + 3)) -> is_hex (dbyte (p + 4)) -> is_hex (dbyte (p + 5)) -> 1 <= ob <= 4 ->
    str_inv p0 q (p + 6) (o + ob) /\ q - (p + 6) < q - p.
  Proof.
    intros p0 q p o ob (H & Hp & Ho) H92 h2 h3 h4 h5 Hob.
    pose proof (bpath_inv_esc data len p q H H92) as H'.
    pose proof (bpath_over_hex4 (p + 2) q H' h2 ltac:(replace (p + 2 + 1) with (p + 3) by lia; exact h3)
                  ltac:(replace (p + 2 + 2) with (p + 4) by lia; exact h4) ltac:(replace (p + 2 + 3) with (p + 5) by lia; exact h5)) as H6.
    replace (p + 2 + 4) with (p + 6) in H6 by lia. pose proof (bpath_bound _ _ _ _ H6).
    repeat split; try lia. exact H6.
  Qed.

  (* [comment removed for export] *)
  Lemma str_pair : forall p0 q p o, str_inv p0 q p o -> dbyte p = 92 ->
    is_hex (dbyte (p + 2)) -> is_hex (dbyte (p + 3)) -> is_hex (dbyte (p + 4)) -> is_hex (dbyte (p + 5)) ->
    dbyte (p + 6) = 92 ->
    is_hex (dbyte (p + 8)) -> is_hex (dbyte (p + 9)) -> is_hex (dbyte (p + 10)) -> is_hex (dbyte (p + 11)) ->
    str_inv p0 q (p + 12) (o + 4) /\ q - (p + 12) < q - p.
  Proof.
    intros p0 q p o HI H92 h2 h3 h4 h5 H92b h8 h9 h10 h11.
    destruct (str_u p0 q p o 1 HI H92 h2 h3 h4 h5 ltac:(lia)) as [(H6 & Hp6 & Ho6) _].
    pose proof (bpath_inv_esc _ _ _ _ H6 H92b) as H8. replace (p + 6 + 2) with (p + 8) in H8 by lia.
    pose proof (bpath_over_hex4 (p + 8) q H8 h8 ltac:(replace (p + 8 + 1) with (p + 9) by lia; exact h9)
                  ltac:(replace (p + 8 + 2) with (p + 10) by lia; exact h10) ltac:(replace (p + 8 + 3) with (p + 11) by lia; exact h11)) as H12.
    replace (p + 8 + 4) with (p + 12) in H12 by lia. pose proof (bpath_bound _ _ _ _ H12). destruct HI as (_ & Hp & Ho).
    repeat split; try lia. exact H12.
  Qed.

  (* [comment removed for export] *)
  Lemma str_read_ok : forall p0 q p o, str_inv p0 q p o -> 0 <= p /\ p + 11 < len + 64.
  Proof. intros p0 q p o (H & _ & _). pose proof (bpath_bound _ _ _ _ H). split; [|lia]. inversion H; lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition is_digit (c : Z) : Prop := 48 <= c <= 57.
  Definition is_numchar (c : Z) : Prop := is_digit c \/ c = 45 \/ c = 43 \/ c = 46 \/ c = 101 \/ c = 69.

  Lemma run_inside : forall (P : Z -> Prop) a b, ~ P 0 -> 0 <= a <= b -> (forall x, a <= x <= b -> P (dbyte x)) -> b < len.
  Proof.
    intros P a b N0 Ha H. destruct (Z_lt_ge_dec b len) as [L|G]; [exact L|].
    exfalso. specialize (H b ltac:(lia)). unfold dbyte in H. rewrite byte_at_past in H by lia. exact (N0 H).
  Qed.

  Lemma digit_run_inside : forall a b, 0 <= a <= b -> (forall x, a <= x <= b -> is_digit (dbyte x)) -> b < len.
  Proof. intros a b Hab H. apply (run_inside is_digit a b); [unfold is_digit; lia|lia|exact H]. Qed.

  Lemma numchar_run_inside : forall a b, 0 <= a <= b -> (forall x, a <= x <= b -> is_numchar (dbyte x)) -> b < len.
  Proof. intros a b Hab H. apply (run_inside is_numchar a b); [unfold is_numchar, is_digit; lia|lia|exact H]. Qed.

  (* [comment removed for export] *)
  Lemma swar_read_ok : forall p, 0 <= p <= len -> p + 7 < len + 64.
  Proof. lia. Qed.

End S2.

(* [comment removed for export] *)
Definition copy_bytes (data : list Z) (i0 : Z) : list Z :=
  firstn (Z.to_nat (Z.of_nat (length data) - i0)) (skipn (Z.to_nat i0) data) ++ repeat 32 64.

Lemma copy_bytes_length : forall data i0, 0 <= i0 <= Z.of_nat (length data) ->
  Z.of_nat (length (copy_bytes data i0)) = Z.of_nat (length data) - i0 + 64.
Proof.
  intros data i0 H. unfold copy_bytes. rewrite length_app, repeat_length, firstn_length, skipn_length. lia.
Qed.

Lemma copy_byte_tail : forall data i0 x, 0 <= i0 <= Z.of_nat (length data) ->
  Z.of_nat (length data) - i0 <= x < Z.of_nat (length data) - i0 + 64 -> byte_at (copy_bytes data i0) x = 32.
Proof.
  intros data i0 x H Hx. unfold byte_at, copy_bytes.
  assert (L : length (firstn (Z.to_nat (Z.of_nat (length data) - i0)) (skipn (Z.to_nat i0) data)) = Z.to_nat (Z.of_nat (length data) - i0)).
  { rewrite firstn_length, skipn_length. lia. }
  rewrite app_nth2 by lia. rewrite L. apply nth_repeat_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma copy_run_inside : forall data i0 (P : Z -> Prop) a b, 0 <= i0 <= Z.of_nat (length data) -> ~ P 32 -> ~ P 0 -> 0 <= a <= b ->
  (forall x, a <= x <= b -> P (byte_at (copy_bytes data i0) x)) -> b < Z.of_nat (length data) - i0.
Proof.
  intros data i0 P a b Hi N32 N0 Ha H.
  destruct (Z_lt_ge_dec b (Z.of_nat (length data) - i0)) as [L|G]; [exact L|].
  exfalso. specialize (H b ltac:(lia)).
  destruct (Z_lt_ge_dec b (Z.of_nat (length data) - i0 + 64)) as [L2|G3].
  - rewrite copy_byte_tail in H by lia. exact (N32 H).
  - rewrite byte_at_past in H; [exact (N0 H)|]. rewrite copy_bytes_length by lia. lia.
Qed.
