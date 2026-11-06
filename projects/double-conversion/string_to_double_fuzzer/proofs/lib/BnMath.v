(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import BnModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Arguments Z.mul : simpl nomatch.
Arguments Z.add : simpl nomatch.
Arguments Z.sub : simpl nomatch.
Arguments Z.pow : simpl nomatch.
Arguments Z.div : simpl nomatch.
Arguments Z.modulo : simpl nomatch.
Arguments Z.leb : simpl nomatch.
Arguments Z.ltb : simpl nomatch.
Arguments Z.eqb : simpl nomatch.
Arguments Z.max : simpl nomatch.
Arguments Z.min : simpl nomatch.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint val (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: t => x + B * val t
  end.

Definition ok (l : list Z) : Prop := Forall (fun x => 0 <= x < B) l.

Definition norm (l : list Z) : Prop := l = [] \/ last l 0 <> 0.

Lemma B_pos : 0 < B. Proof. reflexivity. Qed.
Lemma zlen_cons : forall {A} (x : A) l, zlen (x :: l) = zlen l + 1.
Proof. intros. unfold zlen. cbn [length]. lia. Qed.
Lemma zlen_nil : forall {A}, zlen (@nil A) = 0. Proof. reflexivity. Qed.
Lemma zlen_app : forall {A} (l1 l2 : list A), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_nonneg : forall {A} (l : list A), 0 <= zlen l. Proof. intros. unfold zlen. lia. Qed.

Lemma ok_nil : ok []. Proof. constructor. Qed.
Lemma norm_nil : norm []. Proof. left; reflexivity. Qed.
#[export] Hint Resolve ok_nil norm_nil : core.
Ltac triv := repeat split; cbn; auto; try lia; try congruence.
Lemma ok_cons : forall x l, ok (x :: l) <-> (0 <= x < B) /\ ok l.
Proof. intros. unfold ok. split; [intros H; inversion H; auto | intros [? ?]; constructor; auto]. Qed.
Lemma ok_app : forall l1 l2, ok (l1 ++ l2) <-> ok l1 /\ ok l2.
Proof. intros. unfold ok. apply Forall_app. Qed.

Lemma val_app : forall l1 l2, val (l1 ++ l2) = val l1 + B ^ zlen l1 * val l2.
Proof.
  induction l1 as [|x t IH]; intros l2; cbn [val app].
  - change (zlen (@nil Z)) with 0. rewrite Z.pow_0_r. lia.
  - rewrite IH, zlen_cons, Z.pow_add_r by (pose proof (zlen_nonneg t); lia).
    rewrite Z.pow_1_r. lia.
Qed.

Lemma val_bound : forall l, ok l -> 0 <= val l < B ^ zlen l.
Proof.
  induction l as [|x t IH]; intros Hok.
  - cbn. lia.
  - apply ok_cons in Hok as [Hx Ht]. specialize (IH Ht). cbn [val].
    rewrite zlen_cons, Z.pow_add_r, Z.pow_1_r by (pose proof (zlen_nonneg t); lia).
    unfold B in *. nia.
Qed.

Lemma val_nonneg : forall l, ok l -> 0 <= val l.
Proof. intros l H. apply val_bound in H. lia. Qed.

Lemma last_cons_cons : forall (x y : Z) l d, last (x :: y :: l) d = last (y :: l) d.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma norm_val : forall l, ok l -> l <> [] -> (last l 0 <> 0 <-> B ^ (zlen l - 1) <= val l).
Proof.
  induction l as [|x t IH]; intros Hok Hne; [congruence|].
  apply ok_cons in Hok as [Hx Ht].
  destruct t as [|y t'].
  - cbn [last val zlen length Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
    replace (zlen [x] - 1) with 0 by reflexivity. rewrite Z.pow_0_r. lia.
  - rewrite last_cons_cons. specialize (IH Ht ltac:(congruence)).
    cbn [val]. cbn [val] in IH.
    rewrite zlen_cons. replace (zlen (y :: t') + 1 - 1) with (zlen (y :: t') - 1 + 1)  by lia.
    rewrite Z.pow_add_r, Z.pow_1_r by (pose proof (zlen_nonneg t'); rewrite ?zlen_cons in *; lia).
    pose proof (val_bound (y :: t') Ht) as Hb. cbn [val] in Hb.
    assert (Hp : 0 < B ^ (zlen (y :: t') - 1)) by (apply Z.pow_pos_nonneg; [reflexivity | pose proof (zlen_nonneg t'); rewrite ?zlen_cons in *; lia]).
    split.
    + intros Hl. apply IH in Hl. unfold B in *. nia.
    + intros Hv. apply IH.
      (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (y + B * val t') (B ^ (zlen (y :: t') - 1))) as [Hlt|Hge]; [|exact Hge].
      exfalso. unfold B in *.
      assert (y + 268435456 * val t' + 1 <= 268435456 ^ (zlen (y :: t') - 1)) by lia. nia.
Qed.

Lemma norm_lower : forall l, ok l -> norm l -> l <> [] -> B ^ (zlen l - 1) <= val l.
Proof. intros l Hok [->|Hn] Hne; [congruence|]. apply norm_val; auto. Qed.

Lemma norm_of_val : forall l, ok l -> B ^ (zlen l - 1) <= val l -> norm l.
Proof.
  intros l Hok Hv. destruct l as [|x t]; [left; reflexivity|right].
  apply norm_val; auto. congruence.
Qed.

(* [comment removed for export] *)
Lemma len_bound : forall l k, ok l -> norm l -> 0 <= k -> val l < B ^ k -> zlen l <= k.
Proof.
  intros l k Hok Hn Hk Hv.
  destruct l as [|x t] eqn:El; [rewrite ?zlen_nil; lia|]. rewrite <- El in *.
  assert (Hne : l <> []) by (subst; congruence).
  pose proof (norm_lower l Hok Hn Hne) as Hlo.
  destruct (Z.le_gt_cases (zlen l) k) as [|Hgt]; [assumption|]. exfalso.
  assert (B ^ k <= B ^ (zlen l - 1)) by (apply Z.pow_le_mono_r; [reflexivity|lia]). lia.
Qed.

Lemma norm_snoc : forall l c, c <> 0 -> norm (l ++ [c]).
Proof. intros l c Hc. right. rewrite last_last. exact Hc. Qed.

Lemma norm_app : forall l m, m <> [] -> norm m -> norm (l ++ m).
Proof.
  intros l m Hne [->|Hn]; [congruence|]. right.
  destruct (@exists_last _ m Hne) as (m' & c & ->). rewrite app_assoc, last_last.
  rewrite last_last in Hn. exact Hn.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma split_B : forall p, p = p mod B + B * (p / B).
Proof. intros. pose proof (Z.div_mod p B ltac:(unfold B; lia)). lia. Qed.

Lemma mod_B_range : forall p, 0 <= p mod B < B.
Proof. intros. apply Z.mod_pos_bound. reflexivity. Qed.

Lemma div_B_nonneg : forall p, 0 <= p -> 0 <= p / B.
Proof. intros. apply Z.div_pos; [lia|reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma chunks_spec : forall fuel v, 0 <= v < B ^ Z.of_nat fuel ->
  val (chunks fuel v) = v /\ ok (chunks fuel v) /\ norm (chunks fuel v)
  /\ zlen (chunks fuel v) <= Z.of_nat fuel.
Proof.
  induction fuel as [|f IH]; intros v Hv.
  - cbn in Hv. cbn. rewrite ?zlen_nil. repeat split; try lia. apply ok_nil. left; reflexivity.
  - cbn [chunks]. destruct (Z.eqb_spec v 0) as [->|Hnz].
    + cbn. rewrite ?zlen_nil. repeat split; try lia. apply ok_nil. left; reflexivity.
    + assert (Hv' : 0 <= v / B < B ^ Z.of_nat f).
      { split; [apply div_B_nonneg; lia|].
        apply Z.div_lt_upper_bound; [reflexivity|].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia. lia. }
      destruct (IH _ Hv') as (Hval & Hok & Hn & Hlen).
      cbn [val]. rewrite Hval, zlen_cons. repeat split.
      * symmetry. apply split_B.
      * apply ok_cons. split; [apply mod_B_range | exact Hok].
      * (* [comment removed for export] *)
        destruct (chunks f (v / B)) as [|y r] eqn:Ec.
        -- right. cbn. intros Hm. cbn in Hval.
           pose proof (split_B v). lia.
        -- destruct Hn as [Hn|Hn]; [discriminate|]. right. rewrite last_cons_cons. exact Hn.
      * lia.
Qed.

Lemma chunks_nil_iff : forall fuel v, chunks (S fuel) v = [] <-> v = 0.
Proof.
  intros. cbn. destruct (Z.eqb_spec v 0); split; intros; auto; try discriminate; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mul32_l_spec : forall F l c, ok l -> 0 <= F -> 0 <= c ->
  let (r, c') := mul32_l F c l in
  val r + B ^ zlen l * c' = F * val l + c /\ ok r /\ zlen r = zlen l /\ 0 <= c'
  /\ (c <= F -> c' <= F).
Proof.
  induction l as [|x t IH]; intros c Hok HF Hc.
  - cbn. repeat split; auto using ok_nil; lia.
  - apply ok_cons in Hok as [Hx Ht]. cbn [mul32_l].
    set (p := F * x + c).
    assert (Hp : 0 <= p) by (unfold p; nia).
    specialize (IH (p / B) Ht HF (div_B_nonneg p Hp)).
    destruct (mul32_l F (p / B) t) as [r c']. destruct IH as (Hv & Hokr & Hlen & Hc' & Hcb).
    cbn [val]. rewrite !zlen_cons, Hlen, Z.pow_add_r, Z.pow_1_r by (pose proof (zlen_nonneg t); lia).
    repeat split.
    + pose proof (split_B p). unfold p in *. nia.
    + apply ok_cons. split; [apply mod_B_range | exact Hokr].
    + exact Hc'.
    + intros HcF. apply Hcb. apply Z.div_le_upper_bound; [reflexivity|]. unfold p, B in *. nia.
Qed.

Lemma mul32_spec : forall F b, ok (cells b) -> norm (cells b) -> 0 <= F < 2 ^ 32 ->
  ok (cells (mul32 F b)) /\ norm (cells (mul32 F b)) /\ val (cells (mul32 F b)) = F * val (cells b)
  /\ (F <> 0 -> ex (mul32 F b) = ex b).
Proof.
  intros F b Hok Hn HF. unfold mul32.
  destruct (Z.eqb_spec F 1) as [->|HF1]; [rewrite Z.mul_1_l; tauto|].
  destruct (Z.eqb_spec F 0) as [->|HF0].
  { cbn. repeat split; try lia. apply ok_nil. left; reflexivity. }
  destruct (cells b) as [|x t] eqn:Ec.
  { cbn. rewrite Ec. repeat split; auto; cbn; lia. }
  rewrite <- Ec in *.
  pose proof (mul32_l_spec F (cells b) 0 Hok ltac:(lia) ltac:(lia)) as HS.
  destruct (mul32_l F 0 (cells b)) as [r c]. destruct HS as (Hv & Hokr & Hlen & Hc & Hcb).
  specialize (Hcb ltac:(lia)).
  assert (HcB : 0 <= c < B ^ Z.of_nat 3) by (change (B ^ Z.of_nat 3) with (2^84); lia).
  destruct (chunks_spec 3 c HcB) as (Hcv & Hcok & Hcn & _).
  cbn [cells ex]. rewrite val_app, Hlen, Hcv. refine (conj _ (conj _ (conj _ _))).
  - apply ok_app; auto.
  - (* [comment removed for export] *)
    destruct (Z.eq_dec c 0) as [->|Hcnz].
    + cbn. rewrite app_nil_r. apply norm_of_val; [exact Hokr|]. rewrite Hlen.
      assert (Hne : cells b <> []) by (rewrite Ec; congruence).
      pose proof (norm_lower _ Hok Hn Hne). pose proof (val_nonneg _ Hok).
      rewrite Z.mul_0_r, Z.add_0_r in Hv. nia.
    + apply norm_app; [|exact Hcn]. intros He. apply chunks_nil_iff in He. lia.
  - lia.
  - intros _. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mul32_step_bounds : forall F x c, 0 <= F < 2 ^ 32 -> 0 <= x < B -> 0 <= c <= F ->
  0 <= F * x + c < 2 ^ 64 /\ 0 <= (F * x + c) / B <= F /\ 0 <= (F * x + c) mod B < B.
Proof.
  intros F x c HF Hx Hc. unfold B in *. repeat split; try nia.
  - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; nia.
  - apply Z.mod_pos_bound; lia.
  - apply Z.mod_pos_bound; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation C64 := 9223372036854775808 (only parsing).   (* [comment removed for export] *)

Lemma mul64_step_bounds : forall x c, 0 <= x < B -> 0 <= c < C64 ->
  let tmp := c mod B + kFive27_lo * x in
  let c' := c / B + tmp / B + kFive27_hi * x * 16 in
  0 <= tmp < 2 ^ 64 /\ 0 <= c' < C64 /\ 0 <= kFive27_hi * x * 16 + c / B < 2 ^ 64
  /\ 0 <= c / B /\ 0 <= tmp / B.
Proof.
  intros x c Hx Hc. unfold kFive27_lo, kFive27_hi, B in *.
  pose proof (Z.mod_pos_bound c 268435456 ltac:(lia)) as Hm.
  assert (Hq : 0 <= c / 268435456 < 34359738368).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Ht : 0 <= (c mod 268435456 + 4195354525 * x) / 268435456 < 4195354526).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  cbn zeta. lia.
Qed.

Lemma mul64_l_spec : forall l c, ok l -> 0 <= c < C64 ->
  let (r, c') := mul64_l kFive27_lo kFive27_hi c l in
  val r + B ^ zlen l * c' = 5 ^ 27 * val l + c /\ ok r /\ zlen r = zlen l /\ 0 <= c' < C64.
Proof.
  induction l as [|x t IH]; intros c Hok Hc.
  - cbn. repeat split; auto using ok_nil; lia.
  - apply ok_cons in Hok as [Hx Ht]. cbn [mul64_l].
    pose proof (mul64_step_bounds x c Hx Hc) as HB. cbn zeta in HB. destruct HB as (Htmp & Hc'r & _ & Hcd & Htd).
    set (tmp := c mod B + kFive27_lo * x) in *.
    set (c' := c / B + tmp / B + kFive27_hi * x * 16) in *.
    specialize (IH c' Ht Hc'r).
    destruct (mul64_l kFive27_lo kFive27_hi c' t) as [r c'']. destruct IH as (Hv & Hokr & Hlen & Hc'').
    cbn [val]. rewrite !zlen_cons, Hlen, Z.pow_add_r, Z.pow_1_r by (pose proof (zlen_nonneg t); lia).
    assert (Hokr' : ok ((tmp mod B) :: r)) by (apply ok_cons; split; [apply mod_B_range | exact Hokr]).
    split; [|split; [exact Hokr'|split; [lia|lia]]].
    rewrite <- kFive27_eq.
    pose proof (split_B tmp) as Hs1. pose proof (split_B c) as Hs2.
    set (P := B ^ zlen t) in *.
    assert (H1 : B * val r + B * (P * c'') = B * (5 ^ 27 * val t) + B * c') by lia.
    assert (H2 : tmp mod B + B * c' = (kFive27_hi * 2 ^ 32 + kFive27_lo) * x + c).
    { unfold c'. replace (kFive27_hi * 2 ^ 32) with (B * 16 * kFive27_hi) by reflexivity.
      unfold tmp in *. lia. }
    rewrite <- kFive27_eq in H1. lia.
Qed.

Lemma mul64_spec : forall b, ok (cells b) -> norm (cells b) ->
  let b' := mul64 kFive27_lo kFive27_hi b in
  ok (cells b') /\ norm (cells b') /\ val (cells b') = 5 ^ 27 * val (cells b) /\ ex b' = ex b.
Proof.
  intros b Hok Hn. unfold mul64.
  destruct (cells b) as [|x t] eqn:Ec.
  { cbn zeta. rewrite Ec. repeat split; auto. }
  rewrite <- Ec in *.
  pose proof (mul64_l_spec (cells b) 0 Hok ltac:(lia)) as HS.
  destruct (mul64_l _ _ 0 (cells b)) as [r c]. destruct HS as (Hv & Hokr & Hlen & Hc).
  assert (HcB : 0 <= c < B ^ Z.of_nat 3) by (change (B ^ Z.of_nat 3) with (2^84); lia).
  destruct (chunks_spec 3 c HcB) as (Hcv & Hcok & Hcn & _).
  cbn [cells ex]. rewrite val_app, Hlen, Hcv. refine (conj _ (conj _ (conj _ _))).
  - apply ok_app; auto.
  - destruct (Z.eq_dec c 0) as [->|Hcnz].
    + cbn. rewrite app_nil_r. apply norm_of_val; [exact Hokr|]. rewrite Hlen.
      assert (Hne : cells b <> []) by (rewrite Ec; congruence).
      pose proof (norm_lower _ Hok Hn Hne). pose proof (val_nonneg _ Hok). nia.
    + apply norm_app; [|exact Hcn]. intros He. apply chunks_nil_iff in He. lia.
  - lia.
  - reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shl_step : forall x c s, 0 <= x < B -> 0 <= s < 28 -> 0 <= c < 2 ^ s ->
  (x * 2 ^ s + c) / B = x / 2 ^ (28 - s) /\ 0 <= x / 2 ^ (28 - s) < 2 ^ s.
Proof.
  intros x c s Hx Hs Hc.
  assert (HB : B = 2 ^ s * 2 ^ (28 - s)) by (rewrite <- Z.pow_add_r by lia; replace (s + (28 - s)) with 28 by lia; reflexivity).
  assert (Hp : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 < 2 ^ (28 - s)) by (apply Z.pow_pos_nonneg; lia).
  split.
  - rewrite HB. rewrite <- Z.div_div by lia.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small c) by lia. now rewrite Z.add_0_r.
  - split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    rewrite Z.mul_comm, <- HB. lia.
Qed.

Lemma shl_l_spec : forall s l c, ok l -> 0 <= s < 28 -> 0 <= c < 2 ^ s ->
  let (r, c') := shl_l s c l in
  val r + B ^ zlen l * c' = 2 ^ s * val l + c /\ ok r /\ zlen r = zlen l /\ 0 <= c' < 2 ^ s.
Proof.
  induction l as [|x t IH]; intros c Hok Hs Hc.
  - cbn. repeat split; auto using ok_nil; lia.
  - apply ok_cons in Hok as [Hx Ht]. cbn [shl_l].
    destruct (shl_step x c s Hx Hs Hc) as [Hdiv Hnc].
    specialize (IH (x / 2 ^ (28 - s)) Ht Hs Hnc).
    destruct (shl_l s (x / 2 ^ (28 - s)) t) as [r c']. destruct IH as (Hv & Hokr & Hlen & Hc').
    cbn [val]. rewrite !zlen_cons, Hlen, Z.pow_add_r, Z.pow_1_r by (pose proof (zlen_nonneg t); lia).
    assert (Hokr' : ok ((x * 2 ^ s + c) mod B :: r)) by (apply ok_cons; split; [apply mod_B_range | exact Hokr]).
    split; [|split; [exact Hokr'|split; [lia|lia]]].
    pose proof (split_B (x * 2 ^ s + c)) as Hsp. rewrite Hdiv in Hsp.
    set (P := B ^ zlen t) in *. set (q := x / 2 ^ (28 - s)) in *. nia.
Qed.

Lemma shl_spec : forall n b, ok (cells b) -> norm (cells b) -> 0 <= n ->
  ok (cells (shl n b)) /\ norm (cells (shl n b))
  /\ val (cells (shl n b)) = 2 ^ (n mod 28) * val (cells b)
  /\ (cells b <> [] -> ex (shl n b) = ex b + n / 28)
  /\ zlen (cells (shl n b)) <= zlen (cells b) + 1.
Proof.
  intros n b Hok Hn Hnn. unfold shl.
  destruct (cells b) as [|x t] eqn:Ec.
  { cbn. rewrite Ec, ?zlen_nil. triv. }
  rewrite <- Ec in *.
  assert (Hs : 0 <= n mod 28 < 28) by (apply Z.mod_pos_bound; lia).
  pose proof (shl_l_spec (n mod 28) (cells b) 0 Hok Hs ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as HS.
  destruct (shl_l (n mod 28) 0 (cells b)) as [r c]. destruct HS as (Hv & Hokr & Hlen & Hc).
  assert (Hne : cells b <> []) by (rewrite Ec; congruence).
  pose proof (norm_lower _ Hok Hn Hne) as Hlo. pose proof (val_nonneg _ Hok) as Hv0.
  assert (Hps : 1 <= 2 ^ (n mod 28)) by (pose proof (Z.pow_pos_nonneg 2 (n mod 28)); lia).
  destruct (Z.eqb_spec c 0) as [->|Hcnz]; cbn [cells ex].
  - rewrite Z.mul_0_r, Z.add_0_r in Hv. repeat split; auto; try lia.
    apply norm_of_val; [exact Hokr|]. rewrite Hlen. nia.
  - rewrite val_app, Hlen, zlen_app. cbn [val zlen length Z.of_nat]. repeat split; try lia.
    + apply ok_app. split; [exact Hokr|]. apply ok_cons. split; [|apply ok_nil].
      assert (2 ^ (n mod 28) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia). unfold B. lia.
    + apply norm_snoc. exact Hcnz.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mul32_cells_nil : forall F b, F <> 0 -> (cells (mul32 F b) = [] <-> cells b = []).
Proof.
  intros F b HF. unfold mul32.
  destruct (Z.eqb_spec F 1); [tauto|]. destruct (Z.eqb_spec F 0); [lia|].
  destruct (cells b) as [|x t] eqn:Ec; [rewrite Ec; tauto|].
  destruct (mul32_l F 0 (x :: t)) as [r c] eqn:Em. cbn [cells].
  pose proof (f_equal (@length Z) (f_equal fst Em)) as Hl. cbn [fst] in Hl.
  split; [|discriminate]. intros Ha. apply app_eq_nil in Ha as [-> _].
  cbn [mul32_l] in Em. destruct (mul32_l F ((F * x + 0) / B) t). congruence.
Qed.

Lemma mul64_cells_nil : forall b, cells (mul64 kFive27_lo kFive27_hi b) = [] <-> cells b = [].
Proof.
  intros b. unfold mul64. destruct (cells b) as [|x t] eqn:Ec; [rewrite Ec; tauto|].
  cbn [mul64_l]. destruct (mul64_l _ _ _ t) as [r c]. cbn [cells]. split; [|discriminate].
  intros Ha. apply app_eq_nil in Ha as [? _]. discriminate.
Qed.

Lemma pow27_loop_spec : forall fuel r b, ok (cells b) -> norm (cells b) -> cells b <> [] -> 0 <= r ->
  let (b', r') := pow27_loop fuel r b in
  ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b /\ 0 <= r' <= r
  /\ val (cells b') = 5 ^ (r - r') * val (cells b)
  /\ (r' = r - 27 * Z.of_nat fuel /\ 27 * Z.of_nat fuel <= r \/ r' < 27).
Proof.
  induction fuel as [|f IH]; intros r b Hok Hn Hne Hr.
  - cbn. rewrite Z.sub_diag, Z.pow_0_r. repeat split; auto; lia.
  - cbn [pow27_loop]. destruct (Z.ltb_spec r 27) as [Hlt|Hge].
    + rewrite Z.sub_diag, Z.pow_0_r. repeat split; auto; lia.
    + pose proof (mul64_spec b Hok Hn) as HM. cbn zeta in HM. destruct HM as (Hok1 & Hn1 & Hv1 & Hex1).
      assert (Hne1 : cells (mul64 kFive27_lo kFive27_hi b) <> []) by (intros He; apply (proj1 (mul64_cells_nil _)) in He; exact (Hne He)).
      specialize (IH (r - 27) _ Hok1 Hn1 Hne1 ltac:(lia)).
      destruct (pow27_loop f (r - 27) _) as [b' r']. destruct IH as (Hok' & Hn' & Hne' & Hex' & Hr' & Hv' & Hcase).
      repeat split; auto.
      all: try congruence.
      all: try (rewrite Hv', Hv1; replace (r - r') with ((r - 27 - r') + 27) by lia; rewrite Z.pow_add_r by lia; lia).
      all: rewrite ?Nat2Z.inj_succ; lia.
Qed.

Lemma pow13_loop_spec : forall fuel r b, ok (cells b) -> norm (cells b) -> cells b <> [] -> 0 <= r ->
  let (b', r') := pow13_loop fuel r b in
  ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b /\ 0 <= r' <= r
  /\ val (cells b') = 5 ^ (r - r') * val (cells b)
  /\ (r' = r - 13 * Z.of_nat fuel /\ 13 * Z.of_nat fuel <= r \/ r' < 13).
Proof.
  induction fuel as [|f IH]; intros r b Hok Hn Hne Hr.
  - cbn. rewrite Z.sub_diag, Z.pow_0_r. repeat split; auto; lia.
  - cbn [pow13_loop]. destruct (Z.ltb_spec r 13) as [Hlt|Hge].
    + rewrite Z.sub_diag, Z.pow_0_r. repeat split; auto; lia.
    + pose proof (mul32_spec kFive13 b Hok Hn ltac:(unfold kFive13; lia)) as (Hok1 & Hn1 & Hv1 & Hex1).
      assert (Hne1 : cells (mul32 kFive13 b) <> []) by (intros He; apply (proj1 (mul32_cells_nil kFive13 _ ltac:(unfold kFive13; lia))) in He; exact (Hne He)).
      specialize (IH (r - 13) _ Hok1 Hn1 Hne1 ltac:(lia)).
      destruct (pow13_loop f (r - 13) _) as [b' r']. destruct IH as (Hok' & Hn' & Hne' & Hex' & Hr' & Hv' & Hcase).
      repeat split; auto.
      all: try (rewrite Hex'; apply Hex1; unfold kFive13; lia).
      all: try (rewrite Hv', Hv1, kFive13_eq; replace (r - r') with ((r - 13 - r') + 13) by lia; rewrite Z.pow_add_r by lia; lia).
      all: rewrite ?Nat2Z.inj_succ; lia.
Qed.

Lemma mulpow10_spec : forall e b, ok (cells b) -> norm (cells b) -> 0 <= e ->
  let b' := mulpow10 e b in
  ok (cells b') /\ norm (cells b') /\ val (cells b') = 5 ^ e * 2 ^ (e mod 28) * val (cells b)
  /\ (cells b <> [] -> ex b' = ex b + e / 28)
  /\ (cells b' = [] <-> cells b = []).
Proof.
  intros e b Hok Hn He. unfold mulpow10.
  destruct (Z.eqb_spec e 0) as [->|Hnz].
  { cbn zeta. rewrite Z.pow_0_r. cbn. repeat split; auto; try lia. }
  destruct (cells b) as [|x t] eqn:Ec.
  { cbn zeta. rewrite Ec. cbn. repeat split; auto; try lia. congruence. }
  rewrite <- Ec in *. assert (Hne : cells b <> []) by (rewrite Ec; congruence).
  pose proof (pow27_loop_spec (Z.to_nat (e / 27)) e b Hok Hn Hne He) as H1.
  destruct (pow27_loop _ e b) as [b1 r1]. destruct H1 as (Hok1 & Hn1 & Hne1 & Hex1 & Hr1 & Hv1 & Hc1).
  assert (Hr1' : r1 < 27).
  { destruct Hc1 as [[-> _]|]; [|assumption]. rewrite Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (Z.mul_div_le e 27 ltac:(lia)). pose proof (Z.mod_pos_bound e 27 ltac:(lia)).
    pose proof (Z.div_mod e 27 ltac:(lia)). lia. }
  pose proof (pow13_loop_spec 2 r1 b1 Hok1 Hn1 Hne1 ltac:(lia)) as H2.
  destruct (pow13_loop 2 r1 b1) as [b2 r2]. destruct H2 as (Hok2 & Hn2 & Hne2 & Hex2 & Hr2 & Hv2 & Hc2).
  assert (Hr2' : r2 < 13) by (destruct Hc2 as [[-> _]|]; [cbn; lia|assumption]).
  set (b3 := if 0 <? r2 then mul32 (kFive r2) b2 else b2).
  assert (H3 : ok (cells b3) /\ norm (cells b3) /\ val (cells b3) = 5 ^ r2 * val (cells b2) /\ ex b3 = ex b2 /\ cells b3 <> []).
  { unfold b3. destruct (Z.ltb_spec 0 r2) as [Hp|Hz].
    - assert (HF : 0 <= kFive r2 < 2 ^ 32).
      { unfold kFive. split; [apply Z.pow_nonneg; lia|].
        apply Z.le_lt_trans with (m := 5 ^ 12); [apply Z.pow_le_mono_r; lia | reflexivity]. }
      assert (HF0 : kFive r2 <> 0) by (unfold kFive; apply Z.pow_nonzero; lia).
      pose proof (mul32_spec (kFive r2) b2 Hok2 Hn2 HF) as (? & ? & ? & Hex3).
      repeat split; auto. intros Hee. apply (proj1 (mul32_cells_nil _ _ HF0)) in Hee. exact (Hne2 Hee).
    - replace r2 with 0 by lia. rewrite Z.pow_0_r, Z.mul_1_l. repeat split; auto. }
  destruct H3 as (Hok3 & Hn3 & Hv3 & Hex3 & Hne3).
  pose proof (shl_spec e b3 Hok3 Hn3 He) as (Hok4 & Hn4 & Hv4 & Hex4 & _).
  cbn zeta. repeat split; auto.
  - rewrite Hv4, Hv3, Hv2, Hv1.
    replace (5 ^ e) with (5 ^ (e - r1) * 5 ^ (r1 - r2) * 5 ^ r2); [lia|].
    rewrite <- !Z.pow_add_r by lia. f_equal. lia.
  - intros _. rewrite (Hex4 Hne3), Hex3, Hex2, Hex1. reflexivity.
  - intros Hz. exfalso.
    (* [comment removed for export] *)
    unfold shl in Hz. destruct (cells b3) as [|y u] eqn:E3; [congruence|].
    destruct (shl_l (e mod 28) 0 (y :: u)) as [r c] eqn:Es.
    cbn [shl_l] in Es. destruct (shl_l (e mod 28) (y / 2 ^ (28 - e mod 28)) u).
    injection Es as <- <-. cbn [cells] in Hz. destruct (_ =? 0); [discriminate|].
    apply app_eq_nil in Hz as [? _]; discriminate.
  - intros Hz. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma addc_l_spec : forall l c, ok l -> 0 <= c <= 1 ->
  val (addc_l c l) = val l + c /\ ok (addc_l c l)
  /\ zlen l <= zlen (addc_l c l) <= zlen l + 1
  /\ (norm l -> norm (addc_l c l)).
Proof.
  induction l as [|x t IH]; intros c Hok Hc.
  - cbn [addc_l]. destruct (Z.eqb_spec c 0) as [->|Hcnz].
    + cbn. repeat split; auto; lia.
    + cbn [val]. rewrite zlen_cons, ?zlen_nil. repeat split; try lia.
      * apply ok_cons. unfold B. split; [lia|apply ok_nil].
      * intros _. right. cbn. exact Hcnz.
  - apply ok_cons in Hok as [Hx Ht]. cbn [addc_l]. destruct (Z.eqb_spec c 0) as [->|Hcnz].
    + repeat split; auto; try lia. apply ok_cons; auto.
    + assert (Hc' : 0 <= (x + c) / B <= 1).
      { split; [apply Z.div_pos; unfold B in *; lia|]. apply Z.div_le_upper_bound; unfold B in *; lia. }
      specialize (IH ((x + c) / B) Ht Hc'). destruct IH as (Hv & Hokr & Hlen & Hn).
      cbn [val]. rewrite !zlen_cons.
      split; [|split; [|split; [lia|]]].
      * rewrite Hv. pose proof (split_B (x + c)). lia.
      * apply ok_cons. split; [apply mod_B_range | exact Hokr].
      * intros Hnl. right.
        destruct (addc_l ((x + c) / B) t) as [|y r] eqn:Er.
        -- (* [comment removed for export] *)
           cbn. assert (t = []) as -> by (destruct t; [reflexivity|]; rewrite zlen_cons, ?zlen_nil in Hlen; pose proof (zlen_nonneg t); cbn in Hlen; lia).
           cbn in Hv. pose proof (split_B (x + c)) as Hs.
           assert ((x + c) / B = 0) by lia.
           intros Hm. rewrite Hm in Hs. lia.
        -- rewrite last_cons_cons.
           destruct t as [|x2 t'].
           ++ (* [comment removed for export] *)
              cbn [addc_l] in Er. destruct (Z.eqb_spec ((x + c) / B) 0); [discriminate|].
              injection Er as <- <-. cbn. lia.
           ++ destruct Hnl as [?|Hnl]; [discriminate|]. rewrite last_cons_cons in Hnl.
              destruct (Hn (or_intror Hnl)) as [?|Hg]; [discriminate|exact Hg].
Qed.

Lemma add_l_spec : forall o l c, ok l -> ok o -> 0 <= c <= 1 ->
  val (add_l c l o) = val l + val o + c /\ ok (add_l c l o)
  /\ Z.max (zlen l) (zlen o) <= zlen (add_l c l o) <= Z.max (zlen l) (zlen o) + 1
  /\ (norm l -> norm o -> norm (add_l c l o)).
Proof.
  induction o as [|y o' IH]; intros l c Hok Hoo Hc.
  - cbn [add_l]. pose proof (addc_l_spec l c Hok Hc) as (Hv & Hokr & Hlen & Hn).
    cbn [val]. replace (zlen (@nil Z)) with 0 by reflexivity. pose proof (zlen_nonneg l).
    repeat split; auto; try lia.
  - apply ok_cons in Hoo as [Hy Ho'].
    (* [comment removed for export] *)
    assert (GEN : forall h l', ok l' -> 0 <= h < B -> (l = [] /\ l' = [] /\ h = 0 \/ l = h :: l') ->
      let s := h + y + c in
      val (((s mod B) :: add_l (s / B) l' o')) = val l + val (y :: o') + c
      /\ ok ((s mod B) :: add_l (s / B) l' o')
      /\ Z.max (zlen l) (zlen (y :: o')) <= zlen ((s mod B) :: add_l (s / B) l' o') <= Z.max (zlen l) (zlen (y :: o')) + 1
      /\ (norm l -> norm (y :: o') -> norm ((s mod B) :: add_l (s / B) l' o'))).
    { intros h l' Hokl' Hh Hcase. cbn zeta.
      assert (Hc' : 0 <= (h + y + c) / B <= 1).
      { split; [apply Z.div_pos; unfold B in *; lia|].
        assert ((h + y + c) / B < 2) by (apply Z.div_lt_upper_bound; unfold B in *; lia). lia. }
      specialize (IH l' ((h + y + c) / B) Hokl' Ho' Hc'). destruct IH as (Hv & Hokr & Hlen & Hn).
      assert (Hvl : val l = h + B * val l' /\ zlen l = (if match l with [] => true | _ => false end then 0 else zlen l' + 1)).
      { destruct Hcase as [(E1 & E2 & E3)|E4]; [subst l l' h; cbn; lia | subst l; cbn [val]; rewrite zlen_cons; lia]. }
      destruct Hvl as [Hvl Hzl].
      cbn [val]. rewrite !zlen_cons.
      split; [|split; [|split]].
      + rewrite Hv, Hvl. pose proof (split_B (h + y + c)). lia.
      + apply ok_cons. split; [apply mod_B_range | exact Hokr].
      + rewrite Hzl. pose proof (zlen_nonneg l'). pose proof (zlen_nonneg o').
        destruct l; [destruct Hcase as [(_ & E2 & _)|?]; [subst l'|discriminate]; cbn in *; lia | lia].
      + intros Hnl Hno. right.
        destruct (add_l ((h + y + c) / B) l' o') as [|z r] eqn:Er.
        -- cbn. (* [comment removed for export] *)
           assert (o' = []) as -> by (destruct o'; [reflexivity|]; rewrite zlen_cons, ?zlen_nil in Hlen; pose proof (zlen_nonneg o'); pose proof (zlen_nonneg l'); lia).
           assert (l' = []) as -> by (destruct l'; [reflexivity|]; rewrite zlen_cons, ?zlen_nil in Hlen; pose proof (zlen_nonneg l'); cbn in Hlen; lia).
           cbn in Hv. pose proof (split_B (h + y + c)) as Hs.
           assert ((h + y + c) / B = 0) by lia.
           (* [comment removed for export] *)
           destruct Hno as [?|Hno]; [discriminate|]. cbn in Hno.
           intros Hm. rewrite Hm in Hs. lia.
        -- rewrite last_cons_cons.
           destruct l' as [|h2 l'']; destruct o' as [|y2 o''].
           ++ cbn [add_l addc_l] in Er. destruct (Z.eqb_spec ((h + y + c) / B) 0); [discriminate|].
              injection Er as <- <-. cbn. lia.
           ++ assert (Hn2 : norm (z :: r)); [apply Hn|destruct Hn2 as [?|G]; [discriminate|exact G]].
              ** left; reflexivity.
              ** destruct Hno as [?|Hno]; [discriminate|]. right. exact Hno.
           ++ assert (Hn2 : norm (z :: r)); [apply Hn|destruct Hn2 as [?|G]; [discriminate|exact G]].
              ** destruct Hcase as [(_ & ? & _)|El]; [discriminate|]. subst l.
                 destruct Hnl as [?|Hnl]; [discriminate|]. right. exact Hnl.
              ** left; reflexivity.
           ++ assert (Hn2 : norm (z :: r)); [apply Hn|destruct Hn2 as [?|G]; [discriminate|exact G]].
              ** destruct Hcase as [(_ & ? & _)|El]; [discriminate|]. subst l.
                 destruct Hnl as [?|Hnl]; [discriminate|]. right. exact Hnl.
              ** destruct Hno as [?|Hno]; [discriminate|]. right. exact Hno. }
    destruct l as [|x t].
    + cbn [add_l]. replace (y + c) with (0 + y + c) by lia. apply (GEN 0 []); auto. unfold B; lia.
    + apply ok_cons in Hok as [Hx Ht]. cbn [add_l]. apply (GEN x t); auto.
Qed.

Lemma add_u64_spec : forall d b, ok (cells b) -> norm (cells b) -> 0 <= d < 2 ^ 64 ->
  ok (cells (add_u64 d b)) /\ norm (cells (add_u64 d b)) /\ val (cells (add_u64 d b)) = val (cells b) + d
  /\ ex (add_u64 d b) = ex b /\ zlen (cells (add_u64 d b)) <= Z.max (zlen (cells b)) 3 + 1.
Proof.
  intros d b Hok Hn Hd. unfold add_u64.
  destruct (Z.eqb_spec d 0) as [->|Hnz].
  { pose proof (zlen_nonneg (cells b)). repeat split; auto; lia. }
  assert (HdB : 0 <= d < B ^ Z.of_nat 3) by (change (B ^ Z.of_nat 3) with (2 ^ 84); lia).
  destruct (chunks_spec 3 d HdB) as (Hcv & Hcok & Hcn & Hcl).
  unfold add_bn. cbn [cells ex].
  pose proof (add_l_spec (chunks 3 d) (cells b) 0 Hok Hcok ltac:(lia)) as (Hv & Hokr & Hlen & Hnr).
  repeat split; auto; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition digits_ok (ds : list Z) : Prop := Forall (fun d => 48 <= d <= 57) ds.

Lemma read_digits_bound : forall ds r, digits_ok ds -> 0 <= r ->
  r * 10 ^ zlen ds <= read_digits ds r < (r + 1) * 10 ^ zlen ds.
Proof.
  induction ds as [|d t IH]; intros r Hds Hr.
  - cbn. repeat split; auto using ok_nil; lia.
  - inversion Hds; subst. cbn [read_digits]. rewrite zlen_cons, Z.pow_add_r, Z.pow_1_r by (pose proof (zlen_nonneg t); lia).
    specialize (IH (r * 10 + (d - 48)) ltac:(assumption) ltac:(lia)).
    pose proof (Z.pow_nonneg 10 (zlen t)). nia.
Qed.

Lemma read_digits_app : forall d1 d2 r, read_digits (d1 ++ d2) r = read_digits d2 (read_digits d1 r).
Proof. induction d1; intros; cbn; auto. Qed.

(* [comment removed for export] *)
Definition decval (ds : list Z) : Z := read_digits ds 0.

Lemma decval_bound : forall ds, digits_ok ds -> 0 <= decval ds < 10 ^ zlen ds.
Proof. intros. unfold decval. pose proof (read_digits_bound ds 0 H ltac:(lia)). lia. Qed.

Lemma read_digits_shift : forall ds r, 0 <= r -> digits_ok ds ->
  read_digits ds r = r * 10 ^ zlen ds + decval ds.
Proof.
  induction ds as [|d t IH]; intros r Hr Hds.
  - cbn. rewrite ?zlen_nil. cbn. unfold decval. cbn. lia.
  - inversion Hds; subst. unfold decval. cbn [read_digits].
    rewrite (IH (r * 10 + (d - 48))), (IH (0 * 10 + (d - 48))) by (auto; lia).
    rewrite zlen_cons, Z.pow_add_r, Z.pow_1_r by (pose proof (zlen_nonneg t); lia). lia.
Qed.

Lemma clamp_l_spec : forall fuel l, ok l ->
  val (clamp_l fuel l) = val l /\ ok (clamp_l fuel l) /\ zlen (clamp_l fuel l) <= zlen l
  /\ ((length l <= fuel)%nat -> norm (clamp_l fuel l)).
Proof.
  induction fuel as [|f IH]; intros l Hok.
  - cbn. repeat split; auto; try lia. intros Hl. destruct l; [left; reflexivity | cbn in Hl; lia].
  - cbn [clamp_l]. destruct l as [|x t] eqn:El.
    + cbn. repeat split; auto; try lia.
    + rewrite <- El in *. assert (Hne : l <> []) by (subst; congruence).
      destruct (@exists_last _ l Hne) as (l' & c & El').
      assert (Hlt : (0 <? zlen l) = true) by (apply Z.ltb_lt; rewrite El, zlen_cons; pose proof (zlen_nonneg t); lia).
      rewrite Hlt. cbn [andb].
      assert (Hlast : zget l (zlen l - 1) = c).
      { rewrite El'. unfold zget. rewrite zlen_app. replace (zlen [c]) with 1 by reflexivity.
        replace (Z.to_nat (zlen l' + 1 - 1)) with (length l') by (unfold zlen; lia).
        apply nth_middle. }
      rewrite Hlast. rewrite El' in Hok. apply ok_app in Hok as [Hok' Hc].
      destruct (Z.eqb_spec c 0) as [->|Hcnz].
      * rewrite El', removelast_last. specialize (IH l' Hok') as (Hv & Hokr & Hlen & Hn).
        rewrite val_app, zlen_app. cbn [val]. replace (zlen [0]) with 1 by reflexivity.
        repeat split; auto; try lia. intros Hl. apply Hn. rewrite ?El', length_app in Hl. cbn in Hl. lia.
      * rewrite El'. repeat split; try lia. apply ok_app; auto. intros _. apply norm_snoc. exact Hcnz.
Qed.

Lemma clamp_spec : forall b, ok (cells b) ->
  ok (cells (clamp b)) /\ norm (cells (clamp b)) /\ val (cells (clamp b)) = val (cells b)
  /\ zlen (cells (clamp b)) <= zlen (cells b)
  /\ (cells (clamp b) <> [] -> ex (clamp b) = ex b).
Proof.
  intros b Hok. unfold clamp. pose proof (clamp_l_spec (length (cells b)) (cells b) Hok) as (Hv & Hokr & Hlen & Hn).
  cbn [cells ex]. repeat split; auto. intros Hne. destruct (clamp_l _ _); [congruence|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma clamp_l_norm : forall fuel l, norm l -> clamp_l fuel l = l.
Proof.
  intros fuel l Hn. destruct fuel; [reflexivity|]. cbn [clamp_l].
  destruct l as [|x t] eqn:El; [reflexivity|]. rewrite <- El in *.
  destruct Hn as [Hn|Hn]; [subst; discriminate|].
  assert (Hne : l <> []) by (subst; congruence).
  destruct (@exists_last _ l Hne) as (l' & c & El').
  assert (Hlast : zget l (zlen l - 1) = c).
  { rewrite El'. unfold zget. rewrite zlen_app. replace (zlen [c]) with 1 by reflexivity.
    replace (Z.to_nat (zlen l' + 1 - 1)) with (length l') by (unfold zlen; lia).
    apply nth_middle. }
  rewrite Hlast. rewrite El', last_last in Hn. destruct (Z.eqb_spec c 0); [lia|].
  rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ads_step_spec : forall ds b, ok (cells b) -> norm (cells b) -> ex b = 0 -> digits_ok ds -> zlen ds <= 19 ->
  let b' := ads_step ds b in
  ok (cells b') /\ norm (cells b') /\ ex b' = 0 /\ val (cells b') = val (cells b) * 10 ^ zlen ds + decval ds.
Proof.
  intros ds b Hok Hn Hex Hds Hlen. unfold ads_step.
  pose proof (zlen_nonneg ds) as Hz.
  pose proof (mulpow10_spec (zlen ds) b Hok Hn Hz) as HM. cbn zeta in HM. destruct HM as (Hok1 & Hn1 & Hv1 & Hex1 & Hnil1).
  pose proof (decval_bound ds Hds) as Hdv.
  assert (Hd64 : 0 <= read_digits ds 0 < 2 ^ 64).
  { fold (decval ds). split; [lia|]. apply Z.lt_le_trans with (m := 10 ^ zlen ds); [lia|].
    apply Z.le_trans with (m := 10 ^ 19); [apply Z.pow_le_mono_r; lia | lia]. }
  pose proof (add_u64_spec (read_digits ds 0) _ Hok1 Hn1 Hd64) as (Hok2 & Hn2 & Hv2 & Hex2 & _).
  cbn zeta. repeat split; auto.
  - rewrite Hex2. destruct (cells b) as [|x t] eqn:Ec.
    + (* [comment removed for export] *)
      unfold mulpow10. destruct (zlen ds =? 0); rewrite ?Ec; exact Hex.
    + rewrite Hex1 by congruence. rewrite Hex, Z.div_small by lia. reflexivity.
  - rewrite Hv2, Hv1. fold (decval ds). rewrite Z.mod_small by lia.
    replace (10 ^ zlen ds) with (5 ^ zlen ds * 2 ^ zlen ds); [lia|].
    rewrite <- Z.pow_mul_l. reflexivity.
Qed.

Lemma digits_ok_split : forall n ds, digits_ok ds -> digits_ok (firstn n ds) /\ digits_ok (skipn n ds).
Proof. intros n ds H. unfold digits_ok in *. rewrite <- (firstn_skipn n ds) in H. apply Forall_app in H. exact H. Qed.
Lemma digits_ok_firstn : forall n ds, digits_ok ds -> digits_ok (firstn n ds).
Proof. intros. apply (proj1 (digits_ok_split n ds H)). Qed.
Lemma digits_ok_skipn : forall n ds, digits_ok ds -> digits_ok (skipn n ds).
Proof. intros. apply (proj2 (digits_ok_split n ds H)). Qed.

Lemma decval_app : forall d1 d2, digits_ok d2 -> digits_ok d1 -> decval (d1 ++ d2) = decval d1 * 10 ^ zlen d2 + decval d2.
Proof.
  intros. unfold decval. rewrite read_digits_app. apply read_digits_shift; auto.
  pose proof (decval_bound d1 H0). unfold decval in *. lia.
Qed.

Lemma ads_loop_spec : forall fuel ds b, ok (cells b) -> norm (cells b) -> ex b = 0 -> digits_ok ds ->
  let (b', rest) := ads_loop fuel ds b in
  ok (cells b') /\ norm (cells b') /\ ex b' = 0 /\ digits_ok rest
  /\ (exists done, ds = done ++ rest /\ val (cells b') = val (cells b) * 10 ^ zlen done + decval done)
  /\ ((Nat.div (length ds) 19 <= fuel)%nat -> zlen rest < 19).
Proof.
  induction fuel as [|f IH]; intros ds b Hok Hn Hex Hds.
  - cbn [ads_loop]. split; [auto|split; [auto|split; [auto|split; [auto|split]]]].
    + exists []. split; [reflexivity|]. replace (zlen (@nil Z)) with 0 by reflexivity. unfold decval; cbn [read_digits]. lia.
    + intros Hd. pose proof (Nat.div_mod_eq (length ds) 19).
      assert (E0 : (Nat.div (length ds) 19 = 0)%nat) by lia. apply Nat.div_small_iff in E0; [|lia]. unfold zlen. lia.
  - cbn [ads_loop]. destruct (Z.ltb_spec (zlen ds) 19) as [Hlt|Hge].
    + split; [auto|split; [auto|split; [auto|split; [auto|split; [|intros; assumption]]]]].
      exists []. split; [reflexivity|]. replace (zlen (@nil Z)) with 0 by reflexivity. unfold decval; cbn [read_digits]. lia.
    + pose proof (ads_step_spec (firstn 19 ds) b Hok Hn Hex (digits_ok_firstn _ _ Hds)
                    ltac:(unfold zlen; rewrite length_firstn; lia)) as HS.
      cbn zeta in HS. destruct HS as (Hok1 & Hn1 & Hex1 & Hv1).
      specialize (IH (skipn 19 ds) _ Hok1 Hn1 Hex1 (digits_ok_skipn _ _ Hds)).
      destruct (ads_loop f (skipn 19 ds) _) as [b' rest]. destruct IH as (Hok' & Hn' & Hex' & Hrest & (done & Hsplit & Hv') & Hfuel).
      repeat split; auto.
      * exists (firstn 19 ds ++ done). split.
        -- rewrite <- app_assoc, <- Hsplit. symmetry. apply firstn_skipn.
        -- rewrite Hv', Hv1, zlen_app, Z.pow_add_r by (apply zlen_nonneg || (split; apply zlen_nonneg)).
           rewrite decval_app; [| | apply digits_ok_firstn; auto].
           2:{ unfold digits_ok. rewrite Forall_forall. intros x Hx. pose proof (digits_ok_skipn 19 ds Hds) as Hs.
               rewrite Hsplit in Hs. unfold digits_ok in Hs. rewrite Forall_forall in Hs. apply Hs. apply in_or_app. auto. }
           lia.
      * intros Hd. apply Hfuel. rewrite length_skipn.
        unfold zlen in Hge.
        pose proof (Nat.div_mod_eq (length ds) 19). pose proof (Nat.div_mod_eq (length ds - 19) 19).
        assert (Nat.div (length ds - 19) 19 = Nat.div (length ds) 19 - 1)%nat; [|lia].
        replace (length ds) with ((length ds - 19) + 1 * 19)%nat at 2 by lia.
        rewrite Nat.div_add by lia. lia.
Qed.

Lemma assign_decimal_spec : forall ds, digits_ok ds ->
  let b := assign_decimal ds in
  ok (cells b) /\ norm (cells b) /\ val (cells b) = decval ds /\ (cells b <> [] -> ex b = 0).
Proof.
  intros ds Hds. unfold assign_decimal.
  pose proof (ads_loop_spec (Nat.div (length ds) 19) ds bn_zero ok_nil (or_introl eq_refl) eq_refl Hds) as HL.
  destruct (ads_loop _ ds bn_zero) as [b1 rest]. destruct HL as (Hok1 & Hn1 & Hex1 & Hrest & (done & Hsplit & Hv1) & Hfuel).
  specialize (Hfuel ltac:(lia)).
  pose proof (ads_step_spec rest b1 Hok1 Hn1 Hex1 Hrest ltac:(lia)) as HS. cbn zeta in HS. destruct HS as (Hok2 & Hn2 & Hex2 & Hv2).
  pose proof (clamp_spec (ads_step rest b1) Hok2) as (Hok3 & Hn3 & Hv3 & _ & Hex3).
  cbn zeta. repeat split; auto.
  - assert (Hdone : digits_ok done).
    { unfold digits_ok in *. rewrite Forall_forall in *. intros x Hx. apply Hds. rewrite Hsplit. apply in_or_app; auto. }
    rewrite Hv3, Hv2, Hv1. cbn [val cells bn_zero]. rewrite Hsplit. rewrite decval_app; auto; lia.
  - intros Hne. rewrite (Hex3 Hne). exact Hex2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KBUF : Z := 94.
Definition KDIY : Z := 96.

Lemma env_buf1 : 10 ^ 780 * 2 ^ 27 < B ^ KBUF. Proof. vm_compute. reflexivity. Qed.
Lemma env_buf2 : 10 ^ 309 * 2 ^ 27 * 2 ^ 27 < B ^ KBUF. Proof. vm_compute. reflexivity. Qed.
Lemma env_diy : 2 ^ 64 * 5 ^ 1103 * 2 ^ 27 * 2 ^ 27 < B ^ KDIY. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mul64_len : forall b, zlen (cells b) <= zlen (cells (mul64 kFive27_lo kFive27_hi b))
  /\ (cells b <> [] -> exists r c, mul64_l kFive27_lo kFive27_hi 0 (cells b) = (r, c)
        /\ cells (mul64 kFive27_lo kFive27_hi b) = r ++ chunks 3 c /\ ex (mul64 kFive27_lo kFive27_hi b) = ex b).
Proof.
  intros b. unfold mul64. destruct (cells b) as [|x t] eqn:Ec.
  - rewrite Ec. split; [lia|congruence].
  - destruct (mul64_l kFive27_lo kFive27_hi 0 (x :: t)) as [r c] eqn:Em. cbn [cells ex].
    assert (Hl : length r = length (x :: t)).
    { pose proof (f_equal fst Em) as H. cbn [fst] in H. subst r.
      clear Em. generalize 0. generalize (x :: t). induction l; intros; cbn; [reflexivity|].
      destruct (mul64_l _ _ _ l) eqn:E. cbn. f_equal. specialize (IHl (z / B + (z mod B + kFive27_lo * a) / B + kFive27_hi * a * 16)). rewrite E in IHl. exact IHl. }
    rewrite zlen_app. unfold zlen in *. rewrite Hl. pose proof (zlen_nonneg (chunks 3 c)). unfold zlen in H. split; [lia|].
    intros _. exists r, c. auto.
Qed.

Lemma mul32_len : forall F b, F <> 0 -> zlen (cells b) <= zlen (cells (mul32 F b)).
Proof.
  intros F b HF. unfold mul32. destruct (Z.eqb_spec F 1); [lia|]. destruct (Z.eqb_spec F 0); [lia|].
  destruct (cells b) as [|x t] eqn:Ec; [rewrite Ec; lia|].
  destruct (mul32_l F 0 (x :: t)) as [r c] eqn:Em. cbn [cells].
  assert (Hl : length r = length (x :: t)).
  { pose proof (f_equal fst Em) as H. cbn [fst] in H. subst r.
    clear Em. generalize 0. generalize (x :: t). induction l; intros; cbn; [reflexivity|].
    destruct (mul32_l _ _ l) eqn:E. cbn. f_equal. specialize (IHl ((F * a + z) / B)). rewrite E in IHl. exact IHl. }
  rewrite zlen_app. unfold zlen in *. rewrite Hl. pose proof (zlen_nonneg (chunks 3 c)). unfold zlen in H. lia.
Qed.

Lemma pow27_len : forall fuel r b, zlen (cells b) <= zlen (cells (fst (pow27_loop fuel r b))).
Proof.
  induction fuel as [|f IH]; intros r b; cbn [pow27_loop fst]; [lia|].
  destruct (r <? 27); [cbn; lia|]. eapply Z.le_trans; [apply (proj1 (mul64_len b)) | apply IH].
Qed.

Lemma pow13_len : forall fuel r b, zlen (cells b) <= zlen (cells (fst (pow13_loop fuel r b))).
Proof.
  induction fuel as [|f IH]; intros r b; cbn [pow13_loop fst]; [lia|].
  destruct (r <? 13); [cbn; lia|]. eapply Z.le_trans; [apply (mul32_len kFive13 b); unfold kFive13; lia | apply IH].
Qed.
