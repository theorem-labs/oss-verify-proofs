(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci. Pure Gallina models of the code fuzz_uci's three checks run, and
   the facts that make each check's abort unreachable:
   - rp_uci_int_m      = src/repace_conf.c rp_uci_int (reply, n, cur), over the n reply bytes;
   - expected_value_m  = fuzz_uci.c expected_value (r, n, cur), the harness's own reading of the grammar;
   - hold_m, rp_hot_clamp_m = fuzz_uci.c hold and src/repace_conf.c rp_hot_clamp, over struct rp_hot's five ints.
   Bytes are Z in [0, 255] (riscv64: char is unsigned). The walks of rp_uci_int and rp_hot_clamp state their results by
   these models; check_value's abort is unreachable by uci_value_ok, check_clamp's by the five clamp_* theorems, and
   check_no_overread's because rp_uci_int_m reads only the n bytes it is given (it is a function of that list). *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

Definition INT_MIN : Z := - 2 ^ 31.
Definition INT_MAX : Z := 2 ^ 31 - 1.

Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition is_lead_blank (c : Z) : bool := (c =? 32) || (c =? 9).
Definition is_trail_blank (c : Z) : bool := (c =? 32) || (c =? 9) || (c =? 13).

(* the first line: the bytes before the first LF (memchr (reply, '\n', n)), or all of them *)
Fixpoint first_line (r : list Z) : list Z :=
  match r with
  | [] => []
  | c :: t => if c =? 10 then [] else c :: first_line t
  end.

Fixpoint skip (f : Z -> bool) (l : list Z) : list Z :=
  match l with
  | c :: t => if f c then skip f t else l
  | [] => []
  end.

(* rp_uci_int's digit loop: None is its early `return cur` once v > (long long)INT_MAX + 1 *)
Fixpoint digits_rp (v : Z) (l : list Z) : option (Z * list Z) :=
  match l with
  | c :: t =>
      if is_digit c then
        let v' := v * 10 + (c - 48) in
        if 2 ^ 31 <? v' then None else digits_rp v' t
      else Some (v, l)
  | [] => Some (v, [])
  end.

(* expected_value's digit loop: the value stops growing at 10^10 *)
Fixpoint digits_ev (v : Z) (l : list Z) : Z * list Z :=
  match l with
  | c :: t =>
      if is_digit c then digits_ev (if v <? 10 ^ 10 then v * 10 + (c - 48) else v) t
      else (v, l)
  | [] => (v, [])
  end.

Definition sign_split (l : list Z) : bool * list Z :=
  match l with
  | c :: t => if (c =? 43) || (c =? 45) then (c =? 45, t) else (false, l)
  | [] => (false, [])
  end.

Definition finish (neg : bool) (v : Z) (rest : list Z) (cur : Z) : Z :=
  match skip is_trail_blank rest with
  | [] => let v' := if neg then - v else v in
          if (v' <? INT_MIN) || (INT_MAX <? v') then cur else v'
  | _ => cur
  end.

Definition rp_uci_int_m (r : list Z) (cur : Z) : Z :=
  match r with
  | [] => cur
  | _ =>
      let '(neg, l) := sign_split (skip is_lead_blank (first_line r)) in
      match l with
      | c :: _ =>
          if is_digit c then
            match digits_rp 0 l with
            | None => cur
            | Some (v, rest) => finish neg v rest cur
            end
          else cur
      | [] => cur
      end
  end.

Definition expected_value_m (r : list Z) (cur : Z) : Z :=
  let '(neg, l) := sign_split (skip is_lead_blank (first_line r)) in
  match l with
  | c :: _ =>
      if is_digit c then let '(v, rest) := digits_ev 0 l in finish neg v rest cur else cur
  | [] => cur
  end.

(* ---- check_value: the reader agrees with the harness's grammar ---- *)

Lemma digits_ev_mono : forall l v, 0 <= v -> v <= fst (digits_ev v l).
Proof.
  induction l as [|c t IH]; intros v Hv; cbn [digits_ev fst]; [lia|].
  destruct (is_digit c) eqn:D; [|cbn; lia].
  unfold is_digit in D. apply andb_true_iff in D as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2.
  destruct (v <? 10 ^ 10) eqn:L.
  - specialize (IH (v * 10 + (c - 48)) ltac:(lia)). lia.
  - apply IH. lia.
Qed.

(* when rp_uci_int's loop finishes, the harness's loop reaches the same value and the same rest *)
Lemma digits_rp_some : forall l v v' rest, 0 <= v <= 2 ^ 31 ->
  digits_rp v l = Some (v', rest) -> digits_ev v l = (v', rest) /\ 0 <= v' <= 2 ^ 31.
Proof.
  induction l as [|c t IH]; intros v v' rest Hv H; cbn [digits_rp] in H; cbn [digits_ev].
  - inversion H; subst. split; [reflexivity | lia].
  - destruct (is_digit c) eqn:D.
    + unfold is_digit in D. apply andb_true_iff in D as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2.
      destruct (2 ^ 31 <? v * 10 + (c - 48)) eqn:B; [discriminate|].
      apply Z.ltb_ge in B.
      assert (L : v <? 10 ^ 10 = true) by (apply Z.ltb_lt; lia). rewrite L.
      apply IH; [lia | exact H].
    + inversion H; subst. split; [reflexivity | lia].
Qed.

(* when rp_uci_int's loop returns early, the harness's value is past an int *)
Lemma digits_rp_none : forall l v, 0 <= v -> digits_rp v l = None -> 2 ^ 31 < fst (digits_ev v l).
Proof.
  induction l as [|c t IH]; intros v Hv H; cbn [digits_rp] in H; [discriminate|].
  cbn [digits_ev].
  destruct (is_digit c) eqn:D; [|discriminate].
  unfold is_digit in D. apply andb_true_iff in D as [D1 D2]. apply Z.leb_le in D1. apply Z.leb_le in D2.
  destruct (2 ^ 31 <? v * 10 + (c - 48)) eqn:B.
  - apply Z.ltb_lt in B.
    destruct (v <? 10 ^ 10) eqn:L.
    + pose proof (digits_ev_mono t (v * 10 + (c - 48)) ltac:(lia)). lia.
    + apply Z.ltb_ge in L. pose proof (digits_ev_mono t v Hv). lia.
  - apply Z.ltb_ge in B.
    assert (L : v <? 10 ^ 10 = true) by (apply Z.ltb_lt; lia). rewrite L.
    apply IH; [lia | exact H].
Qed.

Lemma finish_big : forall neg v rest cur, 2 ^ 31 < v -> finish neg v rest cur = cur.
Proof.
  intros neg v rest cur Hv. unfold finish.
  destruct (skip is_trail_blank rest); [|reflexivity].
  unfold INT_MIN, INT_MAX. destruct neg.
  - assert (E : - v <? - 2 ^ 31 = true) by (apply Z.ltb_lt; lia). rewrite E. reflexivity.
  - assert (E : 2 ^ 31 - 1 <? v = true) by (apply Z.ltb_lt; lia). rewrite E, orb_true_r. reflexivity.
Qed.

Theorem uci_value_ok : forall r cur, rp_uci_int_m r cur = expected_value_m r cur.
Proof.
  intros r cur. unfold rp_uci_int_m, expected_value_m.
  destruct r as [|c0 r0].
  - reflexivity.
  - destruct (sign_split (skip is_lead_blank (first_line (c0 :: r0)))) as [neg l].
    destruct l as [|c t]; [reflexivity|].
    destruct (is_digit c) eqn:D; [|reflexivity].
    destruct (digits_rp 0 (c :: t)) as [[v rest]|] eqn:H.
    + destruct (digits_rp_some (c :: t) 0 v rest ltac:(lia) H) as [E _]. rewrite E. reflexivity.
    + pose proof (digits_rp_none (c :: t) 0 ltac:(lia) H) as B.
      destruct (digits_ev 0 (c :: t)) as [v rest] eqn:E. cbn [fst] in B.
      symmetry. apply finish_big. exact B.
Qed.

(* rp_uci_int_m is an int, and so is expected_value_m, for an int cur: the C result is a 32-bit int *)
Lemma finish_range : forall neg v rest cur, INT_MIN <= cur <= INT_MAX ->
  INT_MIN <= finish neg v rest cur <= INT_MAX.
Proof.
  intros neg v rest cur Hc. unfold finish.
  destruct (skip is_trail_blank rest); [|exact Hc].
  cbv zeta. set (x := if neg then - v else v).
  destruct (Z.ltb_spec x INT_MIN); destruct (Z.ltb_spec INT_MAX x); cbn [orb]; lia.
Qed.

Theorem rp_uci_int_range : forall r cur, INT_MIN <= cur <= INT_MAX ->
  INT_MIN <= rp_uci_int_m r cur <= INT_MAX.
Proof.
  intros r cur Hc. unfold rp_uci_int_m.
  destruct r as [|c0 r0]; [exact Hc|].
  destruct (sign_split (skip is_lead_blank (first_line (c0 :: r0)))) as [neg l].
  destruct l as [|c t]; [exact Hc|].
  destruct (is_digit c); [|exact Hc].
  destruct (digits_rp 0 (c :: t)) as [[v rest]|]; [apply finish_range; exact Hc | exact Hc].
Qed.

(* ---- check_clamp: rp_hot_clamp holds each field to the harness's range ---- *)

Definition hold_m (x lo hi : Z) : Z := if x <? lo then lo else if hi <? x then hi else x.

Record rp_hot := RpHot { prefill_ms : Z; adapt_min_ms : Z; adapt_max_ms : Z; adapt_margin : Z; servo_clamp_ppm : Z }.

(* include/repace_conf.h:27-31 *)
Definition RP_PREFILL_MS_MIN : Z := 1.
Definition RP_PREFILL_MS_MAX : Z := 1000.
Definition RP_ADAPT_MS_MIN : Z := 1.
Definition RP_ADAPT_MS_MAX : Z := 1000.
Definition RP_SERVO_CLAMP_PPM_MAX : Z := 50000.

(* src/repace_conf.c rp_hot_clamp, statement by statement, in order *)
Definition rp_hot_clamp_m (p : rp_hot) (margin_max : Z) : rp_hot :=
  let pf0 := prefill_ms p in
  let pf1 := if pf0 <? RP_PREFILL_MS_MIN then RP_PREFILL_MS_MIN else pf0 in
  let pf2 := if RP_PREFILL_MS_MAX <? pf1 then RP_PREFILL_MS_MAX else pf1 in
  let mn0 := adapt_min_ms p in
  let mn1 := if mn0 <? RP_ADAPT_MS_MIN then RP_ADAPT_MS_MIN else mn0 in
  let mn2 := if RP_ADAPT_MS_MAX <? mn1 then RP_ADAPT_MS_MAX else mn1 in
  let mx0 := adapt_max_ms p in
  let mx1 := if RP_ADAPT_MS_MAX <? mx0 then RP_ADAPT_MS_MAX else mx0 in
  let mx2 := if mx1 <? mn2 then mn2 else mx1 in
  let mg0 := adapt_margin p in
  let mg1 := if mg0 <? 0 then 0 else mg0 in
  let mg2 := if margin_max <? mg1 then margin_max else mg1 in
  let sv0 := servo_clamp_ppm p in
  let sv1 := if sv0 <? 0 then 0 else sv0 in
  let sv2 := if RP_SERVO_CLAMP_PPM_MAX <? sv1 then RP_SERVO_CLAMP_PPM_MAX else sv1 in
  RpHot pf2 mn2 mx2 mg2 sv2.

(* fuzz_uci.c's ranges: PREFILL 1..1000, ADAPT 1..1000, SERVO 0..50000, MARGIN_MAX = { 2^11 - 64, 2^14 - 64 } *)
Definition MARGIN_MAX (bit : bool) : Z := if bit then 2 ^ 14 - 64 else 2 ^ 11 - 64.

Ltac clamp_cases := unfold hold_m; repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; lia.

Theorem clamp_prefill : forall p mm, prefill_ms (rp_hot_clamp_m p mm) = hold_m (prefill_ms p) 1 1000.
Proof. intros p mm. unfold rp_hot_clamp_m, RP_PREFILL_MS_MIN, RP_PREFILL_MS_MAX. cbn [prefill_ms]. clamp_cases. Qed.

Theorem clamp_adapt_min : forall p mm, adapt_min_ms (rp_hot_clamp_m p mm) = hold_m (adapt_min_ms p) 1 1000.
Proof. intros p mm. unfold rp_hot_clamp_m, RP_ADAPT_MS_MIN, RP_ADAPT_MS_MAX. cbn [adapt_min_ms]. clamp_cases. Qed.

Theorem clamp_adapt_max : forall p mm, adapt_max_ms (rp_hot_clamp_m p mm) =
  hold_m (adapt_max_ms p) (hold_m (adapt_min_ms p) 1 1000) 1000.
Proof.
  intros p mm. unfold rp_hot_clamp_m, RP_ADAPT_MS_MIN, RP_ADAPT_MS_MAX. cbn [adapt_max_ms]. unfold hold_m.
  (* split the innermost comparison first, so lia sees each condition once *)
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      lazymatch a with context [Z.ltb _ _] => fail | _ =>
      lazymatch b with context [Z.ltb _ _] => fail | _ => destruct (Z.ltb_spec a b) end end
  end; lia.
Qed.

Theorem clamp_margin : forall p mm, 0 <= mm -> adapt_margin (rp_hot_clamp_m p mm) = hold_m (adapt_margin p) 0 mm.
Proof. intros p mm Hm. unfold rp_hot_clamp_m. cbn [adapt_margin]. clamp_cases. Qed.

Theorem clamp_servo : forall p mm, servo_clamp_ppm (rp_hot_clamp_m p mm) = hold_m (servo_clamp_ppm p) 0 50000.
Proof. intros p mm. unfold rp_hot_clamp_m, RP_SERVO_CLAMP_PPM_MAX. cbn [servo_clamp_ppm]. clamp_cases. Qed.

Lemma margin_max_nonneg : forall b, 0 <= MARGIN_MAX b.
Proof. intros []; cbn; lia. Qed.
