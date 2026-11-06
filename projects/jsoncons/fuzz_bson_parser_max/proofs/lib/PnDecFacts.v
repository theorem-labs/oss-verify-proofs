(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNDF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mag9 x : 0 <= x < 1000000000 * 2 ^ 32 -> ((x / 512) * 19342813113834067 / 2 ^ 64) / 2048 = x / 1000000000.
Proof.
  intros Hx. rewrite (Z.div_div (x / 512 * 19342813113834067) (2 ^ 64) 2048) by lia.
  change (2 ^ 64 * 2048) with (2 ^ 75).
  change 1000000000 with (512 * 1953125). rewrite <- (Z.div_div x 512 1953125) by lia.
  set (n := x / 512). assert (Hn : 0 <= n < 8388608000000001) by (subst n; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  clearbody n. clear x Hx.
  symmetry. apply (Zdiv_unique (n * 19342813113834067) (2 ^ 75) (n / 1953125) ((n / 1953125) * 399807 + (n mod 1953125) * 19342813113834067)).
  - pose proof (Z.mod_pos_bound n 1953125 ltac:(lia)). pose proof (Z.div_pos n 1953125 ltac:(lia) ltac:(lia)).
    assert (n / 1953125 < 4294967297) by (apply Z.div_lt_upper_bound; lia). lia.
  - pose proof (Z.div_mod n 1953125 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Definition ltemp (r p : Z) : Z := ((4294967296 * r) mod 2 ^ 64 + p) mod 2 ^ 64.
Definition lquot (r p : Z) : Z := (((ltemp r p / 512) * 19342813113834067) / 2 ^ 64) / 2048.
Definition lrem (r p : Z) : Z := ((4294967296 * r) mod 2 ^ 64 + ((p + ((18446744072709551616 * lquot r p) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64.

Lemma ltemp_val r p : 0 <= r < 1000000000 -> 0 <= p < 2 ^ 32 -> ltemp r p = 4294967296 * r + p.
Proof. intros Hr Hp. unfold ltemp. rewrite (Z.mod_small (4294967296 * r)) by lia. apply Z.mod_small. lia. Qed.
Lemma lquot_val r p : 0 <= r < 1000000000 -> 0 <= p < 2 ^ 32 -> lquot r p = (4294967296 * r + p) / 1000000000.
Proof. intros Hr Hp. unfold lquot. rewrite ltemp_val by lia. apply mag9. lia. Qed.
Lemma lquot_bound r p : 0 <= r < 1000000000 -> 0 <= p < 2 ^ 32 -> 0 <= lquot r p < 2 ^ 32.
Proof. intros Hr Hp. rewrite lquot_val by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. Qed.
Lemma lrem_val r p : 0 <= r < 1000000000 -> 0 <= p < 2 ^ 32 -> lrem r p = (4294967296 * r + p) mod 1000000000.
Proof.
  intros Hr Hp. unfold lrem. rewrite lquot_val by lia. rewrite (Z.mod_small (4294967296 * r)) by lia.
  set (t := 4294967296 * r + p). pose proof (Z.div_mod t 1000000000 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound t 1000000000 ltac:(lia)) as MB.
  set (q := t / 1000000000) in *.
  rewrite Zplus_mod_idemp_r. rewrite Z.add_assoc. rewrite Zplus_mod_idemp_r.
  replace (4294967296 * r + p + 18446744072709551616 * q) with ((t - 1000000000 * q) + q * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  replace (t - 1000000000 * q) with (t mod 1000000000) by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma ldiv4 p0 p1 p2 p3 :
  0 <= p0 < 1000000000 -> 0 <= p1 < 2 ^ 32 -> 0 <= p2 < 2 ^ 32 -> 0 <= p3 < 2 ^ 32 ->
  let q0 := lquot 0 p0 in let r0 := lrem 0 p0 in
  let q1 := lquot r0 p1 in let r1 := lrem r0 p1 in
  let q2 := lquot r1 p2 in let r2 := lrem r1 p2 in
  let q3 := lquot r2 p3 in let r3 := lrem r2 p3 in
  let W := p0 * 2 ^ 96 + p1 * 2 ^ 64 + p2 * 2 ^ 32 + p3 in
  W = 1000000000 * (q0 * 2 ^ 96 + q1 * 2 ^ 64 + q2 * 2 ^ 32 + q3) + r3 /\ 0 <= r3 < 1000000000
  /\ 0 <= q0 < 2 ^ 32 /\ 0 <= q1 < 2 ^ 32 /\ 0 <= q2 < 2 ^ 32 /\ 0 <= q3 < 2 ^ 32
  /\ 0 <= r0 < 1000000000 /\ 0 <= r1 < 1000000000 /\ 0 <= r2 < 1000000000.
Proof.
  intros H0 H1 H2 H3. cbn zeta.
  pose proof (lquot_val 0 p0 ltac:(lia) ltac:(lia)) as Q0. pose proof (lrem_val 0 p0 ltac:(lia) ltac:(lia)) as R0.
  pose proof (Z.mod_pos_bound (4294967296 * 0 + p0) 1000000000 ltac:(lia)) as B0. rewrite <- R0 in B0.
  pose proof (lquot_val (lrem 0 p0) p1 B0 ltac:(lia)) as Q1. pose proof (lrem_val (lrem 0 p0) p1 B0 ltac:(lia)) as R1.
  pose proof (Z.mod_pos_bound (4294967296 * lrem 0 p0 + p1) 1000000000 ltac:(lia)) as B1. rewrite <- R1 in B1.
  pose proof (lquot_val (lrem (lrem 0 p0) p1) p2 B1 ltac:(lia)) as Q2. pose proof (lrem_val (lrem (lrem 0 p0) p1) p2 B1 ltac:(lia)) as R2.
  pose proof (Z.mod_pos_bound (4294967296 * lrem (lrem 0 p0) p1 + p2) 1000000000 ltac:(lia)) as B2. rewrite <- R2 in B2.
  pose proof (lquot_val (lrem (lrem (lrem 0 p0) p1) p2) p3 B2 ltac:(lia)) as Q3. pose proof (lrem_val (lrem (lrem (lrem 0 p0) p1) p2) p3 B2 ltac:(lia)) as R3.
  pose proof (Z.mod_pos_bound (4294967296 * lrem (lrem (lrem 0 p0) p1) p2 + p3) 1000000000 ltac:(lia)) as B3. rewrite <- R3 in B3.
  pose proof (lquot_bound 0 p0 ltac:(lia) ltac:(lia)). pose proof (lquot_bound _ p1 B0 ltac:(lia)). pose proof (lquot_bound _ p2 B1 ltac:(lia)). pose proof (lquot_bound _ p3 B2 ltac:(lia)).
  set (r0 := lrem 0 p0) in *. set (r1 := lrem r0 p1) in *. set (r2 := lrem r1 p2) in *. set (r3 := lrem r2 p3) in *.
  set (q0 := lquot 0 p0) in *. set (q1 := lquot r0 p1) in *. set (q2 := lquot r1 p2) in *. set (q3 := lquot r2 p3) in *.
  pose proof (Z.div_mod (4294967296 * 0 + p0) 1000000000 ltac:(lia)). pose proof (Z.div_mod (4294967296 * r0 + p1) 1000000000 ltac:(lia)).
  pose proof (Z.div_mod (4294967296 * r1 + p2) 1000000000 ltac:(lia)). pose proof (Z.div_mod (4294967296 * r2 + p3) 1000000000 ltac:(lia)).
  repeat split; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Qz (x : Z) : Z := (((((4294967296 * x) mod 2 ^ 64) * 14757395259826634752) / 2 ^ 64) / 34359738368).
Fixpoint Qn (n : nat) (x : Z) : Z := match n with O => x | S n' => Qz (Qn n' x) end.
Definition Dz (x : Z) : Z := ((x + ((18446744073709551606 * Qz x) mod 2 ^ 64)) mod 2 ^ 64).

Lemma Qz_val x : 0 <= x < 2 ^ 32 -> Qz x = x / 10.
Proof.
  intros Hx. unfold Qz. rewrite (Z.mod_small (4294967296 * x)) by lia.
  replace (4294967296 * x * 14757395259826634752) with ((x * 3435973837) * 2 ^ 64) by lia.
  rewrite Z.div_mul by lia. change 34359738368 with (2 ^ 35).
  symmetry. apply (Zdiv_unique (x * 3435973837) (2 ^ 35) (x / 10) (2 * (x / 10) + (x mod 10) * 3435973837)).
  - pose proof (Z.mod_pos_bound x 10 ltac:(lia)). pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)).
    assert (x / 10 < 429496730) by (apply Z.div_lt_upper_bound; lia). lia.
  - pose proof (Z.div_mod x 10 ltac:(lia)). lia.
Qed.
Lemma Qn_val n x : 0 <= x < 2 ^ 32 -> Qn n x = x / 10 ^ Z.of_nat n /\ 0 <= Qn n x < 2 ^ 32.
Proof.
  intros Hx. induction n as [|n IH].
  - cbn [Qn Z.of_nat]. rewrite Z.pow_0_r, Z.div_1_r. split; [reflexivity| exact Hx].
  - cbn [Qn]. destruct IH as [E B]. rewrite (Qz_val _ B), E. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Z.div_div by lia. split; [f_equal; lia|]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    assert (0 < 10 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.
Lemma Dz_val x : 0 <= x < 2 ^ 32 -> Dz x = x mod 10.
Proof.
  intros Hx. unfold Dz. rewrite Qz_val by lia. pose proof (Z.div_mod x 10 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as MB.
  rewrite Zplus_mod_idemp_r. replace (x + 18446744073709551606 * (x / 10)) with (x mod 10 + (x / 10) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* [comment removed for export] *)
Lemma cell0_val r : 0 <= r < 1000000000 -> Qn 8 r = (r / 10 ^ 8) mod 10.
Proof.
  intros Hr. destruct (Qn_val 8 r ltac:(lia)) as [E _]. rewrite E. change (Z.of_nat 8) with 8. symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma cellS_val j r : 0 <= r < 1000000000 -> Dz (Qn j r) = (r / 10 ^ Z.of_nat j) mod 10.
Proof. intros Hr. destruct (Qn_val j r ltac:(lia)) as [E B]. rewrite (Dz_val _ B), E. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dg (V i : Z) : Z := (V / 10 ^ (35 - i)) mod 10.

Lemma dg_range V i : 0 <= dg V i <= 9.
Proof. unfold dg. pose proof (Z.mod_pos_bound (V / 10 ^ (35 - i)) 10 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma pow9 j : 0 <= j -> 1000000000 ^ j = 10 ^ (9 * j).
Proof. intros Hj. change 1000000000 with (10 ^ 9). rewrite <- Z.pow_mul_r by lia. reflexivity. Qed.

Lemma mod_div_mod X A m : 0 <= X -> 0 < A -> 0 <= m ->
  (X mod (A * (10 * 10 ^ m)) / A) mod 10 = (X / A) mod 10.
Proof.
  intros HX HA Hm. assert (HB : 0 < 10 ^ m) by (apply Z.pow_pos_nonneg; lia).
  set (B := 10 * 10 ^ m). assert (HB' : 0 < B) by (subst B; lia).
  rewrite (Z.mod_eq X (A * B)) by nia. set (q := X / (A * B)).
  replace (X - A * B * q) with ((- (B * q)) * A + X) by lia. rewrite Z.div_add_l by lia.
  subst B. replace (- (10 * 10 ^ m * q) + X / A) with (X / A + (- (10 ^ m * q)) * 10) by lia. apply Z.mod_add. lia.
Qed.

Lemma dg_round V k m : 0 <= V -> 0 <= k <= 3 -> 0 <= m <= 8 ->
  ((V / 1000000000 ^ (3 - k)) mod 1000000000 / 10 ^ (8 - m)) mod 10 = dg V (9 * k + m).
Proof.
  intros HV Hk Hm. unfold dg. rewrite pow9 by lia.
  replace (35 - (9 * k + m)) with (9 * (3 - k) + (8 - m)) by lia.
  assert (P1 : 0 < 10 ^ (9 * (3 - k))) by (apply Z.pow_pos_nonneg; lia). assert (P2 : 0 < 10 ^ (8 - m)) by (apply Z.pow_pos_nonneg; lia).
  rewrite (Z.pow_add_r 10 (9 * (3 - k)) (8 - m)) by lia. rewrite <- (Z.div_div V (10 ^ (9 * (3 - k))) (10 ^ (8 - m))) by lia.
  set (X := V / 10 ^ (9 * (3 - k))). assert (HX : 0 <= X) by (subst X; apply Z.div_pos; lia).
  assert (E9 : 1000000000 = 10 ^ (8 - m) * (10 * 10 ^ m)).
  { transitivity (10 ^ ((8 - m) + (1 + m))); [replace (8 - m + (1 + m)) with 9 by lia; reflexivity|].
    rewrite Z.pow_add_r by lia. rewrite (Z.pow_add_r 10 1 m) by lia. change (10 ^ 1) with 10. reflexivity. }
  rewrite E9 at 1. apply mod_div_mod; lia.
Qed.

(* [comment removed for export] *)
Lemma dg_round_zero V k m : 0 <= V -> 0 <= k <= 3 -> 0 <= m <= 8 ->
  (V / 1000000000 ^ (3 - k)) mod 1000000000 = 0 -> dg V (9 * k + m) = 0.
Proof. intros HV Hk Hm Z0. rewrite <- (dg_round V k m) by lia. rewrite Z0. rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). reflexivity. Qed.
Lemma dg_W_zero V k m : 0 <= V -> 0 <= k <= 3 -> 0 <= m <= 8 -> V / 1000000000 ^ (3 - k) = 0 -> dg V (9 * k + m) = 0.
Proof. intros HV Hk Hm Z0. apply dg_round_zero; [lia|lia|lia|]. rewrite Z0. reflexivity. Qed.

(* [comment removed for export] *)
Lemma dg_zero_step V i : 0 <= V -> 0 <= i <= 35 -> V < 10 ^ (35 - i + 1) -> dg V i = 0 -> V < 10 ^ (35 - i).
Proof.
  intros HV Hi HL Hd. unfold dg in Hd. assert (P : 0 < 10 ^ (35 - i)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r, Z.pow_1_r in HL by lia.
  assert (Q : V / 10 ^ (35 - i) < 10) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_pos V (10 ^ (35 - i)) HV P) as Q0.
  rewrite Z.mod_small in Hd by lia.
  pose proof (Z.div_mod V (10 ^ (35 - i)) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound V (10 ^ (35 - i)) P). rewrite Hd in DM. lia.
Qed.
Lemma dg_nonzero_lt V i : 0 <= V -> V < 10 ^ (35 - i) -> 10 ^ (35 - i) <= 10 ^ (35 - i). Proof. intros; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod64_mul32 a : 0 <= a -> (4294967296 * a) mod 2 ^ 64 = 4294967296 * (a mod 2 ^ 32).
Proof. intros Ha. change (2 ^ 64) with (4294967296 * 2 ^ 32). rewrite Z.mul_mod_distr_l by lia. reflexivity. Qed.
Lemma mod64_mul32_div a : 0 <= a -> ((4294967296 * a) mod 2 ^ 64) / 4294967296 = a mod 2 ^ 32.
Proof. intros Ha. rewrite mod64_mul32 by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.
Lemma land_hi_lo a b : 0 <= a -> 0 <= b < 2 ^ 32 -> Z.land (4294967296 * a) b = 0.
Proof.
  intros Ha Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec i 32).
  - change 4294967296 with (2 ^ 32). rewrite Z.mul_comm, Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 b i); [apply Bool.andb_false_r| lia|].
    destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply (Z.lt_le_trans _ 32); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_hi_lo a b : 0 <= a -> 0 <= b < 2 ^ 32 -> Z.lor (4294967296 * a) b = 4294967296 * a + b.
Proof. intros Ha Hb. rewrite <- Z.lxor_lor by (apply land_hi_lo; lia). symmetry. apply Z.add_nocarry_lxor. apply land_hi_lo; lia. Qed.
Lemma lor_bound a b n : 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros Hn Ha Hb. pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as X. split; [exact X|].
  destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|]. destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
  assert (P : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 _ n P)). rewrite Z.log2_lor by lia. apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia)))| apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia)))]; lia.
Qed.
(* [comment removed for export] *)
Lemma dword0_val a2 t5 : 0 <= a2 -> 0 <= t5 ->
  Z.lor ((4294967296 * a2) mod 2 ^ 64) (((4294967296 * t5) mod 2 ^ 64) / 4294967296) = t5 mod 2 ^ 32 + 4294967296 * (a2 mod 2 ^ 32).
Proof.
  intros Ha Ht. rewrite mod64_mul32, mod64_mul32_div by lia. rewrite lor_hi_lo; [lia| apply Z.mod_pos_bound| pose proof (Z.mod_pos_bound t5 (2 ^ 32)); lia]. lia.
Qed.
Lemma parts_zero_iff P0 P1 P2 P3 : 0 <= P0 < 2 ^ 32 -> 0 <= P1 < 2 ^ 32 -> 0 <= P2 < 2 ^ 32 -> 0 <= P3 < 2 ^ 32 ->
  Z.lor (P0 + 4294967296 * P1) (P2 + 4294967296 * P3) = 0 <-> P0 * 2 ^ 96 + P1 * 2 ^ 64 + P2 * 2 ^ 32 + P3 = 0.
Proof. intros H0 H1 H2 H3. rewrite Z.lor_eq_0_iff. lia. Qed.

End PNDF.
