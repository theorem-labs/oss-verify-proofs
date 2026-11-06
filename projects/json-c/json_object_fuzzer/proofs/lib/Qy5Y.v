(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q2qa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import Q2qa.Mq2 Q2qa.Mq0.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition mul_finish_entry := 0x117a0%Z.

Lemma land63_mod : forall y, Z.land y 63 = y mod 64.
Proof. intros. symmetry. apply mod64_land63. Qed.
Lemma landM32_mod : forall y, Z.land y 4294967295 = y mod 2^32.
Proof. intros. change 4294967295 with (2^32 - 1). apply zb_land_mask. lia. Qed.

Ltac amt := rewrite ?land_W64, ?land63_mod, ?landM32_mod;
repeat (rewrite zb_lxor_ones by (Z.div_mod_to_equations; lia));
rewrite ?Z.shiftr_div_pow2 by lia;
zb_fold_lits; Z.div_mod_to_equations; lia.

Lemma pe_n : forall pe, -127 <= pe <= 0 -> Z.land (Z.land pe 18446744073709551615 + 127) 18446744073709551615 = pe + 127.
Proof. intros. amt. Qed.
Lemma pe_shift : forall pe, -127 <= pe <= 0 -> Z.land (1 - Z.land pe 18446744073709551615) 18446744073709551615 = 1 - pe.
Proof. intros. amt. Qed.
Lemma shr_land_W64 : forall x k, (0 <= x < 2^64) -> 0 <= k -> Z.land (Z.shiftr x k) 18446744073709551615 = Z.shiftr x k.
Proof. intros. rewrite land_W64. apply Z.mod_small. apply (zr_shiftr x k); assumption. Qed.

Ltac strip_lands :=
repeat match goal with
| |- context [Z.land (Z.shiftr ?x ?k) 18446744073709551615] =>
rewrite (shr_land_W64 x k) by (first [zrange | zrange_nonneg | lia])
end.

Ltac not_bitop t :=
lazymatch t with
| Z.lor _ _ => fail | Z.shiftl _ _ => fail | Z.b2z _ => fail | Z.ltb _ _ => fail | Z.eqb _ _ => fail
| _ => idtac
end.
Ltac zeq2 :=
first
[ reflexivity
| lazymatch goal with
| |- Z.lor ?a ?b = Z.lor _ _ =>
first [ f_equal; zeq2 | rewrite (Z.lor_comm a b); f_equal; zeq2
| lazymatch a with Z.lor ?a1 ?a2 =>
first [ rewrite <- (Z.lor_assoc a1 a2 b);
first [ f_equal; zeq2 | rewrite (Z.lor_comm a1 (Z.lor a2 b)); f_equal; zeq2 ]
| rewrite (Z.lor_comm (Z.lor a1 a2) b), (Z.lor_assoc b a1 a2); f_equal; zeq2 ] end ]
| |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq2 | rewrite (Z.land_comm a b); f_equal; zeq2 ]
| |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq2 | rewrite (Z.lxor_comm a b); f_equal; zeq2 ]
| |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq2 | rewrite (Z.add_comm a b); f_equal; zeq2 ]
| |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq2
| |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq2
| |- Z.b2z _ = Z.b2z _ => f_equal; zeq2
| |- Z.ltb _ _ = Z.ltb _ _ => f_equal; zeq2
| |- Z.eqb _ _ = Z.eqb _ _ => f_equal; zeq2
end
| lazymatch goal with |- ?l = ?r => not_bitop l; not_bitop r end; amt ].

Lemma sticky_b2z : forall x, 0 <= x -> (if negb (x =? 0) then 1 else 0) = Z.b2z (0 <? x).
Proof. intros. rewrite zb_negb_eqb0 by assumption. reflexivity. Qed.

Ltac mf_pure :=
unfold mul_finish; unfold_sf; zb_fold_lits;
rewrite ?pe_n, ?pe_shift by lia;
decide_tests_b;
rewrite ?sticky_b2z by zrange_nonneg;
strip_lands; rewrite ?Z.lor_0_r, ?Z.lor_0_l;
f_equal; zeq2.

Lemma mf_caseC : forall s pe hh hl lh ll,
-63 < pe <= 0 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
mul_finish s pe hh hl lh ll =
mul_round s (hh ≫ Z.land (1 - pe) 63)
(Z.lor (Z.land (Z.land (hh ≪ 1) W64 ≪ Z.land (Z.land (pe + -2) W64) 63) W64) (Z.land (hl ≫ Z.land (1 - pe) 63) W64))
(Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) W64) (Z.land (lh ≫ Z.land (1 - pe) 63) W64))
(Z.lor (Z.lor (Z.b2z (0 <? Z.lor (Z.land (ll ≪ Z.land (pe + 127) 63) W64) 0)) 0)
(Z.lor (Z.land (Z.land (lh ≪ 1) W64 ≪ Z.land (Z.land (pe + -2) W64) 63) W64) (Z.land (ll ≫ Z.land (1 - pe) 63) W64))).
Proof. intros * Hpe Hhh Hhl Hlh Hll.   unfold mul_finish; unfold_sf; zb_fold_lits;
rewrite ?pe_n, ?pe_shift by lia;
decide_tests_b;
rewrite ?sticky_b2z by zrange_nonneg;
strip_lands; rewrite ?Z.lor_0_r, ?Z.lor_0_l. f_equal; zeq2. Qed.

Lemma mf_caseB : forall s pe hh hl lh ll,
pe = -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
mul_finish s pe hh hl lh ll =
mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
(Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) W64) 0)
(Z.lor (Z.lor (Z.b2z (0 <? Z.lor (Z.land (ll ≪ Z.land (pe + 127) 63) W64) 0)) 0) (Z.land (lh ≫ Z.land (1 - pe) 63) W64)).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mf_caseA : forall s pe hh hl lh ll,
-126 <= pe < -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
mul_finish s pe hh hl lh ll =
mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
(Z.lor (Z.lor (Z.land ((hl ≫ 1) ≫ Z.land (Z.lxor (pe + 127) W64) 63) W64) (Z.land (hh ≪ Z.land (pe + 127) 63) W64)) 0)
(Z.lor (Z.lor (Z.b2z (0 <? Z.lor (Z.lor (Z.land ((ll ≫ 1) ≫ Z.land (Z.lxor (pe + 127) W64) 63) W64)
(Z.land (lh ≪ Z.land (pe + 127) 63) W64))
(Z.land (ll ≪ Z.land (pe + 127) 63) W64)))
(Z.land (hl ≪ Z.land (pe + 127) 63) W64))
(Z.land (lh ≫ Z.land (1 - pe) 63) W64)).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mf_normal : forall s pe hh hl lh ll,
0 < pe <= 131072 ->
mul_finish s pe hh hl lh ll =
mul_round s (Z.lor (Z.land (pe ≪ 48) W64) (Z.land hh 281474976710655)) hl lh ll.
Proof.
intros * Hpe. unfold mul_finish. unfold_sf. zb_fold_lits. decide_tests_b.
rewrite (land_W64 pe), Z.mod_small by lia. reflexivity.
Qed.

Lemma mf_tiny : forall s pe hh hl lh ll,
-131072 <= pe < -126 ->
mul_finish s pe hh hl lh ll = mk128 s 0.
Proof.
intros * Hpe. unfold mul_finish. unfold_sf. zb_fold_lits.
replace (Z.land (1 - Z.land pe 18446744073709551615) 18446744073709551615) with (1 - pe) by (symmetry; amt).
decide_tests_b. reflexivity.
Qed.

Lemma sext32_small : forall z, (-2147483648 <= z < 2147483648)%Z -> bv_swrap 32 z = z.
Proof.
intros. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32 `div` 2)%Z with 2147483648%Z. lia.
Qed.

Lemma land_sub_neg : forall c pe, (pe <= 0)%Z -> (0 <= c)%Z -> (c - pe < 18446744073709551616)%Z ->
Z.land (c - Z.land pe 18446744073709551615) 18446744073709551615 = (c - pe)%Z.
Proof. intros. amt. Qed.

Ltac zz := zsimp; rewrite ?Z.add_0_r; try rewrite !land_sub_neg by alia; try rewrite !sext32_small by alia.
Ltac zzstep := step; zz.

Ltac if_decide :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let K := fresh "K" in
destruct c eqn:K;

[ tryif (exfalso; zify_cond K; sf_prune; zb_masks_fast; lia1) then idtac else clear K
| tryif (exfalso; zify_cond K; sf_prune; zb_masks_fast; lia1) then idtac else clear K ]
| _ => idtac
end.

Ltac zrange2 :=
lazymatch goal with
| |- inr64 ?e =>
lazymatch e with
| Z.shiftr _ _ => apply zr_shiftr; [zrange2 | first [lia | zrange_nonneg]]
| Z.lor _ _ => apply zr_lor; [zrange2 | zrange2]
| _ => zrange
end
| |- (0 <= ?e < _)%Z => change (inr64 e); zrange2
end.

Section MulCore.

End MulCore.

End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 QnDM_c1 QZAi QUZl Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1.
Import QnDM_c1.Mq0 Q2qa.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma swrap_word x : Z_to_bv 64 (bv_swrap 32 x) = wz (sxv x).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

#[using="Type"] Lemma sxv_testbit_lo' v i : 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. apply Z.mod_pow2_bits_low. lia.
Qed.

#[using="Type"] Lemma sxv_cases' v : let u := v mod 2^32 in
(u < 2^31 /\ sxv v = u) \/ (2^31 <= u /\ sxv v = u + 2^64 - 2^32).
Proof.
cbv zeta. pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
rewrite <- (sxv_congr (v mod 2^32) v) by (apply Z.mod_mod; lia).
destruct (sxv_cases (v mod 2^32) ltac:(lia)); tauto.
Qed.

#[using="Type"] Lemma testbit_31_mod32 v : Z.testbit v 31 = (2^31 <=? v mod 2^32).
Proof.
rewrite <- (Z.mod_pow2_bits_low v 32 31) by lia. rewrite Z.testbit_eqb by lia.
pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
destruct (Z.leb_spec (2^31) (v mod 2^32)).
- replace (v mod 2^32 / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
- rewrite Z.div_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma sxv_testbit_hi v i : 31 <= i < 64 -> Z.testbit (sxv v) i = Z.testbit v 31.
Proof.
intros Hi. rewrite testbit_31_mod32. rewrite Z.testbit_eqb by lia.
assert (P31 : 2^31 <= 2^i) by (apply Z.pow_le_mono_r; lia).
assert (P63 : 2^i <= 2^63) by (apply Z.pow_le_mono_r; lia).
assert (E64 : 2^64 = 2^(64-i) * 2^i) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (E2 : 2^(64-i) = 2 * 2^(64-i-1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
assert (P1 : 1 <= 2^(64-i-1)) by (apply Z.pow_le_mono_r with (b:=0) in Hi || idtac; apply (Z.pow_le_mono_r 2 0); lia).
destruct (sxv_cases' v) as [[Hu E]|[Hu E]]; rewrite E.
- rewrite Z.div_small by lia. cbn. symmetry. apply Z.leb_gt. lia.
- pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
replace ((v mod 2^32 + 2^64 - 2^32) / 2^i) with (2^(64-i) - 1) by (Z.div_mod_to_equations; nia).
rewrite E2. replace (2 * 2^(64-i-1) - 1) with (1 + (2^(64-i-1) - 1) * 2) by lia.
rewrite Z.mod_add by lia. cbn. symmetry. apply Z.leb_le. lia.
Qed.

#[using="Type"] Lemma sxv_testbit_high v i : 64 <= i -> Z.testbit (sxv v) i = false.
Proof.
intros. pose proof (sxv_range v). destruct (Z.eq_dec (sxv v) 0) as [->|]. apply Z.bits_0.
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.

#[using="Type"] Lemma sxv_land a b : Z.land (sxv a) (sxv b) = sxv (Z.land a b).
Proof.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 32); [| destruct (Z.lt_ge_cases i 64)].
- rewrite !sxv_testbit_lo' by lia. symmetry. apply Z.land_spec.
- rewrite !sxv_testbit_hi by lia. rewrite Z.land_spec. reflexivity.
- rewrite !sxv_testbit_high by lia. reflexivity.
Qed.

#[using="Type"] Lemma sxv_idem v : sxv (sxv v) = sxv v.
Proof. apply sxv_congr. apply sxv_mod32. Qed.

#[using="Type"] Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
destruct (Z.eq_dec n 0) as [->|].
- rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
- replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

#[using="Type"] Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
destruct (Z.eq_dec n 0) as [->|].
- rewrite !Z.testbit_even_0. reflexivity.
- replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

#[using="Type"] Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
intros m Hm.
pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
intros x IH Hx0 Hx.
destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
- destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
- exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

#[using="Type"] Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

#[using="Type"] Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

#[using="Type"] Lemma lowbit_0 : lowbit 0 = 0.
Proof. reflexivity. Qed.

#[using="Type"] Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

#[using="Type"] Lemma negw_and_lowbit v : 0 <= v < 2^32 ->
Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv v)))))) (bv_unsigned (wz (sxv v))))
= wz (sxv (lowbit v)).
Proof.
intros Hv. rewrite swrap_word. rewrite !wz_unsigned by apply sxv_range.
rewrite sxv_land. unfold lowbit, wz. f_equal.
rewrite (Z.land_comm v (- v)).
transitivity (sxv (Z.land (sxv (0 - sxv v)) (sxv v))); [rewrite sxv_land, sxv_idem; reflexivity|].
transitivity (sxv (Z.land (sxv (- v)) (sxv v))); [| rewrite sxv_land, sxv_idem; reflexivity].
f_equal. f_equal. apply sxv_congr.
rewrite <- Zminus_mod_idemp_r, sxv_mod32, Zminus_mod_idemp_r. replace (0 - v) with (- v) by lia. reflexivity.
Qed.

Definition DB32 : Z := 124511785.
Definition dbi (k : Z) : Z := ((2 ^ k * DB32) mod 2^32) / 2^27.

#[using="Type"] Lemma lowbit_pow2_id k : 0 <= k -> lowbit (2 ^ k) = 2 ^ k.
Proof. intros. unfold lowbit. apply land_opp_pow2. assumption. Qed.

#[using="Type"] Lemma mulw_word a c : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv a)) * c)) = wz (sxv (a * c)).
Proof.
rewrite wz_unsigned by apply sxv_range. rewrite swrap_word. unfold wz. f_equal. apply sxv_congr.
rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

#[using="Type"] Lemma srliw27_val a : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (wz (sxv a)))) 27) = (a mod 2^32) / 2^27.
Proof.
rewrite wz_unsigned by apply sxv_range.
change (bv_wrap 32 (sxv a)) with ((sxv a) mod 2^32). rewrite sxv_mod32.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

#[using="Type"] Lemma dbi_range k : 0 <= dbi k < 32.
Proof. unfold dbi. pose proof (Z.mod_pos_bound (2^k * DB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

#[using="Type"] Lemma le4_avail_sub a b : 0 <= b <= a -> a < 2^32 ->
le4 (wz (sxv (sxv a - sxv b))) = le4 (wz (a - b)).
Proof.
intros. apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
rewrite sxv_mod32, <- Zminus_mod_idemp_r, sxv_mod32, <- Zminus_mod_idemp_l, sxv_mod32, Zminus_mod_idemp_l, Zminus_mod_idemp_r.
reflexivity.
Qed.

#[using="Type"] Lemma srliw27_word a :
Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (wz (sxv a)))) 27)) = wz ((a mod 2^32) / 2^27).
Proof. rewrite srliw27_val. reflexivity. Qed.
End RC__1.

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end. Ltac mkr__mem_after_store_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rw_cells_CB_len segs m A n bs rest : rw_cells segs m A (CB n bs :: rest) -> length bs = n.
Proof. intros [[[H _] _] _]. exact H. Qed.
End RC__2.

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end. Ltac mkr__mem_after_store_1 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs m A ?cs0 |- _ =>
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.

End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import Q2qa.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Local Open Scope Z_scope.

Import QZAa.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Lemma shr56_mul64_range : forall y k, 0 <= Z.shiftr (mul64 y k) 56 < 256.
Proof.
intros. unfold mul64. pose proof (wrap64_range (y * k)) as H.
rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. } apply Z.div_lt_upper_bound; lia.
Qed.

Lemma clz64_mirror_range : forall x, 0 <= clz64_mirror x < 256.
Proof. intros x. unfold clz64_mirror. cbv zeta. apply shr56_mul64_range. Qed.

Lemma clz64_mirror_land : forall x, Z.land (clz64_mirror x) 18446744073709551615 = clz64_mirror x.
Proof. intros. rewrite land_W64. apply Z.mod_small. pose proof (clz64_mirror_range x). lia. Qed.

Lemma b2z_shl6 : forall b, Z.land (Z.shiftl (Z.b2z b) 6) 18446744073709551615 = Z.shiftl (Z.b2z b) 6.
Proof. intros [|]; reflexivity. Qed.

Lemma clz128_val_range : forall w b, 0 <= Z.lor (clz64_mirror w) (Z.shiftl (Z.b2z b) 6) < 2^64.
Proof.
intros. pose proof (clz64_mirror_range w).
apply Z_lor_range; [lia | destruct b; cbv; split; congruence].
Qed.

Lemma lor_lt_256 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
intros a b Ha Hb. split. { apply Z.lor_nonneg; lia. }
destruct (Z.eq_dec a 0) as [->|Na]. { rewrite Z.lor_0_l. lia. }
destruct (Z.eq_dec b 0) as [->|Nb]. { rewrite Z.lor_0_r. lia. }
assert (Hl : Z.lor a b <> 0). { intro E. apply Z.lor_eq_0_iff in E. lia. }
pose proof (Z.lor_nonneg a b).
change 256 with (2^8). apply Z.log2_lt_pow2; [lia|].
rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma clz128_mirror_range : forall hi lo, 0 <= clz128_mirror hi lo < 256.
Proof.
intros. unfold clz128_mirror. cbv zeta. apply lor_lt_256.
- apply clz64_mirror_range.
- destruct (hi =? 0); cbv; split; congruence.
Qed.

Lemma land63_mod : forall y, Z.land y 63 = y mod 64.
Proof. intros. symmetry. apply mod64_land63. Qed.
Lemma landM32_mod : forall y, Z.land y 4294967295 = y mod 2^32.
Proof. intros. change 4294967295 with (2^32 - 1). apply zb_land_mask. lia. Qed.
Lemma swrap32_arith : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. intros. reflexivity. Qed.
Lemma shr_land_W64 : forall x k, (0 <= x < 2^64) -> 0 <= k -> Z.land (Z.shiftr x k) 18446744073709551615 = Z.shiftr x k.
Proof. intros. rewrite land_W64. apply Z.mod_small. apply (zr_shiftr x k); assumption. Qed.
Lemma land_ones_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros. rewrite Z.land_comm, land_W64. apply Z.mod_small. lia. Qed.

Ltac amt := rewrite ?land_W64, ?land63_mod, ?landM32_mod, ?swrap32_arith;
repeat (rewrite zb_lxor_ones by (Z.div_mod_to_equations; lia));
rewrite ?Z.shiftr_div_pow2 by lia;
zb_fold_lits; Z.div_mod_to_equations; lia.
Ltac not_bitop t :=
lazymatch t with
| Z.lor _ _ => fail | Z.shiftl _ _ => fail | Z.b2z _ => fail | Z.ltb _ _ => fail | Z.eqb _ _ => fail
| _ => idtac
end.

Ltac zeq2 :=
first
[ reflexivity
| lazymatch goal with
| |- Z.land _ 63 = Z.land _ 63 => first [ amt | f_equal; zeq2 ]
| |- Z.lor ?a ?b = Z.lor _ _ =>
first [ f_equal; zeq2 | rewrite (Z.lor_comm a b); f_equal; zeq2
| lazymatch a with Z.lor ?a1 ?a2 =>
first [ rewrite <- (Z.lor_assoc a1 a2 b);
first [ f_equal; zeq2 | rewrite (Z.lor_comm a1 (Z.lor a2 b)); f_equal; zeq2 ]
| rewrite (Z.lor_comm (Z.lor a1 a2) b), (Z.lor_assoc b a1 a2); f_equal; zeq2 ] end ]
| |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq2 | rewrite (Z.land_comm a b); f_equal; zeq2 ]
| |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq2 | rewrite (Z.lxor_comm a b); f_equal; zeq2 ]
| |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq2 | rewrite (Z.add_comm a b); f_equal; zeq2 ]
| |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq2
| |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq2
| |- Z.b2z _ = Z.b2z _ => f_equal; zeq2
| |- Z.ltb _ _ = Z.ltb _ _ => f_equal; zeq2
| |- Z.eqb _ _ = Z.eqb _ _ => f_equal; zeq2
end
| lazymatch goal with |- ?l = ?r => not_bitop l; not_bitop r end; amt ].
Ltac strip_lands :=
repeat match goal with
| |- context [Z.land (Z.shiftr ?x ?k) 18446744073709551615] =>
rewrite (shr_land_W64 x k) by (first [zrange | zrange_nonneg | lia])
end.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
end).

Definition nd_hi (sigHi sigLo : Z) : Z := let '(h, _, _) := norm_denormal sigHi sigLo in h.
Definition nd_lo (sigHi sigLo : Z) : Z := let '(_, l, _) := norm_denormal sigHi sigLo in l.
Definition nd_clz (sigHi sigLo : Z) : Z := let '(_, _, c) := norm_denormal sigHi sigLo in c.
Lemma norm_denormal_eta : forall sigHi sigLo,
norm_denormal sigHi sigLo = (nd_hi sigHi sigLo, nd_lo sigHi sigLo, nd_clz sigHi sigLo).
Proof. intros. unfold nd_hi, nd_lo, nd_clz. destruct (norm_denormal sigHi sigLo) as [[h l] c]. reflexivity. Qed.

Lemma nd_clz_eq : forall sigHi sigLo, nd_clz sigHi sigLo = clz128_mirror sigHi sigLo.
Proof.
intros. unfold nd_clz, norm_denormal.
destruct (shl128_mirror sigHi sigLo (sub64 (clz128_mirror sigHi sigLo) 15)) as [h l]. reflexivity.
Qed.
Lemma nd_clz_range : forall sigHi sigLo, 0 <= nd_clz sigHi sigLo < 256.
Proof. intros. rewrite nd_clz_eq. apply clz128_mirror_range. Qed.

Ltac nd_model :=
unfold nd_hi, nd_lo, nd_clz; cbv beta zeta iota delta [norm_denormal shl128_mirror clz128_mirror];
change b2z with Z.b2z; unfold_sf; zb_fold_lits;
decide_tests_b;
change (Z.b2z false) with 0; change (Z.b2z true) with 1; zb_fold_lits; rewrite ?Z.lor_0_r;
decide_tests_b.

Lemma nd_pure_ge64 : forall hi lo c,
0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= c < 2^64 ->
clz128_mirror hi lo = c ->
Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) 18446744073709551615 < 9223372036854775808 ->
Z_to_bv 64 (nd_hi hi lo) = Z_to_bv 64 (lo ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63)
/\ Z_to_bv 64 (nd_lo hi lo) = Z_to_bv 64 0
/\ Z_to_bv 64 (nd_clz hi lo) = Z_to_bv 64 c.
Proof.
intros hi lo c Hhi Hlo Hc E K2.
unfold nd_hi, nd_lo, nd_clz, norm_denormal. rewrite E. cbv beta zeta iota delta [shl128_mirror].
change b2z with Z.b2z. unfold_sf. zb_fold_lits. decide_tests_b.
split; [| split].
- rewrite ?Z_to_bv_land64. f_equal. zeq2.
- rewrite Z.land_0_l. reflexivity.
- reflexivity.
Qed.

Lemma nd_pure_lt64 : forall hi lo c,
0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= c < 2^64 ->
clz128_mirror hi lo = c ->
9223372036854775808 <= Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) 18446744073709551615 ->
Z_to_bv 64 (nd_hi hi lo) =
Z_to_bv 64 (Z.lor (Z.land ((lo ≫ 1) ≫ Z.land (Z.lxor (Z.land (bv_swrap 32 (Z.land (c - 15) 18446744073709551615))
18446744073709551615) 18446744073709551615) 63)
18446744073709551615)
(Z.land (hi ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63) 18446744073709551615))
/\ Z_to_bv 64 (nd_lo hi lo) = Z_to_bv 64 (lo ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63)
/\ Z_to_bv 64 (nd_clz hi lo) = Z_to_bv 64 c.
Proof.
intros hi lo c Hhi Hlo Hc E K2.
unfold nd_hi, nd_lo, nd_clz, norm_denormal. rewrite E. cbv beta zeta iota delta [shl128_mirror].
change b2z with Z.b2z. unfold_sf. zb_fold_lits. decide_tests_b.
split; [| split].
- rewrite ?Z_to_bv_land64. f_equal. strip_lands. zeq2.
- rewrite land_ones_l by zrange. rewrite ?Z_to_bv_land64. reflexivity.
- reflexivity.
Qed.

Lemma clz128_hi_nz : forall hi lo, hi <> 0 -> clz128_mirror hi lo = clz64_mirror hi.
Proof.
intros. unfold clz128_mirror. replace (hi =? 0) with false by (symmetry; apply Z.eqb_neq; assumption).
cbn. apply Z.lor_0_r.
Qed.
Lemma clz128_hi_z : forall hi lo, hi = 0 -> clz128_mirror hi lo = Z.lor (clz64_mirror lo) 64.
Proof. intros. subst. reflexivity. Qed.

Ltac nd_tail FR ST E clz sh n32 p sp :=
let K2 := fresh "K2" in
if_cases K2; zify_cond K2;
[
do 5 (zstep; fix_lit_store); do 4 zstep; release_frame FR ST (bv_unsigned sp);
subst n32 sh;
let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
lazymatch type of E with clz128_mirror ?hi ?lo = _ =>
destruct (nd_pure_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as (E1 & E2 & E3) end;
match goal with O : rw_cells _ _ p _ |- _ => rewrite <- E1, <- E2, <- E3 in O end;
finish
|
do 16 zstep; release_frame FR ST (bv_unsigned sp);
subst n32 sh;
let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
lazymatch type of E with clz128_mirror ?hi ?lo = _ =>
destruct (nd_pure_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as (E1 & E2 & E3) end;
match goal with O : rw_cells _ _ p _ |- _ => rewrite <- E1, <- E2, <- E3 in O end;
finish ].

End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import Q2qa.Mq2 Q2qa.Mq0.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Ltac zeq_fast ::=
first
[ reflexivity
| lazymatch goal with
| |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lor_comm a b); f_equal; zeq_fast ]
| |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq_fast | rewrite (Z.land_comm a b); f_equal; zeq_fast ]
| |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lxor_comm a b); f_equal; zeq_fast ]
| |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq_fast | rewrite (Z.add_comm a b); f_equal; zeq_fast ]
| |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq_fast | rewrite (Z.mul_comm a b); f_equal; zeq_fast ]
| |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq_fast
| |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq_fast
| |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq_fast
| |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq_fast
| |- Z.b2z _ = Z.b2z _ => f_equal; zeq_fast
| |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq_fast); f_equal; zeq_fast
| |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
first [ f_equal; zeq_fast
| unfold1 a; unfold1 c; zeq_boolarith_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
| unfold1 a; unfold1 c; zeq_boolarith_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- Z.leb ?a ?b = Z.leb ?c ?d =>
first [ f_equal; zeq_fast | unfold1 a; unfold1 c; zeq_boolarith_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- negb _ = negb _ => f_equal; zeq_fast
| |- @eq bool _ _ => zeq_boolarith_fast
end
| slim; lia ]. Ltac mkr__zeq_fast_6 := first
[ reflexivity
| lazymatch goal with
| |- Z.lor ?a ?b = Z.lor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lor_comm a b); f_equal; zeq_fast ]
| |- Z.land ?a ?b = Z.land _ _ => first [ f_equal; zeq_fast | rewrite (Z.land_comm a b); f_equal; zeq_fast ]
| |- Z.lxor ?a ?b = Z.lxor _ _ => first [ f_equal; zeq_fast | rewrite (Z.lxor_comm a b); f_equal; zeq_fast ]
| |- Z.add ?a ?b = Z.add _ _ => first [ f_equal; zeq_fast | rewrite (Z.add_comm a b); f_equal; zeq_fast ]
| |- Z.mul ?a ?b = Z.mul _ _ => first [ f_equal; zeq_fast | rewrite (Z.mul_comm a b); f_equal; zeq_fast ]
| |- Z.modulo _ ?m = Z.modulo _ ?m => f_equal; zeq_fast
| |- Z.sub _ _ = Z.sub _ _ => f_equal; zeq_fast
| |- Z.shiftr _ _ = Z.shiftr _ _ => f_equal; zeq_fast
| |- Z.shiftl _ _ = Z.shiftl _ _ => f_equal; zeq_fast
| |- Z.b2z _ = Z.b2z _ => f_equal; zeq_fast
| |- (if ?c then _ else _) = (if ?d then _ else _) => replace d with c by (symmetry; zeq_fast); f_equal; zeq_fast
| |- Z.ltb ?a ?b = Z.ltb ?c ?d =>
first [ f_equal; zeq_fast
| unfold1 a; unfold1 c; zeq_boolarith_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- Z.eqb ?a ?b = Z.eqb ?c ?d =>
first [ f_equal; zeq_fast | rewrite (Z.eqb_sym a b); f_equal; zeq_fast
| unfold1 a; unfold1 c; zeq_boolarith_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- Z.leb ?a ?b = Z.leb ?c ?d =>
first [ f_equal; zeq_fast | unfold1 a; unfold1 c; zeq_boolarith_fast
| unfold1 a; unfold1 b; unfold1 c; unfold1 d; zeq_boolarith_fast ]
| |- negb _ = negb _ => f_equal; zeq_fast
| |- @eq bool _ _ => zeq_boolarith_fast
end
| slim; lia ].

Lemma mulhu_range : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> 0 <= Z.shiftr (x * y) 64 < 18446744073709551616.
Proof.
intros x y Hx Hy. rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; nia. }
apply Z.div_lt_upper_bound; [lia|]. change 18446744073709551616 with (2^64). nia.
Qed.

Ltac name_mulhu n X :=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 (Z.shiftr (?x * ?y) 64) =>
set (X := Z.shiftr (x * y) 64);
let RX := fresh "R" X in
assert (RX : 0 <= X < 18446744073709551616)
by (cbv delta [X]; apply mulhu_range; (change (inr64 x) || idtac); [change (inr64 x); zrange | change (inr64 y); zrange])
end.

Lemma three_hi : forall bHi h, 0 <= bHi < 2^64 -> 0 <= h < 2^64 ->
Z_to_bv 64 (bHi * 3 + h) = Z_to_bv 64 (Z.land (Z.land (h + bHi) 18446744073709551615 + Z.land (Z.shiftl bHi 1) 18446744073709551615) 18446744073709551615).
Proof. intros. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.
Lemma three_lo : forall bLo, 0 <= bLo < 2^64 ->
Z.land (bLo * 3) 18446744073709551615 = Z.land (Z.land (Z.shiftl bLo 1) 18446744073709551615 + bLo) 18446744073709551615.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.
Lemma five_hi : forall bHi h, 0 <= bHi < 2^64 -> 0 <= h < 2^64 ->
Z_to_bv 64 (bHi * 5 + h) = Z_to_bv 64 (Z.land (Z.land (h + bHi) 18446744073709551615 + Z.land (Z.shiftl bHi 2) 18446744073709551615) 18446744073709551615).
Proof. intros. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.
Lemma five_lo : forall bLo, 0 <= bLo < 2^64 ->
Z.land (bLo * 5) 18446744073709551615 = Z.land (Z.land (Z.shiftl bLo 2) 18446744073709551615 + bLo) 18446744073709551615.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. rewrite !land_W64. Z.div_mod_to_equations. lia. Qed.

Ltac subst_head_let :=
lazymatch goal with
| |- (let x := ?v in ?c) = ?r =>
is_var v;
let c' := eval cbv beta in ((fun x : Z => c) v) in
change (c' = r)
end.
Ltac fold_model_lets2 := repeat first [ fold_head_let | subst_head_let ].

Section DivRound.
Variables (w0 w1 w2 w3 w4 w5 w6 : word).

End DivRound.

End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import QnDM_c1.Mq0 QytA.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition block : Type := (bptr * Z * Z)%type.
Definition blk_id (b : block) : bptr := fst (fst b).
Definition blk_slot (b : block) : cptr := fst (fst (fst b)).
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.

Definition brk_link (st : mstate) (pbrk : Z) : Prop :=
match c_brk (ctx st) with
| BrkLive rid off => pbrk = conc st (rid, off)
| _ => True
end.

Inductive AREACH_from (resv : list (Z * Z)) (sec : Z) : mstate -> list block -> Prop :=
| areach_init : 0 <= sec < 2^64 -> AREACH_from resv sec (minit sec resv) []
| areach_malloc_some : forall st LB n (o o' : mem) ans st' (pf : aptr) cst (c : cptr),
AREACH_from resv sec st LB -> 0 <= n ->
follow (mrun o (malloc st n)) ans = Some (o', (st', Some pf)) ->
follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
AREACH_from resv sec st' (((c, fresh_off cst c n), conc st' pf, n) :: LB)
| areach_malloc_none : forall st LB n (o o' : mem) ans st',
AREACH_from resv sec st LB -> 0 <= n ->
follow (mrun o (malloc st n)) ans = Some (o', (st', None)) ->
AREACH_from resv sec st' LB
| areach_free : forall st LB (b : block) (pf : aptr) (o o' : mem) ans st',
AREACH_from resv sec st LB -> In b LB ->
fst pf = fst (blk_slot b) -> conc st pf = blk_addr b ->
follow (mrun o (free st (Some pf))) ans = Some (o', st') ->
AREACH_from resv sec st' (filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB)

| areach_realloc : forall st LB (b : block) (off n : Z) (o o' : mem) ans st' (r : optr) cst (rw : option rr_where),
AREACH_from resv sec st LB -> In b LB -> 0 <= off -> 0 <= n ->
blk_addr b = conc st (blk_slot b) + UNIT * off ->
follow (mrun o (realloc st (Some (aadd (blk_slot b) (UNIT * off))) n)) ans = Some (o', (st', r)) ->
follow (crealloc (strip st) (blk_slot b) off n) ans = Some (cst, rw) ->
AREACH_from resv sec st'
match r, rw with
| Some pf, Some RRSame => ((blk_slot b, off), conc st' pf, n) :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB
| Some pf, Some (RRNew b') => (b', conc st' pf, n) :: filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot b))) LB
| _, _ => LB
end.
End RC__1.
Arguments areach_init {RC__ resv sec}.
Arguments areach_malloc_some {RC__ resv sec}.
Arguments areach_malloc_none {RC__ resv sec}.
Arguments areach_free {RC__ resv sec}.
Arguments areach_realloc {RC__ resv sec}.

Notation AREACH := (AREACH_from agent_reserved 0).

End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition repfoot (st : mstate) (a : Z) : Prop :=
(CTX <= a < CTX + 928) \/ (MLOCK <= a < MLOCK + 4) \/ (NEED_LOCKS <= a < NEED_LOCKS + 1) \/ (PAGE_SIZE_A <= a < PAGE_SIZE_A + 8)
\/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

#[using="Type"] Lemma repfoot_ctx st a : CTX <= a < CTX + 928 -> repfoot st a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma repfoot_mlock st a : MLOCK <= a < MLOCK + 4 -> repfoot st a. Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_nl st a : NEED_LOCKS <= a < NEED_LOCKS + 1 -> repfoot st a. Proof. intros; do 2 right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_pgsz st a : PAGE_SIZE_A <= a < PAGE_SIZE_A + 8 -> repfoot st a. Proof. intros; do 3 right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> repfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
#[using="Type"] Lemma repfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> repfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
#[using="Type"] Lemma repfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> repfoot st a.
Proof. intros; do 6 right. exists rid, r, v. auto. Qed.

Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.

#[using="Type"] Lemma ivs_avoid_nil : forall P, ivs_avoid [] P.
Proof. intros P lo hi a []. Qed.

#[using="Type"] Lemma ivs_avoid_cons : forall lo hi W P,
(forall a, lo <= a < hi -> ~ P a) -> ivs_avoid W P -> ivs_avoid ((lo, hi) :: W) P.
Proof.
intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
- inversion E; subst. apply H1. exact Ha.
- eapply H2; eauto.
Qed.

#[using="Type"] Lemma avoid_outside : forall W P x, ivs_avoid W P -> P x -> outside W x.
Proof.
induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
- intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
- apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.

Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
forall a, A <= a < A + n -> m' (wa a) = m (wa a).

#[using="Type"] Lemma munch_agree : forall W m m' P A n,
munch W m m' -> ivs_avoid W P -> (forall a, A <= a < A + n -> P a) -> 0 <= A -> A + n <= 2^64 ->
agree_on m m' A n.
Proof.
intros W m m' P A n MU HW HP HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
eapply avoid_outside; [exact HW| apply HP; exact Ha].
Qed.

#[using="Type"] Lemma get_meta_rec_put : forall st g mr g',
get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

#[using="Type"] Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma del_slots_eq : forall p s c st, del_slots p s c st = set_slots (s_slots (del_slots p s c st)) st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof. intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.

#[using="Type"] Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
(i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
intros X f n. induction n as [|n IH]; intros s i Hi; [lia|].
cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
rewrite IH by lia. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma actives_nth : forall st sc, 0 <= sc < 48 ->
nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
intros st sc H. unfold actives. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma usages_nth : forall st sc, 0 <= sc < 48 ->
nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
intros st sc H. unfold usages. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma bouncess_nth : forall st i, 0 <= i < 32 ->
nth_error (bouncess st) (Z.to_nat i) = Some (b8 (bounces st i)).
Proof.
intros st i H. unfold bouncess. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma unmap_seqs_nth : forall st i, 0 <= i < 32 ->
nth_error (unmap_seqs st) (Z.to_nat i) = Some (b8 (unmap_seq st i)).
Proof.
intros st i H. unfold unmap_seqs. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma actives_length st : length (actives st) = 48%nat.
Proof. unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma usages_length st : length (usages st) = 48%nat.
Proof. unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma bouncess_length st : length (bouncess st) = 32%nat.
Proof. unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma unmap_seqs_length st : length (unmap_seqs st) = 32%nat.
Proof. unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.

#[using="Type"] Lemma put_meta_put_meta_same : forall st g a b, put_meta g a (put_meta g b st) = put_meta g a st.
Proof. intros. destruct st; unfold put_meta, set_metas; cbn. f_equal. apply insert_insert_eq. Qed.

#[using="Type"] Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof.
intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.

#[using="Type"] Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof.
intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

#[using="Type"] Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.

#[using="Type"] Lemma pw_put_meta : forall st g mr p, pw (put_meta g mr st) p = pw st p. Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p. Proof. reflexivity. Qed.
#[using="Type"] Lemma ctx_put_meta : forall st g mr, ctx (put_meta g mr st) = ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
#[using="Type"] Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r. Proof. reflexivity. Qed.

#[using="Type"] Lemma outside_of_cover : forall (C : Z -> Prop) W a,
(forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) -> ~ C a -> outside W a.
Proof.
induction W as [|[lo hi] W IH]; intros a HW HC; cbn; [exact I|]. split.
- intros Ha. apply HC. apply (HW lo hi); [left; reflexivity| exact Ha].
- apply IH; [|exact HC]. intros lo' hi' Hin x Hx. apply (HW lo' hi'); [right; exact Hin|exact Hx].
Qed.

Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
end.

#[using="Type"] Lemma ivs_covered_In : forall C W, ivs_covered C W -> forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x.
Proof.
induction W as [|[lo hi] W IH]; cbn; intros H lo' hi' Hin x Hx; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; auto| eapply IH; eauto].
Qed.

#[using="Type"] Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof.
intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
intros x Hx. cbn in Hx |- *. tauto.
Qed.
End RC__1.

Ltac munch_grow MU iv :=
lazymatch type of MU with
| munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).

Hypothesis MU : munch W m m'.

Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.

Hypothesis WIN : forall lo hi, In (lo, hi) W -> CTX <= lo /\ hi <= CTX + 928.

#[using="MU WIN"] Lemma ctxW_avoid : forall A n, (A + n <= CTX \/ CTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- destruct HD as [HD|HD].
+ pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
+ pose proof (HD lo hi ltac:(left; reflexivity)). lia.
- apply IH.
+ intros lo' hi' Hin. apply WIN. right; exact Hin.
+ destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.

End CTXFRAME.

#[using="Type"] Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
End RC__2.

Ltac amo_align AMO :=
try (rewrite AMO; cbv beta iota delta [negb]);
try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_step AMO :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end. Ltac mkr__amo_step_0 AMO := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.

Ltac ctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma usage_set_usage st sc v i : usage (set_usage sc v st) i = if Z.eqb i sc then v else usage st i.
Proof.
unfold usage, set_usage, upd_ctx. cbn [ctx s_ctx c_usage set_usage_map].
destruct (Z.eqb_spec i sc); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma usages_set_usage st sc v : 0 <= sc < 48 ->
usages (set_usage sc v st) = upd (usages st) (Z.to_nat sc) (wz v).
Proof.
intros Hsc. unfold usages.
replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
apply (map_seq_upd (fun i => wz (usage st (Z.of_nat i))) (fun i => wz (usage (set_usage sc v st) (Z.of_nat i)))); [|lia].
intros i Hi. rewrite usage_set_usage.
destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

#[using="Type"] Lemma unmap_seq_set st i v j :
unmap_seq (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) j = if Z.eqb j i then v else unmap_seq st j.
Proof.
unfold unmap_seq, upd_ctx. cbn [ctx s_ctx c_unmap_seq set_unmap_seq_map].
destruct (Z.eqb_spec j i); subst.
- rewrite lookup_insert_eq. reflexivity.
- rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma unmap_seqs_set st i v : 0 <= i < 32 ->
unmap_seqs (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) = upd (unmap_seqs st) (Z.to_nat i) (b8 v).
Proof.
intros Hi. unfold unmap_seqs.
replace (Z.to_nat i) with (Z.to_nat i - 0)%nat by lia.
apply (map_seq_upd (fun j => b8 (unmap_seq st (Z.of_nat j)))); [|lia].
intros j Hj. rewrite unmap_seq_set.
destruct (Z.eqb_spec (Z.of_nat j) i); destruct (Nat.eqb_spec j (Z.to_nat i)); try reflexivity; lia.
Qed.

#[using="Type"] Lemma step_seq_eq st :
step_seq st = if c_seq (ctx st) =? 255
then upd_ctx (set_seq 1) (upd_ctx (fun c => set_unmap_seq_map ∅ c) st)
else upd_ctx (set_seq (c_seq (ctx st) + 1)) st.
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.

#[using="Type"] Lemma record_seq_eq sc st :
record_seq sc st = if sc_in_seq_range sc
then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
else st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma le1_lit z : 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [b8 z].
Proof.
intros Hz. unfold le1, b8. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, (bv_wrap_small 64) by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

#[using="Type"] Lemma conc_upd_ctx st f q : conc (upd_ctx f st) q = conc st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_upd_ctx st f q : get_meta_rec (upd_ctx f st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma pw_upd_ctx st f q : pw (upd_ctx f st) q = pw st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma oconc_upd_ctx st f q : oconc (upd_ctx f st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma conc_set_usage st sc v q : conc (set_usage sc v st) q = conc st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_set_usage st sc v q : get_meta_rec (set_usage sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma oconc_set_usage st sc v q : oconc (set_usage sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma conc_set_active st sc v q : conc (set_active sc v st) q = conc st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma rec_set_active st sc v q : get_meta_rec (set_active sc v st) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma oconc_set_active st sc v q : oconc (set_active sc v st) q = oconc st q. Proof. destruct q; reflexivity. Qed.
#[using="Type"] Lemma meta_slot_upd_ctx st f q : meta_slot st q -> meta_slot (upd_ctx f st) q. Proof. intros H; exact H. Qed.
#[using="Type"] Lemma meta_slot_set_usage st sc v q : meta_slot st q -> meta_slot (set_usage sc v st) q. Proof. intros H; exact H. Qed.
#[using="Type"] Lemma meta_slot_set_active st sc v q : meta_slot st q -> meta_slot (set_active sc v st) q. Proof. intros H; exact H. Qed.
End RC__3.

Ltac ctx_norm H := rewrite ?conc_set_usage, ?rec_set_usage, ?oconc_set_usage, ?conc_set_active, ?rec_set_active, ?oconc_set_active,
?conc_upd_ctx, ?rec_upd_ctx, ?oconc_upd_ctx in H.
Section RC__4. Context {RC__ : Q6q3.RunConsts}.

Definition mw_ok (mr : meta) : Prop :=
0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

#[using="Type"] Lemma meta_word_range mr : mw_ok mr -> 0 <= meta_word mr < 2^64.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.
#[using="Type"] Lemma meta_word_last_idx mr : mw_ok mr -> Z.land (meta_word mr) 31 = m_last_idx mr.
Proof.
intros (LI & FB & SCR & ML).
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. unfold meta_word. change (2^5) with 32.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma meta_word_sc mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 6) 63 = m_sizeclass mr.
Proof.
intros (LI & FB & SCR & ML).
change 63 with (Z.ones 6). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^6) with 64.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia.
replace (0 + (m_sizeclass mr + 64 * m_maplen mr)) with (m_sizeclass mr + m_maplen mr * 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma meta_word_shr6_range mr : mw_ok mr -> 0 <= Z.shiftr (meta_word mr) 6 < 2^64.
Proof. intros H. pose proof (meta_word_range mr H). destruct H as (LI & FB & SCR & ML). rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
#[using="Type"] Lemma meta_word_freeable mr : mw_ok mr -> Z.land (meta_word mr) 32 = 32 * m_freeable mr.
Proof.
intros (LI & FB & SCR & ML).
assert (E : 32 = Z.ldiff (Z.ones 6) (Z.ones 5)) by reflexivity. rewrite E at 1. rewrite land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^6) with 64. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr) + (m_sizeclass mr + 64 * m_maplen mr) * 64) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_last_idx mr + 32 * m_freeable mr) with (m_last_idx mr + m_freeable mr * 32) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.
#[using="Type"] Lemma meta_word_maplen mr : mw_ok mr -> Z.shiftr (meta_word mr) 12 = m_maplen mr.
Proof.
intros (LI & FB & SCR & ML).
rewrite Z.shiftr_div_pow2 by lia. unfold meta_word. change (2^12) with 4096.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
#[using="Type"] Lemma meta_word_lt4096 mr : mw_ok mr -> meta_word mr < 4096 <-> m_maplen mr = 0.
Proof. intros (LI & FB & SCR & ML). unfold meta_word. lia. Qed.

#[using="Type"] Lemma negw_word y : Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv y)))) = wz (sxv (- y)).
Proof.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.

#[using="Type"] Lemma land_neg_pow2 f k : 0 <= f -> 0 <= k -> Z.land f (- 2 ^ k) = Z.ldiff f (2 ^ k - 1).
Proof.
intros Hf Hk. replace (- 2 ^ k) with (Z.lnot (2 ^ k - 1)) by (unfold Z.lnot; lia).
rewrite <- Z.ldiff_land. reflexivity.
Qed.

#[using="Type"] Lemma ldiff_le f a : 0 <= f -> 0 <= a -> Z.ldiff f a <= f.
Proof.
intros Hf Ha.
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.

#[using="Type"] Lemma land_upper f a : 0 <= f -> 0 <= a -> 0 <= Z.land f a <= f.
Proof.
intros Hf Ha. split; [apply Z.land_nonneg; lia|].
assert (E : f = Z.lor (Z.ldiff f a) (Z.land f a)).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, Z.land_spec. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
assert (D : Z.land (Z.ldiff f a) (Z.land f a) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit f i), (Z.testbit a i); reflexivity. }
pose proof (Z.add_lor_land (Z.ldiff f a) (Z.land f a)) as S. rewrite D, <- E in S.
pose proof (Z.land_nonneg f a). pose proof (Z.ldiff_nonneg f a). lia.
Qed.

#[using="Type"] Lemma le4_sxv v : 0 <= v < 2^32 -> le4 (Z_to_bv 64 (sxv v)) = le4 (wz v).
Proof.
intros Hv. apply le4_congr. pose proof (sxv_range v). rewrite unsigned_lit by lia. rewrite wz_unsigned by lia.
rewrite sxv_mod32. reflexivity.
Qed.

#[using="Type"] Lemma sllw1_word i : 0 <= i < 32 -> Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (i mod 32))) = wz (sxv (2 ^ i)).
Proof.
intros Hi. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

#[using="Type"] Lemma lor_sxv_zero f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
(Z.lor (sxv f) (sxv a) = 0 <-> Z.lor f a = 0).
Proof.
intros Hf Ha. pose proof (sxv_range f). pose proof (sxv_range a).
rewrite !Z.lor_eq_0_iff. rewrite !sxv_zero by lia. tauto.
Qed.
End RC__4.

Ltac unmask64 K :=
try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).
Section RC__5. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.

End RC__5.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition repfoot (st : mstate) (a : Z) : Prop :=
(CTX <= a < CTX + 928) \/ (MLOCK <= a < MLOCK + 4) \/ (NEED_LOCKS <= a < NEED_LOCKS + 1) \/ (PAGE_SIZE_A <= a < PAGE_SIZE_A + 8)
\/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

#[using="Type"] Lemma repfoot_ctx st a : CTX <= a < CTX + 928 -> repfoot st a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma repfoot_mlock st a : MLOCK <= a < MLOCK + 4 -> repfoot st a. Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_nl st a : NEED_LOCKS <= a < NEED_LOCKS + 1 -> repfoot st a. Proof. intros; do 2 right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_pgsz st a : PAGE_SIZE_A <= a < PAGE_SIZE_A + 8 -> repfoot st a. Proof. intros; do 3 right; left; assumption. Qed.
#[using="Type"] Lemma repfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> repfoot st a.
Proof. intros; do 4 right; left. exists ak, ar. auto. Qed.
#[using="Type"] Lemma repfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> repfoot st a.
Proof. intros; do 5 right; left. exists b, gh. auto. Qed.
#[using="Type"] Lemma repfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> repfoot st a.
Proof. intros; do 6 right. exists rid, r, v. auto. Qed.

Definition ivs_avoid (W : list (Z * Z)) (P : Z -> Prop) : Prop :=
forall lo hi a, In (lo, hi) W -> lo <= a < hi -> ~ P a.

#[using="Type"] Lemma ivs_avoid_nil : forall P, ivs_avoid [] P.
Proof. intros P lo hi a []. Qed.

#[using="Type"] Lemma ivs_avoid_cons : forall lo hi W P,
(forall a, lo <= a < hi -> ~ P a) -> ivs_avoid W P -> ivs_avoid ((lo, hi) :: W) P.
Proof.
intros lo hi W P H1 H2 lo' hi' a [E|Hin] Ha.
- inversion E; subst. apply H1. exact Ha.
- eapply H2; eauto.
Qed.

#[using="Type"] Lemma avoid_outside : forall W P x, ivs_avoid W P -> P x -> outside W x.
Proof.
induction W as [|[lo hi] W IH]; intros P x HW HP; cbn; [exact I|]. split.
- intros Hx. exact (HW lo hi x ltac:(left; reflexivity) Hx HP).
- apply (IH P); [|exact HP]. intros lo' hi' a Hin Ha. apply (HW lo' hi'); [right; exact Hin|exact Ha].
Qed.

Definition agree_on (m m' : word -> option byte) (A n : Z) : Prop :=
forall a, A <= a < A + n -> m' (wa a) = m (wa a).

#[using="Type"] Lemma munch_agree : forall W m m' P A n,
munch W m m' -> ivs_avoid W P -> (forall a, A <= a < A + n -> P a) -> 0 <= A -> A + n <= 2^64 ->
agree_on m m' A n.
Proof.
intros W m m' P A n MU HW HP HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
eapply avoid_outside; [exact HW| apply HP; exact Ha].
Qed.

#[using="Type"] Lemma get_meta_rec_put : forall st g mr g',
get_meta_rec (put_meta g mr st) g' = if aptr_eqb g' g then mr else get_meta_rec st g'.
Proof.
intros. unfold get_meta_rec at 1. unfold put_meta. cbn [s_metas set_metas].
unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

#[using="Type"] Lemma upd_meta_put : forall st g f, upd_meta g f st = put_meta g (f (get_meta_rec st g)) st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma del_slots_eq : forall p s c st, del_slots p s c st = set_slots (s_slots (del_slots p s c st)) st.
Proof. reflexivity. Qed.

#[using="Type"] Lemma meta_slot_same_areas : forall st st' g, s_areas st' = s_areas st -> meta_slot st g -> meta_slot st' g.
Proof. intros st st' g E (a & ar & k & Ha & Hk & Eg). exists a, ar, k. rewrite E. auto. Qed.

#[using="Type"] Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
(i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
intros X f n. induction n as [|n IH]; intros s i Hi; [lia|].
cbn [seq map]. destruct i as [|i]; cbn [nth_error]; [f_equal; f_equal; lia|].
rewrite IH by lia. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma actives_nth : forall st sc, 0 <= sc < 48 ->
nth_error (actives st) (Z.to_nat sc) = Some (pw st (active st sc)).
Proof.
intros st sc H. unfold actives. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma usages_nth : forall st sc, 0 <= sc < 48 ->
nth_error (usages st) (Z.to_nat sc) = Some (wz (usage st sc)).
Proof.
intros st sc H. unfold usages. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma bouncess_nth : forall st i, 0 <= i < 32 ->
nth_error (bouncess st) (Z.to_nat i) = Some (b8 (bounces st i)).
Proof.
intros st i H. unfold bouncess. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma unmap_seqs_nth : forall st i, 0 <= i < 32 ->
nth_error (unmap_seqs st) (Z.to_nat i) = Some (b8 (unmap_seq st i)).
Proof.
intros st i H. unfold unmap_seqs. rewrite nth_error_map_seq by lia. f_equal. f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma actives_length st : length (actives st) = 48%nat.
Proof. unfold actives; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma usages_length st : length (usages st) = 48%nat.
Proof. unfold usages; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma bouncess_length st : length (bouncess st) = 32%nat.
Proof. unfold bouncess; rewrite map_length, seq_length; reflexivity. Qed.
#[using="Type"] Lemma unmap_seqs_length st : length (unmap_seqs st) = 32%nat.
Proof. unfold unmap_seqs; rewrite map_length, seq_length; reflexivity. Qed.

#[using="Type"] Lemma put_meta_put_meta_same : forall st g a b, put_meta g a (put_meta g b st) = put_meta g a st.
Proof. intros. destruct st; unfold put_meta, set_metas; cbn. f_equal. apply insert_insert_eq. Qed.

#[using="Type"] Lemma aptr_eqb_neq : forall a b : aptr, a <> b -> aptr_eqb a b = false.
Proof.
intros [a1 a2] [b1 b2] H. unfold aptr_eqb. cbn.
destruct (N.eqb_spec a1 b1); destruct (Z.eqb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. congruence.
Qed.

#[using="Type"] Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true <-> a = b.
Proof.
intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

#[using="Type"] Lemma get_meta_rec_put_same : forall st g mr, get_meta_rec (put_meta g mr st) g = mr.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_put_other : forall st g mr q, q <> g -> get_meta_rec (put_meta g mr st) q = get_meta_rec st q.
Proof. intros. rewrite get_meta_rec_put, aptr_eqb_neq by assumption. reflexivity. Qed.

#[using="Type"] Lemma pw_put_meta : forall st g mr p, pw (put_meta g mr st) p = pw st p. Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_put_meta : forall st g mr p, conc (put_meta g mr st) p = conc st p. Proof. reflexivity. Qed.
#[using="Type"] Lemma ctx_put_meta : forall st g mr, ctx (put_meta g mr st) = ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma meta_slot_put_meta : forall st g mr q, meta_slot st q -> meta_slot (put_meta g mr st) q.
Proof. intros. eapply meta_slot_same_areas; [|eassumption]. reflexivity. Qed.
#[using="Type"] Lemma meta_cells_put_meta : forall st g mr r, meta_cells (put_meta g mr st) r = meta_cells st r. Proof. reflexivity. Qed.

Definition fm_link (st0 : mstate) (g head : aptr) : mstate :=
let hprev := m_prev (get_meta_rec st0 head) in
let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
upd_meta head (m_set_prev (Some g)) st2.

Definition fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
match get_head st0 h with
| Some head => fm_link st0 g head
| None => fm_single st0 h g
end.

#[using="Type"] Lemma queue_eq : forall R h g st0 (k : mstate -> M R) bail,
m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
queue h g st0 k bail = k (queue_st h g st0).
Proof.
intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
unfold queue_st, fm_link, fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).

#[using="Type"] Lemma free_meta_eq : forall R st g (k : mstate -> M R) bail, free_meta g st k bail = k (fm_st st g).
Proof.
intros. unfold free_meta, fm_st. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

Definition free_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
(lo <= a < sp
\/ CTX <= a < CTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

#[using="Type"] Lemma free_fp_stack st lo sp a : lo <= a < sp -> free_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
#[using="Type"] Lemma free_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> free_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
#[using="Type"] Lemma free_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> free_fp st lo sp a.
Proof. intros; left; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma free_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> free_fp st lo sp a.
Proof. intros; right; left. exists b, gh. auto. Qed.

#[using="Type"] Lemma free_fp_mono : forall st st' lo sp sp' a,
s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
(forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
sp' <= sp ->
free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
intros st st' lo sp sp' a ER ES HG HS H.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
- right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.

#[using="Type"] Lemma outside_of_cover : forall (C : Z -> Prop) W a,
(forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) -> ~ C a -> outside W a.
Proof.
induction W as [|[lo hi] W IH]; intros a HW HC; cbn; [exact I|]. split.
- intros Ha. apply HC. apply (HW lo hi); [left; reflexivity| exact Ha].
- apply IH; [|exact HC]. intros lo' hi' Hin x Hx. apply (HW lo' hi'); [right; exact Hin|exact Hx].
Qed.

Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
match W with
| [] => True
| (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
end.

#[using="Type"] Lemma ivs_covered_In : forall C W, ivs_covered C W -> forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x.
Proof.
induction W as [|[lo hi] W IH]; cbn; intros H lo' hi' Hin x Hx; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [E|Hin]; [inversion E; subst; auto| eapply IH; eauto].
Qed.

#[using="Type"] Lemma munch_grow2 : forall f iv W m m', munch (f :: W) m m' -> munch (f :: iv :: W) m m'.
Proof.
intros [flo fhi] [lo hi] W m m' MU. eapply munch_weaken; [|exact MU].
intros x Hx. cbn in Hx |- *. tauto.
Qed.
End RC__1.

Ltac munch_grow MU iv :=
lazymatch type of MU with
| munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).

Hypothesis MU : munch W m m'.

Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.

Hypothesis WIN : forall lo hi, In (lo, hi) W -> CTX <= lo /\ hi <= CTX + 928.

#[using="MU WIN"] Lemma ctxW_avoid : forall A n, (A + n <= CTX \/ CTX + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof.
intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- destruct HD as [HD|HD].
+ pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
+ pose proof (HD lo hi ltac:(left; reflexivity)). lia.
- apply IH.
+ intros lo' hi' Hin. apply WIN. right; exact Hin.
+ destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.

End CTXFRAME.

#[using="Type"] Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
End RC__2.

Ltac amo_align AMO :=
try (rewrite AMO; cbv beta iota delta [negb]);
try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_step AMO :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end. Ltac mkr__amo_step_0 AMO := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt ]
end end
end.

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS ?R _ ?pc _ ?rv _ _) => idtac "=== PC" pc "RV" rv end.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma sextw_sxv0 v : Z_to_bv 64 (bv_swrap 32 (sxv v + 0)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv. Qed.
#[using="Type"] Lemma sextw_sxv1 v : Z_to_bv 64 (bv_swrap 32 (sxv v)) = wz (sxv v).
Proof. rewrite <- (wz_unsigned (sxv v)) at 1 by (apply sxv_range). apply sextw_sxv'. Qed.

#[using="Type"] Lemma le4_lor_sxv : forall f s, 0 <= f < 2^32 -> 0 <= s < 2^32 ->
le4 (Z_to_bv 64 (Z.lor (sxv s) (sxv f))) = le4 (wz (Z.lor f s)).
Proof.
intros f s Hf Hs. apply le4_congr. pose proof (lor_range64 (sxv s) (sxv f) (sxv_range _) (sxv_range _)).
pose proof (Z_lor_range f s ltac:(lia) ltac:(lia)).
rewrite unsigned_lit by lia. rewrite wz_unsigned.
2:{ split; [lia|]. apply (Z.lt_le_trans _ (2^32)); [|lia]. apply Z_bounded_by_bits; [lia|lia|].
intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity. }
rewrite lor_sxv_mod32 by lia. rewrite Z.lor_comm. symmetry. apply Z.mod_small.
split; [lia|]. apply Z_bounded_by_bits; [lia|lia|].
intros k Hk. rewrite Z.lor_spec, (Z_testbit_high 32 f k), (Z_testbit_high 32 s k) by lia. reflexivity.
Qed.

Definition ntf_mid_post (pc : Z) (R : list cell -> word -> Prop ) : Prop := True.

End RC__3.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma steq_trans {E A R} (t1 t2 t3 : stree E A R) : steq t1 t2 -> steq t2 t3 -> steq t1 t3.
Proof.
intros H1 H2. apply strel_eq_steq. apply strel_eq_steq in H1. apply strel_eq_steq in H2.
eapply strel_trans_eq; [exact H1| exact H2].
Qed.

#[using="Type"] Lemma steq_sbind {E A R S} (t1 t2 : stree E A R) (f1 f2 : R -> stree E A S) :
steq t1 t2 -> (forall r, steq (f1 r) (f2 r)) -> steq (sbind t1 f1) (sbind t2 f2).
Proof.
intros Ht Hf. apply strel_eq_steq. eapply (strel_sbind (RR := eq)); [apply strel_eq_steq; exact Ht|].
intros r1 r2 ->. apply strel_eq_steq. apply Hf.
Qed.

#[using="Type"] Lemma eruns_steq {E A O R} (sel : O -> E -> option A) (upd : O -> E -> A -> O) (t1 t2 : stree E A R) :
steq t1 t2 -> forall o, steq (eruns sel upd o t1) (eruns sel upd o t2).
Proof.
induction 1 as [r|e k1 k2 Hk IH]; intros o; cbn [eruns].
- constructor.
- destruct (sel o e) as [a|]; [apply IH|]. constructor. intros a. apply IH.
Qed.

Definition kS {X Y : Type} : X -> Y -> QUZl.M (option (X * Y)) := fun x y => SRet (Some (x, y)).
Definition bS {T : Type} : QUZl.M (option T) := SRet None.
Definition KF {X Y R : Type} (k : X -> Y -> QUZl.M R) (bail : QUZl.M R) (r : option (X * Y)) : QUZl.M R :=
match r with Some (x, y) => k x y | None => bail end.

Definition kS1 {X : Type} : X -> QUZl.M (option X) := fun x => SRet (Some x).
Definition KF1 {X R : Type} (k : X -> QUZl.M R) (bail : QUZl.M R) (r : option X) : QUZl.M R :=
match r with Some x => k x | None => bail end.
End RC__1.

Ltac nat_leaf := cbn [sbind KF KF1 kS kS1 bS]; apply steq_refl.
Ltac nat_vis := cbn [sbind]; apply steq_vis; intros ?.
Ltac nat_case :=
lazymatch goal with
| |- steq _ (sbind (match ?c with _ => _ end) _) => destruct c
end.

Ltac nat_call NAT :=
eapply steq_trans; [apply NAT|];
eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
apply steq_sbind; [apply steq_refl|];
intros [[? ?]|]; cbn [KF sbind].
Ltac nat_call1 NAT :=
eapply steq_trans; [apply NAT|];
eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
apply steq_sbind; [apply steq_refl|];
intros [?|]; cbn [KF1 sbind].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma guard_nat {X Y R} tag c (K : QUZl.M R) (K' : QUZl.M (option (X * Y))) bail f :
steq K (sbind K' f) -> steq bail (f None) ->
steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

#[using="Type"] Lemma guard_nat1 {X R} tag c (K : QUZl.M R) (K' : QUZl.M (option X)) bail f :
steq K (sbind K' f) -> steq bail (f None) ->
steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

#[using="Type"] Lemma queue_nat {R} h m st (k : mstate -> QUZl.M R) bail :
steq (queue h m st k bail) (sbind (queue h m st kS1 bS) (KF1 k bail)).
Proof.
unfold queue. apply guard_nat1; [|nat_leaf]. apply guard_nat1; [|nat_leaf].
nat_case; cbv zeta; [destruct (m_prev _)|]; nat_leaf.
Qed.

#[using="Type"] Lemma free_meta_nat {R} m st (k : mstate -> QUZl.M R) bail :
steq (free_meta m st k bail) (sbind (free_meta m st kS1 bS) (KF1 k bail)).
Proof. unfold free_meta. apply queue_nat. Qed.

#[using="Type"] Lemma activate_group_nat {R} m st (k : mstate -> Z -> QUZl.M R) bail :
steq (activate_group m st k bail) (sbind (activate_group m st kS bS) (KF k bail)).
Proof. unfold activate_group. apply guard_nat; [|nat_leaf]. cbv zeta. nat_leaf. Qed.
End RC__2.

Ltac nat_auto cal :=
first [ nat_leaf
| cal
| nat_vis; nat_auto cal
| nat_case; nat_auto cal
| progress (cbv zeta); nat_auto cal ].
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma am_take_nat {R} st (k : mstate -> optr -> QUZl.M R) bail :
steq (am_take st k bail) (sbind (am_take st kS bS) (KF k bail)).
Proof. unfold am_take. nat_auto fail. Qed.

#[using="Type"] Lemma am_carve_nat {R} st p (k : mstate -> optr -> QUZl.M R) bail :
steq (am_carve st p k bail) (sbind (am_carve st p kS bS) (KF k bail)).
Proof. unfold am_carve. cbv zeta. apply am_take_nat. Qed.

#[using="Type"] Lemma am_finish_nat {R} st nu (k : mstate -> optr -> QUZl.M R) bail :
steq (am_finish st nu k bail) (sbind (am_finish st nu kS bS) (KF k bail)).
Proof. unfold am_finish, bad_answer. nat_auto ltac:(apply am_carve_nat). Qed.

#[using="Type"] Lemma am_after_brk_nat {R} st nu (k : mstate -> optr -> QUZl.M R) bail :
steq (am_after_brk st nu k bail) (sbind (am_after_brk st nu kS bS) (KF k bail)).
Proof. unfold am_after_brk, bad_answer. nat_auto ltac:(apply am_finish_nat). Qed.

#[using="Type"] Lemma alloc_meta_nat {R} st (k : mstate -> optr -> QUZl.M R) bail :
steq (alloc_meta st k bail) (sbind (alloc_meta st kS bS) (KF k bail)).
Proof.
unfold alloc_meta, bad_answer. nat_auto ltac:(first [apply am_take_nat | apply am_after_brk_nat]).
Qed.

#[using="Type"] Lemma ta_fin_nat {R} st m mask (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) :
steq (ta_fin st m mask k) (sbind (ta_fin st m mask kS) (KF k bail)).
Proof. unfold ta_fin. cbv zeta. nat_leaf. Qed.

#[using="Type"] Lemma try_avail_nat {R} sc st (k : mstate -> Z -> QUZl.M R) bail :
steq (try_avail sc st k bail) (sbind (try_avail sc st kS bS) (KF k bail)).
Proof.
unfold try_avail. nat_case; [|nat_leaf]. cbv zeta. nat_case; [apply ta_fin_nat|].
nat_case.
- destruct p as [st1 m1]. nat_case. destruct p as [st2 m2]. nat_case.
eapply steq_trans; [apply activate_group_nat|].
eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply activate_group_nat| intros ?; apply steq_refl]| apply sbind_assoc]].
apply steq_sbind; [apply steq_refl|]. intros [[st4 mask]|]; cbn [KF sbind]; [|nat_leaf].
apply guard_nat; [apply ta_fin_nat| nat_leaf].
- nat_case; [nat_leaf|]. nat_vis. nat_leaf.
Qed.

#[using="Type"] Lemma ag_tail_nat {R} lay st sc m p cnt ai (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) :
steq (ag_tail lay st sc m p cnt ai k) (sbind (ag_tail lay st sc m p cnt ai kS) (KF k bail)).
Proof. unfold ag_tail. cbv zeta. nat_leaf. Qed.

Section AG.
Variable lay : layout_hook.
Variable rec : forall R, mstate -> Z -> Z -> (mstate -> Z -> QUZl.M R) -> QUZl.M R -> QUZl.M R.
Hypothesis rec_nat : forall R st sc req (k : mstate -> Z -> QUZl.M R) bail,
steq (rec R st sc req k bail) (sbind (rec _ st sc req kS bS) (KF k bail)).

#[using="rec_nat"] Lemma alloc_group_nat {R} st sc req (k : mstate -> optr -> QUZl.M R) bail :
steq (alloc_group R lay (rec R) st sc req k bail)
(sbind (alloc_group _ lay (rec _) st sc req kS bS) (KF k bail)).
Proof.
unfold alloc_group, bad_answer. cbv zeta. nat_call (@alloc_meta_nat); [|nat_leaf].
nat_case; [|nat_leaf]. nat_case.
-
match goal with |- steq _ (sbind (let '(_, _) := ?p in _) _) => destruct p as [cnt' needed] end.
nat_vis. nat_case; [nat_vis; nat_leaf|]. nat_case.
+ nat_call1 (@free_meta_nat); nat_leaf.
+ nat_case. cbv zeta. apply ag_tail_nat.
-
nat_call rec_nat; [|nat_leaf]. nat_case.
+ nat_call1 (@free_meta_nat); nat_leaf.
+ nat_case; [|nat_vis; nat_leaf]. cbv zeta. apply ag_tail_nat.
Qed.
End AG.

#[using="Type"] Lemma alloc_slot_nat lay fuel : forall R st sc req (k : mstate -> Z -> QUZl.M R) bail,
steq (alloc_slot lay fuel st sc req k bail) (sbind (alloc_slot lay fuel st sc req kS bS) (KF k bail)).
Proof.
induction fuel as [|f IH]; intros R st sc req k bail.
- cbn [alloc_slot]. nat_vis. nat_leaf.
- cbn [alloc_slot]. nat_call (@try_avail_nat); [|nat_leaf]. nat_case; [nat_leaf|].
eapply steq_trans; [apply (alloc_group_nat lay (fun R => @alloc_slot _ R lay f) IH)|].
eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply (alloc_group_nat lay (fun R => @alloc_slot _ R lay f) IH)| intros ?; apply steq_refl]| apply sbind_assoc]].
apply steq_sbind; [apply steq_refl|]. intros [[st2 go]|]; cbn [KF sbind]; [|nat_leaf].
nat_case; [|nat_leaf]. cbv zeta. nat_call1 (@queue_nat); nat_leaf.
Qed.

End RC__3.
End Mq7.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Definition zbytes (l : list Z) : list byte := map (Z_to_bv 8) l.

Definition sh_cells (T : Z) (f : shfile) : list cell :=
[C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 (sh_rpos f)); C8 (Z_to_bv 64 (sh_cnt0 f)); C8 (Z_to_bv 64 (sh_n f));
C4 (Z_to_bv 64 (Z.b2z (sh_stdio f))); C4 (Z_to_bv 64 (Z.b2z (sh_shlim_neg f)))].

Definition sh_ok (T : Z) (txt : list Z) (f : shfile) : Prop :=
sh_buf f = txt /\ zlength txt <= 2^40 /\ 0 <= sh_rpos f <= 2^40 /\ 0 <= sh_cnt0 f <= 2^40
/\ 0 <= sh_n f <= zlength txt /\ (sh_stdio f = true -> sh_rpos f <= sh_n f).

Ltac show_goal := match goal with |- ?g => idtac g end.
Ltac show_hyp H := let T := type of H in idtac H ":" T.

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma znth_In' : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
intros l i Hi. unfold znth, zlength in *. destruct (Z.ltb_spec0 i 0); [lia|].
apply nth_In. lia.
Qed.
Lemma zbytes_nth : forall txt i, 0 <= i < zlength txt ->
nth_error (zbytes txt) (Z.to_nat i) = Some (Z_to_bv 8 (znth txt i)).
Proof.
intros txt i Hi. unfold zbytes, zlength, znth in *. rewrite nth_error_map.
destruct (Z.ltb_spec0 i 0); [lia|].
destruct (nth_error txt (Z.to_nat i)) as [c|] eqn:E.
- cbn. f_equal. f_equal. symmetry. apply nth_error_nth. exact E.
- apply nth_error_None in E. lia.
Qed.

