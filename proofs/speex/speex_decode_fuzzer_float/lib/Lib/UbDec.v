(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1od.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma land3_al a : a mod 4 = 0 -> Z.land a 3 = 0.
Proof. intros H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
Lemma land7_al a : a mod 8 = 0 -> Z.land a 7 = 0.
Proof. intros H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.
Lemma sh_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_m4_al : forall x, 0 <= x < 2^64 -> x mod 4 = 0 -> Z.land x 18446744073709551612 = x.
Proof.
intros x Hx H. change 18446744073709551612 with (Z.ldiff (Z.ones 64) (Z.ones 2)).
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.
Lemma lor_al4 : forall a b, 0 <= a -> 0 <= b -> a mod 4 = 0 -> b mod 4 = 0 -> Z.land (Z.lor a b) 3 = 0.
Proof.
intros a b Ha Hb HA HB. rewrite Z.land_lor_distr_l.
change 3 with (Z.ones 2). rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite HA, HB. reflexivity.
Qed.

Lemma ub_ptr_guard_nonneg : forall base idx, 0 <= idx < 2^63 ->
Z.lxor (Z.lxor (Z.b2z (base + idx <? base)) (Z.b2z (Z.lxor idx 9223372036854775808 <? 9223372036854775808))) 1 = 1.
Proof.
intros base idx Hi. change 9223372036854775808 with (2^63). rewrite (zb_lxor_pow2_small idx 63) by lia.
replace (base + idx <? base) with false by (symmetry; apply Z.ltb_ge; lia).
replace (idx + 2^63 <? 2^63) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ptr_sgn_guard : forall A y Y, Y = A + 4 * y ->
Z.lxor (Z.lxor (Z.b2z (Y <? A)) (Z.b2z (y + 9223372036854775808 <? 9223372036854775808))) 1 = 1.
Proof.
intros A y Y ->. destruct (A + 4 * y <? A) eqn:H1; destruct (y + 9223372036854775808 <? 9223372036854775808) eqn:H2;
try apply Z.ltb_lt in H1; try apply Z.ltb_lt in H2; try apply Z.ltb_ge in H1; try apply Z.ltb_ge in H2; try lia; reflexivity.
Qed.

Lemma ip_sgn_guard : forall E p, Z.lxor (Z.lxor (Z.b2z (E - 4 * p <? E)) (Z.b2z (p + 9223372036854775808 <? 9223372036854775809))) 1 = 0.
Proof.
intros E p. destruct (E - 4 * p <? E) eqn:H1; destruct (p + 9223372036854775808 <? 9223372036854775809) eqn:H2;
try apply Z.ltb_lt in H1; try apply Z.ltb_lt in H2; try apply Z.ltb_ge in H1; try apply Z.ltb_ge in H2; try lia; reflexivity.
Qed.

Lemma swrap32_mod64_add : forall x k, -2^31 <= x + k < 2^31 ->
bv_swrap 32 (x mod 18446744073709551616 + k) = x + k.
Proof.
intros x k H. rewrite <- (swrap32_small (x + k)) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. f_equal.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (x - 18446744073709551616 * (x / 18446744073709551616) + k + 2147483648)
with ((x + k + 2147483648) + (- 4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma addr_shift2 : forall base x r, r = base + 4 * x ->
Z_to_bv 64 (base + Z.shiftl (x mod 18446744073709551616) 2) = Z_to_bv 64 r.
Proof.
intros base x r ->. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (base + (x - 18446744073709551616 * (x / 18446744073709551616)) * 4)
with ((base + 4 * x) + (- 4 * (x / 18446744073709551616)) * 18446744073709551616) by lia.
change (2^64) with 18446744073709551616. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma sub_shift2 : forall base x,
Z_to_bv 64 (base - (Z.shiftl (x mod 18446744073709551616) 2) mod 18446744073709551616) = Z_to_bv 64 (base - 4 * x).
Proof.
intros base x. apply Z_to_bv_eqm. change (2^64) with 18446744073709551616.
rewrite Zminus_mod_idemp_r. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
rewrite Zminus_mod, Zmult_mod_idemp_l, <- Zminus_mod. f_equal. lia.
Qed.

Lemma swrap32_sub_mod64 : forall a x, bv_swrap 32 (a - x mod 18446744073709551616) = bv_swrap 32 (a - x).
Proof.
intros a x. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. f_equal.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (a - (x - 18446744073709551616 * (x / 18446744073709551616)) + 2147483648)
with ((a - x + 2147483648) + (4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma zbv_sub_mod : forall a x, Z_to_bv 64 (a - x mod 18446744073709551616) = Z_to_bv 64 (a - x).
Proof.
intros a x. apply Z_to_bv_eqm. change (2^64) with 18446744073709551616.
rewrite Zminus_mod_idemp_r. reflexivity.
Qed.
Lemma zbv_mod_add : forall x k, Z_to_bv 64 (x mod 18446744073709551616 + k) = Z_to_bv 64 (x + k).
Proof. intros. apply Z_to_bv_eqm. change (2^64) with 18446744073709551616. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma lxor_sign_mod : forall p, -2^63 <= p < 2^63 -> Z.lxor (p mod 18446744073709551616) 9223372036854775808 = p + 9223372036854775808.
Proof.
intros p Hp. change 9223372036854775808 with (2^63). rewrite zb_lxor_sign by (split; [apply Z.mod_pos_bound | apply Z.mod_pos_bound]; lia).
change 18446744073709551616 with (2^64). rewrite Zplus_mod_idemp_l. apply Z.mod_small. lia.
Qed.
Lemma lxor_sign_nn : forall j, 0 <= j < 2^63 -> Z.lxor j 9223372036854775808 = j + 9223372036854775808.
Proof. intros j Hj. rewrite <- (lxor_sign_mod j) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma lxs64 : forall x, -2^63 <= x < 2^63 -> Z.lxor (x mod 18446744073709551616) 9223372036854775808 = x + 9223372036854775808.
Proof. exact lxor_sign_mod. Qed.
Lemma subm64 : forall x y, (x - y mod 18446744073709551616) mod 18446744073709551616 = (x - y) mod 18446744073709551616.
Proof. intros. apply Zminus_mod_idemp_r. Qed.

Lemma negw_guard : forall x, -2^31 < x < 0 ->
bv_swrap 32 (0 - x mod 18446744073709551616) = - x /\ Z_to_bv 64 (0 - x mod 18446744073709551616) = Z_to_bv 64 (- x).
Proof.
intros x Hx. split.
- unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.modulo Z.div]. Z.div_mod_to_equations. lia.
- rewrite <- (Z_to_bv_mod64 (0 - x mod 18446744073709551616)), <- (Z_to_bv_mod64 (- x)). f_equal. Z.div_mod_to_equations. lia.
Qed.

Lemma srl30_guard : forall x, 0 <= x < 2^29 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (x + 536870912)) 30) = 0.
Proof.
intros x Hx. unfold bv_wrap, bv_modulus. cbn -[Z.modulo Z.shiftr].
rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma bv_eqb_lit_ne_k : forall r k, -2^63 <= r < 2^63 -> -2^63 <= k < 2^63 -> r <> k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = false.
Proof.
intros r k Hr Hk NE. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
intros E. Z.div_mod_to_equations. nia.
Qed.
Lemma bv_eqb_same_k : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma bv_eqb_lit_eq_k : forall r k, r = k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = true.
Proof. intros r k ->. apply bv_eqb_same_k. Qed.
Lemma lts_lit_k : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed_small by lia. reflexivity. Qed.
Lemma swrap32_eq_k : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.
Lemma sx32_lit_k : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, swrap32_eq_k.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma swrap32_small_k : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite swrap32_eq_k. rewrite Z.mod_small by lia. lia. Qed.
Lemma swrap_mod64_plus1_k : forall x, -2^31 <= x < 2^31 - 1 -> bv_swrap 32 (x mod 18446744073709551616 + 1) = x + 1.
Proof.
intros x Hx. rewrite swrap32_eq_k.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
rewrite (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 (x mod 18446744073709551616 + 1 + 2147483648)) by (lia || exact D).
replace (x mod 18446744073709551616 + 1 + 2147483648) with (x mod 18446744073709551616 + (1 + 2147483648)) by lia.
rewrite Zplus_mod_idemp_l. replace (x + (1 + 2147483648)) with (x + 1 + 2147483648) by lia.
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 (x + 1 + 2147483648)) by (lia || exact D).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma zbv_add_modr_k : forall x y, Z_to_bv 64 (x + y mod 18446744073709551616) = Z_to_bv 64 (x + y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zplus_mod_idemp_r. reflexivity. Qed.
Lemma swrap32_add_modr_k : forall x y, bv_swrap 32 (x + y mod 18446744073709551616) = bv_swrap 32 (x + y).
Proof.
intros x y. rewrite !swrap32_eq_k. f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
replace (x + y mod 18446744073709551616 + 2147483648) with ((x + 2147483648) + y mod 18446744073709551616) by lia.
replace (x + y + 2147483648) with ((x + 2147483648) + y) by lia.
rewrite (Zplus_mod (x + 2147483648) (y mod 18446744073709551616)), (Zplus_mod (x + 2147483648) y).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 y) by (lia || exact D). reflexivity.
Qed.
Lemma zbv_add_modl_k : forall x y, Z_to_bv 64 (x mod 18446744073709551616 + y) = Z_to_bv 64 (x + y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma zbv_sub_modr_k : forall x y, Z_to_bv 64 (x - y mod 18446744073709551616) = Z_to_bv 64 (x - y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zminus_mod_idemp_r. reflexivity. Qed.
Lemma zbv_sub_modl_k : forall x y, Z_to_bv 64 (x mod 18446744073709551616 - y) = Z_to_bv 64 (x - y).
Proof. intros x y. apply Z_to_bv_eqm. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
Lemma zbv_modM_k : forall x, Z_to_bv 64 (x mod 18446744073709551616) = Z_to_bv 64 x.
Proof. intros x. apply Z_to_bv_eqm. rewrite Zmod_mod. reflexivity. Qed.
Lemma swrap32_modM_k : forall x, bv_swrap 32 (x mod 18446744073709551616) = bv_swrap 32 x.
Proof.
intros x. rewrite !swrap32_eq_k. f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
rewrite (Zplus_mod (x mod 18446744073709551616)), (Zplus_mod x).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 x) by (lia || exact D). reflexivity.
Qed.
Lemma swrap32_modl_k : forall x y, bv_swrap 32 (x mod 18446744073709551616 + y) = bv_swrap 32 (x + y).
Proof. intros x y. rewrite (Z.add_comm (x mod 18446744073709551616) y), (Z.add_comm x y). apply swrap32_add_modr_k. Qed.
Lemma swrap32_sub_modr_k : forall x y, bv_swrap 32 (x - y mod 18446744073709551616) = bv_swrap 32 (x - y).
Proof.
intros x y. rewrite !swrap32_eq_k. f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
replace (x - y mod 18446744073709551616 + 2147483648) with ((x + 2147483648) - y mod 18446744073709551616) by lia.
replace (x - y + 2147483648) with ((x + 2147483648) - y) by lia.
rewrite (Zminus_mod (x + 2147483648) (y mod 18446744073709551616)), (Zminus_mod (x + 2147483648) y).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 y) by (lia || exact D). reflexivity.
Qed.
Lemma swrap32_sub_modl_k : forall x y, bv_swrap 32 (x mod 18446744073709551616 - y) = bv_swrap 32 (x - y).
Proof.
intros x y. rewrite !swrap32_eq_k. f_equal.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
replace (x mod 18446744073709551616 - y + 2147483648) with (x mod 18446744073709551616 + (2147483648 - y)) by lia.
replace (x - y + 2147483648) with (x + (2147483648 - y)) by lia.
rewrite (Zplus_mod (x mod 18446744073709551616)), (Zplus_mod x).
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 x) by (lia || exact D). reflexivity.
Qed.
Ltac tnorm :=
repeat match goal with
| |- context [bv_swrap 32 (?x + ?y mod 18446744073709551616)] => rewrite (swrap32_add_modr_k x y)
| |- context [bv_swrap 32 (?x mod 18446744073709551616 + ?y)] => rewrite (swrap32_modl_k x y)
| |- context [bv_swrap 32 (?x - ?y mod 18446744073709551616)] => rewrite (swrap32_sub_modr_k x y)
| |- context [bv_swrap 32 (?x mod 18446744073709551616 - ?y)] => rewrite (swrap32_sub_modl_k x y)
| |- context [bv_swrap 32 (?x mod 18446744073709551616)] => rewrite (swrap32_modM_k x)
| |- context [Z_to_bv 64 (?x + ?y mod 18446744073709551616)] => rewrite (zbv_add_modr_k x y)
| |- context [Z_to_bv 64 (?x mod 18446744073709551616 + ?y)] => rewrite (zbv_add_modl_k x y)
| |- context [Z_to_bv 64 (?x - ?y mod 18446744073709551616)] => rewrite (zbv_sub_modr_k x y)
| |- context [Z_to_bv 64 (?x mod 18446744073709551616 - ?y)] => rewrite (zbv_sub_modl_k x y)
| |- context [Z_to_bv 64 (?x mod 18446744073709551616)] => rewrite (zbv_modM_k x)
| |- context [?x + 0] => rewrite (Z.add_0_r x)
| |- context [bv_swrap 32 ?a] => rewrite (swrap32_small_k a) by lia
end.

Lemma granule_step_range {ptr : Type} (h : hstate ptr) hdr skip : granule_step h hdr = Some skip -> -2^31 < skip < 2^31.
Proof.
intros G. unfold granule_step in G. cbv zeta in G.
lazymatch type of G with (if ?c then _ else _) = _ => destruct c; cbv iota in G end.
- lazymatch type of G with (if ?c then _ else _) = _ => destruct c; cbv iota in G; [discriminate G|] end.
lazymatch type of G with (if (s32 ?x =? _) then _ else _) = _ =>
pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)) as R;
destruct (Z.eqb_spec (s32 x) INT_MIN) as [E|E]; cbv iota in G; [discriminate G|] end.
injection G as <-. unfold s32, INT_MIN in *.
lazymatch goal with |- context [if ?b then _ else _] => destruct b end; lia.
- lazymatch type of G with (if ?c then _ else _) = _ => destruct c; cbv iota in G; [discriminate G|] end.
injection G as <-. lia.
Qed.

Ltac fold_lit_if_core :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
lazymatch c with
| negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) => is_Zlit x; is_Zlit y
| bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) => is_Zlit x; is_Zlit y
| negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) => is_Zlit x; is_Zlit y
| bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) => is_Zlit x; is_Zlit y
| negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) => is_Zlit x; is_Zlit y
| bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) => is_Zlit x; is_Zlit y
end;
let v := eval vm_compute in c in
lazymatch v with
| true => change (evt segs Q (MS R F a fc rv m ro))
| false => change (evt segs Q (MS R F b fc rv m ro))
end
end.
Ltac fold_lit_if := first [ fold_lit_if_core | idtac ].
Ltac ub_step := zstep; fix_lit_store; fold_lit_if.

From Ltac2 Require Ltac2.
Module ChkL2.
Import Ltac2.
Ltac2 rec open_term (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f args => if open_term f then true else Array.exist open_term args
| Constr.Unsafe.Cast c _ _ => open_term c
| Constr.Unsafe.Constant _ _ => false
| Constr.Unsafe.Ind _ _ => false
| Constr.Unsafe.Constructor _ _ => false
| Constr.Unsafe.Sort _ => false
| Constr.Unsafe.Uint63 _ => false
| _ => true
end.
Ltac2 assert_closed (c : constr) : unit :=
if open_term c then Control.zero (Tactic_failure (Some (Message.of_string "lit_if: the condition is not a closed term"))) else ().
End ChkL2.
Ltac assert_closed c := let f := ltac2:(c |- ChkL2.assert_closed (Option.get (Ltac1.to_constr c))) in f c.
Ltac lit_if :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
assert_closed c;
let v := eval vm_compute in c in
lazymatch v with
| true => change (evt segs Q (MS R F a fc rv m ro))
| false => change (evt segs Q (MS R F b fc rv m ro))
end
end.

Ltac alit_bin op a b := is_Zlit a; is_Zlit b; let v := eval vm_compute in (op a b) in change (op a b) with v.
Ltac alit1 :=
match goal with
| |- context [Z.b2z (Z.ltb ?a ?b)] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (Z.ltb a b)) in change (Z.b2z (Z.ltb a b)) with v
| |- context [Z.b2z (Z.eqb ?a ?b)] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (Z.eqb a b)) in change (Z.b2z (Z.eqb a b)) with v
| |- context [Z.sub ?a ?b] => alit_bin Z.sub a b
| |- context [Z.modulo ?a ?b] => alit_bin Z.modulo a b
| |- context [Z.land ?a ?b] => alit_bin Z.land a b
| |- context [Z.lor ?a ?b] => alit_bin Z.lor a b
| |- context [Z.shiftl ?a ?b] => alit_bin Z.shiftl a b
| |- context [Z.shiftr ?a ?b] => alit_bin Z.shiftr a b
| |- context [Z.mul ?a ?b] => alit_bin Z.mul a b
| |- context [Z.add ?a ?b] => alit_bin Z.add a b
| |- context [bv_swrap 32 ?a] => is_Zlit a; let v := eval vm_compute in (bv_swrap 32 a) in change (bv_swrap 32 a) with v
| |- context [bv_swrap 64 ?a] => is_Zlit a; let v := eval vm_compute in (bv_swrap 64 a) in change (bv_swrap 64 a) with v
end.
Ltac alits := repeat alit1.

Ltac ub_show_pc_fail p := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 1 "ato" p ": stuck at" pc end.
Ltac ub_at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => idtac end.
Ltac ub_at_if := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.
Ltac ato p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then lit_if else ub_step)); first [ ub_at_pc p | ub_show_pc_fail p ].

Ltac sh_cond :=
unfold_cond; rewrite ?sh_land7;
repeat match goal with |- context [Z.modulo ?a 8] =>
lazymatch goal with _ : 0 <= a mod 8 < 8 |- _ => fail | _ => pose proof (Z.mod_pos_bound a 8 ltac:(lia)) end end;
fold_lit_ux; rewrite ?zb_signed_small by lia; rewrite ?unsigned_lit by lia;
solve_cond_rec.
Ltac sh_if_true :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; sh_cond] end.
Ltac sh_if_false :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; sh_cond] end.
Ltac sh_if := first [ sh_if_true | sh_if_false ].

Ltac bdec1 :=
lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
match constr:((R, pc)) with
| context [Z.ltb ?a ?b] => first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; lia) ]
| context [Z.eqb ?a ?b] => first [ replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia) ]
end
end.
Ltac alitx1 := match goal with |- context [Z.lxor ?a ?b] => alit_bin Z.lxor a b end.
Ltac balits := repeat first [ alit1 | alitx1 ].
Ltac bdec := repeat bdec1; cbn [Z.b2z negb andb orb]; balits.

Ltac bnorm :=
repeat match goal with
| |- context [bv_swrap 32 ?a] => rewrite (swrap32_small a) by lia
| |- context [Z.shiftl ?a ?k] => rewrite (Z.shiftl_mul_pow2 a k) by lia
| |- context [?a mod 18446744073709551616] => rewrite (Z.mod_small a 18446744073709551616) by lia
| |- context [Z.lxor ?y 9223372036854775808] =>
replace (Z.lxor y 9223372036854775808) with (y + 9223372036854775808) by (change 9223372036854775808 with (2 ^ 63); symmetry; apply zb_lxor_pow2_small; lia)
| |- context [Z.lxor ?y 18446744073709551615] => rewrite (zb_lxor_ones y) by lia
| |- context [Z.lxor ?a ?a] => rewrite (Z.lxor_nilpotent a)
| |- context [Z.land ?a 3] => rewrite (land3_al a) by assumption
| |- context [Z.land ?a 7] => rewrite (land7_al a) by assumption
end; change (2 ^ 2) with 4 in *.

Ltac ub_dec := first [ lit_if | (bdec; lit_if) | sh_if | if_false_z | if_true_z
| (bnorm; bdec; first [ lit_if | sh_if | if_false_z | if_true_z ]) ].
Ltac bato p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then ub_dec else ub_step)); first [ ub_at_pc p | ub_show_pc_fail p ].
