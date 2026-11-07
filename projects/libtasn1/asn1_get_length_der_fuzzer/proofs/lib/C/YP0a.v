(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YP0j YP0g YP0h YP0k YP09.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma lor_add_high a b n : 0 <= a < 2^n -> 0 <= b -> Z.lor a (2^n * b) = a + 2^n * b.
Proof.
intros Ha Hb. assert (Hn : 0 <= n) by (destruct (Z_le_gt_dec 0 n); [lia|rewrite Z.pow_neg_r in Ha; lia]).
assert (Hd : Z.land a (2^n * b) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, (Z.mul_comm (2^n)), Z.mul_pow2_bits by lia.
destruct (Z_lt_le_dec i n).
- rewrite (Z.testbit_neg_r b) by lia. apply andb_false_r.
- rewrite (testbit_high_false a n i) by lia. reflexivity. }
rewrite <- Z.lxor_lor by exact Hd. symmetry. apply Z.add_nocarry_lxor. exact Hd.
Qed.
Lemma lor_add_high' a b n : 0 <= a < 2^n -> 0 <= b -> Z.lor (2^n * b) a = a + 2^n * b.
Proof. intros. rewrite Z.lor_comm. apply lor_add_high; lia. Qed.
Definition bits_enc (last sc maplen : Z) : Z := last + 32 + 64 * sc + 4096 * maplen.
Lemma meta_bits_enc am : meta_bits am = bits_enc (am_last am) (am_sc am) (am_maplen am).
Proof. reflexivity. Qed.
Lemma bits_nonneg last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
0 <= (bits_enc last sc maplen).
Proof.
intros Hl Hs Hm. unfold bits_enc. lia. Qed.
Lemma bits_lt64 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
maplen < 2^52 -> (bits_enc last sc maplen) < 2^64.
Proof.
intros Hl Hs Hm. unfold bits_enc. intros. lia. Qed.
Lemma bits_mod4096 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
(bits_enc last sc maplen) mod 4096 = bits_enc last sc 0.
Proof.
intros Hl Hs Hm.
unfold bits_enc. replace (last + 32 + 64 * sc + 4096 * maplen) with ((last + 32 + 64 * sc) + maplen * 4096) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma bits_div4096 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
(bits_enc last sc maplen) / 4096 = maplen.
Proof.
intros Hl Hs Hm.
unfold bits_enc. symmetry. apply Z.div_unique with (r := last + 32 + 64 * sc); lia.
Qed.
Lemma bits_div64 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
(bits_enc last sc maplen) / 64 = sc + 64 * maplen.
Proof.
intros Hl Hs Hm.
unfold bits_enc. symmetry. apply Z.div_unique with (r := last + 32); lia.
Qed.

Lemma bits_land31 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.land (bits_enc last sc maplen) 31 = last.
Proof.
intros Hl Hs Hm.
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
unfold bits_enc. replace (last + 32 + 64 * sc + 4096 * maplen) with (last + (1 + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma bits_mod32 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
(bits_enc last sc maplen) mod 32 = last.
Proof.
intros Hl Hs Hm. rewrite <- (bits_land31 last sc maplen Hl Hs Hm) at 2. symmetry. change 31 with (Z.ones 5). apply Z.land_ones. lia. Qed.
Lemma bits_shiftr12 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.shiftr (bits_enc last sc maplen) 12 = maplen.
Proof.
intros Hl Hs Hm. rewrite Z.shiftr_div_pow2 by lia. apply (bits_div4096 last sc maplen Hl Hs Hm). Qed.

Lemma bits_sc last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.shiftr (sll64 (bits_enc last sc maplen) 52) 58 = sc.
Proof.
intros Hl Hs Hm.
unfold sll64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^64) with (4096 * 2^52). rewrite Z.mul_mod_distr_r by lia.
rewrite (bits_mod4096 last sc maplen Hl Hs Hm). unfold bits_enc.
replace (2^58) with (2^52 * 64) by reflexivity.
rewrite <- Z.div_div, Z.div_mul by lia.
symmetry. apply Z.div_unique with (r := last + 32); lia.
Qed.

Lemma bits_2sc last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.land (Z.shiftr (bits_enc last sc maplen) 5) 126 = 2 * sc.
Proof.
intros Hl Hs Hm.
change 126 with (2^1 * Z.ones 6). rewrite land_field by lia.
rewrite Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. change (2^(5+1)) with 64. change (2^6) with 64. change (2^1) with 2.
rewrite (bits_div64 last sc maplen Hl Hs Hm). replace (sc + 64 * maplen) with (sc + maplen * 64) by lia.
rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.
Lemma bits_maplen_bytes last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
maplen < 2^52 -> Z.land (bits_enc last sc maplen) (2^64 - 4096) = maplen * 4096.
Proof.
intros Hl Hs Hm.
intros. pose proof (bits_nonneg last sc maplen Hl Hs Hm). pose proof (bits_lt64 last sc maplen Hl Hs Hm ltac:(lia)).
replace (2^64 - 4096) with (2^64 - 2^12) by reflexivity.
rewrite land_neg_pow2_u64 by lia. change (2^12) with 4096.
rewrite (bits_mod4096 last sc maplen Hl Hs Hm). unfold bits_enc. lia.
Qed.





Definition install_bits_machine (b0 sc last : Z) : Z :=
let s0 := Z.shiftr (sll64 sc 58) 52 in
let a0 := Z.land b0 (2^64 - 4096) in
let a1 := Z.lor s0 last in
let a0 := Z.lor a1 a0 in
add64 a0 32.

Definition direct_bits_machine (n : Z) : Z :=
let a0 := 4064 in
let a1 := add64 n a0 in
let a1 := add64 a1 51 in
let a1 := Z.land a1 (2^64 - 2048) in
Z.lor a1 a0.
Lemma direct_bits_ok n : 0 <= n < 2^63 ->
direct_bits_machine n = bits_enc 0 63 (page_round (n + IB + UNIT) / PGSZ).
Proof.
intros Hn. unfold direct_bits_machine, bits_enc, page_round, IB, UNIT, PGSZ.
rewrite (add64_small n 4064) by lia. rewrite add64_small by lia. change 2048 with (2^11) at 1. rewrite land_neg_pow2_u64 by lia.
replace (n + 4 + 16 + 4096 - 1) with (n + 4115) by lia. replace (n + 4064 + 51) with (n + 4115) by lia.
rewrite Z.div_mul by lia.
set (x := n + 4115).
pose proof (Z.div_mod x 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as M.
pose proof (Z.mod_pos_bound x (2^11) ltac:(lia)) as M2.
set (q := x / 4096) in *. set (t := (x / 2^11) mod 2).
assert (Ht : 0 <= t < 2) by (subst t; apply Z.mod_pos_bound; lia).
assert (E : x - x mod 2^11 = 2^11 * t + 2^12 * q).
{ subst t. rewrite (Z.div_mod x (2^11)) at 1 by lia.
rewrite (Z.div_mod (x / 2^11) 2) at 1 by lia.
rewrite Z.div_div by lia. change (2^11 * 2) with 4096. fold q. lia. }
rewrite E.
transitivity (Z.lor (Z.lor (2^11 * t) (2^12 * q)) 4064).
{ f_equal. symmetry. apply lor_add_high; lia. }
rewrite (Z.lor_comm (2^11 * t)), <- Z.lor_assoc.
assert (L : Z.lor (2^11 * t) 4064 = 4064).
{ assert (t = 0 \/ t = 1) as [->| ->] by lia; reflexivity. }
rewrite L. rewrite lor_add_high'; [lia|lia|]. subst q. apply Z.div_pos; lia.
Qed.
Definition g12_bits_machine (b0 needed : Z) : Z :=
let a3 := Z.land needed (2^64 - 4096) in
let a2 := Z.shiftr (sll64 b0 52) 52 in
Z.lor a2 a3.








Definition needed_machine (x : Z) : Z :=
let a4 := 2^64 - 16 in
let a6 := sub64 a4 x in
let a4 := add64 4096 (2^64 - 1) in
let a6 := Z.land a6 a4 in
let a5 := add64 x a6 in
add64 a5 16.

Definition rq_machine (req : Z) : Z :=
let a3 := 2^64 - 20 in
let a3 := sub64 a3 req in
let a3 := Z.land 4095 a3 in
let a3 := add64 req a3 in
add64 a3 20.


Definition mprotect_args_machine (addr len : Z) : Z * Z :=
let a1 := add64 addr len in
let a4 := neg64 4096 in
let a1 := add64 a1 4096 in
let a0 := Z.land a4 addr in
let a1 := add64 a1 (2^64 - 1) in
let a1 := Z.land a1 a4 in
let a1 := sub64 a1 a0 in
(a0, a1).


Definition enframe_slack_machine (stride n : Z) : Z :=
let t0 := sub64 stride n in
let t0 := add64 t0 (2^64 - 4) in
Z.shiftr t0 4.
Definition enframe_off_machine (stride n b : Z) : Z :=
let t0 := sub64 stride n in
let t0 := add64 t0 (2^64 - 4) in
let t1 := Z.shiftr t0 4 in
let a7 := Z.land b 255 in
if a7 <=? t1 then a7
else
let a3 := Z.shiftr t0 5 in
let a3 := Z.lor t1 a3 in
let t0 := Z.shiftr a3 2 in
let a3 := Z.lor t0 a3 in
let t0 := Z.shiftr a3 4 in
let a3 := Z.lor t0 a3 in
let a3 := Z.land a7 a3 in
let a7 := sltu t1 a3 in
let t0 := not64 t1 in
let a7 := negw a7 in
let a7 := Z.land a7 t0 in
addw a7 a3.




Lemma enframe_off_bytes off : 0 <= off < 256 -> sllw off 4 = UNIT * off.
Proof.
intros. unfold sllw, UNIT. change (4 mod 32) with 4. rewrite Z.shiftl_mul_pow2 by lia.
rewrite sx32_small; lia.
Qed.


Lemma enframe_end_minus_reserved e r : 0 < r < 2^31 -> r <= e < 2^64 ->
add64 e (negw r) = e - r /\ add64 e (negw (sx32 r)) = e - r.
Proof.
intros Hr He. rewrite negw_sx32. unfold negw. rewrite sx32_neg_small by lia.
rewrite add64_neg_imm by lia. auto.
Qed.
Definition s64 (x : Z) : Z := if x <? 2^63 then x else x - 2^64.
Lemma s64_small x : 0 <= x < 2^63 -> s64 x = x.
Proof. intros. unfold s64. destruct (x <? 2^63) eqn:E; [reflexivity|apply Z.ltb_ge in E; lia]. Qed.


Lemma enframe_hdr3 idx code : 0 <= idx < 32 -> 0 <= code < 8 ->
Z.lor (sll64 code 5) (Z.land idx 31) = idx + 32 * code /\ 0 <= idx + 32 * code < 256.
Proof.
intros Hi Hc. rewrite sll64_small by lia. change 31 with (Z.ones 5). rewrite Z.land_ones, Z.mod_small by lia.
change (2^5) with 32. replace (code * 32) with (2^5 * code) by lia.
rewrite lor_add_high' by lia. lia.
Qed.
Lemma rsv_code_range am fr : 0 <= stride_of am - IB - UNIT * fr_off fr - fr_n fr -> 0 <= rsv_code am fr <= 5.
Proof.
intros H. unfold rsv_code. destruct (5 <=? _) eqn:E; [lia|]. apply Z.leb_gt in E. lia.
Qed.

Section f.
Variables idx code : Z.
Hypothesis Hi : 0 <= idx < 32.
Hypothesis Hc : 0 <= code < 8.
Let h := idx + 32 * code.





End f.




Definition aidx_machine (cnt q : Z) : Z :=
let a2 := if cnt <? q then cnt else q in
let a1 := add64 a2 (2^64 - 1) in
let a2 := sltu a2 a1 in
let a2 := add64 a2 (2^64 - 1) in
Z.land a2 a1.
Lemma aidx_machine_ok cnt q : 0 <= cnt < 2^63 -> 0 <= q < 2^63 ->
aidx_machine cnt q =
(let a0 := q - 1 in let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in if a1 <? 0 then 0 else a1).
Proof.
intros Hc Hq. unfold aidx_machine. cbn zeta.
set (m := if cnt <? q then cnt else q).
assert (Hm : 0 <= m < 2^63 /\ (if cnt - 1 <? q - 1 then cnt - 1 else q - 1) = m - 1).
{ subst m. destruct (cnt <? q) eqn:E1, (cnt - 1 <? q - 1) eqn:E2;
first [apply Z.ltb_lt in E1|apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2|apply Z.ltb_ge in E2]; lia. }
destruct Hm as [Hm E]. rewrite E. clearbody m.
destruct (Z.eq_dec m 0) as [->|Hne].
- change (add64 0 (2^64 - 1)) with (2^64 - 1). unfold sltu.
replace (0 <? 2^64 - 1) with true by reflexivity. rewrite add64_neg_imm by lia.
rewrite Z.land_0_l. reflexivity.
- rewrite (add64_neg_imm m 1) by lia. unfold sltu.
replace (m <? m - 1) with false by (symmetry; apply Z.ltb_ge; lia).
change (add64 0 (2^64 - 1)) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia.
replace (m - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Definition divu64 (a b : Z) : Z := if b =? 0 then 2^64 - 1 else a / b.
Lemma divu_4080 size : 0 < size -> divu64 4080 size = (4096 - UNIT) / size.
Proof. intros. unfold divu64, UNIT. replace (size =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.







Lemma lor1_even sc : 0 <= sc -> Z.even sc = true -> Z.lor sc 1 = sc + 1.
Proof.
intros Hs He. rewrite Z.even_spec in He. destruct He as [k ->].
change 1 with (2^0 * 1) at 1. rewrite Z.lor_comm.
replace (2 * k) with (2^1 * k) by lia. rewrite lor_add_high; [lia| |lia]. simpl. lia.
Qed.
Lemma land1_even sc : 0 <= sc -> (Z.land sc 1 =? 0) = Z.even sc.
Proof.
intros. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
rewrite Zeven_mod. reflexivity.
Qed.






Lemma size_overflow_test n : 0 <= n < 2^62 -> (n <? 2^63 - 4097) = true /\ size_overflows n = false.
Proof.
intros. split; [apply Z.ltb_lt; lia|]. unfold size_overflows. apply Z.leb_gt. lia.
Qed.

