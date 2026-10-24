(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0a.
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
Lemma bits_div32 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
(bits_enc last sc maplen) / 32 = 1 + 2 * sc + 128 * maplen.
Proof.
intros Hl Hs Hm.
unfold bits_enc. symmetry. apply Z.div_unique with (r := last); lia.
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
Lemma bits_land32 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.land (bits_enc last sc maplen) 32 = 32.
Proof.
intros Hl Hs Hm.
change 32 with (2^5 * Z.ones 1) at 1. rewrite land_field by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. rewrite (bits_div32 last sc maplen Hl Hs Hm).
replace (1 + 2 * sc + 128 * maplen) with (1 + (sc + 64 * maplen) * 2) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
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
Lemma bits_sc_lw last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.shiftr (sll64 (sx32 (bits_enc last sc maplen)) 52) 58 = sc.
Proof.
intros Hl Hs Hm.
transitivity (Z.shiftr (sll64 (bits_enc last sc maplen) 52) 58); [|apply (bits_sc last sc maplen Hl Hs Hm)].
unfold sll64. rewrite !Z.shiftl_mul_pow2 by lia. f_equal.
change (2^64) with (2^12 * 2^52). rewrite !Z.mul_mod_distr_r by lia. f_equal.
rewrite <- (Z.mod_mod_divide (sx32 (bits_enc last sc maplen)) (2^32) (2^12)) by (exists (2^20); reflexivity).
rewrite sx32_mod32. apply Z.mod_mod_divide. exists (2^20); reflexivity.
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
Lemma bits_maplen_bytes' last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.land (bits_enc last sc maplen) (-4096) = maplen * 4096.
Proof.
intros Hl Hs Hm. change (-4096) with (- 2^12). rewrite land_neg_pow2 by lia. change (2^12) with 4096.
rewrite (bits_mod4096 last sc maplen Hl Hs Hm). unfold bits_enc. lia.
Qed.
Lemma bits_stride_mapped last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
0 < maplen < 2^52 ->
add64 (Z.land (bits_enc last sc maplen) (2^64 - 4096)) (2^64 - 16) = maplen * 4096 - UNIT.
Proof.
intros Hl Hs Hm. intros. rewrite bits_maplen_bytes by lia. unfold UNIT. rewrite add64_neg_imm; lia. Qed.
Lemma bits_low12 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.shiftr (sll64 (bits_enc last sc maplen) 52) 52 = bits_enc last sc 0.
Proof.
intros Hl Hs Hm.
unfold sll64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^64) with (4096 * 2^52). rewrite Z.mul_mod_distr_r, Z.div_mul by lia.
apply (bits_mod4096 last sc maplen Hl Hs Hm).
Qed.
Lemma bits_sc_ge48 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
Z.land (bits_enc last sc maplen) 3072 = 3072 <-> 48 <= sc.
Proof.
intros Hl Hs Hm.
change 3072 with (2^10 * Z.ones 2) at 1. rewrite land_field by lia.
rewrite Z.shiftr_div_pow2 by lia.
assert (E : bits_enc last sc maplen / 2^10 = sc / 16 + 4 * maplen).
{ unfold bits_enc. change (2^10) with 1024. symmetry.
pose proof (Z.mod_pos_bound sc 16 ltac:(lia)). pose proof (Z.div_mod sc 16 ltac:(lia)).
apply Z.div_unique with (r := last + 32 + 64 * (sc mod 16)); lia. }
rewrite E. replace (sc / 16 + 4 * maplen) with (sc / 16 + maplen * (2^2)) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
change (Z.ones 2) with 3. change (2^10) with 1024. split; intros H.
- assert (sc / 16 = 3) by lia. assert (16 * 3 <= sc) by (rewrite <- H0; apply Z.mul_div_le; lia). lia.
- replace (sc / 16) with 3; [reflexivity|]. apply Z.div_unique with (r := sc - 48); lia.
Qed.
Lemma maplen_units_m1 last sc maplen :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen ->
0 < maplen < 2^52 -> add64 (sll64 maplen 8) (2^64 - 1) = maplen * 4096 / UNIT - 1.
Proof.
intros Hl Hs Hm.
intros. rewrite sll64_small by lia. unfold UNIT. rewrite add64_neg_imm by lia.
replace (maplen * 4096) with ((maplen * 2^8) * 16) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Definition install_bits_machine (b0 sc last : Z) : Z :=
let s0 := Z.shiftr (sll64 sc 58) 52 in
let a0 := Z.land b0 (2^64 - 4096) in
let a1 := Z.lor s0 last in
let a0 := Z.lor a1 a0 in
add64 a0 32.
Lemma install_bits_ok b0 sc last : 0 <= b0 < 2^64 -> 0 <= sc < 64 -> 0 <= last < 32 ->
install_bits_machine b0 sc last = bits_enc last sc (Z.shiftr b0 12).
Proof.
intros Hb Hs Hl. unfold install_bits_machine, bits_enc.
rewrite sll64_small by lia. rewrite !Z.shiftr_div_pow2 by lia.
replace (sc * 2^58 / 2^52) with (2^6 * sc).
2:{ replace (2^58) with (2^6 * 2^52) by reflexivity. rewrite Z.mul_assoc, Z.div_mul by lia. lia. }
replace (2^64 - 4096) with (2^64 - 2^12) by reflexivity. rewrite land_neg_pow2_u64 by lia.
rewrite lor_add_high' by lia.
pose proof (Z.div_mod b0 (2^12) ltac:(lia)). pose proof (Z.mod_pos_bound b0 (2^12) ltac:(lia)).
replace (b0 - b0 mod 2^12) with (2^12 * (b0 / 2^12)) by lia.
rewrite lor_add_high by (first [lia | split; [lia|]; change (2^12) with (64 * 2^6); lia]).
assert (b0 / 2^12 < 2^52) by (apply Z.div_lt_upper_bound; lia).
rewrite add64_small by lia. change (2^12) with 4096. change (2^6) with 64. lia.
Qed.
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
Lemma g12_bits_ok last sc m0 needed :
0 <= last < 32 -> 0 <= sc < 64 -> 0 <= m0 -> 0 <= needed < 2^64 -> needed mod PGSZ = 0 ->
g12_bits_machine (bits_enc last sc m0) needed = bits_enc last sc (needed / PGSZ).
Proof.
intros Hl Hs Hm Hn Hp. unfold g12_bits_machine, PGSZ in *.
rewrite bits_low12 by lia. replace (2^64 - 4096) with (2^64 - 2^12) by reflexivity.
rewrite land_neg_pow2_u64 by lia.
change (2^12) with 4096. rewrite Hp, Z.sub_0_r.
pose proof (Z.div_mod needed 4096 ltac:(lia)). rewrite Hp in H.
replace needed with (2^12 * (needed / 4096)) at 1 by lia.
unfold bits_enc. rewrite lor_add_high; [lia|lia|apply Z.div_pos; lia].
Qed.
Lemma n4_bits_ok last sc m0 : 0 <= last < 32 -> 0 <= sc < 64 -> 0 <= m0 ->
Z.shiftr (sll64 (bits_enc last sc m0) 52) 52 = bits_enc last sc 0.
Proof. intros. apply bits_low12; lia. Qed.
Lemma page_round_eq x : page_round x = (x + 4095) / 4096 * 4096.
Proof. unfold page_round, PGSZ. replace (x + 4096 - 1) with (x + 4095) by lia. reflexivity. Qed.
Lemma page_round_char x y : y mod PGSZ = 0 -> x <= y < x + PGSZ -> y = page_round x.
Proof.
intros Hy Hr. pose proof (page_round_ge x). pose proof (page_round_lt x). pose proof (page_round_mod x).
unfold PGSZ in *.
pose proof (Z.div_mod y 4096 ltac:(lia)). pose proof (Z.div_mod (page_round x) 4096 ltac:(lia)).
assert (y / 4096 = page_round x / 4096) by lia. lia.
Qed.
Lemma mod_4096_of_64 x : (x mod 2^64) mod 4096 = x mod 4096.
Proof. apply Z.mod_mod_divide. exists (2^52). reflexivity. Qed.
Lemma land_neg_4095 x : Z.land (neg64 x) 4095 = (- x) mod 4096.
Proof.
unfold neg64. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply mod_4096_of_64.
Qed.
Lemma add_neg_mod x : 0 <= x -> x + (- x) mod 4096 = page_round x.
Proof.
intros Hx. apply page_round_char.
- unfold PGSZ. rewrite Zplus_mod, Z.mod_mod, <- Zplus_mod by lia. replace (x + - x) with 0 by lia. reflexivity.
- unfold PGSZ. pose proof (Z.mod_pos_bound (- x) 4096 ltac:(lia)). lia.
Qed.
Lemma brk_round_ok r : 0 <= r < 2^64 - PGSZ ->
add64 (Z.land 4095 (neg64 r)) r = page_round r.
Proof.
intros Hr. rewrite Z.land_comm, land_neg_4095. unfold PGSZ in *.
pose proof (Z.mod_pos_bound (- r) 4096 ltac:(lia)).
rewrite add64_small by lia. rewrite Z.add_comm. apply add_neg_mod. lia.
Qed.
Definition needed_machine (x : Z) : Z :=
let a4 := 2^64 - 16 in
let a6 := sub64 a4 x in
let a4 := add64 4096 (2^64 - 1) in
let a6 := Z.land a6 a4 in
let a5 := add64 x a6 in
add64 a5 16.
Lemma needed_machine_ok x : 0 <= x < 2^62 -> needed_machine x = page_round (x + UNIT).
Proof.
intros Hx. unfold needed_machine, UNIT.
rewrite (add64_neg_imm 4096 1) by lia. change (4096 - 1) with 4095.
unfold sub64. replace (2^64 - 16 - x) with (- (x + 16) + 1 * 2^64) by lia. rewrite Z.mod_add by lia.
fold (neg64 (x + 16)). rewrite land_neg_4095.
pose proof (Z.mod_pos_bound (- (x + 16)) 4096 ltac:(lia)).
rewrite (add64_small x) by lia. rewrite add64_small by lia. rewrite <- add_neg_mod by lia. lia.
Qed.
Definition rq_machine (req : Z) : Z :=
let a3 := 2^64 - 20 in
let a3 := sub64 a3 req in
let a3 := Z.land 4095 a3 in
let a3 := add64 req a3 in
add64 a3 20.
Lemma rq_machine_ok req : 0 <= req < 2^62 -> rq_machine req = page_round (req + IB + UNIT).
Proof.
intros Hr. unfold rq_machine, IB, UNIT.
unfold sub64. replace (2^64 - 20 - req) with (- (req + 20) + 1 * 2^64) by lia. rewrite Z.mod_add by lia.
fold (neg64 (req + 20)). rewrite Z.land_comm, land_neg_4095.
pose proof (Z.mod_pos_bound (- (req + 20)) 4096 ltac:(lia)).
rewrite (add64_small req) by lia. rewrite add64_small by lia. replace (req + 4 + 16) with (req + 20) by lia. rewrite <- add_neg_mod by lia. lia.
Qed.
Lemma land_round_up x : 0 <= x < 2^64 - 4096 -> Z.land (x + 4095) (2^64 - 4096) = page_round x.
Proof.
intros Hx. replace (2^64 - 4096) with (2^64 - 2^12) by reflexivity.
rewrite land_neg_pow2_u64 by lia. change (2^12) with 4096.
rewrite page_round_eq. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). lia.
Qed.
Definition mprotect_args_machine (addr len : Z) : Z * Z :=
let a1 := add64 addr len in
let a4 := neg64 4096 in
let a1 := add64 a1 4096 in
let a0 := Z.land a4 addr in
let a1 := add64 a1 (2^64 - 1) in
let a1 := Z.land a1 a4 in
let a1 := sub64 a1 a0 in
(a0, a1).
Lemma mprotect_args_ok addr len : 0 <= addr -> 0 <= len -> addr + len < 2^64 - 8192 ->
mprotect_args_machine addr len = (addr - addr mod PGSZ, page_round (addr + len) - (addr - addr mod PGSZ)).
Proof.
intros Ha Hl Hs. unfold mprotect_args_machine, PGSZ.
rewrite (neg64_eq 4096) by lia.
rewrite !(Z.land_comm (2^64 - 4096)).
rewrite (add64_small addr len), (add64_small (addr + len) 4096) by lia.
rewrite add64_neg_imm by lia. replace (addr + len + 4096 - 1) with (addr + len + 4095) by lia.
rewrite land_round_up by lia.
replace (2^64 - 4096) with (2^64 - 2^12) by reflexivity. rewrite land_neg_pow2_u64 by lia. change (2^12) with 4096.
pose proof (Z.mod_pos_bound addr 4096 ltac:(lia)).
pose proof (page_round_ge (addr + len)). pose proof (page_round_lt (addr + len)). unfold PGSZ in *.
rewrite sub64_small by lia. reflexivity.
Qed.
Lemma mprotect_args_aligned addr : 0 <= addr -> addr mod PGSZ = 0 -> addr < 2^64 - 3 * 4096 ->
mprotect_args_machine addr 4096 = (addr, 4096).
Proof.
intros Ha Hm Hs. rewrite mprotect_args_ok by lia. rewrite Hm, Z.sub_0_r.
rewrite (page_round_fixed (addr + 4096)); [f_equal; lia|].
unfold PGSZ in *. rewrite Zplus_mod, Hm. reflexivity.
Qed.
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
Lemma enframe_slack_ok stride n : 0 <= n -> n + IB <= stride -> stride < 2^63 ->
enframe_slack_machine stride n = (stride - IB - n) / UNIT.
Proof.
intros Hn Hs Hb. unfold enframe_slack_machine, IB, UNIT in *.
rewrite sub64_small, add64_neg_imm, Z.shiftr_div_pow2 by lia. change (2^4) with 16. f_equal. lia.
Qed.
Theorem enframe_off_ok stride n b : 0 <= n -> n + IB <= stride -> stride < 2^35 -> 0 <= b ->
enframe_off_machine stride n b = fold_off ((stride - IB - n) / UNIT) (Z.land b 255) /\
0 <= enframe_off_machine stride n b <= (stride - IB - n) / UNIT.
Proof.
intros Hn Hs Hb Hb0.
assert (Hoff0 : 0 <= Z.land b 255 < 256) by (change 256 with (2^8); apply land_range_r; lia).
unfold IB, UNIT in *.
assert (Hsl : 0 <= (stride - 4 - n) / 16 < 2^31).
{ split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
pose proof (fold_off_ok ((stride - 4 - n) / 16) (Z.land b 255) ltac:(lia) ltac:(lia)) as Hf.
cut (enframe_off_machine stride n b = fold_off ((stride - 4 - n) / 16) (Z.land b 255)); [intros E; rewrite E; auto|].
unfold enframe_off_machine, fold_off.
rewrite sub64_small, add64_neg_imm by lia. replace (stride - n - 4) with (stride - 4 - n) by lia.
set (t0 := stride - 4 - n) in *. set (off0 := Z.land b 255) in *.
replace (Z.shiftr t0 5) with (Z.shiftr (Z.shiftr t0 4) 1) by (rewrite Z.shiftr_shiftr by lia; reflexivity).
replace (Z.shiftr t0 4) with (t0 / 16) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
set (slack := t0 / 16) in *.
destruct (off0 <=? slack) eqn:E1.
- apply Z.leb_le in E1. replace (slack <? off0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- apply Z.leb_gt in E1. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia).
cbn zeta.
set (m1 := Z.lor slack (Z.shiftr slack 1)).
rewrite (Z.lor_comm (Z.shiftr m1 2) m1). set (m2 := Z.lor m1 (Z.shiftr m1 2)).
rewrite (Z.lor_comm (Z.shiftr m2 4) m2). set (m3 := Z.lor m2 (Z.shiftr m2 4)).
set (off1 := Z.land off0 m3).
assert (Hm : 0 <= m3) by (subst m3 m2 m1; repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; try lia;
repeat (apply Z.lor_nonneg; split); repeat apply Z.shiftr_nonneg; try lia;
apply Z.lor_nonneg; split; [lia|apply Z.shiftr_nonneg; lia]).
assert (Ho1 : 0 <= off1 <= off0).
{ subst off1. split; [apply Z.land_nonneg; lia|].
apply zland_le_l; lia. }
rewrite not64_eq by lia.
unfold sltu. destruct (slack <? off1) eqn:E2.
+ apply Z.ltb_lt in E2. unfold negw. rewrite (sx32_neg_small 1) by lia.
change (2^64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
change (Z.ones 64) with (2^64 - 1). rewrite Z.mod_small by lia.
unfold addw. rewrite (sx32_congr _ (off1 - (slack + 1))).
* apply sx32_small. lia.
* replace (2^64 - 1 - slack + off1) with ((off1 - (slack + 1)) + 2^32 * 2^32) by lia.
rewrite Z.mod_add by lia. reflexivity.
+ apply Z.ltb_ge in E2. unfold negw. change (sx32 (- 0)) with 0. rewrite Z.land_0_l.
unfold addw. rewrite Z.add_0_l. apply sx32_small. lia.
Qed.
Lemma enframe_off0_hdr h16 : 0 <= h16 -> Z.land (add64 h16 1) 255 = Z.land (h16 + 1) 255.
Proof.
intros. unfold add64. rewrite (land_small_r ((h16 + 1) mod 2^64)), (land_small_r (h16 + 1)) by lia.
rewrite mod64_mod32. reflexivity.
Qed.
Lemma enframe_off0_ctr c : Z.land (sx32 c) 255 = Z.land c 255.
Proof. apply land_255_sx32. Qed.
Lemma enframe_off_bytes off : 0 <= off < 256 -> sllw off 4 = UNIT * off.
Proof.
intros. unfold sllw, UNIT. change (4 mod 32) with 4. rewrite Z.shiftl_mul_pow2 by lia.
rewrite sx32_small; lia.
Qed.
Lemma enframe_hdr16 mem d : 0 <= mem -> UNIT <= d < 2^31 ->
Z.shiftr (add64 (subw (mem + d) mem) (2^64 - 16)) 4 = (d - UNIT) / UNIT.
Proof.
intros Hm Hd. unfold UNIT in *. rewrite subw_small by lia. replace (mem + d - mem) with d by lia.
rewrite add64_neg_imm, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma enframe_reserved e qn : 0 <= qn <= e -> e - qn < 2^31 -> subw e qn = e - qn.
Proof. intros. apply subw_small. lia. Qed.
Lemma enframe_end_minus_reserved e r : 0 < r < 2^31 -> r <= e < 2^64 ->
add64 e (negw r) = e - r /\ add64 e (negw (sx32 r)) = e - r.
Proof.
intros Hr He. rewrite negw_sx32. unfold negw. rewrite sx32_neg_small by lia.
rewrite add64_neg_imm by lia. auto.
Qed.
Definition s64 (x : Z) : Z := if x <? 2^63 then x else x - 2^64.
Lemma s64_small x : 0 <= x < 2^63 -> s64 x = x.
Proof. intros. unfold s64. destruct (x <? 2^63) eqn:E; [reflexivity|apply Z.ltb_ge in E; lia]. Qed.
Lemma s64_sx32_nonneg a : 0 <= a < 2^31 -> s64 (sx32 a) = a.
Proof. intros. rewrite sx32_small by lia. apply s64_small. lia. Qed.
Lemma s64_sx32_neg a : 0 < a <= 2^31 -> s64 (sx32 (- a)) = - a.
Proof.
intros. rewrite sx32_neg_small by lia. unfold s64.
destruct (2^64 - a <? 2^63) eqn:E; [apply Z.ltb_lt in E; lia|lia].
Qed.
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
Lemma hdr3_to_group idx code : 0 <= idx < 32 -> 0 <= code ->
Z.land (idx + 32 * code) 31 + 192 = idx + 192.
Proof.
intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
replace (idx + 32 * code) with (idx + code * 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.
Section f.
Variables idx code : Z.
Hypothesis Hi : 0 <= idx < 32.
Hypothesis Hc : 0 <= code < 8.
Let h := idx + 32 * code.
Lemma hdr3_idx : Z.land h 31 = idx.
Proof.
unfold h. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
replace (idx + 32 * code) with (idx + code * 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.
Lemma hdr3_code : Z.shiftr h 5 = code.
Proof.
unfold h. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
symmetry. apply Z.div_unique with (r := idx); lia.
Qed.
Lemma hdr3_lt160 : (h <? 160) = (code <? 5).
Proof.
unfold h. destruct (code <? 5) eqn:E.
- apply Z.ltb_lt in E. apply Z.ltb_lt. lia.
- apply Z.ltb_ge in E. apply Z.ltb_ge. lia.
Qed.
Lemma hdr3_range : 0 <= h < 256.
Proof. unfold h. lia. Qed.
Lemma hdr3_zero_iff : h = 0 <-> idx = 0 /\ code = 0.
Proof. unfold h. lia. Qed.
End f.
Lemma hdr3_freed_byte : (2^64 - 1) mod 256 = 255.
Proof. reflexivity. Qed.
Lemma hdr3_offset_marker : (2^64 - 32) mod 256 = 224 /\ Z.land 224 31 = 0 /\ Z.shiftr 224 5 = 7.
Proof. repeat split; reflexivity. Qed.
Lemma aidx_byte_write old v : 0 <= old < 256 -> 0 <= v ->
let nb := Z.lor (Z.land old 224) (Z.land v 31) in
0 <= nb < 256 /\ nb mod 32 = v mod 32 /\ Z.land nb 31 = v mod 32.
Proof.
intros Ho Hv. cbn zeta.
assert (E224 : Z.land old 224 = 2^5 * (Z.shiftr old 5 mod 2^3)).
{ change 224 with (2^5 * Z.ones 3). apply land_field; lia. }
rewrite E224, !land_31_mod.
pose proof (Z.mod_pos_bound (Z.shiftr old 5) (2^3) ltac:(lia)).
pose proof (Z.mod_pos_bound v 32 ltac:(lia)).
rewrite lor_add_high' by (change (2^5) with 32; lia).
change (2^5) with 32.
rewrite (Z.mul_comm 32), Z.mod_add, Z.mod_mod by lia.
change (2^3) with 8 in *. repeat split; lia.
Qed.
Lemma aidx_byte_read byte aidx : 0 <= byte -> byte mod 32 = aidx -> sllw 2 byte = sx32 (2 ^ (aidx + 1)).
Proof. intros Hb E. rewrite sllw_2, E by lia. reflexivity. Qed.
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
Lemma g3_cnt half x : subw 2 (sltu half x) = (if x <=? half then 2 else 1).
Proof.
unfold sltu. destruct (half <? x) eqn:E1, (x <=? half) eqn:E2;
first [apply Z.ltb_lt in E1|apply Z.ltb_ge in E1]; first [apply Z.leb_le in E2|apply Z.leb_gt in E2];
try lia; reflexivity.
Qed.
Lemma add64_negimm_cases x c : 0 <= x < 2^64 -> 0 < c < 2^64 ->
add64 x (2^64 - c) = (if c <=? x then x - c else x - c + 2^64).
Proof.
intros Hx Hc. unfold add64. destruct (c <=? x) eqn:E.
- apply Z.leb_le in E. replace (x + (2^64 - c)) with ((x - c) + 1 * 2^64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
- apply Z.leb_gt in E. rewrite Z.mod_small by lia. lia.
Qed.
Lemma range_test64 x c d : 0 <= x < 2^64 -> 0 < c -> 0 <= d -> c + d < 2^64 ->
(add64 x (2^64 - c) <=? d) = (c <=? x) && (x <=? c + d).
Proof.
intros. rewrite add64_negimm_cases by lia.
destruct (c <=? x) eqn:E1; [apply Z.leb_le in E1|apply Z.leb_gt in E1]; cbn.
- destruct (x <=? c + d) eqn:E2; [apply Z.leb_le in E2; apply Z.leb_le|apply Z.leb_gt in E2; apply Z.leb_gt]; lia.
- apply Z.leb_gt. lia.
Qed.
Lemma addw_negimm_cases x c : 0 <= x < 2^31 -> 0 < c <= 2^31 ->
addw x (- c) = (if c <=? x then x - c else x - c + 2^64).
Proof.
intros Hx Hc. unfold addw. destruct (c <=? x) eqn:E.
- apply Z.leb_le in E. apply sx32_small. lia.
- apply Z.leb_gt in E. replace (x + - c) with (- (c - x)) by lia. rewrite sx32_neg_small by lia. lia.
Qed.
Lemma range_test32 x c d : 0 <= x < 2^31 -> 0 < c <= 2^31 -> 0 <= d -> c + d < 2^63 ->
(addw x (- c) <=? d) = (c <=? x) && (x <=? c + d).
Proof.
intros. rewrite addw_negimm_cases by lia.
destruct (c <=? x) eqn:E1; [apply Z.leb_le in E1|apply Z.leb_gt in E1]; cbn.
- destruct (x <=? c + d) eqn:E2; [apply Z.leb_le in E2; apply Z.leb_le|apply Z.leb_gt in E2; apply Z.leb_gt]; lia.
- apply Z.leb_gt. lia.
Qed.
Lemma addw_imm_u32 x c : addw x (2^32 - c) = addw x (- c).
Proof. apply addw_congr; [reflexivity|]. replace (2^32 - c) with (- c + 1 * 2^32) by lia. apply Z.mod_add. lia. Qed.
Lemma addw_imm_u64 x c : addw x (2^64 - c) = addw x (- c).
Proof. apply addw_congr; [reflexivity|]. replace (2^64 - c) with (- c + 2^32 * 2^32) by lia. apply Z.mod_add. lia. Qed.
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
Lemma fg_usage_sub u b : 0 <= b < 2^64 -> Z.land b 31 + 1 <= u < 2^64 ->
add64 u (Z.lor (not64 b) (2^64 - 32)) = u - (Z.land b 31 + 1).
Proof.
intros Hb Hu.
assert (E : Z.lor (not64 b) (2^64 - 32) = 2^64 - 1 - Z.land b 31).
{ rewrite not64_eq by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
assert (H31 : 0 <= Z.land b 31 < 32) by (change 32 with (2^5); apply land_range_r; lia).
replace (2^64 - 1 - b) with (Z.lnot b mod 2^64) by (rewrite <- not64_eq by lia; reflexivity).
replace (2^64 - 1 - Z.land b 31) with (Z.lnot (Z.land b 31) mod 2^64).
2:{ unfold Z.lnot. replace (Z.pred (- Z.land b 31)) with ((2^64 - 1 - Z.land b 31) + (-1) * 2^64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
replace (2^64 - 32) with ((- (2^5)) mod 2^64) by reflexivity.
rewrite !testbit_mod_pow2 by lia. destruct (i <? 64) eqn:E64; [|reflexivity].
rewrite !Z.lnot_spec, Z.land_spec by lia.
replace (- 2^5) with (Z.lnot (Z.ones 5)) by reflexivity. rewrite Z.lnot_spec, Z.testbit_ones by lia.
change 31 with (Z.ones 5). rewrite Z.testbit_ones by lia.
replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn.
destruct (i <? 5); cbn; [rewrite orb_false_r|rewrite orb_true_r];
[rewrite andb_true_r | rewrite andb_false_r]; reflexivity. }
rewrite E. unfold add64. replace (u + (2^64 - 1 - Z.land b 31)) with ((u - (Z.land b 31 + 1)) + 1 * 2^64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small.
assert (0 <= Z.land b 31) by (apply Z.land_nonneg; lia). lia.
Qed.
Lemma fg_usage_sub_bits u last sc maplen : 0 <= last < 32 -> 0 <= sc < 64 -> 0 <= maplen < 2^52 ->
last + 1 <= u < 2^64 ->
add64 u (Z.lor (not64 (bits_enc last sc maplen)) (2^64 - 32)) = u - (last + 1).
Proof.
intros. pose proof (bits_land31 last sc maplen ltac:(lia) ltac:(lia) ltac:(lia)) as E.
rewrite fg_usage_sub; rewrite ?E; try lia. unfold bits_enc. lia.
Qed.
Lemma byte_diff_signed a b : 0 <= a < 256 -> 0 <= b < 256 -> s64 (sub64 a b) = a - b.
Proof.
intros Ha Hb. unfold sub64. destruct (Z_le_gt_dec b a).
- rewrite Z.mod_small by lia. apply s64_small. lia.
- replace ((a - b) mod 2^64) with (a - b + 2^64).
2:{ symmetry. replace (a - b) with ((a - b + 2^64) + (-1) * 2^64) at 1 by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
unfold s64. destruct (a - b + 2^64 <? 2^63) eqn:E; [apply Z.ltb_lt in E; lia|lia].
Qed.
Lemma nosmall_flag b : Z.lxor (sltu b 100) 1 = (if 100 <=? b then 1 else 0).
Proof.
unfold sltu. destruct (b <? 100) eqn:E1, (100 <=? b) eqn:E2;
first [apply Z.ltb_lt in E1|apply Z.ltb_ge in E1]; first [apply Z.leb_le in E2|apply Z.leb_gt in E2];
try lia; reflexivity.
Qed.
Lemma mulhu_zero_iff a b : 0 <= a < 2^64 -> 0 <= b < 2^64 ->
(Z.shiftr (a * b) 64 = 0 <-> a * b < 2^64).
Proof.
intros Ha Hb. rewrite Z.shiftr_div_pow2 by lia. split.
- intros E. destruct (Z_lt_le_dec (a * b) (2^64)); [lia|].
assert (1 <= a * b / 2^64) by (apply Z.div_le_lower_bound; lia). lia.
- intros. apply Z.div_small. lia.
Qed.
Lemma size_overflow_const : Z.shiftr (sx32 (0xffffe000 - 1)) 1 = 2^63 - 4097.
Proof. reflexivity. Qed.
Lemma size_overflow_test n : 0 <= n < 2^62 -> (n <? 2^63 - 4097) = true /\ size_overflows n = false.
Proof.
intros. split; [apply Z.ltb_lt; lia|]. unfold size_overflows. apply Z.leb_gt. lia.
Qed.
Lemma mmap_threshold_const : addw 0x20000 (-20) = MMAP_THRESHOLD.
Proof. reflexivity. Qed.
