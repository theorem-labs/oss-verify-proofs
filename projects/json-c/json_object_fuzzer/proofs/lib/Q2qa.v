(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 QZAa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Export QZAa.
Import ListNotations.
Local Open Scope Z_scope.
Import Q6q3.

Definition mul_core_entry := 0x118b8%Z.
Definition mul_core_mid_pc := 0x11a6c%Z.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_2 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_3 := zsimp_fast.

Ltac model_reg_tac n X mexpr ::=
let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
first [ constr_eq e mexpr
| replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
by (first [ zeq_special e mexpr
| f_equal; zeq_fast
| rewrite Z_to_bv_land64; f_equal; zeq_fast
| apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq_fast
| idtac "note: model_reg" X ": slow path for" e; fail
| f_equal; zeq
| apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
| apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
name_as_tac X mexpr
| _ => fail "model_reg: register" n "holds" w
end. Ltac mkr__model_reg_tac_4 n X mexpr := let w := getreg n in
lazymatch w with
| Z_to_bv 64 ?e =>
first [ constr_eq e mexpr
| replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
by (first [ zeq_special e mexpr
| f_equal; zeq_fast
| rewrite Z_to_bv_land64; f_equal; zeq_fast
| apply Z_to_bv_eqm; rewrite ?Z.mod_mod by lia; zeq_fast
| idtac "note: model_reg" X ": slow path for" e; fail
| f_equal; zeq
| apply Z_to_bv_eqm; slim; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia
| apply Z_to_bv_eqm; zb_masks; pose_word_ranges; Z.div_mod_to_equations; lia ]) ];
name_as_tac X mexpr
| _ => fail "model_reg: register" n "holds" w
end.

Ltac sf_vocab :=
cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI];
rewrite ?b2z_Zb2z. Ltac mkr__sf_vocab_5 := cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
is_neg64 sra63 lt_s64 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI];
rewrite ?b2z_Zb2z.

Ltac fold_head_let :=
lazymatch goal with
| |- (let x := ?b in ?c) = ?r =>
match goal with
| H := ?b' : Z |- _ =>
constr_eq b b';
let c' := eval cbv beta in ((fun x : Z => c) H) in
change ((let x := b in c) = r) with (c' = r)
end
end.
Ltac fold_model_lets := repeat fold_head_let.

Definition MC_tail (signHi expSum hi_hi hi_lo lo_hi lo_lo scale : Z) : Z :=
let scaleAdj := scale - 0x3fff in
let productExponent := expSum + scaleAdj in
if is_neg64 (shl64 hi_hi 15) then
let productExponent1 := productExponent + 1 in
if negb (productExponent1 <? 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
else mul_finish signHi productExponent1 hi_hi hi_lo lo_hi lo_lo
else
let hi_hi1 := Z.lor (shl64 hi_hi 1) (shr64 hi_lo 63) in
let hi_lo1 := Z.lor (shl64 hi_lo 1) (shr64 lo_hi 63) in
let lo_hi1 := Z.lor (shl64 lo_hi 1) (shr64 lo_lo 63) in
let lo_lo1 := shl64 lo_lo 1 in
if 0x7fff <=? productExponent then mk128 (Z.lor signHi INF_HI) 0
else mul_finish signHi productExponent hi_hi1 hi_lo1 lo_hi1 lo_lo1.

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
Import QnDM_c1.Mq0.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition AGP : Z := 0x1a800.

Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.

#[using="Type"] Lemma sxv_range v : 0 <= sxv v < 2^64.
Proof. unfold sxv. apply Z.mod_pos_bound. lia. Qed.

#[using="Type"] Lemma swrap32_eq' z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.
End RC__1.

Ltac pow_lits :=
change (2^64)%Z with 18446744073709551616%Z in *;
change (2^63)%Z with 9223372036854775808%Z in *;
change (2^33)%Z with 8589934592%Z in *;
change (2^32)%Z with 4294967296%Z in *;
change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma sxv_small v : 0 <= v < 2^31 -> sxv v = v.
Proof. intros. unfold sxv. rewrite swrap32_eq'. rewrite (Z.mod_small (v + 2^31)) by lia. rewrite Z.mod_small by lia. lia. Qed.

#[using="Type"] Lemma mod64_mod32 z : (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. apply mod_mod_pow2. lia. Qed.

#[using="Type"] Lemma sxv_mod32 v : (sxv v) mod 2^32 = v mod 2^32.
Proof. unfold sxv. rewrite mod64_mod32, swrap32_eq'. mlia. Qed.

#[using="Type"] Lemma sx32_wz_sxv v : 0 <= v < 2^64 -> sx32 (wz v) = wz (sxv v).
Proof. intros. unfold sx32, sxv. rewrite wz_unsigned by lia. unfold wz. rewrite Z_to_bv_mod64. reflexivity. Qed.

#[using="Type"] Lemma sextw_sxv v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)) + 0)) = wz (sxv v).
Proof.
rewrite wz_unsigned by (apply sxv_range). rewrite Z.add_0_r. unfold wz, sxv.
rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 v mod 2^64))). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.
#[using="Type"] Lemma sextw_sxv' v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)))) = wz (sxv v).
Proof. rewrite <- (Z.add_0_r (bv_unsigned _)). apply sextw_sxv. Qed.

#[using="Type"] Lemma self_word b3 : 0 <= b3 < 256 ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 b3))) 31)) mod 32)))
= wz (sxv (2 ^ (Z.land b3 31))).
Proof.
intros. rewrite zxb_b8, (wz_unsigned b3) by lia.
assert (0 <= Z.land b3 31 < 32).
{ split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

#[using="Type"] Lemma all_word mword : 0 <= mword ->
Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (mword mod 32)))) + -1))
= wz (sxv (2 ^ (mword mod 32 + 1) - 1)).
Proof.
intros. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
replace (2 * 2 ^ (mword mod 32)) with (2 ^ (mword mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
set (y := 2 ^ (mword mod 32 + 1)). rewrite !swrap32_eq'. mlia.
Qed.

#[using="Type"] Lemma lor_range64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof. intros. apply (zr_lor a b); unfold inr64; lia. Qed.

#[using="Type"] Lemma land_range64 a b : 0 <= a < 2^64 -> 0 <= b -> 0 <= Z.land a b < 2^64.
Proof. intros. apply (zr_land_l a b); unfold inr64; lia. Qed.

#[using="Type"] Lemma sxv_testbit_lo v i : 0 <= v < 2^32 -> 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

#[using="Type"] Lemma sxv_cases v : 0 <= v < 2^32 -> (v < 2^31 /\ sxv v = v) \/ (2^31 <= v /\ sxv v = v + 2^64 - 2^32).
Proof.
intros. unfold sxv. rewrite swrap32_eq'.
destruct (Z.lt_ge_cases v (2^31)); [left|right]; split; auto; pow_lits; Z.div_mod_to_equations; nia.
Qed.

#[using="Type"] Lemma free_assert_ok freed avail idx :
0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx < 32 ->
Z.testbit freed idx = false -> Z.testbit avail idx = false ->
Z.land (sxv (2^idx)) (Z.lor (sxv freed) (sxv avail)) = 0.
Proof.
intros HF HA HI TF TA.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 64).
2:{ rewrite (Z.bits_above_log2 (sxv (2^idx))); [reflexivity| apply sxv_range |].
pose proof (sxv_range (2^idx)). destruct (Z.eq_dec (sxv (2^idx)) 0) as [->|]. cbn; lia.
apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia]. }
destruct (Z.lt_ge_cases idx 31).
- rewrite (sxv_small (2^idx)) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
rewrite Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec idx n); [|reflexivity]. subst n. cbn.
rewrite !sxv_testbit_lo by lia. rewrite TF, TA. reflexivity.
- assert (idx = 31) by lia. subst idx.

assert (Hlt : forall v, 0 <= v < 2^32 -> Z.testbit v 31 = false -> v < 2^31).
{ intros v Hv Hb. destruct (Z.lt_ge_cases v (2^31)); auto.
exfalso. assert (Z.testbit v 31 = true); [|congruence].
rewrite Z.testbit_true by lia. replace (v / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity. }
pose proof (Hlt freed HF TF). pose proof (Hlt avail HA TA).
rewrite (sxv_small freed), (sxv_small avail) by lia.
destruct (Z.lt_ge_cases n 31).
+ replace (Z.testbit (sxv (2^31)) n) with false; [reflexivity|].
symmetry. rewrite sxv_testbit_lo by lia. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
+ assert (Lg : forall v, 0 <= v < 2^31 -> Z.testbit v n = false).
{ intros v Hv. destruct (Z.eq_dec v 0) as [->|]. apply Z.bits_0.
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 31); [apply Z.log2_lt_pow2; lia| lia]. }
rewrite (Lg freed), (Lg avail) by lia. apply andb_false_r.
Qed.

#[using="Type"] Lemma sxv_zero v : 0 <= v < 2^32 -> sxv v = 0 <-> v = 0.
Proof. intros. destruct (sxv_cases v H) as [[? ->]|[? ->]]; lia. Qed.

#[using="Type"] Lemma add_bit_nocarry v idx : 0 <= v < 2^32 -> 0 <= idx < 32 -> Z.testbit v idx = false ->
v + 2^idx < 2^32.
Proof.
intros Hv Hi Hb.
assert (HL : Z.land v (2^idx) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec idx n); [subst; rewrite Hb; reflexivity | apply andb_false_r]. }
rewrite (Z.add_nocarry_lxor _ _ HL).
assert (0 <= 2^idx < 2^32) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
apply Z_bounded_by_bits; [lia | apply Z.lxor_nonneg; lia |].
intros k Hk. rewrite Z.lxor_spec, (Z_testbit_high 32 v k), (Z_testbit_high 32 (2^idx) k) by lia. reflexivity.
Qed.

#[using="Type"] Lemma sxv_congr v w : v mod 2^32 = w mod 2^32 -> sxv v = sxv w.
Proof. intros E. unfold sxv. rewrite !swrap32_eq'. f_equal. f_equal. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l. reflexivity. Qed.

#[using="Type"] Lemma lor_sxv_mod32 f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
(Z.lor (sxv f) (sxv a)) mod 2^32 = Z.lor f a.
Proof.
intros. rewrite <- zb_land_mask, zb_land_lor_distr_l, !zb_land_mask, !sxv_mod32, !Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma addw_word x y : Z_to_bv 64 (bv_swrap 32 (x + y)) = wz (sxv (x + y)).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

#[using="Type"] Lemma wz_inj a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> wz a = wz b -> a = b.
Proof. intros Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !wz_unsigned in E by lia. exact E. Qed.

#[using="Type"] Lemma sxv_eq_iff v w : sxv v = sxv w <-> v mod 2^32 = w mod 2^32.
Proof. split; [| apply sxv_congr]. intros E. rewrite <- (sxv_mod32 v), <- (sxv_mod32 w), E. reflexivity. Qed.

#[using="Type"] Lemma free_all_test freed avail idx li :
0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx <= li -> li < 32 ->
(sxv (sxv (2^idx) + Z.lor (sxv freed) (sxv avail)) = sxv (2^(li + 1) - 1)
<-> Z.lor freed avail + 2^idx = 2^(li+1) - 1).
Proof.
intros HF HA HI HL. rewrite sxv_eq_iff.
rewrite <- Zplus_mod_idemp_r, lor_sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32 by lia.
assert (X1 : 0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
assert (XY : 2^idx < 2^(li+1)) by (apply Z.pow_lt_mono_r; lia).
assert (Y32 : 2^(li+1) <= 2^32) by (apply Z.pow_le_mono_r; lia).
pose proof (Z_lor_range freed avail ltac:(lia) ltac:(lia)).
assert (HLr : Z.lor freed avail < 2^32).
{ apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |]. intros k Hk.
rewrite Z.lor_spec, (Z_testbit_high 32 freed k), (Z_testbit_high 32 avail k) by lia. reflexivity. }
set (X := 2^idx) in *. set (Y := 2^(li+1)) in *. set (L := Z.lor freed avail) in *.
clearbody X Y L. rewrite (Z.mod_small X) by lia. mlia.
Qed.

#[using="Type"] Lemma le4_congr (a b : word) : bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> le4 a = le4 b.
Proof. intros E. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia). rewrite E. reflexivity. Qed.

#[using="Type"] Lemma free_store_val freed idx : 0 <= freed < 2^32 -> 0 <= idx < 32 -> Z.testbit freed idx = false ->
le4 (wz (sxv (sxv (2^idx) + sxv freed))) = le4 (wz (freed + 2^idx)).
Proof.
intros. pose proof (add_bit_nocarry freed idx ltac:(lia) ltac:(lia) ltac:(assumption)).
assert (0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
rewrite sxv_mod32, <- Zplus_mod_idemp_r, sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32, !Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma self_word' b3 : 0 <= b3 < 256 ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land b3 31)) mod 32)))
= wz (sxv (2 ^ (Z.land b3 31))).
Proof.
intros.
assert (0 <= Z.land b3 31 < 32).
{ split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

#[using="Type"] Lemma sllw2_word e : 0 <= e ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (e mod 32))) = wz (sxv (2 ^ (e mod 32 + 1))).
Proof.
intros. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
replace (2 * 2 ^ (e mod 32)) with (2 ^ (e mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

#[using="Type"] Lemma addiw_m1_word y : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv y)) + -1)) = wz (sxv (y - 1)).
Proof.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. mlia.
Qed.

#[using="Type"] Lemma rw_cells_congr segs m A cs cs' :
cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. intros EB ES WF [[_ B] W]. split; [split; [exact WF| rewrite <- EB; exact B] | rewrite <- ES; exact W]. Qed.

#[using="Type"] Lemma le1_neg1 : le1 (Z_to_bv 64 (-1)) = [b8 255].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.
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
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

Definition frozen (P : Prop) : Prop := P.

Definition free_W (sp : word) (P G : Z) : list (Z * Z) :=
[(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.
End RC__3.

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
Section RC__4. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma wr_at_sub : forall segs m A n A' n',
wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
intros segs m A n A' n' (H0 & H1 & H) LA LB. split; [lia|]. split; [lia|].
intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.

#[using="Type"] Lemma rw_cells_prefix : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1.
Proof.
intros segs m A cs1 cs2 [[WF B] W].
apply cells_wf_app in WF. destruct WF as [WF1 WF2].
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 _].
split; [split; [exact WF1 | exact B1] |].
rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

#[using="Type"] Lemma bytes_at_at : forall segs m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

#[using="Type"] Lemma rw_cells_of_bytes : forall segs m A cs,
cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros. split; [split|]; assumption. Qed.

#[using="Type"] Lemma area_of_slot : forall (a : aptr) k, snd a mod 4096 = 0 -> 0 <= k < 101 ->
area_of (aadd a (24 + 40 * k)) = a.
Proof.
intros [ar ao] k Hm Hk. unfold area_of, aadd. cbn [fst snd] in *. f_equal.
replace (ao + (24 + 40 * k)) with ((24 + 40 * k) + (ao / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add, Z.mod_small by lia. Z.div_mod_to_equations; nia.
Qed.

#[using="Type"] Lemma page_off_mod : forall b o x, b mod 4096 = 0 -> o mod 4096 = 0 -> 0 <= x < 4096 -> (b + o + x) mod 4096 = x.
Proof.
intros b o x Hb Ho Hx.
replace (b + o + x) with (x + (b / 4096 + o / 4096) * 4096) by (Z.div_mod_to_equations; nia).
rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma base16_mod : forall b po, b mod 4096 = 0 -> po mod 16 = 0 -> (b + po) mod 16 = 0.
Proof.
intros b po Hb Hp. replace (b + po) with ((b / 4096) * 256 * 16 + (po / 16) * 16) by (Z.div_mod_to_equations; lia).
rewrite <- Z.mul_add_distr_r, Z.mod_mul. reflexivity. lia.
Qed.

Definition freeW (sp : word) (P G : Z) : list (Z * Z) :=
[(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.

#[using="Type"] Lemma rd8_known {R} st q v (k : Z -> M R) :
cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma rd16_known {R} st q v0 v1 (k : Z -> M R) :
cell_read (get_shadow st (fst q)) (snd q) = Known v0 ->
cell_read (get_shadow st (fst q)) (snd q + 1) = Known v1 ->
rd16 st q k = k (v0 + 256 * v1).
Proof. intros H0 H1. unfold rd16, rd8. rewrite H0. cbn [fst snd aadd]. rewrite H1. reflexivity. Qed.

#[using="Type"] Lemma get_meta_rec_wr8 st q v g : get_meta_rec (wr8 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_wr16 st q v g : get_meta_rec (wr16 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.

#[using="Type"] Lemma optr_eqb_refl : forall q : aptr, optr_eqb (Some q) (Some q) = true.
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma free_trivial_model : forall st (p : aptr) g gh ar (b3 lo hi : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo + 256 * hi in
let idx := Z.land b3 31 in
let base := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) (wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)) in
let reserved := Z.shiftr b3 5 in
let e := aadd (slot_start' mr idx) (get_stride mr - IB) in
po mod 16 = 0 ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base = Some gh -> g_meta gh = Some g ->
m_mem mr = Some base ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr -> 0 <= m_freed mr -> 0 <= b3 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 4096 / UNIT - 1) ->

reserved < 5 -> reserved <= snd e - po ->
cell_read sh (snd e - reserved) = Known 0 -> cell_read sh (snd e) = Known 0 ->

m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
free st (Some p) = ret st'.
Proof.
intros until hi. intros sh po off16 idx base mr st' reserved e AL C4 C3 C2 C1 Hgh Hg Hmem Har Hchk AV FR B3
Hidx Hav Hfr Hsc Hsc63 Hml RES5 RESe E1 E0 Hfz Hall.
unfold free, free_hdr, get_meta, guard. fold po. rewrite (proj2 (Z.eqb_eq _ _) AL).
rewrite (rd16_known st (aadd p (-2)) lo hi) by (cbn [fst snd aadd]; fold po; first [replace (po + -2) with (po - 2) by lia; exact C2 | replace (po + -2 + 1) with (po - 1) by lia; exact C1]).
cbv beta.
rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
cbv beta.
rewrite (rd8_known st (aadd p (-4)) 0) by (cbn [fst snd aadd]; fold po; replace (po + -4) with (po - 4) by lia; exact C4).
cbv beta. cbn [Z.eqb negb].
fold off16. fold base. unfold get_group. rewrite Hgh, Hg. fold mr. rewrite Hmem, optr_eqb_refl.
fold idx. replace (idx <=? m_last_idx mr) with true by (symmetry; apply Z.leb_le; lia).
unfold testbit. rewrite Hav, Hfr. cbn [negb].
rewrite Har, Hchk, Z.eqb_refl.
match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 16)) _] =>
replace (if c then x else y) with true end.
2:{ destruct (Z.ltb_spec (m_sizeclass mr) 48).
- specialize (Hsc ltac:(lia)). symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- specialize (Hsc63 ltac:(lia)). symmetry. apply Z.eqb_eq. lia. }
match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 17)) _] =>
replace (if c then x else y) with true end.
2:{ destruct (Z.eqb_spec (m_maplen mr) 0); cbn [negb]; [reflexivity|]. symmetry. apply Z.leb_le. apply Hml. assumption. }
unfold slot_start. rewrite Hmem.
assert (He : aadd (aadd base (UNIT + get_stride mr * idx)) (get_stride mr - IB) = e) by (unfold e, slot_start'; rewrite Hmem; reflexivity).
rewrite He.
assert (Fe : fst e = fst p) by (rewrite <- He; reflexivity).
unfold get_nominal_size.
rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
cbv beta. fold reserved.
replace (5 <=? reserved) with false by (symmetry; apply Z.leb_gt; lia).
fold po. replace (reserved <=? snd e - po) with true by (symmetry; apply Z.leb_le; lia).
rewrite (rd8_known st (aadd e (- reserved)) 0) by (cbn [fst snd aadd]; rewrite Fe; fold sh; replace (snd e + - reserved) with (snd e - reserved) by lia; exact E1).
cbv beta. cbn [Z.eqb].
rewrite (rd8_known st e 0) by (rewrite Fe; exact E0).
unfold guard. cbn [Z.eqb]. unfold QUZl.ret at 1. rewrite sbind_ret_l.
unfold free_tail, guard. rewrite !get_meta_rec_wr16, !get_meta_rec_wr8. fold mr.
unfold testbit. rewrite Z.lor_spec, Hfr, Hav. cbn [orb negb].
replace (m_freed mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfz).
replace (Z.lor (m_freed mr) (m_avail mr) + bit idx =? mask_upto (m_last_idx mr)) with false by (symmetry; apply Z.eqb_neq; exact Hall).
cbn [orb negb]. reflexivity.
Qed.

End RC__4.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Local Open Scope Z_scope.

Import QZAa.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Definition clz64_mirror_entry := 0x10688%Z.
Definition clz128_mirror_entry := 0x10cfc%Z.
Definition norm_denormal_entry := 0x10c10%Z.
Definition mul_round_entry := 0x10cb0%Z.

End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QnDM_c1.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Local Open Scope Z_scope.

Strategy expand [wrap64 lo64 hi64 add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 is_neg64 lt_s64 sra63 zext32 b2z
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K HALF60 DQUIET].
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Definition add_M8 (SHi SLo aExp signHi : Z) : Z :=
let '(SHi, SLo, aExp) :=
if negb (lt_s64 0 aExp)
then (let '(SHi, SLo) := denorm_mirror SHi SLo aExp in (SHi, SLo, 0))
else (SHi, SLo, aExp) in
round_mirror SHi SLo aExp signHi.

Definition add_M7 (xHi SHi SLo aExp : Z) : Z :=
let signHi := shl64 (shr64 xHi 63) 63 in
if negb (lt_s64 aExp 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
else add_M8 SHi SLo aExp signHi.

Definition add_M6 (xHi subtraction AHi ALo BHi BLo aExp : Z) : Z :=
match addsub_mirror subtraction AHi ALo BHi BLo aExp with
| None => mk128 0 0
| Some (SHi, SLo, aExp) => add_M7 xHi SHi SLo aExp
end.

Definition addsub_sub (AHi ALo BHi BLo aExp : Z) : option (Z * Z * Z) :=
if Z.eqb (Z.lor (Z.lxor ALo BLo) (Z.lxor AHi BHi)) 0 then None
else
let borrow := b2z (Z.ltb ALo BLo) in
let SHi := sub64 (sub64 AHi BHi) borrow in
let SLo := sub64 ALo BLo in
if Z.eqb (shr64 SHi 51) 0 then
let clzS := clz128_mirror SHi SLo in
let shiftS := sub64 clzS 12 in
let '(SHi, SLo) := shl128_mirror SHi SLo shiftS in
let aExp := sub64 aExp shiftS in
Some (SHi, SLo, aExp)
else Some (SHi, SLo, aExp).
Definition addsub_add (AHi ALo BHi BLo aExp : Z) : option (Z * Z * Z) :=
let SLo := add64 BLo ALo in
let carry := b2z (Z.ltb SLo BLo) in
let SHi := add64 (add64 BHi AHi) carry in
if is_neg64 (shl64 SHi 11) then
let st := Z.land BLo 1 in
let SLo := Z.lor (Z.lor (shr64 SLo 1) st) (shl64 SHi 63) in
let SHi := shr64 SHi 1 in
let aExp := add64 aExp 1 in
Some (SHi, SLo, aExp)
else Some (SHi, SLo, aExp).
Definition add_M6s (xHi AHi ALo BHi BLo aExp : Z) : Z :=
match addsub_sub AHi ALo BHi BLo aExp with
| None => mk128 0 0
| Some (SHi, SLo, aExp) => add_M7 xHi SHi SLo aExp
end.
Definition add_M6a (xHi AHi ALo BHi BLo aExp : Z) : Z :=
match addsub_add AHi ALo BHi BLo aExp with
| None => mk128 0 0
| Some (SHi, SLo, aExp) => add_M7 xHi SHi SLo aExp
end.

Definition add_M4 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp : Z) : Z :=
let subtraction := shr64 (Z.lxor bHi aHi) 63 in
let aSigHi3 := Z.lor (shl64 aSigHi 3) (shr64 aSigLo 61) in
let bSigHi3 := Z.lor (shl64 bSigHi 3) (Z.lor (shr64 bSigLo 61) IMPL3_HI) in
let bSigLo3 := shl64 bSigLo 3 in
let AHi := Z.lor aSigHi3 IMPL3_HI in
let ALo := shl64 aSigLo 3 in
let '(BHi, BLo) := align_mirror aExp bExp bSigHi3 bSigLo3 in
add_M6 xHi subtraction AHi ALo BHi BLo aExp.

Definition add_M3b (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp : Z) : Z :=
let '(bSigHi, bSigLo, bExp) :=
if Z.eqb bExp 0 then normalize_mirror bSigHi bSigLo else (bSigHi, bSigLo, bExp) in
add_M4 aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp.

Definition add_M2 (aHi bHi xLo xHi yLo yHi : Z) : Z :=
let aExp := shr64 (shl64 xHi 1) 49 in
let bExp := shr64 (shl64 yHi 1) 49 in
let aSigHi := Z.land xHi MASK48 in
let aSigLo := xLo in
let bSigHi := Z.land yHi MASK48 in
let bSigLo := yLo in
let '(aSigHi, aSigLo, aExp) :=
if Z.eqb aExp 0 then normalize_mirror aSigHi aSigLo else (aSigHi, aSigLo, aExp) in
add_M3b aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp.

Definition add_M1 (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
let swap := if Z.eqb bAbsHi aAbsHi then Z.ltb aLo bLo else Z.ltb aAbsHi bAbsHi in
let '(yLo, yHi, xLo, xHi) := if swap then (aLo, aHi, bLo, bHi) else (bLo, bHi, aLo, aHi) in
add_M2 aHi bHi xLo xHi yLo yHi.

Strategy expand [addsub_sub addsub_add add_M6s add_M6a].

Lemma add_main_split : forall aLo aHi bLo bHi aAbsHi bAbsHi,
add_main aLo aHi bLo bHi aAbsHi bAbsHi = add_M1 aLo aHi bLo bHi aAbsHi bAbsHi.
Proof. intros. unfold add_M1, add_M2, add_M3b, add_M4, add_M6, add_M7, add_M8. reflexivity. Qed.

Definition add_S3 (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
if Z.eqb (Z.lor aLo (Z.lxor aAbsHi INF_HI)) 0 then
let x := Z.lor (Z.lxor bLo aLo) (Z.lxor (Z.lxor bHi aHi) SIGN64) in
let m := sub64 (b2z (Z.eqb x 0)) 1 in
let rhi := if negb (Z.eqb x 0) then aHi else QNAN_HI in
mk128 rhi (Z.land m aLo)
else if Z.eqb (Z.lor bLo (Z.lxor bAbsHi INF_HI)) 0 then mk128 bHi bLo
else if Z.eqb (Z.lor aLo aAbsHi) 0 then
(if negb (Z.eqb (Z.lor bLo bAbsHi) 0) then mk128 bHi bLo
else mk128 (Z.land bHi aHi) (Z.land bLo aLo))
else if negb (Z.eqb (Z.lor bLo bAbsHi) 0) then add_M1 aLo aHi bLo bHi aAbsHi bAbsHi
else mk128 aHi aLo.

Definition add_S2 (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
let bIsNaN := if Z.eqb bAbsHi INF_HI then negb (Z.eqb bLo 0) else negb (Z.ltb bAbsHi INF_HI) in
if bIsNaN then mk128 (Z.lor bHi QUIET_HI) bLo
else add_S3 aLo aHi bLo bHi aAbsHi bAbsHi.

Definition add_S (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
let aIsNaN := if Z.eqb aAbsHi INF_HI then negb (Z.eqb aLo 0) else negb (Z.ltb aAbsHi INF_HI) in
if aIsNaN then mk128 (Z.lor aHi QUIET_HI) aLo
else add_S2 aLo aHi bLo bHi aAbsHi bAbsHi.

Definition add_top2 (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
let tb := add64 bAbsHi SPEC_K in
let bSpecial := if Z.eqb tb SPEC_K then Z.eqb bLo 0 else negb (Z.ltb SPEC_K tb) in
if bSpecial then add_S aLo aHi bLo bHi aAbsHi bAbsHi
else add_M1 aLo aHi bLo bHi aAbsHi bAbsHi.

Definition add_top (aLo aHi bLo bHi : Z) : Z :=
let aAbsHi := Z.land aHi ABS_HI in
let bAbsHi := Z.land bHi ABS_HI in
let aSpecial := if Z.eqb aAbsHi 0 then Z.eqb aLo 0 else Z.ltb (add64 aAbsHi SPEC_K) SPEC_K in
let tb := add64 bAbsHi SPEC_K in
let bSpecial := if Z.eqb tb SPEC_K then Z.eqb bLo 0 else negb (Z.ltb SPEC_K tb) in
if aSpecial || bSpecial then add_S aLo aHi bLo bHi aAbsHi bAbsHi
else add_M1 aLo aHi bLo bHi aAbsHi bAbsHi.

Strategy expand [add_S3 add_S2 add_S add_top add_top2].

Lemma f128_add_split : forall aLo aHi bLo bHi,
(0 <= aLo < 2^64)%Z -> (0 <= aHi < 2^64)%Z -> (0 <= bLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
f128_add (aLo + 2^64 * aHi) (bLo + 2^64 * bHi) = add_top aLo aHi bLo bHi.
Proof.
intros. unfold f128_add. rewrite !lo64_words, !hi64_words by assumption.
unfold add_top, add_S, add_S2, add_S3. rewrite add_main_split. reflexivity.
Qed.

Definition clz128_w (word hz : Z) : Z := Z.lor (clz64_mirror word) (Z.shiftl hz 6).
Strategy expand [clz128_w].
Lemma clz128_mirror_w : forall hi lo,
clz128_mirror hi lo = clz128_w (if hi =? 0 then lo else hi) (b2z (hi =? 0)).
Proof. intros. unfold clz128_w. reflexivity. Qed.

Definition norm_w2 (hi lo word hz : Z) : Z * Z * Z :=
let clz := clz128_w word hz in
let sh := sub64 clz 15 in
let '(h, l) := shl128_mirror hi lo sh in
(h, l, sub64 16 clz).
Strategy expand [norm_w2].
Lemma normalize_mirror_w : forall hi lo,
normalize_mirror hi lo = norm_w2 hi lo (if hi =? 0 then lo else hi) (b2z (hi =? 0)).
Proof. intros. unfold norm_w2, clz128_w. reflexivity. Qed.

Definition shl128_lo (lo s mask : Z) : Z := Z.land mask (shl64 lo (Z.land s 63)).

Definition normA3 (aHi bHi xHi aSigLo yHi yLo bExp clz sh mask nhi : Z) : Z :=
add_M3b aHi bHi xHi nhi (shl128_lo aSigLo sh mask) (sub64 16 clz) (Z.land yHi MASK48) yLo bExp.

Definition normB3 (aHi bHi xHi aSigHi aSigLo aExp bSigLo clz sh mask nhi : Z) : Z :=
add_M4 aHi bHi xHi aSigHi aSigLo aExp nhi (shl128_lo bSigLo sh mask) (sub64 16 clz).

Definition align_4 (xHi subtraction AHi ALo aExp bSigHi3 align mask2 sticky newLo : Z) : Z :=
let newHi := Z.land mask2 (shr64 bSigHi3 (Z.land align 63)) in
add_M6 xHi subtraction AHi ALo newHi (Z.lor newLo sticky) aExp.
Definition align_3 (xHi subtraction AHi ALo aExp bSigHi3 bSigLo3 align mask1 negal outHi : Z) : Z :=
let outLoRaw := shl64 bSigLo3 (Z.land negal 63) in
let outLo := Z.land mask1 outLoRaw in
let n2 := zext32 align in
let sticky := b2z (negb (Z.eqb (Z.lor outLo outHi) 0)) in
let d2 := sub64 n2 64 in
let newLo := if is_neg64 d2
then Z.lor (shr64 bSigLo3 (Z.land align 63)) (shl64 (shl64 bSigHi3 1) (Z.land (not64 n2) 63))
else shr64 bSigHi3 (Z.land n2 63) in
align_4 xHi subtraction AHi ALo aExp bSigHi3 align (sra63 d2) sticky newLo.

Definition subR2 (xHi SHi SLo aExp word hz : Z) : Z :=
let clzS := clz128_w word hz in
let shiftS := sub64 clzS 12 in
let '(SHi', SLo') := shl128_mirror SHi SLo shiftS in
add_M7 xHi SHi' SLo' (sub64 aExp shiftS).
Definition subR3 (xHi SLo aExp shiftS mask nhi : Z) : Z :=
add_M7 xHi nhi (shl128_lo SLo shiftS mask) (sub64 aExp shiftS).

Definition denorm_3 (signHi hiSh mask4 sticky newLo : Z) : Z :=
round_mirror (Z.land mask4 hiSh) (Z.lor newLo sticky) 0 signHi.
Definition denorm_2 (signHi SHi SLo shift mask3 t outHi : Z) : Z :=
let outLo := Z.land mask3 t in
let hiSh := shr64 SHi (Z.land shift 63) in
let n3 := zext32 shift in
let sticky := b2z (negb (Z.eqb (Z.lor outLo outHi) 0)) in
let d4 := sub64 n3 64 in
let mask4 := sra63 d4 in
let newLo := if is_neg64 d4
then Z.lor (shr64 SLo (Z.land shift 63)) (shl64 (shl64 SHi 1) (Z.land (not64 n3) 63))
else shr64 SHi (Z.land n3 63) in
denorm_3 signHi hiSh mask4 sticky newLo.

Definition round_2 (resHi resLo inc : Z) : Z :=
let sumLo := add64 resLo inc in
let resHi := add64 resHi (b2z (Z.ltb sumLo resLo)) in
mk128 resHi sumLo.

Strategy expand [shl128_lo normA3 normB3 align_4 align_3 subR2 subR3 denorm_3 denorm_2 round_2].
