(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep F_malloc_free.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma swrap_word x : Z_to_bv 64 (bv_swrap 32 x) = wz (sxv x).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.
#[using="Type"] Lemma sxv_testbit_lo' v i : 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
intros. Local Ltac2 Set LiaHints.tbl := fun () => "0010=15378538415.4000003S1H".
rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. apply Z.mod_pow2_bits_low. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_cases' v : let u := v mod 2^32 in
(u < 2^31 /\ sxv v = u) \/ (2^31 <= u /\ sxv v = u + 2^64 - 2^32).
Proof.
cbv zeta. Local Ltac2 Set LiaHints.tbl := fun () => "0030=32538436502.338717875063.342465062063.2000003004005S1HSS".
pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
rewrite <- (sxv_congr (v mod 2^32) v) by (apply Z.mod_mod; lia).
destruct (sxv_cases (v mod 2^32) ltac:(lia)); tauto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma testbit_31_mod32 v : Z.testbit v 31 = (2^31 <=? v mod 2^32).
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=36911047484.242465062063.258294783518.47227581400.2 000001002008009SSS1H2H0S".
rewrite <- (Z.mod_pow2_bits_low v 32 31) by lia. rewrite Z.testbit_eqb by lia.
pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
destruct (Z.leb_spec (2^31) (v mod 2^32)).
- replace (v mod 2^32 / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
- rewrite Z.div_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_testbit_hi v i : 31 <= i < 64 -> Z.testbit (sxv v) i = Z.testbit v 31.
Proof.
intros Hi. rewrite testbit_31_mod32. Local Ltac2 Set LiaHints.tbl := fun () => "00B0>10351595562.4 10354097908.6 17068999465.6 23511125814.1139539021036.1241415987093.4 41416041292.8 41417957581.5 42334719592.1242464293982.1151096881380.5 5226247455.7  54752808891.1259497544542.4 60192684857.8 60194781503.7 63887539878.119213669597.6  00000400800<00G00H00I00J00K00L00M00Q00R00V00Z00^00b00f00gS2HiS2HiS2HiS2Hi3P312HuSSSSSSS2HiSS2HuS2HiS2HiS2HiS2HuS".
rewrite Z.testbit_eqb by lia.
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_testbit_high v i : 64 <= i -> Z.testbit (sxv v) i = false.
Proof.
intros. pose proof (sxv_range v). destruct (Z.eq_dec (sxv v) 0) as [->|]. apply Z.bits_0.
Local Ltac2 Set LiaHints.tbl := fun () => "0030=12713706643.619457651979.660358684254.600000400700=S2H0S1HS2H01n".
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_land a b : Z.land (sxv a) (sxv b) = sxv (Z.land a b).
Proof.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
destruct (Z.lt_ge_cases i 32); [| destruct (Z.lt_ge_cases i 64)].
- Local Ltac2 Set LiaHints.tbl := fun () => "0030=19456170581.72860235939.7 63043746671.600000400:00@S2H0S1H2H0S2Hi1H".
rewrite !sxv_testbit_lo' by lia. symmetry. apply Z.land_spec.
- rewrite !sxv_testbit_hi by lia. rewrite Z.land_spec. reflexivity.
- rewrite !sxv_testbit_high by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_idem v : sxv (sxv v) = sxv v.
Proof. apply sxv_congr. apply sxv_mod32. Qed.
#[using="Type"] Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
Local Ltac2 Set LiaHints.tbl := fun () => "0060=15045740034.520845743302.52424960062.4 3251038285.4 3429368897.5 65704169587.500000100500900:00;00BSS2n0S2HnSSS2Hn2n0".
rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
destruct (Z.eq_dec n 0) as [->|].
- rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
- replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. Local Ltac2 Set LiaHints.tbl := fun () => "0030=3429368897.5 42868082462.465704169587.5000001002009SSS2Hn2n0".
replace (- (2 * a)) with (2 * (- a)) by lia.
destruct (Z.eq_dec n 0) as [->|].
- rewrite !Z.testbit_even_0. reflexivity.
- replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
intros m Hm.
pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
cbv beta in G. Local Ltac2 Set LiaHints.tbl := fun () => "0070=10360761986.526983596513.536224421892.448852849032.951796758275.965170181345.56757948034.9 00000400800<00B00F00J00KS2HxS2HxS2HmS2Hk1LS2HkS2HxS".
apply G; [|lia|lia]. clear G m Hm.
intros x IH Hx0 Hx.
destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
- destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
- exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
intros Hk. apply Z.bits_inj'. intros n Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0020=2424960062.5 51794599521.5000004008S2HnS2Hk".
rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.
#[using="Type"] Lemma lowbit_0 : lowbit 0 = 0.
Proof. reflexivity. Qed.
#[using="Type"] Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. Local Ltac2 Set LiaHints.tbl := fun () => "0010=51796692231.3000003S1H".
rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
rewrite <- Zminus_mod_idemp_r, sxv_mod32, Zminus_mod_idemp_r. Local Ltac2 Set LiaHints.tbl := fun () => "0010=11335764043.3000001S".
replace (0 - v) with (- v) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le4_avail_sub a b : 0 <= b <= a -> a < 2^32 ->
le4 (wz (sxv (sxv a - sxv b))) = le4 (wz (a - b)).
Proof.
intros. apply le4_congr. Local Ltac2 Set LiaHints.tbl := fun () => "0010<7219655166.5000006S1H2H0".
rewrite !wz_unsigned by (first [apply sxv_range | lia]).
rewrite sxv_mod32, <- Zminus_mod_idemp_r, sxv_mod32, <- Zminus_mod_idemp_l, sxv_mod32, Zminus_mod_idemp_l, Zminus_mod_idemp_r.
reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
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
end.
Section CANSEC2. Context {rc : runConstT}.
End CANSEC2.
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
end.
