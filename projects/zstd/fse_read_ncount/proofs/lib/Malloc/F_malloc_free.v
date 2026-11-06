(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.
#[using="Type"] Lemma sxv_range v : 0 <= sxv v < 2^64.
Proof. unfold sxv. apply Z.mod_pos_bound. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38955519663.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma swrap32_eq' z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.
End CANSEC1.
Ltac pow_lits :=
change (2^64)%Z with 18446744073709551616%Z in *;
change (2^63)%Z with 9223372036854775808%Z in *;
change (2^33)%Z with 8589934592%Z in *;
change (2^32)%Z with 4294967296%Z in *;
change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma sxv_small v : 0 <= v < 2^31 -> sxv v = v.
Proof. intros. unfold sxv. rewrite swrap32_eq'. Local Ltac2 Set LiaHints.tbl := fun () => "0030=29687186879.332538436502.38931307546.3 000001004007SS1HS1H".
rewrite (Z.mod_small (v + 2^31)) by lia. rewrite Z.mod_small by lia. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma mod64_mod32 z : (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. apply mod_mod_pow2. Local Ltac2 Set LiaHints.tbl := fun () => "0010<2587212961.2000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_mod32 v : (sxv v) mod 2^32 = v mod 2^32.
Proof. unfold sxv. rewrite mod64_mod32, swrap32_eq'. Local Ltac2 Set LiaHints.tbl := fun () => "0010>11447729963.2300000?S1H2H02H42H52H9".
mlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sx32_wz_sxv v : 0 <= v < 2^64 -> sx32 (wz v) = wz (sxv v).
Proof. intros. unfold sx32, sxv. Local Ltac2 Set LiaHints.tbl := fun () => "0010=29436288106.3000003S1H".
rewrite wz_unsigned by lia. unfold wz. rewrite Z_to_bv_mod64. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sextw_sxv v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)) + 0)) = wz (sxv v).
Proof.
rewrite wz_unsigned by (apply sxv_range). rewrite Z.add_0_r. unfold wz, sxv.
rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 v mod 2^64))). f_equal.
rewrite !swrap32_eq'. Local Ltac2 Set LiaHints.tbl := fun () => "0010>11447729958.3000000KS1H2H02H42H52H93H103H143H15".
mlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sextw_sxv' v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)))) = wz (sxv v).
Proof. rewrite <- (Z.add_0_r (bv_unsigned _)). apply sextw_sxv. Qed.
#[using="Type"] Lemma all_word mword : 0 <= mword ->
Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (mword mod 32)))) + -1))
= wz (sxv (2 ^ (mword mod 32 + 1) - 1)).
Proof.
intros. rewrite unsigned_lit_wrap. Local Ltac2 Set LiaHints.tbl := fun () => "0040>11447730085.4644021460374.3 54364220727.3 6758013062.3  00000[00\00]00^S1H2H02H12H52H63H103H113H153H163H203H253H26SSS".
rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
replace (2 * 2 ^ (mword mod 32)) with (2 ^ (mword mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
set (y := 2 ^ (mword mod 32 + 1)). rewrite !swrap32_eq'. mlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lor_range64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof. intros. apply (zr_lor a b); unfold inr64; lia. Qed.
#[using="Type"] Lemma land_range64 a b : 0 <= a < 2^64 -> 0 <= b -> 0 <= Z.land a b < 2^64.
Proof. intros. apply (zr_land_l a b); unfold inr64; lia. Qed.
#[using="Type"] Lemma sxv_testbit_lo v i : 0 <= v < 2^32 -> 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
intros. Local Ltac2 Set LiaHints.tbl := fun () => "0010=15380636567.5000004S2H0".
rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
pose proof (sxv_range (2^idx)). destruct (Z.eq_dec (sxv (2^idx)) 0) as [->|]. Local Ltac2 Set LiaHints.tbl := fun () => "00I0>10043560124.1910124650571.1914346836204.142424953696.13 27690590944.1527690651451.1729446485344.1431622984827.1731623043488.1534850472426.1335048969106.123818386347.16 38838253647.1440354531172.1340599905003.1241415991886.1347217125819.1653920096142.1654239824408.1967258640210.127224918174.13 7224918301.16 7224918555.16 8534516254.13 9538480250.13 00000400800;00>00E00L00P00W00^00b00f00j01101801<01=01>01E01L01P01Q01R01S01W01XS2H3S2HvS1HS1HS2HF2H1S2HF2H1S2H0S2HA2H2S2HA2H2S2H0S2HAS2H3S2H02n0S2HI2H0S2HISSS2Hn2H3S2Hv2n0S2HFSSSS2HIS".
cbn; lia.
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_zero v : 0 <= v < 2^32 -> sxv v = 0 <-> v = 0.
Proof. intros. destruct (sxv_cases v H) as [[? ->]|[? ->]]; lia. Qed.
#[using="Type"] Lemma add_bit_nocarry v idx : 0 <= v < 2^32 -> 0 <= idx < 32 -> Z.testbit v idx = false ->
v + 2^idx < 2^32.
Proof.
intros Hv Hi Hb.
assert (HL : Z.land v (2^idx) = 0).
{ apply Z.bits_inj'. intros n Hn. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>10364763902.101848940486.7  33610422243.1036557432975.1041415990386.7 41728505643.8 44015169426.7 44015173491.1044021460374.8 8534510912.8  9538475590.7  00000400800;00?00@00F00G00H00I00M00NS2HkS2HiS1HS2HvSS2Hv1HSSSS2HiS".
rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec idx n); [subst; rewrite Hb; reflexivity | apply andb_false_r]. }
rewrite (Z.add_nocarry_lxor _ _ HL).
assert (0 <= 2^idx < 2^32) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
apply Z_bounded_by_bits; [lia | apply Z.lxor_nonneg; lia |].
intros k Hk. rewrite Z.lxor_spec, (Z_testbit_high 32 v k), (Z_testbit_high 32 (2^idx) k) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sxv_congr v w : v mod 2^32 = w mod 2^32 -> sxv v = sxv w.
Proof. intros E. unfold sxv. rewrite !swrap32_eq'. f_equal. f_equal. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l. reflexivity. Qed.
#[using="Type"] Lemma lor_sxv_mod32 f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
(Z.lor (sxv f) (sxv a)) mod 2^32 = Z.lor f a.
Proof.
intros. rewrite <- zb_land_mask, zb_land_lor_distr_l, !zb_land_mask, !sxv_mod32, !Z.mod_small by lia. reflexivity.
Qed.
#[using="Type"] Lemma addw_word x y : Z_to_bv 64 (bv_swrap 32 (x + y)) = wz (sxv (x + y)).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.
#[using="Type"] Lemma sxv_eq_iff v w : sxv v = sxv w <-> v mod 2^32 = w mod 2^32.
Proof. split; [| apply sxv_congr]. intros E. rewrite <- (sxv_mod32 v), <- (sxv_mod32 w), E. reflexivity. Qed.
#[using="Type"] Lemma free_all_test freed avail idx li :
0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx <= li -> li < 32 ->
(sxv (sxv (2^idx) + Z.lor (sxv freed) (sxv avail)) = sxv (2^(li + 1) - 1)
<-> Z.lor freed avail + 2^idx = 2^(li+1) - 1).
Proof.
intros HF HA HI HL. rewrite sxv_eq_iff.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0>10364763902.1527663336653.1134760710487.1335048975790.9 35048979791.1541415727077.1141415990386.9 42166184720.1243789627561.1043962928877.1044015173491.1544021460374.1348708655088.175650071504.12 67258632591.1567258636654.9 7562033986.31 8534514722.9  9538742777.10 00000400800?00C00G00H00I00M00Q00U00V00W00b00f00j00n01K01O01PS2HkS2HLS2HF2HAS2HAS2HASSS2HAS2HIS2HISSS2X12XY3Y32S2HFS2HFS2HFS2X12XY3Y321H3HLr2H02H12H52H6S2HIS".
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le4_congr (a b : word) : bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> le4 a = le4 b.
Proof. intros E. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia). rewrite E. reflexivity. Qed.
#[using="Type"] Lemma free_store_val freed idx : 0 <= freed < 2^32 -> 0 <= idx < 32 -> Z.testbit freed idx = false ->
le4 (wz (sxv (sxv (2^idx) + sxv freed))) = le4 (wz (freed + 2^idx)).
Proof.
intros. Local Ltac2 Set LiaHints.tbl := fun () => "00:0=16039846055.829876706355.833610431419.836991546931.840599905128.641415992140.75420484291.8 67258639831.867258640081.68534516508.7 00000<00E00N00W00[00\00]00`00c00gS1H2H02H22H3S1H2H22H3S1H2H22H3S1H2H22H3S2H0SSS1HS1HS2H0".
pose proof (add_bit_nocarry freed idx ltac:(lia) ltac:(lia) ltac:(assumption)).
assert (0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
rewrite sxv_mod32, <- Zplus_mod_idemp_r, sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32, !Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma sllw2_word e : 0 <= e ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (e mod 32))) = wz (sxv (2 ^ (e mod 32 + 1))).
Proof.
intros. Local Ltac2 Set LiaHints.tbl := fun () => "0030=44021460374.354364220727.36758013062.3 000001002003SSS".
rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
replace (2 * 2 ^ (e mod 32)) with (2 ^ (e mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma addiw_m1_word y : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv y)) + -1)) = wz (sxv (y - 1)).
Proof.
rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
rewrite !swrap32_eq'. Local Ltac2 Set LiaHints.tbl := fun () => "0010>11447730086.4400000[S1H2H02H42H52H93H103H143H153H193H203H243H25".
mlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_congr segs m A cs cs' :
cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. intros EB ES WF [[_ B] W]. split; [split; [exact WF| rewrite <- EB; exact B] | rewrite <- ES; exact W]. Qed.
#[using="Type"] Lemma le1_neg1 : le1 (Z_to_bv 64 (-1)) = [b8 255].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.
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
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Section CANSEC3. Context {rc : runConstT}.
Definition frozen (P : Prop) : Prop := P.
End CANSEC3.
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
Section CANSEC4. Context {rc : runConstT}.
#[using="Type"] Lemma wr_at_sub : forall segs m A n A' n',
wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
intros segs m A n A' n' (H0 & H1 & H) LA LB. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1354083521.12 22615015996.1442726273952.1457921084252.1200000700A00B00IS2H02LAS2LA2LB2HiSS2H12LB".
split; [lia|]. split; [lia|].
intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
intros b po Hb Hp. Local Ltac2 Set LiaHints.tbl := fun () => "0020>24890858932.5 55724189863.1900000100=SS2Hb2Hp1H2H4".
replace (b + po) with ((b / 4096) * 256 * 16 + (po / 16) * 16) by (Z.div_mod_to_equations; lia).
rewrite <- Z.mul_add_distr_r, Z.mod_mul. reflexivity. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma optr_eqb_refl : forall q : aptr, optr_eqb (Some q) (Some q) = true.
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.
End CANSEC4.
