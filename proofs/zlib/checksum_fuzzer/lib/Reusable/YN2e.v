(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP09 YN32.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0b YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Notation Z64 := (Z_to_bv 64).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma Z64_eq_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z64 a = Z64 b.
Proof.
intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
Lemma Z64_mod : forall a, Z64 (a mod 2 ^ 64) = Z64 a.
Proof. intros a. apply Z64_eq_mod. apply Z.mod_mod. lia. Qed.
Lemma u64_of_Z : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z64 a) = a.
Proof. intros a H. apply u_Z2bv; lia. Qed.
Lemma u64_of_Z_mod : forall a, bv_unsigned (Z64 a) = a mod 2 ^ 64.
Proof. intros a. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma add64_range a b : 0 <= add64 a b < 2 ^ 64.
Proof. unfold add64. apply Z.mod_pos_bound. lia. Qed.
Lemma sub64_range a b : 0 <= sub64 a b < 2 ^ 64.
Proof. unfold sub64. apply Z.mod_pos_bound. lia. Qed.
Lemma mul64_range a b : 0 <= mul64 a b < 2 ^ 64.
Proof. unfold mul64. apply Z.mod_pos_bound. lia. Qed.
Lemma sll64_range a k : 0 <= sll64 a k < 2 ^ 64.
Proof. unfold sll64. apply Z.mod_pos_bound. lia. Qed.
Lemma not64_range a : 0 <= not64 a < 2 ^ 64.
Proof. unfold not64. apply Z.mod_pos_bound. lia. Qed.
Lemma neg64_range a : 0 <= neg64 a < 2 ^ 64.
Proof. unfold neg64. apply Z.mod_pos_bound. lia. Qed.
Lemma sltu_range a b : 0 <= sltu a b < 2 ^ 64.
Proof. unfold sltu. destruct (a <? b); lia. Qed.
Lemma land_range64 a b : 0 <= a < 2 ^ 64 -> 0 <= b -> 0 <= Z.land a b < 2 ^ 64.
Proof. intros. apply land_range; lia. Qed.
Lemma land_range64_r a b : 0 <= a -> 0 <= b < 2 ^ 64 -> 0 <= Z.land a b < 2 ^ 64.
Proof. intros. apply land_range_r; lia. Qed.
Lemma lor_range64 a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof. intros. apply lor_range; lia. Qed.
Lemma shiftr_range64 a k : 0 <= a < 2 ^ 64 -> 0 <= k -> 0 <= Z.shiftr a k < 2 ^ 64.
Proof. intros. apply shiftr_range; lia. Qed.
Lemma vz_add a b : v_add (Z64 a) (Z64 b) = Z64 (add64 a b).
Proof. rewrite v_add_lit. unfold add64. symmetry. apply Z64_mod. Qed.
Lemma vz_sub a b : v_sub (Z64 a) (Z64 b) = Z64 (sub64 a b).
Proof. rewrite v_sub_lit. unfold sub64. symmetry. apply Z64_mod. Qed.
Lemma vz_addi a i : v_addi (Z64 a) i = Z64 (add64 a i).
Proof. rewrite v_addi_lit. unfold add64. symmetry. apply Z64_mod. Qed.
Lemma vz_addi_neg a c : v_addi (Z64 a) (- c) = Z64 (add64 a (2 ^ 64 - c)).
Proof.
rewrite v_addi_lit. apply Z64_eq_mod. unfold add64. rewrite Z.mod_mod by lia.
replace (a + (2 ^ 64 - c)) with (a + - c + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma Z64_add64_wrap a k : Z64 (a + k) = Z64 (add64 a (k + 2 ^ 64)).
Proof.
apply Z64_eq_mod. unfold add64. rewrite Z.mod_mod by lia.
replace (a + (k + 2 ^ 64)) with (a + k + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma vz_mul a b : v_mul (Z64 a) (Z64 b) = Z64 (mul64 a b).
Proof.
unfold v_mul, mul64. rewrite <- Z64_mod. apply Z64_eq_mod.
rewrite !u64_of_Z_mod, <- Z.mul_mod, !Z.mod_mod by lia. reflexivity.
Qed.
Lemma vz_and a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_and (Z64 a) (Z64 b) = Z64 (Z.land a b).
Proof. intros Ha Hb. unfold v_and. rewrite !u64_of_Z by lia. reflexivity. Qed.
Lemma vz_or a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_or (Z64 a) (Z64 b) = Z64 (Z.lor a b).
Proof. intros Ha Hb. unfold v_or. rewrite !u64_of_Z by lia. reflexivity. Qed.
Lemma vz_xor a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_xor (Z64 a) (Z64 b) = Z64 (Z.lxor a b).
Proof. intros Ha Hb. unfold v_xor. rewrite !u64_of_Z by lia. reflexivity. Qed.
Lemma vz_andi a i : 0 <= a < 2 ^ 64 -> v_andi (Z64 a) i = Z64 (Z.land a (i mod 2 ^ 64)).
Proof. intros Ha. unfold v_andi. rewrite u64_of_Z by lia. reflexivity. Qed.
Lemma vz_ori a i : 0 <= a < 2 ^ 64 -> v_ori (Z64 a) i = Z64 (Z.lor a (i mod 2 ^ 64)).
Proof. intros Ha. unfold v_ori. rewrite u64_of_Z by lia. reflexivity. Qed.
Lemma vz_not a : 0 <= a < 2 ^ 64 -> v_xori (Z64 a) (-1) = Z64 (not64 a).
Proof.
intros Ha. unfold v_xori. rewrite u64_of_Z by lia.
change (bv_wrap 64 (-1)) with (Z.ones 64).
unfold not64. apply Z64_eq_mod. rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi.
rewrite !Z.testbit_mod_pow2 by lia.
destruct (i <? 64) eqn:E; [|reflexivity]. cbn [andb].
rewrite Z.lxor_spec, Z.lnot_spec, Z.testbit_ones_nonneg, E by lia.
destruct (Z.testbit a i); reflexivity.
Qed.
Lemma vz_srli a k : 0 <= a < 2 ^ 64 -> v_srli (Z64 a) k = Z64 (Z.shiftr a k).
Proof. intros Ha. unfold v_srli. rewrite u64_of_Z by lia. reflexivity. Qed.
Lemma vz_slli a k : 0 <= a < 2 ^ 64 -> 0 <= k -> v_slli (Z64 a) k = Z64 (sll64 a k).
Proof. intros Ha Hk. unfold v_slli, sll64. rewrite u64_of_Z by lia. symmetry. apply Z64_mod. Qed.
Lemma vz_sltu a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_sltu (Z64 a) (Z64 b) = Z64 (sltu a b).
Proof.
intros Ha Hb. unfold v_sltu, c_ltu, bv_ltu, sltu. rewrite !u64_of_Z by lia.
destruct (a <? b); reflexivity.
Qed.
Lemma vz_slt a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
v_slt (Z64 a) (Z64 b) = Z64 (if s64 a <? s64 b then 1 else 0).
Proof.
intros Ha Hb. unfold v_slt, c_lts, bv_lts.
rewrite !bv_signed_s64, !u64_of_Z by lia. destruct (s64 a <? s64 b); reflexivity.
Qed.
Lemma Z64_swrap32 z : Z64 (bv_swrap 32 z) = Z64 (sx32 z).
Proof.
apply bv_eq. rewrite !Z_to_bv_unsigned, wrap64_swrap32.
pose proof (sx32_range z). symmetry. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma vz_addiw a i : 0 <= a < 2 ^ 64 -> v_addiw (Z64 a) i = Z64 (addw a i).
Proof. intros Ha. unfold v_addiw, addw. rewrite u64_of_Z by lia. apply Z64_swrap32. Qed.
Lemma vz_addw a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_addw (Z64 a) (Z64 b) = Z64 (addw a b).
Proof. intros Ha Hb. unfold v_addw, addw. rewrite !u64_of_Z by lia. apply Z64_swrap32. Qed.
Lemma vz_subw a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_subw (Z64 a) (Z64 b) = Z64 (subw a b).
Proof. intros Ha Hb. unfold v_subw, subw. rewrite !u64_of_Z by lia. apply Z64_swrap32. Qed.
Lemma vz_negw b : 0 <= b < 2 ^ 64 -> v_subw (Z64 0) (Z64 b) = Z64 (negw b).
Proof. intros Hb. rewrite vz_subw by lia. rewrite subw_0_l. reflexivity. Qed.
Lemma vz_slliw a k : 0 <= a < 2 ^ 64 -> 0 <= k < 32 -> v_slliw (Z64 a) k = Z64 (sllw a k).
Proof.
intros Ha Hk. unfold v_slliw, sllw. rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. apply Z64_swrap32.
Qed.
Lemma vz_srliw a k : 0 <= a < 2 ^ 64 -> 0 <= k < 32 -> v_srliw (Z64 a) k = Z64 (srlw a k).
Proof.
intros Ha Hk. unfold v_srliw, srlw, lo32. rewrite u64_of_Z by lia. rewrite (Z.mod_small k) by lia.
rewrite bv_wrap32. apply Z64_swrap32.
Qed.
Lemma vz_lw (v : word) : v_lw v = Z64 (sx32 (bv_unsigned v)).
Proof. unfold v_lw. apply Z64_swrap32. Qed.
Lemma vz_lui z : v_lui z = Z64 z.
Proof. reflexivity. Qed.
Lemma brz_eq a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_EQ (Z64 a) (Z64 b) = (a =? b).
Proof. intros. rewrite branch_eq, !u64_of_Z by lia. reflexivity. Qed.
Lemma brz_ne a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_NE (Z64 a) (Z64 b) = negb (a =? b).
Proof. intros. rewrite branch_ne, !u64_of_Z by lia. reflexivity. Qed.
Lemma brz_ltu a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_LTU (Z64 a) (Z64 b) = (a <? b).
Proof. intros. rewrite branch_ltu, !u64_of_Z by lia. reflexivity. Qed.
Lemma brz_geu a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_GEU (Z64 a) (Z64 b) = negb (a <? b).
Proof. intros. rewrite branch_geu, !u64_of_Z by lia. reflexivity. Qed.
Lemma brz_lt a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_LT (Z64 a) (Z64 b) = (s64 a <? s64 b).
Proof. intros. rewrite branch_lt, !u64_of_Z by lia. reflexivity. Qed.
Lemma brz_ge a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_GE (Z64 a) (Z64 b) = negb (s64 a <? s64 b).
Proof. intros. rewrite branch_ge, !u64_of_Z by lia. reflexivity. Qed.
Section e.
Variable segs : list Segment.
Lemma rdn1_mbyte : forall mem a b,
mbyte segs mem a = Some b -> rdn segs mem (Z64 a) 1 = Some [b].
Proof.
intros mem a b H. apply (proj2 (rdn_mbytes segs mem 1 a [b])). split; [reflexivity|].
intros i Hi. destruct i; [|lia]. rewrite Z.add_0_r. exact H.
Qed.
Lemma rdn2_mbyte : forall mem a b0 b1,
mbyte segs mem a = Some b0 -> mbyte segs mem (a + 1) = Some b1 ->
rdn segs mem (Z64 a) 2 = Some [b0; b1].
Proof.
intros mem a b0 b1 H0 H1. apply (proj2 (rdn_mbytes segs mem 2 a [b0; b1])). split; [reflexivity|].
intros i Hi. destruct i as [|[|]]; [rewrite Z.add_0_r; exact H0 | exact H1 | lia].
Qed.
Definition le_list (v : Z) (w : nat) : list byte := map (fun k => Z_to_bv 8 (le_byte v w k)) (seq 0 w).
Lemma le_list_length v w : length (le_list v w) = w.
Proof. unfold le_list. rewrite length_map, length_seq. reflexivity. Qed.
Lemma rdn_cell : forall mem a v w,
(forall k, (k < w)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v w k))) ->
rdn segs mem (Z64 a) w = Some (le_list v w).
Proof.
intros mem a v w H. apply (proj2 (rdn_mbytes segs mem w a (le_list v w))). split; [apply le_list_length|].
intros i Hi. rewrite H by exact Hi. unfold le_list.
rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt i w) Hi). reflexivity.
Qed.
Lemma word_mem_rdn : forall mem a v,
word_mem segs mem a v -> rdn segs mem (Z64 a) 8 = Some (le_list v 8).
Proof. intros mem a v H. apply rdn_cell. exact H. Qed.
Lemma le_byte_testbit v w k j : 0 <= j ->
Z.testbit (le_byte v w k) j = if j <? 8 then (if 8 * Z.of_nat k + j <? 8 * Z.of_nat w then Z.testbit v (8 * Z.of_nat k + j) else false) else false.
Proof.
intros Hj. unfold le_byte. change 256 with (2 ^ 8).
rewrite testbit_mod_pow2 by lia. destruct (j <? 8) eqn:E; [|reflexivity].
rewrite Z.shiftr_spec by lia. rewrite testbit_mod_pow2 by lia.
replace (j + 8 * Z.of_nat k) with (8 * Z.of_nat k + j) by lia. reflexivity.
Qed.
Lemma bytes_le_to_Z_le_list_gen : forall w v s,
bytes_le_to_Z (map (fun k => Z_to_bv 8 (le_byte v (s + w) k)) (seq s w)) =
Z.shiftr (v mod 2 ^ (8 * Z.of_nat (s + w))) (8 * Z.of_nat s).
Proof.
induction w as [|w IH]; intros v s.
- cbn [map seq bytes_le_to_Z]. rewrite Nat.add_0_r.
apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0, Z.shiftr_spec by lia.
rewrite (testbit_high_false _ (8 * Z.of_nat s)); [reflexivity| apply Z.mod_pos_bound; lia | lia].
- cbn [map seq bytes_le_to_Z]. replace (s + S w)%nat with (S s + w)%nat by lia. rewrite IH.
apply Z.bits_inj'. intros j Hj.
rewrite Z.lor_spec, Z.shiftr_spec by lia.
rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2 ^ 8).
rewrite testbit_mod_pow2 by lia.
destruct (j <? 8) eqn:E.
+ apply Z.ltb_lt in E. rewrite Z.shiftl_spec_low by lia. rewrite orb_false_r. cbn [andb].
rewrite le_byte_testbit by lia. rewrite (proj2 (Z.ltb_lt j 8)) by lia.
rewrite testbit_mod_pow2 by lia.
replace (j + 8 * Z.of_nat s) with (8 * Z.of_nat s + j) by lia.
replace (8 * Z.of_nat (S s + w)) with (8 * (Z.of_nat s + 1 + Z.of_nat w)) by lia.
destruct (8 * Z.of_nat s + j <? 8 * (Z.of_nat s + 1 + Z.of_nat w)) eqn:E2; reflexivity.
+ apply Z.ltb_ge in E. rewrite Z.shiftl_spec_high by lia. cbn [andb orb].
rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.
Lemma bytes_le_to_Z_le_list : forall v w,
bytes_le_to_Z (le_list v w) = v mod 2 ^ (8 * Z.of_nat w).
Proof.
intros v w. unfold le_list. pose proof (bytes_le_to_Z_le_list_gen w v 0) as H.
cbn [Nat.add] in H. rewrite H. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
Qed.
Lemma word_mem_value : forall v, 0 <= v < 2 ^ 64 -> bytes_le_to_Z (le_list v 8) = bv_unsigned (Z64 v).
Proof. intros v Hv. rewrite bytes_le_to_Z_le_list, u64_of_Z by lia. apply Z.mod_small. lia. Qed.
Lemma word_mem_value_mod : forall v, bytes_le_to_Z (le_list v 8) = bv_unsigned (Z64 v).
Proof. intros v. rewrite bytes_le_to_Z_le_list, u64_of_Z_mod. reflexivity. Qed.
Lemma store_ok_writable : forall mem a n,
0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall x, a <= x < a + Z.of_nat n -> writable_at segs mem x) ->
RiscvSemantics.store_ok segs mem (Z64 a) n = true.
Proof.
intros mem a n. revert a. induction n as [|n IH]; intros a Ha Hn Hw; [reflexivity|].
cbn [RiscvSemantics.store_ok].
pose proof (Hw a ltac:(lia)) as W. unfold writable_at in W.
destruct (wview segs mem (Z64 a)); [|exfalso; apply W; reflexivity].
rewrite Z_to_bv64_add1. apply IH; [lia | lia |]. intros x Hx. apply Hw. lia.
Qed.
Lemma present_writable : forall mem a, present mem a -> writable_at segs mem a.
Proof. intros mem a [b Hb]. unfold writable_at, wview. rewrite Hb. discriminate. Qed.
Lemma wbytes_other : forall bs m a x,
0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
~ (a <= x < a + Z.of_nat (length bs)) ->
wbytes m (Z64 a) bs (Z64 x) = m (Z64 x).
Proof.
intros bs m a x Ha Hn Hx Hout. destruct bs as [|b bs']; [reflexivity|].
cbn [length] in *.
destruct (Z_lt_le_dec x a).
- apply wbytes_below; cbn [length]; rewrite ?u64_of_Z by lia; lia.
- apply wbytes_above; cbn [length]; rewrite ?u64_of_Z by lia; lia.
Qed.
Lemma wbytes_mbyte_in : forall bs m a x,
0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> a <= x < a + Z.of_nat (length bs) ->
mbyte segs (wbytes m (Z64 a) bs) x = nth_error bs (Z.to_nat (x - a)).
Proof.
intros bs m a x Ha Hn Hx. rewrite wbytes_mbyte by lia.
replace ((a <=? x) && (x <? a + Z.of_nat (length bs))) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma wbytes_mbyte_out : forall bs m a x,
0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
~ (a <= x < a + Z.of_nat (length bs)) ->
mbyte segs (wbytes m (Z64 a) bs) x = mbyte segs m x.
Proof.
intros bs m a x Ha Hn Hx Hout. unfold mbyte. rewrite wbytes_other by assumption. reflexivity.
Qed.
Lemma wbytes_present : forall bs m a x, m x <> None -> wbytes m a bs x <> None.
Proof. intros bs m a x H. apply (wbytes_grows bs m a). exact H. Qed.
Lemma wbytes_writable : forall bs m a x, writable_at segs m x -> writable_at segs (wbytes m a bs) x.
Proof.
intros bs m a x H. unfold writable_at, wview in *.
destruct (m (Z64 x)) as [b|] eqn:E.
- pose proof (wbytes_grows bs m a (Z64 x)) as G. rewrite E in G.
destruct (wbytes m a bs (Z64 x)); [discriminate | exfalso; apply G; [discriminate | reflexivity]].
- destruct (wbytes m a bs (Z64 x)); [discriminate | exact H].
Qed.
End e.
Lemma Z_to_le_bytes_nth : forall n z k, (k < n)%nat ->
nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth_error]. rewrite IH by lia. f_equal. f_equal.
rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma le_byte_bv : forall v w k, (k < w)%nat ->
Z_to_bv 8 (le_byte v w k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
intros v w k Hk. apply bv_eq. rewrite !Z_to_bv_unsigned.
change (bv_wrap 8 ?x) with (x mod 2 ^ 8).
apply Z.bits_inj'. intros i Hi. rewrite !testbit_mod_pow2 by lia.
destruct (i <? 8) eqn:E; [|reflexivity]. cbn [andb]. apply Z.ltb_lt in E.
unfold le_byte. change 256 with (2 ^ 8). rewrite testbit_mod_pow2 by lia.
rewrite (proj2 (Z.ltb_lt i 8)) by lia. cbn [andb].
rewrite !Z.shiftr_spec by lia. rewrite testbit_mod_pow2 by lia.
replace (i + 8 * Z.of_nat k <? 8 * Z.of_nat w) with true; [reflexivity|].
symmetry. apply Z.ltb_lt. nia.
Qed.
Lemma word_to_le_bytes_nth : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ 64 ->
nth_error (word_to_le_bytes n (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (le_byte v n k)).
Proof.
intros n v k Hk Hv. unfold word_to_le_bytes. rewrite Z_to_le_bytes_nth by exact Hk.
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite le_byte_bv by exact Hk. reflexivity.
Qed.
Theorem enframe_off_ok' stride n b : 0 <= n -> n + IB <= stride -> stride < 2^63 -> stride - IB - n < 2 ^ 35 -> 0 <= b ->
enframe_off_machine stride n b = fold_off ((stride - IB - n) / UNIT) (Z.land b 255) /\
0 <= enframe_off_machine stride n b <= (stride - IB - n) / UNIT.
Proof.
intros Hn Hs Hb Hsmall Hb0.
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
End d.
