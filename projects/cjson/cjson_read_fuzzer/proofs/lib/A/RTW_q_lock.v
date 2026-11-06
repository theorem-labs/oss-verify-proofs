(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_lib4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition lkw (a b u : Z) : Z := a + 256 * b + 65536 * u.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lkw_bytes : forall a b (b2 b3 : byte), 0 <= a < 256 -> 0 <= b < 256 ->
  le4 (wz (lkw a b (bv_unsigned b2 + 256 * bv_unsigned b3))) = [zb a; zb b; b2; b3].
Proof.
  intros a b b2 b3 Ha Hb.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R2, R3. cbn in R2, R3.
  unfold le4, wz, zb, lkw. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  f_equal; [apply zb8_eq; Z.div_mod_to_equations; lia|].
  f_equal; [apply zb8_eq; Z.div_mod_to_equations; lia|].
  f_equal; [rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b2) at 2; apply zb8_eq; Z.div_mod_to_equations; lia|].
  f_equal. rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b3) at 2. apply zb8_eq. Z.div_mod_to_equations. lia.
Qed.

Local Ltac rebytes_side :=
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size Cells.csize app length Nat.add];
  rewrite ?lkw_bytes by lia; cbn [app];
  first [reflexivity | tauto | lia | (repeat split; lia)].


(* [comment removed for export] *)
Lemma qlock_of : forall m p a b j, 0 <= a < 256 -> 0 <= b < 256 ->
  rw_cells asegs m p [W1 a; W1 b; CB 6 j] ->
  exists (b2 b3 : byte) j4,
    rw_cells asegs m p [C4 (wz (lkw a b (bv_unsigned b2 + 256 * bv_unsigned b3)))] /\ rw_cells asegs m (p + 4) [CB 4 j4].
Proof.
  intros m p a b j Ha Hb H.
  apply (rw_cells_split_CB _ _ _ [W1 a; W1 b] _ _ _ [2; 4]%nat) in H; [| cbn; destruct H as [[W _] _]; cbn in W; lia].
  cbn [mk_CB_cells app] in H.
  pose proof (proj1 (rw_cells_app m p [W1 a; W1 b; CB 2 (firstn 2 j)] [CB 4 (firstn 4 (skipn 2 j))]) H) as [H1 H2].
  cbn [cells_size Cells.csize Nat.add] in H2.
  pose proof H1 as [[W _] _]. cbn in W. destruct W as (_ & _ & L2 & _).
  destruct (firstn 2 j) as [|b2 [|b3 [|? ?]]] eqn:E2; cbn in L2; try lia.
  exists b2, b3, (firstn 4 (skipn 2 j)). split; [| exact H2].
  refine (rw_cells_rebytes _ _ _ _ _ _ _ H1); rebytes_side.
Qed.

Lemma qlock_to : forall m p (w : word) a b (b2 b3 : byte) j4, 0 <= a < 256 -> 0 <= b < 256 ->
  le4 w = [zb a; zb b; b2; b3] ->
  rw_cells asegs m p [C4 w] -> rw_cells asegs m (p + 4) [CB 4 j4] ->
  rw_cells asegs m p [W1 a; W1 b; CB 6 ([b2; b3] ++ j4)].
Proof.
  intros m p w a b b2 b3 j4 Ha Hb E H1 H2.
  pose proof H2 as [[W _] _]. cbn in W. destruct W as [L4 _].
  assert (H : rw_cells asegs m p ([C4 w] ++ [CB 4 j4])) by (apply (proj2 (rw_cells_app _ _ _ _)); split; [exact H1| exact H2]).
  refine (rw_cells_rebytes _ _ _ _ _ _ _ H); cbn [cells_bytes cbytes app]; rewrite ?E; rebytes_side.
Qed.

(* [comment removed for export] *)
Lemma qlock_w3 : forall m p (w : word) a b (b2 b3 : byte), 0 <= a < 256 -> 0 <= b < 256 ->
  le4 w = [zb a; zb b; b2; b3] ->
  rw_cells asegs m p [C4 w] -> rw_cells asegs m p [W1 a; W1 b; CB 2 [b2; b3]].
Proof.
  intros m p w a b b2 b3 Ha Hb E H. refine (rw_cells_rebytes _ _ _ _ _ _ _ H); cbn [cells_bytes cbytes app]; rewrite ?E; rebytes_side.
Qed.
Lemma qlock_w1 : forall m p a b (b2 b3 : byte), 0 <= a < 256 -> 0 <= b < 256 ->
  rw_cells asegs m p [W1 a; W1 b; CB 2 [b2; b3]] -> rw_cells asegs m p [C4 (wz (lkw a b (bv_unsigned b2 + 256 * bv_unsigned b3)))].
Proof.
  intros m p a b b2 b3 Ha Hb H. refine (rw_cells_rebytes _ _ _ _ _ _ _ H); rebytes_side.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_word_facts : forall v, 0 <= v < 2^32 ->
  let X := bv_unsigned (sx32 (Z_to_bv 64 v)) in 0 <= X < 2^64 /\ X mod 2^32 = v /\ (X = v \/ X = 2^64 - 2^32 + v).
Proof.
  intros v Hv X. subst X. unfold sx32. rewrite (unsigned_lit v) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32). change (Z.of_N 32 - 1) with 31.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land_255' : forall v, Z.land v 255 = v mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lxor_pow2_clear : forall v k, 0 <= v -> 0 <= k -> (v / 2^k) mod 2 = 0 -> Z.lxor v (2^k) = v + 2^k.
Proof.
  intros v k Hv Hk Hm. symmetry. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, (Z.pow2_bits_eqb k n) by lia.
  destruct (Z.eqb_spec k n); [| apply andb_false_r]. subst n.
  pose proof (Z.testbit_spec' v k Hk) as T. rewrite Hm in T. destruct (Z.testbit v k); cbn in T; [lia| reflexivity].
Qed.

Lemma land_65280 : forall Y, 0 <= Y -> Z.land Y 65280 = 256 * ((Y / 256) mod 256).
Proof.
  intros Y HY.
  replace (256 * ((Y / 256) mod 256)) with (Z.shiftl ((Z.shiftr Y 8) mod 2^8) 8)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2^8) with 256; lia).
  change 65280 with (Z.shiftl (Z.ones 8) 8).
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z_lt_le_dec (n - 8) 0) as [L|L].
  - rewrite !(Z.testbit_neg_r _ (n - 8)) by lia. apply andb_false_r.
  - destruct (Z_lt_le_dec (n - 8) 8) as [L2|L2].
    + rewrite Z.ones_spec_low, Z.mod_pow2_bits_low, Z.shiftr_spec by lia. replace (n - 8 + 8) with n by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high, Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma lane0_facts : forall X b u, 0 <= X < 2^64 -> X mod 2^32 = lkw 0 b u -> 0 <= b < 256 -> 0 <= u < 65536 ->
  Z.land (Z.lxor X 1) 255 = 1 /\ Z.lxor X 1 = X + 1 /\ Z.land X 255 = 0
  /\ 0 <= X + 1 < 2^64 /\ (X + 1) mod 2^32 = lkw 1 b u.
Proof.
  intros X b u HX HM Hb Hu. unfold lkw in *.
  assert (E2 : X mod 2 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (lxor_pow2_clear X 0 ltac:(lia) ltac:(lia)) as L1. change (2^0) with 1 in L1. rewrite Z.div_1_r in L1. specialize (L1 E2).
  rewrite L1, !land_255'. repeat split; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma lane1_facts : forall X a u, 0 <= X < 2^64 -> X mod 2^32 = lkw a 0 u -> 0 <= a < 256 -> 0 <= u < 65536 ->
  Z.land (Z.lxor X 256) 65280 = 256 /\ Z.lxor X 256 = X + 256
  /\ Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 8) mod 18446744073709551616) 255 = 0
  /\ 0 <= X + 256 < 2^64 /\ (X + 256) mod 2^32 = lkw a 1 u.
Proof.
  intros X a u HX HM Ha Hu. unfold lkw in *.
  assert (E2 : (X / 2^8) mod 2 = 0) by (change (2^8) with 256; Z.div_mod_to_equations; lia).
  pose proof (lxor_pow2_clear X 8 ltac:(lia) ltac:(lia) E2) as L1. change (2^8) with 256 in L1.
  rewrite L1, land_65280, land_255' by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (Z.of_N 32 - 1) with 31.
  rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256 in *.
  repeat split; Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
Lemma le4_mod32' : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> x mod 2^32 = y mod 2^32 -> le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 y).
Proof.
  intros x y Hx Hy E. unfold le4. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  f_equal; [apply zb8_eq; Z.div_mod_to_equations; lia|].
  f_equal; [apply zb8_eq; Z.div_mod_to_equations; lia|].
  f_equal; [apply zb8_eq; Z.div_mod_to_equations; lia|].
  f_equal. apply zb8_eq; Z.div_mod_to_equations; lia.
Qed.

Lemma lkw_range : forall a b u, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= u < 65536 -> 0 <= lkw a b u < 2^32.
Proof. intros. unfold lkw. lia. Qed.

(* [comment removed for export] *)
Lemma cas_le4 : forall R a' b' (b2 b3 : byte), 0 <= R < 2^64 -> 0 <= a' < 256 -> 0 <= b' < 256 ->
  R mod 2^32 = lkw a' b' (bv_unsigned b2 + 256 * bv_unsigned b3) ->
  le4 (Z_to_bv 64 R) = [zb a'; zb b'; b2; b3].
Proof.
  intros R a' b' b2 b3 HR Ha Hb E.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R2, R3. cbn in R2, R3.
  rewrite <- lkw_bytes by lia. unfold wz. apply le4_mod32'; [lia| unfold lkw; lia|].
  rewrite E. symmetry. apply Z.mod_small. unfold lkw. lia.
Qed.


End CeilWrap.
