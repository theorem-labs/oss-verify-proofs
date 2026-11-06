(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fk_kind_lim : to_Z kind_lim = 2 ^ 60.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fk_vkind_cases (t : int) :
  (to_Z t < 2 ^ 60 /\ vkind t = 0%uint63)
  \/ (2 ^ 60 <= to_Z t < 2 * 2 ^ 60 /\ vkind t = 1%uint63)
  \/ (2 * 2 ^ 60 <= to_Z t < 3 * 2 ^ 60 /\ vkind t = 2%uint63)
  \/ (3 * 2 ^ 60 <= to_Z t < 4 * 2 ^ 60 /\ vkind t = 3%uint63)
  \/ (4 * 2 ^ 60 <= to_Z t < 5 * 2 ^ 60 /\ vkind t = 4%uint63)
  \/ (5 * 2 ^ 60 <= to_Z t < 6 * 2 ^ 60 /\ vkind t = 5%uint63)
  \/ (6 * 2 ^ 60 <= to_Z t < 7 * 2 ^ 60 /\ vkind t = 6%uint63)
  \/ (7 * 2 ^ 60 <= to_Z t /\ vkind t = 7%uint63).
Proof.
  unfold vkind.
  destruct (ltbP t 1152921504606846976) as [H0|H0]; [left; split; [exact H0 | reflexivity]|].
  destruct (ltbP t 2305843009213693952) as [H1|H1]; [right; left; split; [split; [|exact H1]|reflexivity]|].
  { change (to_Z 1152921504606846976) with (2 ^ 60) in H0. lia. }
  destruct (ltbP t 3458764513820540928) as [H2|H2]; [right; right; left; split; [split; [|exact H2]|reflexivity]|].
  { change (to_Z 2305843009213693952) with (2 * 2 ^ 60) in H1. lia. }
  destruct (ltbP t 4611686018427387904) as [H3|H3]; [right; right; right; left; split; [split; [|exact H3]|reflexivity]|].
  { change (to_Z 3458764513820540928) with (3 * 2 ^ 60) in H2. lia. }
  destruct (ltbP t 5764607523034234880) as [H4|H4]; [right; right; right; right; left; split; [split; [|exact H4]|reflexivity]|].
  { change (to_Z 4611686018427387904) with (4 * 2 ^ 60) in H3. lia. }
  destruct (ltbP t 6917529027641081856) as [H5|H5]; [right; right; right; right; right; left; split; [split; [|exact H5]|reflexivity]|].
  { change (to_Z 5764607523034234880) with (5 * 2 ^ 60) in H4. lia. }
  destruct (ltbP t 8070450532247928832) as [H6|H6]; [right; right; right; right; right; right; left; split; [split; [|exact H6]|reflexivity]|].
  { change (to_Z 6917529027641081856) with (6 * 2 ^ 60) in H5. lia. }
  right; right; right; right; right; right; right. split; [|reflexivity].
  change (to_Z 8070450532247928832) with (7 * 2 ^ 60) in H6. lia.
Qed.

(* [comment removed for export] *)
Lemma fk_vkind_le5 t : 0 <= to_Z (vkind t) <= 7.
Proof.
  destruct (fk_vkind_cases t) as [[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]]]]]; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma fk_tag_decomp t :
  to_Z t = to_Z (vkind t) * 2 ^ 60 + to_Z (vbase t) /\ 0 <= to_Z (vbase t).
Proof.
  pose proof (i63_range t) as Ht. unfold vbase. rewrite sub_spec, mul_spec, fk_kind_lim, i63_wB.
  destruct (fk_vkind_cases t) as [[H ->]|[[H ->]|[[H ->]|[[H ->]|[[H ->]|[[H ->]|[[H ->]|[H ->]]]]]]]];
    match goal with |- context [to_Z ?c * 2 ^ 60] => let z := eval cbv in (to_Z c) in change (to_Z c) with z end;
    rewrite (Z.mod_small (_ * 2 ^ 60)) by lia; rewrite Z.mod_small by lia; lia.
Qed.

Lemma fk_vkind_plain t : to_Z t < 2 ^ 60 -> vkind t = 0%uint63.
Proof. intros H. destruct (fk_vkind_cases t) as [[_ E]|[[B _]|[[B _]|[[B _]|[[B _]|[[B _]|[[B _]|[B _]]]]]]]]; [exact E | lia ..]. Qed.

Lemma fk_vbase_plain t : to_Z t < 2 ^ 60 -> vbase t = t.
Proof.
  intros H. apply to_Z_inj. destruct (fk_tag_decomp t) as [E _].
  rewrite (fk_vkind_plain t H) in E. change (to_Z 0) with 0 in E. lia.
Qed.

Lemma fk_vbase_lt t : to_Z t < 5 * 2 ^ 60 -> to_Z (vbase t) < 2 ^ 60.
Proof.
  intros H. destruct (fk_tag_decomp t) as [E _].
  destruct (fk_vkind_cases t) as [[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[B K]]]]]]]]; rewrite K in E;
    match type of E with context [to_Z ?c * 2 ^ 60] => let z := eval cbv in (to_Z c) in change (to_Z c) with z in E end; lia.
Qed.

(* [comment removed for export] *)
Lemma fk_vbase_lt7 t : to_Z (vbase t) < 2 ^ 60.
Proof.
  destruct (fk_tag_decomp t) as [E _]. pose proof (i63_range t) as Ht.
  destruct (fk_vkind_cases t) as [[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[[B K]|[B K]]]]]]]]; rewrite K in E;
    match type of E with context [to_Z ?c * 2 ^ 60] => let z := eval cbv in (to_Z c) in change (to_Z c) with z in E end; lia.
Qed.

Lemma fk_to_Z_ktag k b :
  to_Z k <= 7 -> to_Z b < 2 ^ 60 -> to_Z (ktag k b) = to_Z k * 2 ^ 60 + to_Z b.
Proof.
  intros Hk Hb. pose proof (i63_range k). pose proof (i63_range b).
  unfold ktag. rewrite add_spec, mul_spec, fk_kind_lim, i63_wB.
  rewrite (Z.mod_small (to_Z k * 2 ^ 60)) by lia. apply Z.mod_small. lia.
Qed.

Lemma fk_vkind_ktag k b : to_Z k <= 5 -> to_Z b < 2 ^ 60 -> vkind (ktag k b) = k.
Proof.
  intros Hk Hb. pose proof (i63_range k) as Hk0. pose proof (i63_range b) as Hb0.
  pose proof (fk_to_Z_ktag k b ltac:(lia) Hb) as E. apply to_Z_inj.
  destruct (fk_vkind_cases (ktag k b)) as [[B ->]|[[B ->]|[[B ->]|[[B ->]|[[B ->]|[[B ->]|[[B ->]|[B ->]]]]]]]];
    rewrite E in B;
    match goal with |- to_Z ?c = _ => let z := eval cbv in (to_Z c) in change (to_Z c) with z end; lia.
Qed.

Lemma fk_vbase_ktag k b : to_Z k <= 5 -> to_Z b < 2 ^ 60 -> vbase (ktag k b) = b.
Proof.
  intros Hk Hb. apply to_Z_inj. destruct (fk_tag_decomp (ktag k b)) as [E _].
  rewrite (fk_vkind_ktag k b Hk Hb), (fk_to_Z_ktag k b ltac:(lia) Hb) in E. lia.
Qed.

Lemma fk_ktag_0 b : ktag 0 b = b.
Proof. unfold ktag. apply to_Z_inj. rewrite add_spec, mul_spec. change (to_Z 0) with 0.
  rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_l. apply Z.mod_small. apply to_Z_bounded. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fk_dvk_P x w : dvk K_P x w = bv_add x w. Proof. reflexivity. Qed.
Lemma fk_dvk_N x w : dvk K_N x w = bv_add (bv_opp x) w. Proof. reflexivity. Qed.
Lemma fk_dvk_LO x w : dvk K_LO x w = sx32 (bv_add x w). Proof. reflexivity. Qed.
Lemma fk_dvk_HI x w : dvk K_HI x w = hi32 (bv_add x w). Proof. reflexivity. Qed.
Lemma fk_dvk_NLO x w : dvk K_NLO x w = sx32 (bv_add (bv_opp x) w). Proof. reflexivity. Qed.
Lemma fk_dvk_B5 x w : dvk K_B5 x w = b5 (bv_add x w). Proof. reflexivity. Qed.
Lemma fk_dvk_PG x w : dvk K_PG x w = alu64 ALU_SRL (bv_add x w) (Z_to_bv 64 12). Proof. reflexivity. Qed.
Lemma fk_dvk_SL3 x w : dvk K_SL3 x w = alu64 ALU_SLL (bv_add x w) (Z_to_bv 64 3). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fk_vkind_ktag7 k b : to_Z k <= 7 -> to_Z b < 2 ^ 60 -> vkind (ktag k b) = k.
Proof.
  intros Hk Hb. pose proof (i63_range k) as Hk0. pose proof (i63_range b) as Hb0.
  pose proof (fk_to_Z_ktag k b Hk Hb) as E. apply to_Z_inj.
  destruct (fk_vkind_cases (ktag k b)) as [[B ->]|[[B ->]|[[B ->]|[[B ->]|[[B ->]|[[B ->]|[[B ->]|[B ->]]]]]]]];
    rewrite E in B;
    match goal with |- to_Z ?c = _ => let z := eval cbv in (to_Z c) in change (to_Z c) with z end; lia.
Qed.

Lemma fk_vbase_ktag7 k b : to_Z k <= 7 -> to_Z b < 2 ^ 60 -> vbase (ktag k b) = b.
Proof.
  intros Hk Hb. apply to_Z_inj. destruct (fk_tag_decomp (ktag k b)) as [E _].
  rewrite (fk_vkind_ktag7 k b Hk Hb), (fk_to_Z_ktag k b Hk Hb) in E. lia.
Qed.

(* [comment removed for export] *)
Lemma fk_pg_unsigned (x : word) : bv_unsigned (alu64 ALU_SRL x (Z_to_bv 64 12)) = bv_unsigned x / 4096.
Proof.
  unfold alu64, alu. rewrite bv_shiftr_unsigned.
  replace (bv_unsigned (bv_and (Z_to_bv 64 12) (Z_to_bv 64 63))) with 12 by reflexivity.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Section Dv.
Variable rho : int -> word.

Lemma fk_dv_plain v : to_Z (vtag v) < 2 ^ 60 -> dv rho v = bv_add (rho (vtag v)) (wbv (vw v)).
Proof. intros H. unfold dv. rewrite (fk_vkind_plain _ H), (fk_vbase_plain _ H). reflexivity. Qed.

Lemma fk_dv_ktag k b w :
  to_Z k <= 5 -> to_Z b < 2 ^ 60 -> dv rho (FV (ktag k b) w) = dvk k (rho b) (wbv w).
Proof. intros Hk Hb. unfold dv. cbn [vtag vw]. rewrite (fk_vkind_ktag k b Hk Hb), (fk_vbase_ktag k b Hk Hb). reflexivity. Qed.

Lemma fk_dv_ktag7 k b w :
  to_Z k <= 7 -> to_Z b < 2 ^ 60 -> dv rho (FV (ktag k b) w) = dvk k (rho b) (wbv w).
Proof. intros Hk Hb. unfold dv. cbn [vtag vw]. rewrite (fk_vkind_ktag7 k b Hk Hb), (fk_vbase_ktag7 k b Hk Hb). reflexivity. Qed.

Lemma fk_dv_conc w : rho 0%uint63 = Z_to_bv 64 0 -> dv rho (FV 0 w) = wbv w.
Proof.
  intros H0. rewrite fk_dv_plain by (cbn; lia). cbn [vtag vw]. rewrite H0.
  apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite Z.add_0_l. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
End Dv.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fk_wbytes8_nth (x : word) (j : nat) :
  (j < 8)%nat -> nth_error (wbytes8 x) j = Some (Z_to_bv 8 (bv_unsigned x / 2 ^ (8 * Z.of_nat j))).
Proof. intros Hj. unfold wbytes8. apply Z_to_le_bytes_nth. exact Hj. Qed.

(* [comment removed for export] *)
Lemma fk_sx32_unsigned_mod (x : word) : bv_unsigned (sx32 x) mod 2 ^ 32 = bv_unsigned x mod 2 ^ 32.
Proof.
  unfold sx32. rewrite bv_sext64_extract_unsigned, zsext32_eq.
  set (z := bv_unsigned x). Z.div_mod_to_equations. lia.
Qed.

Lemma fk_hi32_unsigned_mod (x : word) : bv_unsigned (hi32 x) mod 2 ^ 32 = bv_unsigned x / 2 ^ 32.
Proof.
  unfold hi32, sext. rewrite bv_sign_extend_unsigned. unfold bv_signed.
  rewrite bv_extract_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 32) with 32. change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 32 `div` 2) with (2 ^ 31).
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx. change (Z.of_N 64) with 64 in Hx.
  set (z := bv_unsigned x) in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma fk_byte_mod32 (a b : Z) (j : nat) :
  (j < 4)%nat -> a mod 2 ^ 32 = b mod 2 ^ 32 ->
  Z_to_bv 8 (a / 2 ^ (8 * Z.of_nat j)) = Z_to_bv 8 (b / 2 ^ (8 * Z.of_nat j)).
Proof.
  intros Hj H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with (2 ^ 8).
  assert (E : forall z, (z / 2 ^ (8 * Z.of_nat j)) mod 2 ^ 8 = ((z mod 2 ^ 32) / 2 ^ (8 * Z.of_nat j)) mod 2 ^ 8).
  { intros z. destruct j as [|[|[|[|j]]]]; try lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul];
      Z.div_mod_to_equations; lia. }
  rewrite (E a), (E b), H. reflexivity.
Qed.

Lemma fk_bytes_sx32 (x : word) (j : nat) :
  (j < 4)%nat -> nth_error (wbytes8 (sx32 x)) j = nth_error (wbytes8 x) j.
Proof.
  intros Hj. rewrite !fk_wbytes8_nth by lia. f_equal.
  apply fk_byte_mod32; [exact Hj | apply fk_sx32_unsigned_mod].
Qed.

Lemma fk_bytes_hi32 (x : word) (j : nat) :
  (j < 4)%nat -> nth_error (wbytes8 (hi32 x)) j = nth_error (wbytes8 x) (4 + j).
Proof.
  intros Hj. rewrite !fk_wbytes8_nth by lia. f_equal.
  rewrite (fk_byte_mod32 _ (bv_unsigned x / 2 ^ 32) j Hj).
  - f_equal. rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia. do 2 f_equal. lia.
  - rewrite fk_hi32_unsigned_mod. symmetry. apply Z.mod_small.
    pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx. change (Z.of_N 64) with 64 in Hx.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
Lemma fk_load_lo (x : word) :
  sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (wbytes8 x)))) = sx32 x.
Proof.
  unfold wbytes8. rewrite Z_to_le_bytes_firstn by lia.
  pose proof (bv_unsigned_in_range _ x) as Hx.
  rewrite (load_value_of_bytes 32 4 (bv_unsigned x)) by (try reflexivity; lia).
  unfold sx32. f_equal. all: apply bv_eq; rewrite bv_extract_unsigned, Z_to_bv_unsigned, Z.shiftr_0_r; reflexivity.
Qed.

Lemma fk_load_hi (x : word) :
  sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 4 (wbytes8 x))))) = hi32 x.
Proof.
  unfold wbytes8. change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_app.
  rewrite skipn_app, skipn_all2 by (rewrite length_Z_to_le_bytes; lia).
  rewrite length_Z_to_le_bytes, Nat.sub_diag, skipn_O. cbn [app].
  rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia).
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx. change (Z.of_N 64) with 64 in Hx.
  rewrite (load_value_of_bytes 32 4) by (try reflexivity; try lia; apply Z.div_pos; lia).
  unfold hi32. f_equal. all: apply bv_eq; rewrite bv_extract_unsigned, Z_to_bv_unsigned;
    rewrite Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fk_sx32_sext (y : bv 32) : sx32 (sext 64 y) = sext 64 y.
Proof.
  unfold sx32. f_equal. apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed.
  pose proof (bv_unsigned_in_range _ y) as Hy. unfold bv_modulus in Hy. change (Z.of_N 32) with 32 in Hy.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 32) with 32. change (Z.of_N 64) with 64. change (2 ^ 32 `div` 2) with (2 ^ 31).
  set (z := bv_unsigned y) in *. Z.div_mod_to_equations. lia.
Qed.

Lemma fk_sx32_sx32 (x : word) : sx32 (sx32 x) = sx32 x.
Proof. unfold sx32 at 2 3. apply fk_sx32_sext. Qed.

Lemma fk_sx32_hi32 (x : word) : sx32 (hi32 x) = hi32 x.
Proof. unfold hi32. apply fk_sx32_sext. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fk_b5_unsigned (x : word) : bv_unsigned (b5 x) = (bv_unsigned x / 2 ^ 40) mod 256.
Proof.
  unfold b5, zext. rewrite bv_zero_extend_unsigned by lia. rewrite bv_extract_unsigned.
  unfold bv_wrap, bv_modulus. change (Z.of_N 40) with 40. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fk_load_b5 (x : word) :
  zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn 5 (wbytes8 x))))) = b5 x.
Proof.
  unfold wbytes8. change 8%nat with (5 + 3)%nat. rewrite Z_to_le_bytes_app.
  rewrite skipn_app, skipn_all2 by (rewrite length_Z_to_le_bytes; lia).
  rewrite length_Z_to_le_bytes, Nat.sub_diag, skipn_O. cbn [app].
  rewrite Z_to_le_bytes_firstn by lia.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx. change (Z.of_N 64) with 64 in Hx.
  rewrite (load_value_of_bytes 8 1) by (try reflexivity; try lia; apply Z.div_pos; lia).
  unfold b5. f_equal. apply bv_eq. rewrite bv_extract_unsigned, Z_to_bv_unsigned.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fk_div_bounded (A B x d : Z) : 0 < d -> A <= x <= B -> A / d = B / d -> x / d = A / d.
Proof.
  intros Hd [H1 H2] E.
  pose proof (Z.div_le_mono A x d Hd H1). pose proof (Z.div_le_mono x B d Hd H2). lia.
Qed.

(* [comment removed for export] *)
Lemma fk_byte_of_mod (y B : Z) : 0 < B -> (y / B) mod 256 = (y mod (B * 256)) / B.
Proof.
  intros HB. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm B), Z.div_add by lia.
  rewrite (Z.div_small (y mod B)) by (apply Z.mod_pos_bound; exact HB). reflexivity.
Qed.

Lemma fk_low_byte_aligned (r w al j : Z) :
  0 <= j <= 7 -> 8 * (j + 1) <= al -> r mod 2 ^ al = 0 ->
  (((r + w) mod 2 ^ 64) / 2 ^ (8 * j)) mod 256 = (w / 2 ^ (8 * j)) mod 256.
Proof.
  intros Hj Hal Hr.
  assert (HB : 0 < 2 ^ (8 * j)) by (apply Z.pow_pos_nonneg; lia).
  rewrite !fk_byte_of_mod by exact HB. f_equal.
  assert (EK : 2 ^ (8 * j) * 256 = 2 ^ (8 * (j + 1))).
  { change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite EK. set (K := 2 ^ (8 * (j + 1))).
  assert (HK : 0 < K) by (apply Z.pow_pos_nonneg; lia).
  assert (HK64 : (K | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * (j + 1))). unfold K. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (HKr : (K | r)).
  { apply Z.mod_divide in Hr; [|apply Z.pow_nonzero; lia]. eapply Z.divide_trans; [|exact Hr].
    exists (2 ^ (al - 8 * (j + 1))). unfold K. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite (Z.mod_mod_divide _ _ _ HK64).
  rewrite Z.add_mod by lia. apply Z.mod_divide in HKr; [|lia]. rewrite HKr, Z.add_0_l, Z.mod_mod by lia.
  reflexivity.
Qed.

Section Bounds.
Variable rho : int -> word.

(* [comment removed for export] *)
Lemma fk_ptr_unsigned t rg top off :
  region_ok rho t rg -> to_Z top mod 2 = 0 -> to_Z off < 2 ^ 62 -> to_Z (rg_chi rg) < 2 ^ 62 ->
  bv_unsigned (bv_add (rho t) (wbv (W64 top off))) = bv_unsigned (rho t) + to_Z off
  /\ to_Z (rg_clo rg) + to_Z off <= bv_unsigned (rho t) + to_Z off <= to_Z (rg_chi rg) + to_Z off.
Proof.
  intros (_ & _ & _ & _ & _ & Hclo & Hchi) Htop Hoff Hc.
  pose proof (i63_range off) as Ho. pose proof (bv_unsigned_in_range _ (rho t)) as Hr.
  rewrite bv_add_unsigned, wbv_unsigned, (wZ_even_top top off Htop).
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma fk_b5_nonzero M b w :
  (forall t rg, iget t M = Some rg -> region_ok rho t rg) ->
  b5_nonzero M b w = true -> bv_unsigned (b5 (bv_add (rho b) (wbv w))) <> 0.
Proof.
  intros HM H. destruct w as [top off]. unfold b5_nonzero in H.
  destruct (iget b M) as [rg|] eqn:Hg; [|discriminate].
  repeat match type of H with (_ && _ = true) =>
    let H' := fresh "Hc" in apply andb_true_iff in H as [H H'] end.
  apply Uint63.eqb_spec in H. apply (f_equal to_Z) in H. rewrite i63_land1 in H. change (to_Z 0) with 0 in H.
  apply ltb_spec in Hc2, Hc1, Hc. apply leb_spec in Hc0.
  change (to_Z off_bound) with (2 ^ 62) in Hc2, Hc1.
  change (to_Z 1099511627776) with (2 ^ 40) in Hc0. change (to_Z 281474976710656) with (2 ^ 48) in Hc.
  destruct (fk_ptr_unsigned b rg top off (HM _ _ Hg) H Hc2 Hc1) as [E [B1 B2]].
  pose proof (i63_range off) as Ho. pose proof (i63_range (rg_clo rg)) as Hcl. pose proof (i63_range (rg_chi rg)) as Hch.
  rewrite add_spec, i63_wB in Hc0. rewrite Z.mod_small in Hc0 by (clear - Ho Hcl Hc1 Hc2 B1 B2; lia).
  rewrite add_spec, i63_wB, Z.mod_small in Hc by (clear - Ho Hch Hc1 Hc2; lia).
  rewrite fk_b5_unsigned, E.
  set (x := bv_unsigned (rho b) + to_Z off) in *.
  assert (Hx : 2 ^ 40 <= x < 2 ^ 48) by (clear - Hc0 Hc B1 B2; lia).
  clearbody x. clear - Hx.
  assert (E' : (x / 2 ^ 40) mod 256 = x / 2 ^ 40).
  { apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite E'. assert (1 <= x / 2 ^ 40) by (apply Z.div_le_lower_bound; lia). lia.
Qed.
End Bounds.
