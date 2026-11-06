(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.Lists.List Stdlib.micromega.Lia stdpp.list.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module ListFacts.
(* [comment removed for export] *)

Import Stdlib.Lists.List Stdlib.micromega.Lia.
Import stdpp.list.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.




End ListFacts.
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefEnframeArith.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_and_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_and (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof. intros. unfold v_and. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma v_or_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros. unfold v_or. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma v_andi_lit : forall a i, 0 <= a < 2 ^ 64 -> 0 <= i < 2 ^ 64 ->
  v_andi (Z_to_bv 64 a) i = Z_to_bv 64 (Z.land a i).
Proof.
  intros. unfold v_andi. rewrite u64_lit by lia. rewrite bv_wrap64_mod, Z.mod_small by lia.
  reflexivity.
Qed.

Lemma v_srli_lit : forall a s, 0 <= a < 2 ^ 64 -> 0 <= s ->
  v_srli (Z_to_bv 64 a) s = Z_to_bv 64 (a / 2 ^ s).
Proof. intros. unfold v_srli. rewrite u64_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma v_slli_lit : forall a s, 0 <= a -> 0 <= s -> a * 2 ^ s < 2 ^ 64 ->
  v_slli (Z_to_bv 64 a) s = Z_to_bv 64 (a * 2 ^ s).
Proof.
  intros. unfold v_slli. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
  rewrite u64_lit by nia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma v_mul_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. intros. unfold v_mul. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma v_sltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
  intros. unfold v_sltu, c_ltu, bv_ltu. rewrite !u64_lit by lia.
  destruct (a <? b); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_range : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= a.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
  pose proof (Z.add_lor_land a b). pose proof (Z.lor_nonneg a b).
  assert (Z.land a b <= Z.lor a b).
  { (* [comment removed for export] *)
    apply Z.ldiff_le; [apply Z.lor_nonneg; lia|].
    apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.land_spec, Z.lor_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  (* [comment removed for export] *)
  pose proof (Z.add_lor_land a b).
  assert (Z.land a b = Z.land b a) by apply Z.land_comm.
  assert (b <= Z.lor a b).
  { apply Z.ldiff_le; [apply Z.lor_nonneg; lia|].
    apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.lor_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  lia.
Qed.

Lemma lor_range : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Hk Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
  intros i Hi. rewrite Z.lor_spec.
  rewrite (Z_testbit_high k a i) by lia. rewrite (Z_testbit_high k b i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_not : forall s, 0 <= s < 2 ^ 64 ->
  bv_unsigned (v_xori (Z_to_bv 64 s) (-1)) = 2 ^ 64 - 1 - s.
Proof.
  intros s Hs. unfold v_xori. rewrite (u64_lit s) by lia.
  change (bv_wrap 64 (-1)) with (Z.ones 64).
  assert (E : Z.lxor s (Z.ones 64) = 2 ^ 64 - 1 - s).
  { rewrite <- Z.ldiff_ones_l_low; [| lia |].
    - rewrite Z.ldiff_land.
      rewrite <- Z.sub_land_same_l. rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia.
      rewrite Z.ones_equiv. lia.
    - destruct (Z.eq_dec s 0) as [->|Hz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite E. apply u64_lit. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma swrap32_small : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity.
  replace (2 ^ 32 `div` 2) with (2 ^ 31) by reflexivity. lia.
Qed.

Lemma swrap32_add_mod : forall x k, bv_swrap 32 (x + k * 2 ^ 32) = bv_swrap 32 x.
Proof.
  intros x k. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity. lia.
Qed.

Lemma v_subw_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  - 2 ^ 31 <= a - b < 2 ^ 31 ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros. unfold v_subw. rewrite !u64_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma v_slliw_lit : forall a s, 0 <= a -> 0 <= s -> a * 2 ^ s < 2 ^ 31 ->
  v_slliw (Z_to_bv 64 a) s = Z_to_bv 64 (a * 2 ^ s).
Proof.
  intros. unfold v_slliw. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
  rewrite u64_lit by nia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite swrap32_small by nia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addw_small : forall (x y : word) r,
  - 2 ^ 31 <= r < 2 ^ 31 ->
  (exists k, bv_unsigned x + bv_unsigned y = r + k * 2 ^ 32) ->
  v_addw x y = Z_to_bv 64 r.
Proof.
  intros x y r Hr [k Hk]. unfold v_addw. rewrite Hk, swrap32_add_mod, swrap32_small by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fld_lastidx : forall W, Z.land W 31 = W mod 32.
Proof. intros W. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_126_check :
  zall (N.to_nat 128%N) (fun r => Z.land r 126 =? 2 * ((r / 2) mod 64)) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma land_126 : forall x, 0 <= x -> Z.land x 126 = 2 * ((x / 2) mod 64).
Proof.
  intros x Hx.
  transitivity (Z.land (x mod 128) 126).
  { change 128 with (2 ^ 7). rewrite <- (Z.land_ones x 7) by lia.
    rewrite <- Z.land_assoc. reflexivity. }
  pose proof (zallN_spec _ _ land_126_check (x mod 128) ltac:(cbn; lia)) as E.
  apply Z.eqb_eq in E. rewrite E. f_equal. lia.
Qed.

Lemma fld_sizeclass2 : forall W, 0 <= W -> Z.land (W / 32) 126 = 2 * ((W / 64) mod 64).
Proof. intros W HW. rewrite land_126 by lia. f_equal. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma fld_hi : forall W, 0 <= W < 2 ^ 64 -> Z.land W (2 ^ 64 - 4096) = 4096 * (W / 4096).
Proof.
  intros W HW.
  apply Z.bits_inj'. intros i Hi.
  change (2 ^ 64 - 4096) with (Z.ones 52 * 2 ^ 12).
  rewrite Z.land_spec, Z.mul_pow2_bits, Z.testbit_ones by lia.
  replace (4096 * (W / 4096)) with ((W / 2 ^ 12) * 2 ^ 12) by (change (2 ^ 12) with 4096; lia).
  rewrite Z.mul_pow2_bits by lia.
  destruct (Z.lt_ge_cases i 12) as [Hlt|Hge].
  - rewrite (Z.testbit_neg_r (W / 2 ^ 12)) by lia.
    replace ((0 <=? i - 12) && (i - 12 <? 52))%bool with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    apply andb_false_r.
  - rewrite Z.div_pow2_bits by lia. replace (i - 12 + 12) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [Hlt'|Hge'].
    + replace ((0 <=? i - 12) && (i - 12 <? 52))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply andb_true_r.
    + rewrite (Z_testbit_high 64 W i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_shift5 : forall rc l, 0 <= rc -> 0 <= l < 32 -> Z.lor (rc * 2 ^ 5) l = l + 32 * rc.
Proof.
  intros rc l Hrc Hl.
  pose proof (Z.add_lor_land (rc * 2 ^ 5) l) as E.
  assert (Z : Z.land (rc * 2 ^ 5) l = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.mul_pow2_bits by lia.
    destruct (Z.lt_ge_cases i 5) as [Hlt|Hge].
    - rewrite (Z.testbit_neg_r rc) by lia. reflexivity.
    - rewrite (Z_testbit_high 5 l i) by lia. apply andb_false_r. }
  change (2 ^ 5) with 32 in *. lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma enframe_off_check :
  zall (N.to_nat 65536%N)
    (fun i => let slack := i / 256 in let off0 := i mod 256 in
              let r := enframe_off slack off0 in (0 <=? r) && (r <=? slack))%bool 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.


Lemma enframe_off_le : forall slack off0,
  0 <= slack -> 0 <= off0 < 256 -> 0 <= enframe_off slack off0 <= slack.
Proof.
  intros slack off0 Hs Ho.
  destruct (Z.lt_ge_cases slack 256) as [Hl|Hg].
  - pose proof (zallN_spec _ _ enframe_off_check (slack * 256 + off0) ltac:(cbn; lia)) as E.
    cbv beta zeta in E.
    replace ((slack * 256 + off0) / 256) with slack in E by lia.
    replace ((slack * 256 + off0) mod 256) with off0 in E by lia.
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - unfold enframe_off. rewrite (proj2 (Z.leb_le off0 slack)) by lia. lia.
Qed.


Lemma enframe_off_255 : forall slack off0,
  0 <= slack -> 0 <= off0 < 256 -> enframe_off slack off0 <= 255.
Proof.
  intros slack off0 Hs Ho.
  destruct (Z.le_gt_cases off0 slack) as [Hle|Hgt].
  - unfold enframe_off. rewrite (proj2 (Z.leb_le off0 slack) Hle). lia.
  - pose proof (enframe_off_le slack off0 Hs Ho). lia.
Qed.

Lemma div_range64 : forall a d, 0 <= a < 2 ^ 64 -> 0 < d -> 0 <= a / d < 2 ^ 64.
Proof. intros a d Ha Hd. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. Qed.

Lemma div_le_self : forall a d, 0 <= a -> 0 < d -> 0 <= a / d <= a.
Proof.
  intros a d Ha Hd. split; [apply Z.div_pos; lia|].
  destruct (Z.eq_dec d 1) as [->|Hne]; [rewrite Z.div_1_r; lia|].
  destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.div_0_l by lia; lia|].
  apply Z.lt_le_incl. apply Z.div_lt; lia.
Qed.

Lemma u8_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. cbn. lia. Qed.

Lemma v_andi_255 : forall x : word, v_andi x 255 = Z_to_bv 64 (bv_unsigned x mod 256).
Proof.
  intros x. unfold v_andi. change (bv_wrap 64 255) with (Z.ones 8).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma v_andi_31 : forall x : word, v_andi x 31 = Z_to_bv 64 (bv_unsigned x mod 32).
Proof.
  intros x. unfold v_andi. change (bv_wrap 64 31) with (Z.ones 5).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma v_not_lit : forall s, 0 <= s < 2 ^ 64 ->
  v_xori (Z_to_bv 64 s) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - s).
Proof.
  intros s Hs. rewrite <- (Z_to_bv_bv_unsigned 64 (v_xori (Z_to_bv 64 s) (-1))).
  rewrite u_not by lia. reflexivity.
Qed.

Lemma smear_via_regs : forall S, 0 <= S ->
  let m1 := Z.lor S (S / 2) in
  let m2 := Z.lor (m1 / 4) m1 in
  Z.lor (m2 / 16) m2 = smear S.
Proof.
  intros S HS. cbv zeta. unfold smear.
  rewrite (Z.lor_comm (Z.lor S (S / 2) / 4)).
  rewrite (Z.lor_comm (_ / 16)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma neg_mask : forall (b : bool) K, 0 <= K < 2 ^ 64 ->
  v_and (v_subw (Z_to_bv 64 0) (Z_to_bv 64 (if b then 1 else 0))) (Z_to_bv 64 K)
  = Z_to_bv 64 (if b then K else 0).
Proof.
  intros b K HK. destruct b.
  - rewrite v_subw_lit by lia. rewrite (Z_to_bv_64_mod (0 - 1)).
    change ((0 - 1) mod 2 ^ 64) with (2 ^ 64 - 1).
    rewrite v_and_lit by lia. change (2 ^ 64 - 1) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. reflexivity.
  - rewrite v_subw_lit by lia. rewrite v_and_lit by lia. rewrite Z.land_0_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma addw_mask : forall (b : bool) S om,
  0 <= S < 2 ^ 64 -> 0 <= om < 2 ^ 31 -> (b = true -> S < om) ->
  v_addw (Z_to_bv 64 (if b then 2 ^ 64 - 1 - S else 0)) (Z_to_bv 64 om)
  = Z_to_bv 64 (if b then om - S - 1 else om).
Proof.
  intros b S om HS Hom Hb. destruct b.
  - specialize (Hb eq_refl). apply v_addw_small; [lia|]. exists (2 ^ 32). rewrite !u64_lit by lia.
    change (2 ^ 32 * 2 ^ 32) with (2 ^ 64). lia.
  - apply v_addw_small; [lia|]. exists 0. rewrite !u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_neg : forall e r, 0 <= r <= e -> e < 2 ^ 64 ->
  v_add (Z_to_bv 64 e) (Z_to_bv 64 (0 - r)) = Z_to_bv 64 (e - r).
Proof.
  intros e r Hr He. unfold v_add. rewrite (u64_lit e) by lia.
  rewrite (Z_to_bv_unsigned 64 (0 - r)), bv_wrap64_mod.
  rewrite (Z_to_bv_64_mod (e + (0 - r) mod 2 ^ 64)). rewrite Z.add_mod_idemp_r by lia.
  rewrite <- Z_to_bv_64_mod. f_equal; lia.
Qed.

Lemma c_lts_lit : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !bv_signed_small by lia. reflexivity. Qed.
End RefEnframeArith.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare RefEnframeArith.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Definition swar_smear (x : word) : word :=
  let a1 := v_or x (v_srli x 1) in
  let a1 := v_or a1 (v_srli a1 2) in
  let a1 := v_or a1 (v_srli a1 4) in
  let a1 := v_or a1 (v_srli a1 8) in
  let a1 := v_or a1 (v_srli a1 16) in
  v_or a1 (v_srli a1 32).
(* [comment removed for export] *)
Definition swar_pop (a1 : word) : word :=
  let c5 := v_addiw (v_lui 0x55555000) 1365 in
  let c3 := v_addiw (v_lui 0x33333000) 819 in
  let cf := v_addiw (v_lui 0x0f0f1000) (-241) in
  let c5 := v_add c5 (v_slli c5 32) in
  let c3 := v_add c3 (v_slli c3 32) in
  let cf := v_add cf (v_slli cf 32) in
  let a1 := v_xori a1 (-1) in
  let a1 := v_sub a1 (v_and (v_srli a1 1) c5) in
  let a2 := v_and (v_srli a1 2) c3 in
  let a1 := v_and a1 c3 in
  let c1 := v_addiw (v_lui 0x01010000) 257 in
  let a1 := v_add a1 a2 in
  let a1 := v_add a1 (v_srli a1 4) in
  let a1 := v_and a1 cf in
  let c1 := v_add c1 (v_slli c1 32) in
  v_srli (v_mul a1 c1) 56.
Definition swar_clz (x : word) : word := swar_pop (swar_smear x).

(* [comment removed for export] *)
Definition top_set (y k m : Z) : Prop :=
  (forall i, k < i -> Z.testbit y i = false) /\ (forall i, 0 <= i -> k + 1 - m <= i <= k -> Z.testbit y i = true).

Lemma top_set_step : forall y k m, 0 <= k -> 0 < m -> 0 <= y -> top_set y k m -> top_set (Z.lor y (Z.shiftr y m)) k (2 * m).
Proof.
  intros y k m Hk Hm Hy [HA HB]. split.
  - intros i Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite HA by lia. rewrite HA by lia. reflexivity.
  - intros i Hi0 Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia.
    destruct (Z_le_gt_dec (k + 1 - m) i) as [L|G].
    + rewrite HB by lia. reflexivity.
    + rewrite (HB (i + m)) by lia. apply Bool.orb_true_r.
Qed.

Lemma top_set_all : forall y k m, 0 <= k -> k + 1 <= m -> 0 <= y -> top_set y k m -> y = 2 ^ (k + 1) - 1.
Proof.
  intros y k m Hk Hm Hy [HA HB]. replace (2 ^ (k + 1) - 1) with (Z.ones (k + 1)) by (rewrite Z.ones_equiv; lia).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i (k + 1)) as [L|G].
  - rewrite Z.ones_spec_low by lia. apply HB; lia.
  - rewrite Z.ones_spec_high by lia. apply HA; lia.
Qed.
Lemma top_set_init : forall y k, 0 <= k -> 2 ^ k <= y < 2 ^ (k + 1) -> top_set y k 1.
Proof.
  intros y k Hk Hy. assert (L : Z.log2 y = k) by (apply Z.log2_unique; lia). split.
  - intros i Hi. apply Z.bits_above_log2; lia.
  - intros i Hi0 Hi. replace i with k by lia. rewrite <- L. apply Z.bit_log2. lia.
Qed.

(* [comment removed for export] *)
Lemma u_or_srli : forall (a : word) m, 0 <= m -> U (v_or a (v_srli a m)) = Z.lor (U a) (Z.shiftr (U a) m).
Proof.
  intros a m Hm. pose proof (u64_range a) as Ha.
  assert (S1 : 0 <= Z.shiftr (U a) m < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with (U a); [|lia]. apply Z.div_le_upper_bound; [lia|]. pose proof (Z.pow_pos_nonneg 2 m ltac:(lia) Hm). nia. }
  (lazymatch goal with |- ?G => let G' := eval unfold v_or, v_srli in G in change_no_check G' end). rewrite (u_Z2bv (Z.shiftr (U a) m)) by lia.
  apply u_Z2bv; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor (U a) (Z.shiftr (U a) m)) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg (U a) (Z.shiftr (U a) m)); lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - destruct (Z.eq_dec (U a) 0) as [E|NE]; [rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec (Z.shiftr (U a) m) 0) as [E|NE]; [rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | apply Z.log2_lt_pow2; lia].
Qed.

Lemma swar_smear_ones : forall (x : word) k, 0 <= k <= 63 -> 2 ^ k <= U x < 2 ^ (k + 1) -> swar_smear x = Z_to_bv 64 (2 ^ (k + 1) - 1).
Proof.
  intros x k Hk Hx. (lazymatch goal with |- ?G => let G' := eval unfold swar_smear in G in change_no_check G' end).
  set (a1 := v_or x (v_srli x 1)). set (a2 := v_or a1 (v_srli a1 2)). set (a3 := v_or a2 (v_srli a2 4)).
  set (a4 := v_or a3 (v_srli a3 8)). set (a5 := v_or a4 (v_srli a4 16)). set (a6 := v_or a5 (v_srli a5 32)).
  pose proof (top_set_init (U x) k ltac:(lia) Hx) as T0.
  assert (T1 : top_set (U a1) k 2) by ((lazymatch goal with |- ?G => let G' := eval unfold a1 in G in change_no_check G' end); rewrite u_or_srli by lia; apply (top_set_step _ k 1); [lia | lia | pose proof (u64_range x); lia | exact T0]).
  assert (T2 : top_set (U a2) k 4) by ((lazymatch goal with |- ?G => let G' := eval unfold a2 in G in change_no_check G' end); rewrite u_or_srli by lia; apply (top_set_step _ k 2); [lia | lia | pose proof (u64_range a1); lia | exact T1]).
  assert (T3 : top_set (U a3) k 8) by ((lazymatch goal with |- ?G => let G' := eval unfold a3 in G in change_no_check G' end); rewrite u_or_srli by lia; apply (top_set_step _ k 4); [lia | lia | pose proof (u64_range a2); lia | exact T2]).
  assert (T4 : top_set (U a4) k 16) by ((lazymatch goal with |- ?G => let G' := eval unfold a4 in G in change_no_check G' end); rewrite u_or_srli by lia; apply (top_set_step _ k 8); [lia | lia | pose proof (u64_range a3); lia | exact T3]).
  assert (T5 : top_set (U a5) k 32) by ((lazymatch goal with |- ?G => let G' := eval unfold a5 in G in change_no_check G' end); rewrite u_or_srli by lia; apply (top_set_step _ k 16); [lia | lia | pose proof (u64_range a4); lia | exact T4]).
  assert (T6 : top_set (U a6) k 64) by ((lazymatch goal with |- ?G => let G' := eval unfold a6 in G in change_no_check G' end); rewrite u_or_srli by lia; apply (top_set_step _ k 32); [lia | lia | pose proof (u64_range a5); lia | exact T5]).
  rewrite <- (top_set_all (U a6) k 64 ltac:(lia) ltac:(lia) ltac:(pose proof (u64_range a6); lia) T6).
  symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma swar_pop_ones : forall k : nat, (k <= 63)%nat -> swar_pop (Z_to_bv 64 (2 ^ (Z.of_nat k + 1) - 1)) = Z_to_bv 64 (63 - Z.of_nat k).
Proof.
  intros k Hk. do 64 (destruct k as [|k]; [apply bv_eq; vm_compute; reflexivity|]). lia.
Qed.

Theorem swar_clz_log2 : forall (x : word) k, 0 <= k <= 63 -> 2 ^ k <= U x < 2 ^ (k + 1) -> swar_clz x = Z_to_bv 64 (63 - k).
Proof.
  intros x k Hk Hx. (lazymatch goal with |- ?G => let G' := eval unfold swar_clz in G in change_no_check G' end). rewrite (swar_smear_ones x k Hk Hx).
  replace k with (Z.of_nat (Z.to_nat k)) by lia. apply swar_pop_ones. lia.
Qed.

Theorem swar_clz_bound : forall x : word, 0 < U x -> 0 <= U (swar_clz x) <= 63.
Proof.
  intros x Hx. pose proof (u64_range x) as Hr.
  pose proof (Z.log2_spec (U x) Hx) as [L1 L2]. pose proof (Z.log2_nonneg (U x)) as L0.
  assert (L3 : Z.log2 (U x) <= 63).
  { destruct (Z_le_gt_dec (Z.log2 (U x)) 63) as [L|G]; [exact L|]. exfalso.
    assert (2 ^ 64 <= 2 ^ Z.log2 (U x)) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite (swar_clz_log2 x (Z.log2 (U x)) ltac:(lia) ltac:(replace (Z.log2 (U x) + 1) with (Z.succ (Z.log2 (U x))) by lia; lia)).
  rewrite u_Z2bv by lia. lia.
Qed.
