(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "le"; "lt"; "testbit"; "add"; "land"; "sub"; "lor"; "modulo"; "ltb"; "of_nat"; "div"; "mul"; "ones"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "sx32"; "toS"; "@Corelib.Init.Datatypes"; "bool"; "nat"; "false"; "true"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ZEval.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma toS32_cases : ltac2:(tb__ "0|5|
S0S10S2Z0R1A2S3R1S1Z2M0Z20M1A2M2A2A2S12S10S3R2S1G0Z1fA2M3A2SfS0S14G1R2A2M4R2A3A2S10S2G3R2A2SfS0G4S7R2G2A2A3A2A2F_;Fx;").
Proof.
  intros x Hx. unfold toS. rewrite Z.mod_small by lia. change (2 ^ (32 - 1)) with (2 ^ 31).
  destruct (x <? 2 ^ 31) eqn:E; [apply Z.ltb_lt in E; left | apply Z.ltb_ge in E; right]; lia.
Qed.

Lemma sx32_small : ltac2:(tb__ "0|0|
S0S10S2Z0R1A2S3R1S1Z2Z1fA2A2A2SfS0S13R2A1R2A3F_;Fx;").
Proof.
  intros x Hx. unfold sx32. destruct (toS32_cases x ltac:(lia)) as [[_ ->]|[? _]]; [|lia].
  apply Z.mod_small. lia.
Qed.

Lemma sx32_big : ltac2:(tb__ "0|2|
S0S10S2S1Z2M0Z1fA2R1A2S3R1S1G0Z20A2M1A2A2SfS0S13R2A1S7S5R2S1G0Z40A2A2G1A2A3F_;Fx;").
Proof.
  intros x Hx. unfold sx32. destruct (toS32_cases x ltac:(lia)) as [[? _]|[_ ->]]; [lia|].
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma div_near_top : ltac2:(tb__ "0|2|
S0S0S0S10S2Z0M0R2A2S2R2R3A2A2S10S3G0R2A2S2R2S1Z2M1R3A2A2A2SfS0ScS7S1G1R5A2R3A2S1G1R4A2A2S7S1G1S7R5R4A2A2Z1A2A3F_;F_;Fr;Fn;FN;").
Proof.
  intros N n r Hn Hr.
  assert (P : 2 ^ N = 2 ^ n * 2 ^ (N - n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  symmetry. apply (Z.div_unique _ _ _ (2 ^ n - r)); [left; lia|]. rewrite P. nia.
Qed.

Lemma testbit_add_mul_high : ltac2:(tb__ "0|1|
S0S0S0S0S2Z0R4A2M0G0S10G0S3R4R3A2A2SfS15S4S5R7SdR6S1Z2R4A2A2A2R5A2S4R7R5A2A3F_;F_;F_;Fk;Fn;Fc;Fx;").
Proof.
  intros x c n k Hx Hc Hn.
  rewrite <- (Z.mod_pow2_bits_low (x + c * 2 ^ k) k n) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma sx32_testbit : ltac2:(tb__ "0|3|
S0S0S10S2Z0R2A2M0S3R2S1Z2Z20M1A2A2A2G0SfS15S4S13R4A1R3A2S15S15L_;M2SaR3G1A2S4R4R3A2G2SaR3Z40A2S4R4Z1fA2S17X15x2X15x2A3F_;F_;Fn;Fx;").
Proof.
  intros x n Hx Hn.
  destruct (Z_lt_dec x (2 ^ 31)) as [Hs|Hb].
  - rewrite sx32_small by lia.
    destruct (n <? 32) eqn:E32; [reflexivity|]. apply Z.ltb_ge in E32.
    rewrite (testbit_high_small x 31 n) by lia.
    destruct (n <? 64); [|reflexivity]. symmetry. apply (testbit_high_small x 31 31); lia.
  - rewrite sx32_big by lia.
    assert (T31 : Z.testbit x 31 = true).
    { rewrite Z.testbit_true by lia. replace (x / 2 ^ 31) with 1; [reflexivity|].
      apply (Z.div_unique _ _ _ (x - 2 ^ 31)); [left; lia | lia]. }
    destruct (n <? 32) eqn:E32.
    + apply Z.ltb_lt in E32.
      replace (x + 2 ^ 64 - 2 ^ 32) with (x + (2 ^ 32 - 1) * 2 ^ 32) by lia.
      apply testbit_add_mul_high; lia.
    + apply Z.ltb_ge in E32. rewrite T31.
      destruct (n <? 64) eqn:E64.
      * apply Z.ltb_lt in E64. rewrite Z.testbit_true by lia.
        replace (x + 2 ^ 64 - 2 ^ 32) with (2 ^ 64 - (2 ^ 32 - x)) by lia.
        rewrite (div_near_top 64 n (2 ^ 32 - x)); [|lia|].
        2:{ split; [lia|]. apply Z.le_trans with (2 ^ 32); [lia|]. apply Z.pow_le_mono_r; lia. }
        assert (P2 : 2 ^ (64 - n) = 2 * 2 ^ (64 - n - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
        rewrite P2. replace (2 * 2 ^ (64 - n - 1) - 1) with (1 + (2 ^ (64 - n - 1) - 1) * 2) by lia.
        rewrite Z.mod_add by lia. reflexivity.
      * apply Z.ltb_ge in E64. apply (testbit_high_small _ 64); lia.
Qed.

Lemma sx32_range : ltac2:(tb__ "0|3|
S0S10S2Z0M0R1A2S3R1S1Z2M1Z20A2A2A2S10S2G0S13R2A1M2A2S3G2S1G1Z40A2A2A2F_;Fx;").
Proof. intros x Hx. unfold sx32. apply Z.mod_pos_bound. lia. Qed.

Lemma sx32_land : ltac2:(tb__ "0|1|
S0S0S10S2Z0R2A2S3R2S1Z2Z20A2A2A2M0G0SfS0S6S13R4A1S13R3A1A2S13S6R4R3A2A1A3F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. pose proof (land_bound a b 32 ltac:(lia) Hb) as Hab.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !sx32_testbit by lia.
  destruct (n <? 32); [apply eq_sym, Z.land_spec|]. destruct (n <? 64); [apply eq_sym, Z.land_spec| reflexivity].
Qed.

Lemma lor_bound32 : ltac2:(tb__ "0|4|
S0S0S10S2Z0M0R2A2S3R2S1Z2Z20A2M1A2A2M2G2S10S2G0S8R4R3A2M3A2S3G3G1A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply (proj2 (Z.bounded_iff_bits_nonneg 32 (Z.lor a b) ltac:(lia) ltac:(apply Z.lor_nonneg; lia))).
  intros m Hm. rewrite Z.lor_spec, (testbit_high_small a 32 m), (testbit_high_small b 32 m) by lia. reflexivity.
Qed.

Lemma sx32_lor : ltac2:(tb__ "0|1|
S0S0S10S2Z0R2A2S3R2S1Z2Z20A2A2A2M0G0SfS0S8S13R4A1S13R3A1A2S13S8R4R3A2A1A3F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. pose proof (lor_bound32 a b Ha Hb) as Hab.
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !sx32_testbit by lia.
  destruct (n <? 32); [apply eq_sym, Z.lor_spec|]. destruct (n <? 64); [apply eq_sym, Z.lor_spec| reflexivity].
Qed.

Lemma sx32_zero_iff : ltac2:(tb__ "0|1|
S0S10S2Z0M0R1A2S3R1S1Z2Z20A2A2A2S11SfS0S13R2A1G0A3SfS0R2G0A3A2F_;Fx;").
Proof.
  intros x Hx. destruct (Z_lt_dec x (2 ^ 31)) as [Hs|Hb].
  - rewrite sx32_small by lia. tauto.
  - rewrite sx32_big by lia. split; intros; lia.
Qed.

Lemma sx32_inj : ltac2:(tb__ "0|1|
S0S0S10S2Z0R2A2S3R2S1Z2Z20A2A2A2M0G0SfS0S13R4A1S13R3A1A3SfS0R5R4A3F_;F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb E.
  destruct (Z_lt_dec a (2 ^ 31)) as [A|A], (Z_lt_dec b (2 ^ 31)) as [B|B].
  - rewrite (sx32_small a), (sx32_small b) in E by lia. lia.
  - rewrite (sx32_small a), (sx32_big b) in E by lia. lia.
  - rewrite (sx32_big a), (sx32_small b) in E by lia. lia.
  - rewrite (sx32_big a), (sx32_big b) in E by lia. lia.
Qed.

Lemma sx32_mod32 : ltac2:(tb__ "0|1|
S0S10S2Z0R1A2S3R1S1Z2Z20A2M0A2A2SfS0S9S13R2A1G0A2R2A3F_;Fx;").
Proof.
  intros x Hx. destruct (Z_lt_dec x (2 ^ 31)).
  - rewrite sx32_small by lia. apply Z.mod_small. lia.
  - rewrite sx32_big by lia. replace (x + 2 ^ 64 - 2 ^ 32) with (x + (2 ^ 32 - 1) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma land_ones_low : ltac2:(tb__ "0|0|
S0S0S2Z0R1A2SfS0S6R3SeR2A1A2S9R3S1Z2R2A2A2A3F_;Fn;Fx;").
Proof. intros. apply Z.land_ones. assumption. Qed.

Lemma land_31 : ltac2:(tb__ "0|0|
S0SfS0S6R1Z1fA2S9R1Z20A2A3Fx;").
Proof. intros. change 31 with (Z.ones 5). apply Z.land_ones. lia. Qed.

Lemma land_pow2_testbit : ltac2:(tb__ "0|3|
S0S0S2Z0M0R2A2M1G1SfS0S6R4S1Z2R3A2M2A2S15S0L_;S4R4R3A2G2G0X15x2A3F_;F_;Fk;Fx;").
Proof.
  intros x k Hx Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k n) as [<-|Hne].
  - destruct (Z.testbit x k) eqn:E; [rewrite Z.pow2_bits_true by lia; reflexivity | rewrite Z.bits_0; reflexivity].
  - rewrite Bool.andb_false_r. destruct (Z.testbit x k); [rewrite Z.pow2_bits_false by lia | rewrite Z.bits_0]; reflexivity.
Qed.

Lemma lor_add_disjoint_bit : ltac2:(tb__ "0|2|
S0S0S2Z0R2A2M0G0SfS15S4R4R3A2S17A3SfS0S5R5S1Z2R4A2M1A2S8R5G1A2A3F_;F_;F_;Fk;Fm;").
Proof.
  intros m k Hm Hk Hb.
  assert (HL : Z.land m (2 ^ k) = 0) by (rewrite land_pow2_testbit by lia; rewrite Hb; reflexivity).
  rewrite <- Z.lxor_lor by exact HL. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma forall_range_dec : ltac2:(tb__ "0|0|
S0S15F_;S0S16SfS15S1bS0R3S19S16S0S16S5R3SbR1A1A2Lk;S1aU0R1A2A4A3S18A3S0S10S2R4R1A2S3R1S5R4SbR3A1A2A2A2SfS15R6R2A1S18A3F_;Fx;F_;Fn;Flo;FP;").
Proof.
  intros P lo n H x Hx.
  apply (proj1 (forallb_forall _ _) H x). apply in_map_iff. exists (Z.to_nat (x - lo)).
  split; [lia|]. apply in_seq. lia.
Qed.
