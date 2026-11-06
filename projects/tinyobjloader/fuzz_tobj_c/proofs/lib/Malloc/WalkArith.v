(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "modulo"; "land"; "mul"; "add"; "shiftr"; "sub"; "lor"; "lxor"; "opp"; "to_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "sx32"; "zalu"; "zeval"; "zle"; "zsublist"; "zsupported"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "ctz_tab_bytes"; "size_classes_bytes"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "lowbit"; "ones"; "ctz32"; "size_classes"; "znth"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLemmasBase MallocLayout MallocWfSlot ZEval ZBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Local Open Scope Z_scope.

Open Scope Z_scope.

Lemma ctz_tab_bytes_range : ltac2:(tb__ "0|0|
S19S0S0SfS2Z0R1A2S3R1Z100A2A2Lb;S1bA3").
Proof.
  apply Forall_forall. intros b Hb.
  assert (H : forallb (fun b => (0 <=? b) && (b <? 256))%bool ctz_tab_bytes = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H b Hb) as Hb'. apply andb_prop in Hb' as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma zl_ctz : ltac2:(tb__ "0|2|
S10S1dS0A1S18S27Q8M0A1M1S0G1S26G0R1A2Lb;S18S0G1S25G0A1S1bA4A4S1bA3").
Proof.
  rewrite map_map. rewrite <- (map_id ctz_tab_bytes) at 2. apply map_ext_in.
  intros b Hb. pose proof (proj1 (Forall_forall _ _) ctz_tab_bytes_range b Hb) as R.
  cbn beta in R. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= b < 256). lia.
Qed.

Lemma ctz_lookup : ltac2:(tb__ "0|2|
S0SfS2Z0R1A2S3R1Z20M0A2A2S10S0S1aS0SeS9S5S7S4Z2M1R2A2Z77cb531A2S4G1G0A2A2Z1bA2A1S1bZ63A4R2A3F_;Fk;").
Proof.
  intros k Hk.
  pose proof (forall_range_dec (fun k => nth (Z.to_nat (Z.shiftr ((2 ^ k * 0x077cb531) mod 2 ^ 32) 27)) ctz_tab_bytes 99 =? k) 0 32
                ctz_tab_ok k Hk) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma bitop_range : ltac2:(tb__ "0|6|
S0S0SfS2Z0M0R2A2S3R2S4Z2Z40A2M1A2A2M2G2SfSfS2G0S6R4R3A2M3A2S3G3G1A2A2SfSfS2G0SbR4R3A2M4A2S3G4G1A2A2SfS2G0ScR4R3A2M5A2S3G5G1A2A2A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb.
  assert (La : Z.log2 a < 64). { destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  assert (Lb : Z.log2 b < 64). { destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  pose proof (Z.land_nonneg a b). pose proof (Z.lor_nonneg a b). pose proof (Z.lxor_nonneg a b).
  pose proof (Z.log2_land a b). pose proof (Z.log2_lor a b). pose proof (Z.log2_lxor a b).
  assert (UP : forall x, 0 <= x -> Z.log2 x < 64 -> x < 2 ^ 64).
  { intros x Hx Hl. destruct (Z.eq_dec x 0) as [->|]; [lia|]. apply Z.log2_lt_pow2; lia. }
  repeat split; try lia; apply UP; lia.
Qed.

Lemma zeval_range : ltac2:(tb__ "0|1|
S1S0F_;S1S1dS0A1F_;S2aS10S1eS17R1A1S1fA3SfS2Z0S14R4R3R2A3M0A2S3G0S4Z2Z40A2A2A2F_;Fe;Fzl;Fzr;").
Proof.
  intros zr zl e. induction e; cbn [zsupported zeval]; intros Hs.
  - apply Z.mod_pos_bound. lia.
  - apply Z.mod_pos_bound. lia.
  - apply andb_prop in Hs as [H1 H2]. specialize (IHe1 H1). specialize (IHe2 H2).
    set (a := zeval zr zl e1) in *. set (b := zeval zr zl e2) in *.
    destruct op; cbn [zalu]; try (apply Z.mod_pos_bound; lia).
    + destruct (toS 64 a <? toS 64 b); lia.
    + destruct (a mod 2 ^ 64 <? b mod 2 ^ 64); lia.
    + rewrite !Z.mod_small by lia. apply bitop_range; lia.
    + rewrite Z.mod_small by lia. split; [apply Z.shiftr_nonneg; lia|].
      rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; [lia | apply Z.mod_pos_bound; lia]|].
      pose proof (Z.pow_le_mono_r 2 0 (b mod 64) ltac:(lia) ltac:(apply Z.mod_pos_bound; lia)). nia.
    + rewrite !Z.mod_small by lia. apply bitop_range; lia.
    + rewrite !Z.mod_small by lia. apply bitop_range; lia.
  - unfold sx32. apply Z.mod_pos_bound. lia.
  - destruct op; try discriminate. apply Z.mod_pos_bound. lia.
  - destruct op; try discriminate. unfold sx32. apply Z.mod_pos_bound. lia.
  - apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2.
    destruct sgn; [apply Z.mod_pos_bound; lia|].
    pose proof (Z.mod_pos_bound (zeval zr zl e) (2 ^ Z.of_N w) ltac:(apply Z.pow_pos_nonneg; lia)).
    pose proof (Z.pow_le_mono_r 2 (Z.of_N w) 64 ltac:(lia) H2). lia.
  - apply Z.mod_pos_bound. lia.
Qed.

Lemma ones_range k : ltac2:(tb__ "0|2|
SfS2Z0M0Vk;A2S2Vk;Z1fA2A2SfS3G0S21Vk;A1M1A2S2G1SaS4Z2Z20A2Z1A2A2A2F_;").
Proof.
  intros Hk. unfold ones. assert (2 ^ (k + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ 1 <= 2 ^ (k + 1)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 1) with 2 in *. lia.
Qed.

Lemma sx32_inj a b : ltac2:(tb__ "0|2|
SfS2Z0M0Va;A2S3Va;S4Z2Z20A2M1A2A2SfS2G0Vb;A2S3Vb;G1A2A2S10S0S12Va;A1S12Vb;A1A3S10S0Va;Vb;A3F_;F_;F_;").
Proof.
  intros Ha Hb E. unfold sx32, toS in E. rewrite (Z.mod_small a) in E by lia. rewrite (Z.mod_small b) in E by lia.
  change (2 ^ (32 - 1)) with (2 ^ 31) in E.
  destruct (a <? 2 ^ 31) eqn:Ea, (b <? 2 ^ 31) eqn:Eb;
    first [apply Z.ltb_lt in Ea | apply Z.ltb_ge in Ea]; first [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb];
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma sx32_zero a : ltac2:(tb__ "0|1|
SfS2Z0M0Va;A2S3Va;S4Z2Z20A2A2A2S11S10S0S12Va;A1G0A3S10S0Va;G0A3A2F_;").
Proof.
  intros Ha. split; intros E.
  - apply (sx32_inj a 0 Ha ltac:(lia)). rewrite E. reflexivity.
  - subst a. reflexivity.
Qed.

Lemma sx32_range a : ltac2:(tb__ "0|1|
SfS2Z0S12Va;A1M0A2S3G0S4Z2Z40A2A2A2").
Proof. unfold sx32. apply Z.mod_pos_bound. lia. Qed.

Lemma sx32_mod32_any x : ltac2:(tb__ "0|1|
S2Z0Vx;A2S10S0S5S12Vx;A1S4Z2Z20A2M0A2S5Vx;G0A2A3F_;").
Proof.
  intros Hx. unfold sx32. rewrite <- Znumtheory.Zmod_div_mod; [|lia|lia|exists (2 ^ 32); reflexivity].
  apply toS_mod_back. lia.
Qed.

Lemma u64 : ltac2:(tb__ "0|1|
S0SfS2Z0R1A2S3R1S4Z2Z40A2A2A2S10S0S26Q40M0S25G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.
Lemma m64 : ltac2:(tb__ "0|1|
S0SfS2Z0R1A2S3R1S4Z2Z40A2M0A2A2S10S0S5R2G0A2R2A3F_;Fz;").
Proof. intros z Hz. apply Z.mod_small. exact Hz. Qed.

Lemma size_classes_bytes_range : ltac2:(tb__ "0|0|
S19S0S0SfS2Z0R1A2S3R1Z100A2A2Lb;S1cA3").
Proof.
  apply Forall_forall. intros b Hb.
  assert (H : forallb (fun b => (0 <=? b) && (b <? 256))%bool size_classes_bytes = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H b Hb) as Hb'. apply andb_prop in Hb' as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma zl_table : ltac2:(tb__ "0|2|
S10S1dS0A1S18S27Q8M0A1M1S0G1S26G0R1A2Lb;S18S0G1S25G0A1S1cA4A4S1cA3").
Proof.
  rewrite map_map. rewrite <- (map_id size_classes_bytes) at 2. apply map_ext_in.
  intros b Hb. pose proof (proj1 (Forall_forall _ _) size_classes_bytes_range b Hb) as R.
  cbn beta in R. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (0 <= b < 256). lia.
Qed.

Lemma table_u16 : ltac2:(tb__ "0|1|
S0SfS2Z0R1A2S3R1Z30A2A2S10S0S15S16S7Z2M0R2A2G0S1cA3A1S24R2S23A2A3F_;Fsc;").
Proof.
  intros sc Hsc.
  pose proof (forall_range_dec (fun sc => zle (zsublist (2 * sc) 2 size_classes_bytes) =? znth sc size_classes) 0 48
                ltac:(vm_compute; reflexivity) sc ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma znth_size_classes_range : ltac2:(tb__ "0|1|
S0SfS2Z0R1A2S3R1Z30A2A2SfS2Z1S24R2S23A2M0A2S2G0Z1fffA2A2F_;Fsc;").
Proof.
  intros sc Hsc.
  pose proof (forall_range_dec (fun sc => (1 <=? znth sc size_classes) && (znth sc size_classes <=? 8191))%bool 0 48
                ltac:(vm_compute; reflexivity) sc ltac:(lia)) as H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma land_126_odd : ltac2:(tb__ "0|2|
S0S0SfS2Z0R2A2M0S3R2Z30A2A2G0S10S0S6S8S8Z1S7Z2R4A2M1A2S7Z80R3A2A2Z7eA2G1A3F_;F_;Fm;Fsc;").
Proof.
  intros sc m Hsc Hm.
  rewrite (land_low_congr (1 + 2 * sc + 128 * m) (1 + 2 * sc) 126 7); [| lia | cbn; lia | change (2 ^ 7) with 128; lia].
  pose proof (forall_range_dec (fun sc => Z.land (1 + 2 * sc) 126 =? 2 * sc) 0 48 ltac:(vm_compute; reflexivity) sc ltac:(lia)) as H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma land_neg_mod32 : ltac2:(tb__ "0|1|
S0SfS3Z0R1A2S3R1S4Z2Z20A2M0A2A2S10S0S6R2S5SdR2A1G0A2A2S20R2A1A3F_;Fm;").
Proof.
  intros m Hm. unfold lowbit. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_dec i 32).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_false_of_lt m 32 i) by lia. reflexivity.
Qed.

Lemma lowbit_range m : ltac2:(tb__ "0|2|
SfS3Z0M0Vm;A2S3Vm;S4Z2Z20A2A2A2SfS3G0S20Vm;A1M1A2S2G1Vm;A2A2F_;").
Proof.
  intros Hm. destruct (lowbit_spec m ltac:(lia)) as (k & Hk & Hl & Hb & _).
  rewrite Hl. unfold bit. split; [apply Z.pow_pos_nonneg; lia|].
  destruct (Z_le_dec (2 ^ k) m) as [|H]; [assumption|]. exfalso.
  rewrite (testbit_false_of_lt m k k) in Hb; [discriminate| |lia]. split; [lia|]. lia.
Qed.

Lemma ctz32_lowbit m : ltac2:(tb__ "0|0|
S3Z0Vm;A2S10S0S22S20Vm;A1A1S22Vm;A1A3F_;").
Proof.
  intros Hm. destruct (lowbit_spec m Hm) as (k & Hk & Hl & _). unfold ctz32. rewrite Hl.
  f_equal. destruct (lowbit_spec (bit k) ltac:(unfold bit; apply Z.pow_pos_nonneg; lia)) as (k' & Hk' & Hl' & Hb' & _).
  rewrite Hl'. rewrite testbit_bit in Hb' by lia. apply Z.eqb_eq in Hb'. subst k'. reflexivity.
Qed.

Lemma land_sx32_r a b : ltac2:(tb__ "0|2|
SfS2Z0M0Va;A2S3Va;S4Z2Z20A2M1A2A2S2G0Vb;A2S10S0S6Va;S12Vb;A1A2S6Va;S5Vb;G1A2A2A3F_;F_;").
Proof.
  intros Ha Hb. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_dec i 32).
  - f_equal. rewrite <- (Z.mod_pow2_bits_low (sx32 b) 32 i) by lia. rewrite sx32_mod32_any by lia.
    reflexivity.
  - rewrite (testbit_false_of_lt a 32 i) by lia. reflexivity.
Qed.

Lemma ones_w_val k : ltac2:(tb__ "0|3|
S2Z0Vk;A2S10S0S12S13Z20M0S28S5S12S13G0S29Z2M1S5Vk;S4G1G0A2M2A2A4A1G2A2SaG2Z1A2A4A1S12S21S5Vk;G0A2A1A1A3F_;").
Proof.
  intros Hk. cbn [zalu]. rewrite sx32_mod32_any by lia.
  replace ((k mod 2 ^ 32) mod 32) with (k mod 32)
    by (rewrite <- Znumtheory.Zmod_div_mod; [reflexivity|lia|lia|exists (2 ^ 27); reflexivity]).
  pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as M.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_mod by lia.
  f_equal.
  unfold ones. replace (2 * 2 ^ (k mod 32)) with (2 ^ (k mod 32 + 1)) by (rewrite Z.pow_add_r by lia; lia).
  destruct (Z.eq_dec (k mod 32) 31) as [E|NE].
  - rewrite E. reflexivity.
  - assert (2 ^ (k mod 32 + 1) < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
    assert (0 < 2 ^ (k mod 32 + 1)) by (apply Z.pow_pos_nonneg; lia).
    rewrite (Z.mod_small (2 ^ (k mod 32 + 1))) by lia.
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma ones_u32 k : ltac2:(tb__ "0|2|
SfS2Z0M0Vk;A2S2Vk;Z1fA2A2SfS3G0S21Vk;A1M1A2S3G1S4Z2Z20A2A2A2F_;").
Proof. intros Hk. pose proof (ones_range k Hk). lia. Qed.

Lemma dbidx_lt32 x : ltac2:(tb__ "0|2|
SfS2Z0S9S5Vx;S4Z2Z20M0A2A2Z1bA2M1A2S3G1G0A2A2").
Proof.
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)) as M.
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  change (2 ^ 27 * 32) with (2 ^ 32). lia.
Qed.
