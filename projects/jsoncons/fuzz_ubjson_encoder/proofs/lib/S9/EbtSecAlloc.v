(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac EbtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r41498_42984 Eb0_code_r731ac_733ac Eb0_code_r73d7c_73f88 Eb0_code_r719b0_719e8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma sa_testbit_drop_low : forall q r j i, (0 <= j)%Z -> (0 <= r < 2 ^ j)%Z -> (j <= i)%Z ->
  Z.testbit (q * 2 ^ j + r) i = Z.testbit (q * 2 ^ j) i.
Proof.
  intros q r j i Hj Hr Hi.
  replace i with ((i - j) + j)%Z by lia.
  rewrite <- !Z.div_pow2_bits by lia.
  f_equal. rewrite Z.div_add_l by lia. rewrite (Z.div_small r) by lia.
  rewrite Z_div_mult by lia. lia.
Qed.

Lemma sa_testbit_mask : forall k j i, (0 <= j <= k)%Z -> (0 <= i)%Z ->
  Z.testbit (2 ^ k - 2 ^ j) i = ((j <=? i) && (i <? k))%Z%bool.
Proof.
  intros k j i Hjk Hi.
  replace (2 ^ k - 2 ^ j)%Z with (Z.ones (k - j) * 2 ^ j)%Z.
  2:{ unfold Z.ones. rewrite Z.shiftl_1_l, <- Z.sub_1_r, Z.mul_sub_distr_r, <- Z.pow_add_r by lia. replace (k - j + j)%Z with k by lia. lia. }
  destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
  - rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
  - rewrite Z.mul_pow2_bits by lia. replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.lt_ge_cases i k) as [Hk|Hk].
    + rewrite Z.ones_spec_low by lia. symmetry. apply Z.ltb_lt. lia.
    + rewrite Z.ones_spec_high by lia. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma sa_land_down : forall k j x, (0 <= j <= k)%Z -> (0 <= x < 2 ^ k)%Z -> Z.land x (2 ^ k - 2 ^ j) = (x - x mod 2 ^ j)%Z.
Proof.
  intros k j x Hjk Hx.
  assert (Hp : (0 < 2 ^ j)%Z) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod x (2 ^ j) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x (2 ^ j) Hp) as Hm.
  set (q := (x / 2 ^ j)%Z) in *. set (r := (x mod 2 ^ j)%Z) in *.
  replace (x - r)%Z with (q * 2 ^ j)%Z by lia.
  rewrite Hdm. replace (2 ^ j * q + r)%Z with (q * 2 ^ j + r)%Z by lia.
  assert (Hq : (0 <= q)%Z) by lia.
  assert (Hqk : (q * 2 ^ j < 2 ^ k)%Z) by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, sa_testbit_mask by lia.
  destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
  - replace (j <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    rewrite andb_false_r. symmetry. apply Z.mul_pow2_bits_low. lia.
  - rewrite sa_testbit_drop_low by lia. replace (j <=? i)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z.lt_ge_cases i k) as [Hik|Hik].
    + replace (i <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia). now rewrite andb_true_r.
    + replace (i <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      symmetry. destruct (Z.eq_dec (q * 2 ^ j) 0) as [E|NE]; [rewrite E; apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2 ^ k)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

Definition art_sec_pre_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (stat sec msz n nm : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4
  (Wn 8 (Wn 8 (Wn 8 (Wn 8
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
    (s - 56) (U (getr rg 21))) (s - 64) (U (getr rg 22))) (s - 72) (U (getr rg 23))) (s - 80) (U (getr rg 24))) (s - 88) (U (getr rg 25)))
    (s - 104) 0x580e0) (s - 112) stat) (s - 120) sec) (s - 128) msz)
    (s - 132) 34)
    (s - 152) 0x8e760) (s - 160) nm) (s - 168) msz) (s - 176) 0x1d5ba0) (s - 184) n) (s - 192) (U (getr rg 20))) (s - 200) 8.

#[using="Type"] Lemma art_sec_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s sec stat n q nm F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 sec -> getr regs 11 = Z_to_bv 64 stat -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
  0x69c000 <= s - 416 -> s < 2 ^ 47 -> 65536 < n < 2 ^ 40 -> n = 4096 * q - (4096 * q - n) -> 4096 * (q - 1) < n <= 4096 * q ->
  0x10000 <= sec -> sec + 1024 < 0x69c000 -> 0x10000 <= nm < 2 ^ 47 -> 0x10000 <= F -> F + 512 < 0x69c000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 416) 416 ->
  cellA M sec 8 4096 -> cellA M 0x13d8b0 8 0x13f910 -> cellA M 0x13f910 8 nm -> cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 ->
  cellA M 0x13d8b8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x58024 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8e77c)) 2 (Z_to_bv 64 (s - 144))) 8 (Z_to_bv 64 nm)) 9 (Z_to_bv 64 (4096 * q + 4096))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (4096 * q + 4096)))
             12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 34)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 0x1d5ba0)) 19 (Z_to_bv 64 n))
             20 (getr regs 20)) 21 (Z_to_bv 64 8)) 24 (Z_to_bv 64 7))
          (0x8ce2c : word) (art_sec_pre_mem M s raw regs stat sec (4096 * q + 4096) n nm) rom).
Proof.
  intros regs M rom raw s sec stat n q nm F fb H1 H2 H10 H11 H12 H13 Hs Hs' Hn Hq Hq' Hsec Hsec' Hnm HF HF' Hfb Hfb1 W Cpg Cg30 Cnm Cg28 Cpc Cg38 Cfl.
  zstep F_57fd4 D_57fd4.
  zsd F_57fd8 D_57fd8 (s - 8) (U raw) ltac:(rewok W).
  zsd F_57fdc D_57fdc (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_57fe0 D_57fe0 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_57fe4 D_57fe4 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_57fe8 D_57fe8 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_57fec D_57fec (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_57ff0 D_57ff0 (s - 56) (U (getr regs 21)) ltac:(rewok W).
  zsd F_57ff4 D_57ff4 (s - 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_57ff8 D_57ff8 (s - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_57ffc D_57ffc (s - 80) (U (getr regs 24)) ltac:(rewok W).
  zsd F_58000 D_58000 (s - 88) (U (getr regs 25)) ltac:(rewok W).
  zstep F_58004 D_58004.
  zstep F_58008 D_58008.
  zstep F_5800c D_5800c.
  zbft F_58010 D_58010.
  zstep F_58014 D_58014.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg1 : cellA X sec 8 4096) by zcell end.
  zld F_58018 D_58018 sec Cpg1.
  zstep F_5801c D_5801c.
  zstep F_58020 D_58020.
  zbft F_58024 D_58024.
  zstep F_58028 D_58028.
  zstep F_5802c D_5802c.
  zstep F_58030 D_58030.
  zstep F_58034 D_58034.
  assert (RU : (n + 4095) mod 4096 = n + 4095 - 4096 * q) by (symmetry; apply (Z.mod_unique_pos (n + 4095) 4096 q); lia).
  stepn F_58038 D_58038. rwH.
  replace (n + 4096 + -1) with (n + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (n + 4095 - (n + 4095) mod 4096) with (4096 * q) by lia.
  zstep F_5803c D_5803c.
  zstep F_58040 D_58040.
  zstep F_58044 D_58044.
  zstep F_58048 D_58048.
  zstep F_5804c D_5804c.
  zbtk F_58050 D_58050.
  zstep F_58078 D_58078.
  stepn F_5807c D_5807c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C30 : cellA X 0x13d8b0 8 0x13f910) by zcell; assert (Cnm' : cellA X 0x13f910 8 nm) by zcell;
    assert (C28 : cellA X 0x13d8a8 8 0x1d5ba0) by zcell; assert (Cpc' : cellA X 0x1d5ba0 8 4096) by zcell;
    assert (C38 : cellA X 0x13d8b8 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
  zld F_58080 D_58080 0x13d8b0 C30.
  zld F_58084 D_58084 0x13f910 Cnm'.
  zstep F_58088 D_58088.
  stepn F_5808c D_5808c.
  zstep F_8e6a4 D_8e6a4.
  zsd F_8e6a8 D_8e6a8 (s - 104) 0x580e0 ltac:(rewok W).
  zsd F_8e6ac D_8e6ac (s - 112) stat ltac:(rewok W).
  zsd F_8e6b0 D_8e6b0 (s - 120) sec ltac:(rewok W).
  zsd F_8e6b4 D_8e6b4 (s - 128) (4096 * q + 4096) ltac:(rewok W).
  zstep F_8e6b8 D_8e6b8.
  stepn F_8e6bc D_8e6bc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C28b : cellA X 0x13d8a8 8 0x1d5ba0) by zcell; assert (Cpcb : cellA X 0x1d5ba0 8 4096) by zcell end.
  zld F_8e6c0 D_8e6c0 0x13d8a8 C28b.
  zld F_8e6c4 D_8e6c4 0x1d5ba0 Cpcb.
  zstep F_8e6c8 D_8e6c8.
  zbtk F_8e6cc D_8e6cc.
  zstep F_8e6dc D_8e6dc. zstep F_8e6e0 D_8e6e0.
  zbft F_8e6e4 D_8e6e4.
  zstep F_8e6e8 D_8e6e8. zstep F_8e6ec D_8e6ec. zstep F_8e6f0 D_8e6f0.
  stepn F_8e6f4 D_8e6f4. rwH.
  replace (4096 * q + 4096 + 4096 + -1) with (4096 * q + 8191) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (4096 * q + 8191 - (4096 * q + 8191) mod 4096) with (4096 * q + 4096)
    by (rewrite (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) || (symmetry; erewrite <- (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) by lia; lia); lia).
  zstep F_8e6f8 D_8e6f8.
  zsw F_8e6fc D_8e6fc (s - 132) 34 ltac:(rewok W).
  zstep F_8e700 D_8e700. zstep F_8e704 D_8e704. zstep F_8e708 D_8e708.
  stepn F_8e70c D_8e70c.
  zstep F_8f184 D_8f184.
  zsd F_8f188 D_8f188 (s - 152) 0x8e760 ltac:(rewok W).
  zsd F_8f18c D_8f18c (s - 160) nm ltac:(rewok W).
  zsd F_8f190 D_8f190 (s - 168) (4096 * q + 4096) ltac:(rewok W).
  zsd F_8f194 D_8f194 (s - 176) 0x1d5ba0 ltac:(rewok W).
  zsd F_8f198 D_8f198 (s - 184) n ltac:(rewok W).
  zsd F_8f19c D_8f19c (s - 192) (U (getr regs 20)) ltac:(rewok W).
  zsd F_8f1a0 D_8f1a0 (s - 200) 8 ltac:(rewok W).
  zstep F_8f1a4 D_8f1a4.
  zstep F_8f1a8 D_8f1a8.
  zbft F_8f1ac D_8f1ac.
  zstep F_8f1b0 D_8f1b0.
  stepn F_8f1b4 D_8f1b4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x13d8b8 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_8f1b8 D_8f1b8 0x13d8b8 C38c.
  zlbu F_8f1bc D_8f1bc (F + 260) Cflc.
  stepn F_8f1c0 D_8f1c0. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
  zbtk F_8f1c4 D_8f1c4.
  stepn F_8f2d4 D_8f2d4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 152) 8 0x8e760) by zcell; assert (R2 : cellA X (s - 160) 8 nm) by zcell;
    assert (R3 : cellA X (s - 168) 8 (4096 * q + 4096)) by zcell; assert (R4 : cellA X (s - 176) 8 0x1d5ba0) by zcell;
    assert (R5 : cellA X (s - 184) 8 n) by zcell; assert (R6 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
    assert (R7 : cellA X (s - 200) 8 8) by zcell; assert (R8 : cellA X (s - 132) 4 34) by zcell end.
  zld F_8f2d8 D_8f2d8 (s - 152) R1.
  zld F_8f2dc D_8f2dc (s - 160) R2.
  zld F_8f2e0 D_8f2e0 (s - 168) R3.
  zld F_8f2e4 D_8f2e4 (s - 176) R4.
  zld F_8f2e8 D_8f2e8 (s - 184) R5.
  zld F_8f2ec D_8f2ec (s - 192) R6. rewrite Z_to_bv_bv_unsigned.
  zld F_8f2f0 D_8f2f0 (s - 200) R7.
  zstep F_8f2f4 D_8f2f4.
  stepret F_8f2f8 D_8f2f8 (Z_to_bv 64 0x8e760 : word) ltac:(rwH; reflexivity).
  zlw F_8e710 D_8e710 (s - 132) R8.
  zstep F_8e714 D_8e714. zstep F_8e718 D_8e718. zstep F_8e71c D_8e71c. zstep F_8e720 D_8e720. zstep F_8e724 D_8e724.
  stepn F_8e728 D_8e728.
  zstep F_8cdd8 D_8cdd8.
  unfold art_sec_pre_mem. zret.
Qed.
End FPX.
