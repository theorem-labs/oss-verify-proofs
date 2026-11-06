(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac EatDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r41498_42984 Ea0_code_r731ac_733ac Ea0_code_r73d7c_73f88 Ea0_code_r719b0_719e8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
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
    (s - 104) 0x578b8) (s - 112) stat) (s - 120) sec) (s - 128) msz)
    (s - 132) 34)
    (s - 152) 0x8df38) (s - 160) nm) (s - 168) msz) (s - 176) 0x1d14a0) (s - 184) n) (s - 192) (U (getr rg 20))) (s - 200) 8.

#[using="Type"] Lemma art_sec_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s sec stat n q nm F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 sec -> getr regs 11 = Z_to_bv 64 stat -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
  0x698000 <= s - 416 -> s < 2 ^ 47 -> 65536 < n < 2 ^ 40 -> n = 4096 * q - (4096 * q - n) -> 4096 * (q - 1) < n <= 4096 * q ->
  0x10000 <= sec -> sec + 1024 < 0x698000 -> 0x10000 <= nm < 2 ^ 47 -> 0x10000 <= F -> F + 512 < 0x698000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 416) 416 ->
  cellA M sec 8 4096 -> cellA M 0x1391a0 8 0x13b200 -> cellA M 0x13b200 8 nm -> cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 ->
  cellA M 0x1391a8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x577fc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8df54)) 2 (Z_to_bv 64 (s - 144))) 8 (Z_to_bv 64 nm)) 9 (Z_to_bv 64 (4096 * q + 4096))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (4096 * q + 4096)))
             12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 34)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 0x1d14a0)) 19 (Z_to_bv 64 n))
             20 (getr regs 20)) 21 (Z_to_bv 64 8)) 24 (Z_to_bv 64 7))
          (0x8c604 : word) (art_sec_pre_mem M s raw regs stat sec (4096 * q + 4096) n nm) rom).
Proof.
  intros regs M rom raw s sec stat n q nm F fb H1 H2 H10 H11 H12 H13 Hs Hs' Hn Hq Hq' Hsec Hsec' Hnm HF HF' Hfb Hfb1 W Cpg Cg30 Cnm Cg28 Cpc Cg38 Cfl.
  zstep F_577ac D_577ac.
  zsd F_577b0 D_577b0 (s - 8) (U raw) ltac:(rewok W).
  zsd F_577b4 D_577b4 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_577b8 D_577b8 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_577bc D_577bc (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_577c0 D_577c0 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_577c4 D_577c4 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_577c8 D_577c8 (s - 56) (U (getr regs 21)) ltac:(rewok W).
  zsd F_577cc D_577cc (s - 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_577d0 D_577d0 (s - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_577d4 D_577d4 (s - 80) (U (getr regs 24)) ltac:(rewok W).
  zsd F_577d8 D_577d8 (s - 88) (U (getr regs 25)) ltac:(rewok W).
  zstep F_577dc D_577dc.
  zstep F_577e0 D_577e0.
  zstep F_577e4 D_577e4.
  zbft F_577e8 D_577e8.
  zstep F_577ec D_577ec.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg1 : cellA X sec 8 4096) by zcell end.
  zld F_577f0 D_577f0 sec Cpg1.
  zstep F_577f4 D_577f4.
  zstep F_577f8 D_577f8.
  zbft F_577fc D_577fc.
  zstep F_57800 D_57800.
  zstep F_57804 D_57804.
  zstep F_57808 D_57808.
  zstep F_5780c D_5780c.
  assert (RU : (n + 4095) mod 4096 = n + 4095 - 4096 * q) by (symmetry; apply (Z.mod_unique_pos (n + 4095) 4096 q); lia).
  stepn F_57810 D_57810. rwH.
  replace (n + 4096 + -1) with (n + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (n + 4095 - (n + 4095) mod 4096) with (4096 * q) by lia.
  zstep F_57814 D_57814.
  zstep F_57818 D_57818.
  zstep F_5781c D_5781c.
  zstep F_57820 D_57820.
  zstep F_57824 D_57824.
  zbtk F_57828 D_57828.
  zstep F_57850 D_57850.
  stepn F_57854 D_57854.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C30 : cellA X 0x1391a0 8 0x13b200) by zcell; assert (Cnm' : cellA X 0x13b200 8 nm) by zcell;
    assert (C28 : cellA X 0x139198 8 0x1d14a0) by zcell; assert (Cpc' : cellA X 0x1d14a0 8 4096) by zcell;
    assert (C38 : cellA X 0x1391a8 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
  zld F_57858 D_57858 0x1391a0 C30.
  zld F_5785c D_5785c 0x13b200 Cnm'.
  zstep F_57860 D_57860.
  stepn F_57864 D_57864.
  zstep F_8de7c D_8de7c.
  zsd F_8de80 D_8de80 (s - 104) 0x578b8 ltac:(rewok W).
  zsd F_8de84 D_8de84 (s - 112) stat ltac:(rewok W).
  zsd F_8de88 D_8de88 (s - 120) sec ltac:(rewok W).
  zsd F_8de8c D_8de8c (s - 128) (4096 * q + 4096) ltac:(rewok W).
  zstep F_8de90 D_8de90.
  stepn F_8de94 D_8de94.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C28b : cellA X 0x139198 8 0x1d14a0) by zcell; assert (Cpcb : cellA X 0x1d14a0 8 4096) by zcell end.
  zld F_8de98 D_8de98 0x139198 C28b.
  zld F_8de9c D_8de9c 0x1d14a0 Cpcb.
  zstep F_8dea0 D_8dea0.
  zbtk F_8dea4 D_8dea4.
  zstep F_8deb4 D_8deb4. zstep F_8deb8 D_8deb8.
  zbft F_8debc D_8debc.
  zstep F_8dec0 D_8dec0. zstep F_8dec4 D_8dec4. zstep F_8dec8 D_8dec8.
  stepn F_8decc D_8decc. rwH.
  replace (4096 * q + 4096 + 4096 + -1) with (4096 * q + 8191) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (4096 * q + 8191 - (4096 * q + 8191) mod 4096) with (4096 * q + 4096)
    by (rewrite (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) || (symmetry; erewrite <- (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) by lia; lia); lia).
  zstep F_8ded0 D_8ded0.
  zsw F_8ded4 D_8ded4 (s - 132) 34 ltac:(rewok W).
  zstep F_8ded8 D_8ded8. zstep F_8dedc D_8dedc. zstep F_8dee0 D_8dee0.
  stepn F_8dee4 D_8dee4.
  zstep F_8e95c D_8e95c.
  zsd F_8e960 D_8e960 (s - 152) 0x8df38 ltac:(rewok W).
  zsd F_8e964 D_8e964 (s - 160) nm ltac:(rewok W).
  zsd F_8e968 D_8e968 (s - 168) (4096 * q + 4096) ltac:(rewok W).
  zsd F_8e96c D_8e96c (s - 176) 0x1d14a0 ltac:(rewok W).
  zsd F_8e970 D_8e970 (s - 184) n ltac:(rewok W).
  zsd F_8e974 D_8e974 (s - 192) (U (getr regs 20)) ltac:(rewok W).
  zsd F_8e978 D_8e978 (s - 200) 8 ltac:(rewok W).
  zstep F_8e97c D_8e97c.
  zstep F_8e980 D_8e980.
  zbft F_8e984 D_8e984.
  zstep F_8e988 D_8e988.
  stepn F_8e98c D_8e98c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x1391a8 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_8e990 D_8e990 0x1391a8 C38c.
  zlbu F_8e994 D_8e994 (F + 260) Cflc.
  stepn F_8e998 D_8e998. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
  zbtk F_8e99c D_8e99c.
  stepn F_8eaac D_8eaac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 152) 8 0x8df38) by zcell; assert (R2 : cellA X (s - 160) 8 nm) by zcell;
    assert (R3 : cellA X (s - 168) 8 (4096 * q + 4096)) by zcell; assert (R4 : cellA X (s - 176) 8 0x1d14a0) by zcell;
    assert (R5 : cellA X (s - 184) 8 n) by zcell; assert (R6 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
    assert (R7 : cellA X (s - 200) 8 8) by zcell; assert (R8 : cellA X (s - 132) 4 34) by zcell end.
  zld F_8eab0 D_8eab0 (s - 152) R1.
  zld F_8eab4 D_8eab4 (s - 160) R2.
  zld F_8eab8 D_8eab8 (s - 168) R3.
  zld F_8eabc D_8eabc (s - 176) R4.
  zld F_8eac0 D_8eac0 (s - 184) R5.
  zld F_8eac4 D_8eac4 (s - 192) R6. rewrite Z_to_bv_bv_unsigned.
  zld F_8eac8 D_8eac8 (s - 200) R7.
  zstep F_8eacc D_8eacc.
  stepret F_8ead0 D_8ead0 (Z_to_bv 64 0x8df38 : word) ltac:(rwH; reflexivity).
  zlw F_8dee8 D_8dee8 (s - 132) R8.
  zstep F_8deec D_8deec. zstep F_8def0 D_8def0. zstep F_8def4 D_8def4. zstep F_8def8 D_8def8. zstep F_8defc D_8defc.
  stepn F_8df00 D_8df00.
  zstep F_8c5b0 D_8c5b0.
  unfold art_sec_pre_mem. zret.
Qed.
End FPX.
