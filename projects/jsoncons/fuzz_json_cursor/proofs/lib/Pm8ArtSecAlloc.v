(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac Pm8ArtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5d000_5e000 Pm8_code_92000_93000 Pm8_code_94000_95000 Pm8_code_95000_96000      .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
    (s - 104) 0x5df48) (s - 112) stat) (s - 120) sec) (s - 128) msz)
    (s - 132) 34)
    (s - 152) 0x94794) (s - 160) nm) (s - 168) msz) (s - 176) 0x1ec460) (s - 184) n) (s - 192) (U (getr rg 20))) (s - 200) 8.

Lemma art_sec_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s sec stat n q nm F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 sec -> getr regs 11 = Z_to_bv 64 stat -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
  0x6b3000 <= s - 416 -> s < 2 ^ 47 -> 65536 < n < 2 ^ 40 -> n = 4096 * q - (4096 * q - n) -> 4096 * (q - 1) < n <= 4096 * q ->
  0x10000 <= sec -> sec + 1024 < 0x6b3000 -> 0x10000 <= nm < 2 ^ 47 -> 0x10000 <= F -> F + 512 < 0x6b3000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 416) 416 ->
  cellA M sec 8 4096 -> cellA M 0x153120 8 0x155198 -> cellA M 0x155198 8 nm -> cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 ->
  cellA M 0x153128 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x5de8c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x947b0)) 2 (Z_to_bv 64 (s - 144))) 8 (Z_to_bv 64 nm)) 9 (Z_to_bv 64 (4096 * q + 4096))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (4096 * q + 4096)))
             12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 34)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 0x1ec460)) 19 (Z_to_bv 64 n))
             20 (getr regs 20)) 21 (Z_to_bv 64 8)) 24 (Z_to_bv 64 7))
          (0x92e60 : word) (art_sec_pre_mem M s raw regs stat sec (4096 * q + 4096) n nm) rom).
Proof.
  intros regs M rom raw s sec stat n q nm F fb H1 H2 H10 H11 H12 H13 Hs Hs' Hn Hq Hq' Hsec Hsec' Hnm HF HF' Hfb Hfb1 W Cpg Cg30 Cnm Cg28 Cpc Cg38 Cfl.
  zstep F_5de3c D_5de3c.
  zsd F_5de40 D_5de40 (s - 8) (U raw) ltac:(rewok W).
  zsd F_5de44 D_5de44 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5de48 D_5de48 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5de4c D_5de4c (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_5de50 D_5de50 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_5de54 D_5de54 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_5de58 D_5de58 (s - 56) (U (getr regs 21)) ltac:(rewok W).
  zsd F_5de5c D_5de5c (s - 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_5de60 D_5de60 (s - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_5de64 D_5de64 (s - 80) (U (getr regs 24)) ltac:(rewok W).
  zsd F_5de68 D_5de68 (s - 88) (U (getr regs 25)) ltac:(rewok W).
  zstep F_5de6c D_5de6c.
  zstep F_5de70 D_5de70.
  zstep F_5de74 D_5de74.
  zbft F_5de78 D_5de78.
  zstep F_5de7c D_5de7c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg1 : cellA X sec 8 4096) by zcell end.
  zld F_5de80 D_5de80 sec Cpg1.
  zstep F_5de84 D_5de84.
  zstep F_5de88 D_5de88.
  zbft F_5de8c D_5de8c.
  zstep F_5de90 D_5de90.
  zstep F_5de94 D_5de94.
  zstep F_5de98 D_5de98.
  zstep F_5de9c D_5de9c.
  assert (RU : (n + 4095) mod 4096 = n + 4095 - 4096 * q) by (symmetry; apply (Z.mod_unique_pos (n + 4095) 4096 q); lia).
  stepn F_5dea0 D_5dea0. rwH.
  replace (n + 4096 + -1) with (n + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (n + 4095 - (n + 4095) mod 4096) with (4096 * q) by lia.
  zstep F_5dea4 D_5dea4.
  zstep F_5dea8 D_5dea8.
  zstep F_5deac D_5deac.
  zstep F_5deb0 D_5deb0.
  zstep F_5deb4 D_5deb4.
  zbtk F_5deb8 D_5deb8.
  zstep F_5dee0 D_5dee0.
  stepn F_5dee4 D_5dee4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C30 : cellA X 0x153120 8 0x155198) by zcell; assert (Cnm' : cellA X 0x155198 8 nm) by zcell;
    assert (C28 : cellA X 0x153118 8 0x1ec460) by zcell; assert (Cpc' : cellA X 0x1ec460 8 4096) by zcell;
    assert (C38 : cellA X 0x153128 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
  zld F_5dee8 D_5dee8 0x153120 C30.
  zld F_5deec D_5deec 0x155198 Cnm'.
  zstep F_5def0 D_5def0.
  stepn F_5def4 D_5def4.
  zstep F_946d8 D_946d8.
  zsd F_946dc D_946dc (s - 104) 0x5df48 ltac:(rewok W).
  zsd F_946e0 D_946e0 (s - 112) stat ltac:(rewok W).
  zsd F_946e4 D_946e4 (s - 120) sec ltac:(rewok W).
  zsd F_946e8 D_946e8 (s - 128) (4096 * q + 4096) ltac:(rewok W).
  zstep F_946ec D_946ec.
  stepn F_946f0 D_946f0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C28b : cellA X 0x153118 8 0x1ec460) by zcell; assert (Cpcb : cellA X 0x1ec460 8 4096) by zcell end.
  zld F_946f4 D_946f4 0x153118 C28b.
  zld F_946f8 D_946f8 0x1ec460 Cpcb.
  zstep F_946fc D_946fc.
  zbtk F_94700 D_94700.
  zstep F_94710 D_94710. zstep F_94714 D_94714.
  zbft F_94718 D_94718.
  zstep F_9471c D_9471c. zstep F_94720 D_94720. zstep F_94724 D_94724.
  stepn F_94728 D_94728. rwH.
  replace (4096 * q + 4096 + 4096 + -1) with (4096 * q + 8191) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (4096 * q + 8191 - (4096 * q + 8191) mod 4096) with (4096 * q + 4096)
    by (rewrite (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) || (symmetry; erewrite <- (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) by lia; lia); lia).
  zstep F_9472c D_9472c.
  zsw F_94730 D_94730 (s - 132) 34 ltac:(rewok W).
  zstep F_94734 D_94734. zstep F_94738 D_94738. zstep F_9473c D_9473c.
  stepn F_94740 D_94740.
  zstep F_951b8 D_951b8.
  zsd F_951bc D_951bc (s - 152) 0x94794 ltac:(rewok W).
  zsd F_951c0 D_951c0 (s - 160) nm ltac:(rewok W).
  zsd F_951c4 D_951c4 (s - 168) (4096 * q + 4096) ltac:(rewok W).
  zsd F_951c8 D_951c8 (s - 176) 0x1ec460 ltac:(rewok W).
  zsd F_951cc D_951cc (s - 184) n ltac:(rewok W).
  zsd F_951d0 D_951d0 (s - 192) (U (getr regs 20)) ltac:(rewok W).
  zsd F_951d4 D_951d4 (s - 200) 8 ltac:(rewok W).
  zstep F_951d8 D_951d8.
  zstep F_951dc D_951dc.
  zbft F_951e0 D_951e0.
  zstep F_951e4 D_951e4.
  stepn F_951e8 D_951e8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x153128 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_951ec D_951ec 0x153128 C38c.
  zlbu F_951f0 D_951f0 (F + 260) Cflc.
  stepn F_951f4 D_951f4. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
  zbtk F_951f8 D_951f8.
  stepn F_95308 D_95308.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 152) 8 0x94794) by zcell; assert (R2 : cellA X (s - 160) 8 nm) by zcell;
    assert (R3 : cellA X (s - 168) 8 (4096 * q + 4096)) by zcell; assert (R4 : cellA X (s - 176) 8 0x1ec460) by zcell;
    assert (R5 : cellA X (s - 184) 8 n) by zcell; assert (R6 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
    assert (R7 : cellA X (s - 200) 8 8) by zcell; assert (R8 : cellA X (s - 132) 4 34) by zcell end.
  zld F_9530c D_9530c (s - 152) R1.
  zld F_95310 D_95310 (s - 160) R2.
  zld F_95314 D_95314 (s - 168) R3.
  zld F_95318 D_95318 (s - 176) R4.
  zld F_9531c D_9531c (s - 184) R5.
  zld F_95320 D_95320 (s - 192) R6. rewrite Z_to_bv_bv_unsigned.
  zld F_95324 D_95324 (s - 200) R7.
  zstep F_95328 D_95328.
  stepret F_9532c D_9532c (Z_to_bv 64 0x94794 : word) ltac:(rwH; reflexivity).
  zlw F_94744 D_94744 (s - 132) R8.
  zstep F_94748 D_94748. zstep F_9474c D_9474c. zstep F_94750 D_94750. zstep F_94754 D_94754. zstep F_94758 D_94758.
  stepn F_9475c D_9475c.
  zstep F_92e0c D_92e0c.
  unfold art_sec_pre_mem. zret.
Qed.
End FPX.
