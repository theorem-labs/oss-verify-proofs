(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac Pm9ArtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_5e000_5f000 Pm9_code_93000_94000 Pm9_code_94000_95000 Pm9_code_95000_96000         .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
    (s - 104) 0x5e308) (s - 112) stat) (s - 120) sec) (s - 128) msz)
    (s - 132) 34)
    (s - 152) 0x94b54) (s - 160) nm) (s - 168) msz) (s - 176) 0x1ed7a0) (s - 184) n) (s - 192) (U (getr rg 20))) (s - 200) 8.

Lemma art_sec_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s sec stat n q nm F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 sec -> getr regs 11 = Z_to_bv 64 stat -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
  0x6b4000 <= s - 416 -> s < 2 ^ 47 -> 65536 < n < 2 ^ 40 -> n = 4096 * q - (4096 * q - n) -> 4096 * (q - 1) < n <= 4096 * q ->
  0x10000 <= sec -> sec + 1024 < 0x6b4000 -> 0x10000 <= nm < 2 ^ 47 -> 0x10000 <= F -> F + 512 < 0x6b4000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 416) 416 ->
  cellA M sec 8 4096 -> cellA M 0x1544e8 8 0x156560 -> cellA M 0x156560 8 nm -> cellA M 0x1544e0 8 0x1ed7a0 -> cellA M 0x1ed7a0 8 4096 ->
  cellA M 0x1544f0 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x5e24c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x94b70)) 2 (Z_to_bv 64 (s - 144))) 8 (Z_to_bv 64 nm)) 9 (Z_to_bv 64 (4096 * q + 4096))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (4096 * q + 4096)))
             12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 34)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 0x1ed7a0)) 19 (Z_to_bv 64 n))
             20 (getr regs 20)) 21 (Z_to_bv 64 8)) 24 (Z_to_bv 64 7))
          (0x93220 : word) (art_sec_pre_mem M s raw regs stat sec (4096 * q + 4096) n nm) rom).
Proof.
  intros regs M rom raw s sec stat n q nm F fb H1 H2 H10 H11 H12 H13 Hs Hs' Hn Hq Hq' Hsec Hsec' Hnm HF HF' Hfb Hfb1 W Cpg Cg30 Cnm Cg28 Cpc Cg38 Cfl.
  zstep F_5e204 D_5e204.
  zsd F_5e208 D_5e208 (s - 8) (U raw) ltac:(rewok W).
  zsd F_5e20c D_5e20c (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5e210 D_5e210 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5e214 D_5e214 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_5e218 D_5e218 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_5e21c D_5e21c (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_5e220 D_5e220 (s - 56) (U (getr regs 21)) ltac:(rewok W).
  zsd F_5e224 D_5e224 (s - 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_5e228 D_5e228 (s - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_5e22c D_5e22c (s - 80) (U (getr regs 24)) ltac:(rewok W).
  zsd F_5e230 D_5e230 (s - 88) (U (getr regs 25)) ltac:(rewok W).
  zstep F_5e234 D_5e234.
  zstep F_5e238 D_5e238.
  zstep F_5e23c D_5e23c.
  zbft F_5e240 D_5e240.
  zstep F_5e244 D_5e244.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg1 : cellA X sec 8 4096) by zcell end.
  zld F_5e248 D_5e248 sec Cpg1.
  zstep F_5e24c D_5e24c.
  zstep F_5e250 D_5e250.
  zbft F_5e254 D_5e254.
  zstep F_5e258 D_5e258.
  zstep F_5e25c D_5e25c.
  zstep F_5e260 D_5e260.
  zstep F_5e264 D_5e264.
  assert (RU : (n + 4095) mod 4096 = n + 4095 - 4096 * q) by (symmetry; apply (Z.mod_unique_pos (n + 4095) 4096 q); lia).
  stepn F_5e268 D_5e268. rwH.
  replace (n + 4096 + -1) with (n + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (n + 4095 - (n + 4095) mod 4096) with (4096 * q) by lia.
  zstep F_5e26c D_5e26c.
  zstep F_5e270 D_5e270.
  zstep F_5e274 D_5e274.
  zstep F_5e278 D_5e278.
  zstep F_5e27c D_5e27c.
  zbtk F_5e280 D_5e280.
  zstep F_5e2a8 D_5e2a8.
  stepn F_5e2ac D_5e2ac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C30 : cellA X 0x1544e8 8 0x156560) by zcell; assert (Cnm' : cellA X 0x156560 8 nm) by zcell;
    assert (C28 : cellA X 0x1544e0 8 0x1ed7a0) by zcell; assert (Cpc' : cellA X 0x1ed7a0 8 4096) by zcell;
    assert (C38 : cellA X 0x1544f0 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
  zld F_5e2b0 D_5e2b0 0x1544e8 C30.
  zld F_5e2b4 D_5e2b4 0x156560 Cnm'.
  zstep F_5e2b8 D_5e2b8.
  stepn F_5e2bc D_5e2bc.
  zstep F_94aa0 D_94aa0.
  zsd F_94aa4 D_94aa4 (s - 104) 0x5e308 ltac:(rewok W).
  zsd F_94aa8 D_94aa8 (s - 112) stat ltac:(rewok W).
  zsd F_94aac D_94aac (s - 120) sec ltac:(rewok W).
  zsd F_94ab0 D_94ab0 (s - 128) (4096 * q + 4096) ltac:(rewok W).
  zstep F_94ab4 D_94ab4.
  stepn F_94ab8 D_94ab8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C28b : cellA X 0x1544e0 8 0x1ed7a0) by zcell; assert (Cpcb : cellA X 0x1ed7a0 8 4096) by zcell end.
  zld F_94abc D_94abc 0x1544e0 C28b.
  zld F_94ac0 D_94ac0 0x1ed7a0 Cpcb.
  zstep F_94ac4 D_94ac4.
  zbtk F_94ac8 D_94ac8.
  zstep F_94ad8 D_94ad8. zstep F_94adc D_94adc.
  zbft F_94ae0 D_94ae0.
  zstep F_94ae4 D_94ae4. zstep F_94ae8 D_94ae8. zstep F_94aec D_94aec.
  stepn F_94af0 D_94af0. rwH.
  replace (4096 * q + 4096 + 4096 + -1) with (4096 * q + 8191) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (4096 * q + 8191 - (4096 * q + 8191) mod 4096) with (4096 * q + 4096)
    by (rewrite (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) || (symmetry; erewrite <- (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) by lia; lia); lia).
  zstep F_94af4 D_94af4.
  zsw F_94af8 D_94af8 (s - 132) 34 ltac:(rewok W).
  zstep F_94afc D_94afc. zstep F_94b00 D_94b00. zstep F_94b04 D_94b04.
  stepn F_94b08 D_94b08.
  zstep F_95580 D_95580.
  zsd F_95584 D_95584 (s - 152) 0x94b54 ltac:(rewok W).
  zsd F_95588 D_95588 (s - 160) nm ltac:(rewok W).
  zsd F_9558c D_9558c (s - 168) (4096 * q + 4096) ltac:(rewok W).
  zsd F_95590 D_95590 (s - 176) 0x1ed7a0 ltac:(rewok W).
  zsd F_95594 D_95594 (s - 184) n ltac:(rewok W).
  zsd F_95598 D_95598 (s - 192) (U (getr regs 20)) ltac:(rewok W).
  zsd F_9559c D_9559c (s - 200) 8 ltac:(rewok W).
  zstep F_955a0 D_955a0.
  zstep F_955a4 D_955a4.
  zbft F_955a8 D_955a8.
  zstep F_955ac D_955ac.
  stepn F_955b0 D_955b0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x1544f0 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_955b4 D_955b4 0x1544f0 C38c.
  zlbu F_955b8 D_955b8 (F + 260) Cflc.
  stepn F_955bc D_955bc. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
  zbtk F_955c0 D_955c0.
  stepn F_956d0 D_956d0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 152) 8 0x94b54) by zcell; assert (R2 : cellA X (s - 160) 8 nm) by zcell;
    assert (R3 : cellA X (s - 168) 8 (4096 * q + 4096)) by zcell; assert (R4 : cellA X (s - 176) 8 0x1ed7a0) by zcell;
    assert (R5 : cellA X (s - 184) 8 n) by zcell; assert (R6 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
    assert (R7 : cellA X (s - 200) 8 8) by zcell; assert (R8 : cellA X (s - 132) 4 34) by zcell end.
  zld F_956d4 D_956d4 (s - 152) R1.
  zld F_956d8 D_956d8 (s - 160) R2.
  zld F_956dc D_956dc (s - 168) R3.
  zld F_956e0 D_956e0 (s - 176) R4.
  zld F_956e4 D_956e4 (s - 184) R5.
  zld F_956e8 D_956e8 (s - 192) R6. rewrite Z_to_bv_bv_unsigned.
  zld F_956ec D_956ec (s - 200) R7.
  zstep F_956f0 D_956f0.
  stepret F_956f4 D_956f4 (Z_to_bv 64 0x94b54 : word) ltac:(rwH; reflexivity).
  zlw F_94b0c D_94b0c (s - 132) R8.
  zstep F_94b10 D_94b10. zstep F_94b14 D_94b14. zstep F_94b18 D_94b18. zstep F_94b1c D_94b1c. zstep F_94b20 D_94b20.
  stepn F_94b24 D_94b24.
  zstep F_931d4 D_931d4.
  unfold art_sec_pre_mem. zret.
Qed.
End FPX.
