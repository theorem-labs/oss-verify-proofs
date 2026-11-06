(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_415bc_42aa8 As0_code_7333c_7353c As0_code_73f0c_74118 As0_code_71b40_71b78.
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

(* [comment removed for export] *)
Definition art_sec_pre_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (stat sec msz n nm : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4
  (Wn 8 (Wn 8 (Wn 8 (Wn 8
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
    (s - 56) (U (getr rg 21))) (s - 64) (U (getr rg 22))) (s - 72) (U (getr rg 23))) (s - 80) (U (getr rg 24))) (s - 88) (U (getr rg 25)))
    (s - 104) 0x41e5c) (s - 112) stat) (s - 120) sec) (s - 128) msz)
    (s - 132) 34)
    (s - 152) 0x73498) (s - 160) nm) (s - 168) msz) (s - 176) 0x16d5e0) (s - 184) n) (s - 192) (U (getr rg 20))) (s - 200) 8.

Lemma art_sec_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s sec stat n q nm F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 sec -> getr regs 11 = Z_to_bv 64 stat -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
  0x633000 <= s - 416 -> s < 2 ^ 47 -> 65536 < n < 2 ^ 40 -> n = 4096 * q - (4096 * q - n) -> 4096 * (q - 1) < n <= 4096 * q ->
  0x10000 <= sec -> sec + 1024 < 0x633000 -> 0x10000 <= nm < 2 ^ 47 -> 0x10000 <= F -> F + 512 < 0x633000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 416) 416 ->
  cellA M sec 8 4096 -> cellA M 0xd58a0 8 0xd7850 -> cellA M 0xd7850 8 nm -> cellA M 0xd5898 8 0x16d5e0 -> cellA M 0x16d5e0 8 4096 ->
  cellA M 0xd58a8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x41da0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x734b4)) 2 (Z_to_bv 64 (s - 144))) 8 (Z_to_bv 64 nm)) 9 (Z_to_bv 64 (4096 * q + 4096))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (4096 * q + 4096)))
             12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 34)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 0x16d5e0)) 19 (Z_to_bv 64 n))
             20 (getr regs 20)) 21 (Z_to_bv 64 8)) 24 (Z_to_bv 64 7))
          (0x71b64 : word) (art_sec_pre_mem M s raw regs stat sec (4096 * q + 4096) n nm) rom).
Proof.
  intros regs M rom raw s sec stat n q nm F fb H1 H2 H10 H11 H12 H13 Hs Hs' Hn Hq Hq' Hsec Hsec' Hnm HF HF' Hfb Hfb1 W Cpg Cg30 Cnm Cg28 Cpc Cg38 Cfl.
  zstep F_41da0 D_41da0.                                                         (* [comment removed for export] *)
  zsd F_41da4 D_41da4 (s - 8) (U raw) ltac:(rewok W).
  zsd F_41da8 D_41da8 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_41dac D_41dac (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_41db0 D_41db0 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_41db4 D_41db4 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_41db8 D_41db8 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_41dbc D_41dbc (s - 56) (U (getr regs 21)) ltac:(rewok W).
  zsd F_41dc0 D_41dc0 (s - 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_41dc4 D_41dc4 (s - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_41dc8 D_41dc8 (s - 80) (U (getr regs 24)) ltac:(rewok W).
  zsd F_41dcc D_41dcc (s - 88) (U (getr regs 25)) ltac:(rewok W).
  zstep F_41dd0 D_41dd0.                                                         (* [comment removed for export] *)
  zstep F_41dd4 D_41dd4.                                                         (* [comment removed for export] *)
  zstep F_41dd8 D_41dd8.                                                         (* [comment removed for export] *)
  zbft F_41ddc D_41ddc.                                                          (* [comment removed for export] *)
  zstep F_41de0 D_41de0.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg1 : cellA X sec 8 4096) by zcell end.
  zld F_41de4 D_41de4 sec Cpg1.                                                  (* [comment removed for export] *)
  zstep F_41de8 D_41de8.                                                         (* [comment removed for export] *)
  zstep F_41dec D_41dec.                                                         (* [comment removed for export] *)
  zbft F_41df0 D_41df0.                                                          (* [comment removed for export] *)
  zstep F_41df4 D_41df4.                                                         (* [comment removed for export] *)
  zstep F_41df8 D_41df8.                                                         (* [comment removed for export] *)
  zstep F_41dfc D_41dfc.                                                         (* [comment removed for export] *)
  zstep F_41e00 D_41e00.                                                         (* [comment removed for export] *)
  assert (RU : (n + 4095) mod 4096 = n + 4095 - 4096 * q) by (symmetry; apply (Z.mod_unique_pos (n + 4095) 4096 q); lia).
  stepn F_41e04 D_41e04. rwH.                                                    (* [comment removed for export] *)
  replace (n + 4096 + -1) with (n + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (n + 4095 - (n + 4095) mod 4096) with (4096 * q) by lia.
  zstep F_41e08 D_41e08.                                                         (* [comment removed for export] *)
  zstep F_41e0c D_41e0c.                                                         (* [comment removed for export] *)
  zstep F_41e10 D_41e10.                                                         (* [comment removed for export] *)
  zstep F_41e14 D_41e14.                                                         (* [comment removed for export] *)
  zstep F_41e18 D_41e18.                                                         (* [comment removed for export] *)
  zbtk F_41e1c D_41e1c.                                                          (* [comment removed for export] *)
  zstep F_41e44 D_41e44.                                                         (* [comment removed for export] *)
  stepn F_41e48 D_41e48.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C30 : cellA X 0xd58a0 8 0xd7850) by zcell; assert (Cnm' : cellA X 0xd7850 8 nm) by zcell;
    assert (C28 : cellA X 0xd5898 8 0x16d5e0) by zcell; assert (Cpc' : cellA X 0x16d5e0 8 4096) by zcell;
    assert (C38 : cellA X 0xd58a8 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
  zld F_41e4c D_41e4c 0xd58a0 C30.                                               (* [comment removed for export] *)
  zld F_41e50 D_41e50 0xd7850 Cnm'.                                              (* [comment removed for export] *)
  zstep F_41e54 D_41e54.                                                         (* [comment removed for export] *)
  stepn F_41e58 D_41e58.                                                         (* [comment removed for export] *)
  zstep F_7342c D_7342c.                                                         (* [comment removed for export] *)
  zsd F_73430 D_73430 (s - 104) 0x41e5c ltac:(rewok W).                             (* [comment removed for export] *)
  zsd F_73434 D_73434 (s - 112) stat ltac:(rewok W).                               (* [comment removed for export] *)
  zsd F_73438 D_73438 (s - 120) sec ltac:(rewok W).                                (* [comment removed for export] *)
  zsd F_7343c D_7343c (s - 128) (4096 * q + 4096) ltac:(rewok W).                   (* [comment removed for export] *)
  zstep F_73440 D_73440.                                                         (* [comment removed for export] *)
  stepn F_73444 D_73444.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C28b : cellA X 0xd5898 8 0x16d5e0) by zcell; assert (Cpcb : cellA X 0x16d5e0 8 4096) by zcell end.
  zld F_73448 D_73448 0xd5898 C28b.                                              (* [comment removed for export] *)
  zld F_7344c D_7344c 0x16d5e0 Cpcb.                                             (* [comment removed for export] *)
  zstep F_73450 D_73450.                                                         (* [comment removed for export] *)
  zbtk F_73454 D_73454.                                                          (* [comment removed for export] *)
  zstep F_73464 D_73464. zstep F_73468 D_73468.                                  (* [comment removed for export] *)
  zbft F_7346c D_7346c.                                                          (* [comment removed for export] *)
  zstep F_73470 D_73470. zstep F_73474 D_73474. zstep F_73478 D_73478.           (* [comment removed for export] *)
  stepn F_7347c D_7347c. rwH.                                                    (* [comment removed for export] *)
  replace (4096 * q + 4096 + 4096 + -1) with (4096 * q + 8191) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (4096 * q + 8191 - (4096 * q + 8191) mod 4096) with (4096 * q + 4096)
    by (rewrite (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) || (symmetry; erewrite <- (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) by lia; lia); lia).
  zstep F_73480 D_73480.                                                         (* [comment removed for export] *)
  zsw F_73484 D_73484 (s - 132) 34 ltac:(rewok W).                                 (* [comment removed for export] *)
  zstep F_73488 D_73488. zstep F_7348c D_7348c. zstep F_73490 D_73490.           (* [comment removed for export] *)
  stepn F_73494 D_73494.                                                         (* [comment removed for export] *)
  zstep F_73f0c D_73f0c.                                                         (* [comment removed for export] *)
  zsd F_73f10 D_73f10 (s - 152) 0x73498 ltac:(rewok W).
  zsd F_73f14 D_73f14 (s - 160) nm ltac:(rewok W).
  zsd F_73f18 D_73f18 (s - 168) (4096 * q + 4096) ltac:(rewok W).
  zsd F_73f1c D_73f1c (s - 176) 0x16d5e0 ltac:(rewok W).
  zsd F_73f20 D_73f20 (s - 184) n ltac:(rewok W).
  zsd F_73f24 D_73f24 (s - 192) (U (getr regs 20)) ltac:(rewok W).
  zsd F_73f28 D_73f28 (s - 200) 8 ltac:(rewok W).
  zstep F_73f2c D_73f2c.                                                         (* [comment removed for export] *)
  zstep F_73f30 D_73f30.                                                         (* [comment removed for export] *)
  zbft F_73f34 D_73f34.                                                          (* [comment removed for export] *)
  zstep F_73f38 D_73f38.                                                         (* [comment removed for export] *)
  stepn F_73f3c D_73f3c.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0xd58a8 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_73f40 D_73f40 0xd58a8 C38c.                                              (* [comment removed for export] *)
  zlbu F_73f44 D_73f44 (F + 260) Cflc.                                           (* [comment removed for export] *)
  stepn F_73f48 D_73f48. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.          (* [comment removed for export] *)
  zbtk F_73f4c D_73f4c.                                                          (* [comment removed for export] *)
  stepn F_7405c D_7405c.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 152) 8 0x73498) by zcell; assert (R2 : cellA X (s - 160) 8 nm) by zcell;
    assert (R3 : cellA X (s - 168) 8 (4096 * q + 4096)) by zcell; assert (R4 : cellA X (s - 176) 8 0x16d5e0) by zcell;
    assert (R5 : cellA X (s - 184) 8 n) by zcell; assert (R6 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
    assert (R7 : cellA X (s - 200) 8 8) by zcell; assert (R8 : cellA X (s - 132) 4 34) by zcell end.
  zld F_74060 D_74060 (s - 152) R1.                                              (* [comment removed for export] *)
  zld F_74064 D_74064 (s - 160) R2.
  zld F_74068 D_74068 (s - 168) R3.
  zld F_7406c D_7406c (s - 176) R4.
  zld F_74070 D_74070 (s - 184) R5.
  zld F_74074 D_74074 (s - 192) R6. rewrite Z_to_bv_bv_unsigned.
  zld F_74078 D_74078 (s - 200) R7.
  zstep F_7407c D_7407c.                                                         (* [comment removed for export] *)
  stepret F_74080 D_74080 (Z_to_bv 64 0x73498 : word) ltac:(rwH; reflexivity).
  zlw F_73498 D_73498 (s - 132) R8.                                              (* [comment removed for export] *)
  zstep F_7349c D_7349c. zstep F_734a0 D_734a0. zstep F_734a4 D_734a4. zstep F_734a8 D_734a8. zstep F_734ac D_734ac.   (* [comment removed for export] *)
  stepn F_734b0 D_734b0.                                                         (* [comment removed for export] *)
  zstep F_71b60 D_71b60.                                                         (* [comment removed for export] *)
  unfold art_sec_pre_mem. zret.
Qed.
End FPX.
