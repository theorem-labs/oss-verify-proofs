(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatDepotA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b Ba0_code_r731ac_733ac_b Ba0_code_r73d7c_73f88_b Ba0_code_r719b0_719e8_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
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

(* [comment removed for export] *)
Definition art_sec_pre_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (stat sec msz n nm : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4
  (Wn 8 (Wn 8 (Wn 8 (Wn 8
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
    (s - 56) (U (getr rg 21))) (s - 64) (U (getr rg 22))) (s - 72) (U (getr rg 23))) (s - 80) (U (getr rg 24))) (s - 88) (U (getr rg 25)))
    (s - 104) 0x570d0) (s - 112) stat) (s - 120) sec) (s - 128) msz)
    (s - 132) 34)
    (s - 152) 0x8d5b4) (s - 160) nm) (s - 168) msz) (s - 176) 0x1cf6e0) (s - 184) n) (s - 192) (U (getr rg 20))) (s - 200) 8.

#[using="Type"] Lemma art_sec_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s sec stat n q nm F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 sec -> getr regs 11 = Z_to_bv 64 stat -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
  0x696000 <= s - 416 -> s < 2 ^ 47 -> 65536 < n < 2 ^ 40 -> n = 4096 * q - (4096 * q - n) -> 4096 * (q - 1) < n <= 4096 * q ->
  0x10000 <= sec -> sec + 1024 < 0x696000 -> 0x10000 <= nm < 2 ^ 47 -> 0x10000 <= F -> F + 512 < 0x696000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 416) 416 ->
  cellA M sec 8 4096 -> cellA M 0x1374a8 8 0x139508 -> cellA M 0x139508 8 nm -> cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 ->
  cellA M 0x1374b0 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x57014 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x8d5d0)) 2 (Z_to_bv 64 (s - 144))) 8 (Z_to_bv 64 nm)) 9 (Z_to_bv 64 (4096 * q + 4096))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (4096 * q + 4096)))
             12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 34)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 0x1cf6e0)) 19 (Z_to_bv 64 n))
             20 (getr regs 20)) 21 (Z_to_bv 64 8)) 24 (Z_to_bv 64 7))
          (0x8bc80 : word) (art_sec_pre_mem M s raw regs stat sec (4096 * q + 4096) n nm) rom).
Proof.
  intros regs M rom raw s sec stat n q nm F fb H1 H2 H10 H11 H12 H13 Hs Hs' Hn Hq Hq' Hsec Hsec' Hnm HF HF' Hfb Hfb1 W Cpg Cg30 Cnm Cg28 Cpc Cg38 Cfl.
  zstep F_56bfc D_56bfc.                                                         (* [comment removed for export] *)
  zsd F_56c00 D_56c00 (s - 8) (U raw) ltac:(rewok W).
  zsd F_56c04 D_56c04 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_56c08 D_56c08 (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_56c0c D_56c0c (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_56c10 D_56c10 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_56c14 D_56c14 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_56c18 D_56c18 (s - 56) (U (getr regs 21)) ltac:(rewok W).
  zsd F_56c1c D_56c1c (s - 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_56c20 D_56c20 (s - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_56c24 D_56c24 (s - 80) (U (getr regs 24)) ltac:(rewok W).
  zsd F_56c28 D_56c28 (s - 88) (U (getr regs 25)) ltac:(rewok W).
  zstep F_56c2c D_56c2c.                                                         (* [comment removed for export] *)
  zstep F_56c30 D_56c30.                                                         (* [comment removed for export] *)
  zstep F_56c34 D_56c34.                                                         (* [comment removed for export] *)
  zbft F_56c38 D_56c38.                                                          (* [comment removed for export] *)
  zstep F_56c3c D_56c3c.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg1 : cellA X sec 8 4096) by zcell end.
  zld F_56c40 D_56c40 sec Cpg1.                                                  (* [comment removed for export] *)
  zstep F_56c44 D_56c44.                                                         (* [comment removed for export] *)
  zstep F_56c48 D_56c48.                                                         (* [comment removed for export] *)
  zbft F_56c4c D_56c4c.                                                          (* [comment removed for export] *)
  zstep F_56c50 D_56c50.                                                         (* [comment removed for export] *)
  zstep F_56c54 D_56c54.                                                         (* [comment removed for export] *)
  zstep F_56c58 D_56c58.                                                         (* [comment removed for export] *)
  zstep F_56c5c D_56c5c.                                                         (* [comment removed for export] *)
  assert (RU : (n + 4095) mod 4096 = n + 4095 - 4096 * q) by (symmetry; apply (Z.mod_unique_pos (n + 4095) 4096 q); lia).
  stepn F_56c60 D_56c60. rwH.                                                    (* [comment removed for export] *)
  replace (n + 4096 + -1) with (n + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (n + 4095 - (n + 4095) mod 4096) with (4096 * q) by lia.
  zstep F_56c64 D_56c64.                                                         (* [comment removed for export] *)
  zstep F_56c68 D_56c68.                                                         (* [comment removed for export] *)
  zstep F_56c6c D_56c6c.                                                         (* [comment removed for export] *)
  zstep F_56c70 D_56c70.                                                         (* [comment removed for export] *)
  zstep F_56c74 D_56c74.                                                         (* [comment removed for export] *)
  zbtk F_56c78 D_56c78.                                                          (* [comment removed for export] *)
  zstep F_56ca0 D_56ca0.                                                         (* [comment removed for export] *)
  stepn F_56ca4 D_56ca4.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C30 : cellA X 0x1374a8 8 0x139508) by zcell; assert (Cnm' : cellA X 0x139508 8 nm) by zcell;
    assert (C28 : cellA X 0x1374a0 8 0x1cf6e0) by zcell; assert (Cpc' : cellA X 0x1cf6e0 8 4096) by zcell;
    assert (C38 : cellA X 0x1374b0 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
  zld F_56ca8 D_56ca8 0x1374a8 C30.                                               (* [comment removed for export] *)
  zld F_56cac D_56cac 0x139508 Cnm'.                                              (* [comment removed for export] *)
  zstep F_56cb0 D_56cb0.                                                         (* [comment removed for export] *)
  stepn F_56cb4 D_56cb4.                                                         (* [comment removed for export] *)
  zstep F_8d130 D_8d130.                                                         (* [comment removed for export] *)
  zsd F_8d134 D_8d134 (s - 104) 0x570d0 ltac:(rewok W).                             (* [comment removed for export] *)
  zsd F_8d138 D_8d138 (s - 112) stat ltac:(rewok W).                               (* [comment removed for export] *)
  zsd F_8d13c D_8d13c (s - 120) sec ltac:(rewok W).                                (* [comment removed for export] *)
  zsd F_8d140 D_8d140 (s - 128) (4096 * q + 4096) ltac:(rewok W).                   (* [comment removed for export] *)
  zstep F_8d144 D_8d144.                                                         (* [comment removed for export] *)
  stepn F_8d148 D_8d148.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C28b : cellA X 0x1374a0 8 0x1cf6e0) by zcell; assert (Cpcb : cellA X 0x1cf6e0 8 4096) by zcell end.
  zld F_8d14c D_8d14c 0x1374a0 C28b.                                              (* [comment removed for export] *)
  zld F_8d150 D_8d150 0x1cf6e0 Cpcb.                                             (* [comment removed for export] *)
  zstep F_8d154 D_8d154.                                                         (* [comment removed for export] *)
  zbtk F_8d158 D_8d158.                                                          (* [comment removed for export] *)
  zstep F_8d168 D_8d168. zstep F_8d16c D_8d16c.                                  (* [comment removed for export] *)
  zbft F_8d170 D_8d170.                                                          (* [comment removed for export] *)
  zstep F_8d174 D_8d174. zstep F_8d178 D_8d178. zstep F_8d17c D_8d17c.           (* [comment removed for export] *)
  stepn F_8d180 D_8d180. rwH.                                                    (* [comment removed for export] *)
  replace (4096 * q + 4096 + 4096 + -1) with (4096 * q + 8191) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (4096 * q + 8191 - (4096 * q + 8191) mod 4096) with (4096 * q + 4096)
    by (rewrite (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) || (symmetry; erewrite <- (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) by lia; lia); lia).
  zstep F_8d184 D_8d184.                                                         (* [comment removed for export] *)
  zsw F_8d188 D_8d188 (s - 132) 34 ltac:(rewok W).                                 (* [comment removed for export] *)
  zstep F_8d18c D_8d18c. zstep F_8d190 D_8d190. zstep F_8d194 D_8d194.           (* [comment removed for export] *)
  stepn F_8d198 D_8d198.                                                         (* [comment removed for export] *)
  zstep F_8dc10 D_8dc10.                                                         (* [comment removed for export] *)
  zsd F_8dc14 D_8dc14 (s - 152) 0x8d5b4 ltac:(rewok W).
  zsd F_8dc18 D_8dc18 (s - 160) nm ltac:(rewok W).
  zsd F_8dc1c D_8dc1c (s - 168) (4096 * q + 4096) ltac:(rewok W).
  zsd F_8dc20 D_8dc20 (s - 176) 0x1cf6e0 ltac:(rewok W).
  zsd F_8dc24 D_8dc24 (s - 184) n ltac:(rewok W).
  zsd F_8dc28 D_8dc28 (s - 192) (U (getr regs 20)) ltac:(rewok W).
  zsd F_8dc2c D_8dc2c (s - 200) 8 ltac:(rewok W).
  zstep F_8dc30 D_8dc30.                                                         (* [comment removed for export] *)
  zstep F_8dc34 D_8dc34.                                                         (* [comment removed for export] *)
  zbft F_8dc38 D_8dc38.                                                          (* [comment removed for export] *)
  zstep F_8dc3c D_8dc3c.                                                         (* [comment removed for export] *)
  stepn F_8dc40 D_8dc40.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x1374b0 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_8dc44 D_8dc44 0x1374b0 C38c.                                              (* [comment removed for export] *)
  zlbu F_8dc48 D_8dc48 (F + 260) Cflc.                                           (* [comment removed for export] *)
  stepn F_8dc4c D_8dc4c. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.          (* [comment removed for export] *)
  zbtk F_8dc50 D_8dc50.                                                          (* [comment removed for export] *)
  stepn F_8dd60 D_8dd60.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 152) 8 0x8d5b4) by zcell; assert (R2 : cellA X (s - 160) 8 nm) by zcell;
    assert (R3 : cellA X (s - 168) 8 (4096 * q + 4096)) by zcell; assert (R4 : cellA X (s - 176) 8 0x1cf6e0) by zcell;
    assert (R5 : cellA X (s - 184) 8 n) by zcell; assert (R6 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
    assert (R7 : cellA X (s - 200) 8 8) by zcell; assert (R8 : cellA X (s - 132) 4 34) by zcell end.
  zld F_8dd64 D_8dd64 (s - 152) R1.                                              (* [comment removed for export] *)
  zld F_8dd68 D_8dd68 (s - 160) R2.
  zld F_8dd6c D_8dd6c (s - 168) R3.
  zld F_8dd70 D_8dd70 (s - 176) R4.
  zld F_8dd74 D_8dd74 (s - 184) R5.
  zld F_8dd78 D_8dd78 (s - 192) R6. rewrite Z_to_bv_bv_unsigned.
  zld F_8dd7c D_8dd7c (s - 200) R7.
  zstep F_8dd80 D_8dd80.                                                         (* [comment removed for export] *)
  stepret F_8dd84 D_8dd84 (Z_to_bv 64 0x8d5b4 : word) ltac:(rwH; reflexivity).
  zlw F_8d19c D_8d19c (s - 132) R8.                                              (* [comment removed for export] *)
  zstep F_8d1a0 D_8d1a0. zstep F_8d1a4 D_8d1a4. zstep F_8d1a8 D_8d1a8. zstep F_8d1ac D_8d1ac. zstep F_8d1b0 D_8d1b0.   (* [comment removed for export] *)
  stepn F_8d1b4 D_8d1b4.                                                         (* [comment removed for export] *)
  zstep F_8b864 D_8b864.                                                         (* [comment removed for export] *)
  unfold art_sec_pre_mem. zret.
Qed.
End FPX.
