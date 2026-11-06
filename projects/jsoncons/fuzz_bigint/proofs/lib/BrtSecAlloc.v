(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac BrtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_4183c_42d28 Bo0_code_735bc_737bc Bo0_code_7418c_74398 Bo0_code_71dc0_71df8.
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

(* [comment removed for export] *)
Definition art_sec_pre_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (stat sec msz n nm : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4
  (Wn 8 (Wn 8 (Wn 8 (Wn 8
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
    (s - 56) (U (getr rg 21))) (s - 64) (U (getr rg 22))) (s - 72) (U (getr rg 23))) (s - 80) (U (getr rg 24))) (s - 88) (U (getr rg 25)))
    (s - 104) 0x420dc) (s - 112) stat) (s - 120) sec) (s - 128) msz)
    (s - 132) 34)
    (s - 152) 0x73718) (s - 160) nm) (s - 168) msz) (s - 176) 0x16e1e0) (s - 184) n) (s - 192) (U (getr rg 20))) (s - 200) 8.

Lemma art_sec_pre_fn : forall regs (M rom : word -> option byte) (raw : word) (s sec stat n q nm F fb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 sec -> getr regs 11 = Z_to_bv 64 stat -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 8 ->
  0x634000 <= s - 416 -> s < 2 ^ 47 -> 65536 < n < 2 ^ 40 -> n = 4096 * q - (4096 * q - n) -> 4096 * (q - 1) < n <= 4096 * q ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> 0x10000 <= nm < 2 ^ 47 -> 0x10000 <= F -> F + 512 < 0x634000 -> 0 <= fb < 256 -> Z.land fb 1 = 0 ->
  wrA M (s - 416) 416 ->
  cellA M sec 8 4096 -> cellA M 0xd64b0 8 0xd8460 -> cellA M 0xd8460 8 nm -> cellA M 0xd64a8 8 0x16e1e0 -> cellA M 0x16e1e0 8 4096 ->
  cellA M 0xd64b8 8 F -> cellA M (F + 260) 1 fb ->
  msteps ASEGS (mkst regs (0x42020 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x73734)) 2 (Z_to_bv 64 (s - 144))) 8 (Z_to_bv 64 nm)) 9 (Z_to_bv 64 (4096 * q + 4096))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (4096 * q + 4096)))
             12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 34)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 0x16e1e0)) 19 (Z_to_bv 64 n))
             20 (getr regs 20)) 21 (Z_to_bv 64 8)) 24 (Z_to_bv 64 7))
          (0x71de4 : word) (art_sec_pre_mem M s raw regs stat sec (4096 * q + 4096) n nm) rom).
Proof.
  intros regs M rom raw s sec stat n q nm F fb H1 H2 H10 H11 H12 H13 Hs Hs' Hn Hq Hq' Hsec Hsec' Hnm HF HF' Hfb Hfb1 W Cpg Cg30 Cnm Cg28 Cpc Cg38 Cfl.
  zstep F_42020 D_42020.                                                         (* [comment removed for export] *)
  zsd F_42024 D_42024 (s - 8) (U raw) ltac:(rewok W).
  zsd F_42028 D_42028 (s - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_4202c D_4202c (s - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_42030 D_42030 (s - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_42034 D_42034 (s - 40) (U (getr regs 19)) ltac:(rewok W).
  zsd F_42038 D_42038 (s - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_4203c D_4203c (s - 56) (U (getr regs 21)) ltac:(rewok W).
  zsd F_42040 D_42040 (s - 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_42044 D_42044 (s - 72) (U (getr regs 23)) ltac:(rewok W).
  zsd F_42048 D_42048 (s - 80) (U (getr regs 24)) ltac:(rewok W).
  zsd F_4204c D_4204c (s - 88) (U (getr regs 25)) ltac:(rewok W).
  zstep F_42050 D_42050.                                                         (* [comment removed for export] *)
  zstep F_42054 D_42054.                                                         (* [comment removed for export] *)
  zstep F_42058 D_42058.                                                         (* [comment removed for export] *)
  zbft F_4205c D_4205c.                                                          (* [comment removed for export] *)
  zstep F_42060 D_42060.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg1 : cellA X sec 8 4096) by zcell end.
  zld F_42064 D_42064 sec Cpg1.                                                  (* [comment removed for export] *)
  zstep F_42068 D_42068.                                                         (* [comment removed for export] *)
  zstep F_4206c D_4206c.                                                         (* [comment removed for export] *)
  zbft F_42070 D_42070.                                                          (* [comment removed for export] *)
  zstep F_42074 D_42074.                                                         (* [comment removed for export] *)
  zstep F_42078 D_42078.                                                         (* [comment removed for export] *)
  zstep F_4207c D_4207c.                                                         (* [comment removed for export] *)
  zstep F_42080 D_42080.                                                         (* [comment removed for export] *)
  assert (RU : (n + 4095) mod 4096 = n + 4095 - 4096 * q) by (symmetry; apply (Z.mod_unique_pos (n + 4095) 4096 q); lia).
  stepn F_42084 D_42084. rwH.                                                    (* [comment removed for export] *)
  replace (n + 4096 + -1) with (n + 4095) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (n + 4095 - (n + 4095) mod 4096) with (4096 * q) by lia.
  zstep F_42088 D_42088.                                                         (* [comment removed for export] *)
  zstep F_4208c D_4208c.                                                         (* [comment removed for export] *)
  zstep F_42090 D_42090.                                                         (* [comment removed for export] *)
  zstep F_42094 D_42094.                                                         (* [comment removed for export] *)
  zstep F_42098 D_42098.                                                         (* [comment removed for export] *)
  zbtk F_4209c D_4209c.                                                          (* [comment removed for export] *)
  zstep F_420c4 D_420c4.                                                         (* [comment removed for export] *)
  stepn F_420c8 D_420c8.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (C30 : cellA X 0xd64b0 8 0xd8460) by zcell; assert (Cnm' : cellA X 0xd8460 8 nm) by zcell;
    assert (C28 : cellA X 0xd64a8 8 0x16e1e0) by zcell; assert (Cpc' : cellA X 0x16e1e0 8 4096) by zcell;
    assert (C38 : cellA X 0xd64b8 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
  zld F_420cc D_420cc 0xd64b0 C30.                                               (* [comment removed for export] *)
  zld F_420d0 D_420d0 0xd8460 Cnm'.                                              (* [comment removed for export] *)
  zstep F_420d4 D_420d4.                                                         (* [comment removed for export] *)
  stepn F_420d8 D_420d8.                                                         (* [comment removed for export] *)
  zstep F_736ac D_736ac.                                                         (* [comment removed for export] *)
  zsd F_736b0 D_736b0 (s - 104) 0x420dc ltac:(rewok W).                             (* [comment removed for export] *)
  zsd F_736b4 D_736b4 (s - 112) stat ltac:(rewok W).                               (* [comment removed for export] *)
  zsd F_736b8 D_736b8 (s - 120) sec ltac:(rewok W).                                (* [comment removed for export] *)
  zsd F_736bc D_736bc (s - 128) (4096 * q + 4096) ltac:(rewok W).                   (* [comment removed for export] *)
  zstep F_736c0 D_736c0.                                                         (* [comment removed for export] *)
  stepn F_736c4 D_736c4.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C28b : cellA X 0xd64a8 8 0x16e1e0) by zcell; assert (Cpcb : cellA X 0x16e1e0 8 4096) by zcell end.
  zld F_736c8 D_736c8 0xd64a8 C28b.                                              (* [comment removed for export] *)
  zld F_736cc D_736cc 0x16e1e0 Cpcb.                                             (* [comment removed for export] *)
  zstep F_736d0 D_736d0.                                                         (* [comment removed for export] *)
  zbtk F_736d4 D_736d4.                                                          (* [comment removed for export] *)
  zstep F_736e4 D_736e4. zstep F_736e8 D_736e8.                                  (* [comment removed for export] *)
  zbft F_736ec D_736ec.                                                          (* [comment removed for export] *)
  zstep F_736f0 D_736f0. zstep F_736f4 D_736f4. zstep F_736f8 D_736f8.           (* [comment removed for export] *)
  stepn F_736fc D_736fc. rwH.                                                    (* [comment removed for export] *)
  replace (4096 * q + 4096 + 4096 + -1) with (4096 * q + 8191) by lia.
  rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (4096 * q + 8191 - (4096 * q + 8191) mod 4096) with (4096 * q + 4096)
    by (rewrite (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) || (symmetry; erewrite <- (Z.mod_unique_pos (4096 * q + 8191) 4096 (q + 1) 4095) by lia; lia); lia).
  zstep F_73700 D_73700.                                                         (* [comment removed for export] *)
  zsw F_73704 D_73704 (s - 132) 34 ltac:(rewok W).                                 (* [comment removed for export] *)
  zstep F_73708 D_73708. zstep F_7370c D_7370c. zstep F_73710 D_73710.           (* [comment removed for export] *)
  stepn F_73714 D_73714.                                                         (* [comment removed for export] *)
  zstep F_7418c D_7418c.                                                         (* [comment removed for export] *)
  zsd F_74190 D_74190 (s - 152) 0x73718 ltac:(rewok W).
  zsd F_74194 D_74194 (s - 160) nm ltac:(rewok W).
  zsd F_74198 D_74198 (s - 168) (4096 * q + 4096) ltac:(rewok W).
  zsd F_7419c D_7419c (s - 176) 0x16e1e0 ltac:(rewok W).
  zsd F_741a0 D_741a0 (s - 184) n ltac:(rewok W).
  zsd F_741a4 D_741a4 (s - 192) (U (getr regs 20)) ltac:(rewok W).
  zsd F_741a8 D_741a8 (s - 200) 8 ltac:(rewok W).
  zstep F_741ac D_741ac.                                                         (* [comment removed for export] *)
  zstep F_741b0 D_741b0.                                                         (* [comment removed for export] *)
  zbft F_741b4 D_741b4.                                                          (* [comment removed for export] *)
  zstep F_741b8 D_741b8.                                                         (* [comment removed for export] *)
  stepn F_741bc D_741bc.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0xd64b8 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
  zld F_741c0 D_741c0 0xd64b8 C38c.                                              (* [comment removed for export] *)
  zlbu F_741c4 D_741c4 (F + 260) Cflc.                                           (* [comment removed for export] *)
  stepn F_741c8 D_741c8. rwH. rewrite art_zb_andi by lia. rewrite Hfb1.          (* [comment removed for export] *)
  zbtk F_741cc D_741cc.                                                          (* [comment removed for export] *)
  stepn F_742dc D_742dc.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 152) 8 0x73718) by zcell; assert (R2 : cellA X (s - 160) 8 nm) by zcell;
    assert (R3 : cellA X (s - 168) 8 (4096 * q + 4096)) by zcell; assert (R4 : cellA X (s - 176) 8 0x16e1e0) by zcell;
    assert (R5 : cellA X (s - 184) 8 n) by zcell; assert (R6 : cellA X (s - 192) 8 (U (getr regs 20))) by zcell;
    assert (R7 : cellA X (s - 200) 8 8) by zcell; assert (R8 : cellA X (s - 132) 4 34) by zcell end.
  zld F_742e0 D_742e0 (s - 152) R1.                                              (* [comment removed for export] *)
  zld F_742e4 D_742e4 (s - 160) R2.
  zld F_742e8 D_742e8 (s - 168) R3.
  zld F_742ec D_742ec (s - 176) R4.
  zld F_742f0 D_742f0 (s - 184) R5.
  zld F_742f4 D_742f4 (s - 192) R6. rewrite Z_to_bv_bv_unsigned.
  zld F_742f8 D_742f8 (s - 200) R7.
  zstep F_742fc D_742fc.                                                         (* [comment removed for export] *)
  stepret F_74300 D_74300 (Z_to_bv 64 0x73718 : word) ltac:(rwH; reflexivity).
  zlw F_73718 D_73718 (s - 132) R8.                                              (* [comment removed for export] *)
  zstep F_7371c D_7371c. zstep F_73720 D_73720. zstep F_73724 D_73724. zstep F_73728 D_73728. zstep F_7372c D_7372c.   (* [comment removed for export] *)
  stepn F_73730 D_73730.                                                         (* [comment removed for export] *)
  zstep F_71de0 D_71de0.                                                         (* [comment removed for export] *)
  unfold art_sec_pre_mem. zret.
Qed.
End FPX.
