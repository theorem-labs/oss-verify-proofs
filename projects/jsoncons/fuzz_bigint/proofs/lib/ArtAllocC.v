(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_3d034_3dfbc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_land_m8_48 : forall x, 0 <= x < 2 ^ 48 -> Z.land x 281474976710648 = x / 8 * 8.
Proof.
  intros x Hx. change 281474976710648 with (Z.shiftl (Z.ones 45) 3).
  change 8 with (2 ^ 3). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 3) as [L|G].
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
    replace (i - 3 + 3) with i by lia.
    destruct (Z.lt_ge_cases i 48) as [L2|G2].
    + replace ((0 <=? i - 3) && (i - 3 <? 45))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply Bool.andb_true_r.
    + assert (Tf : Z.testbit x i = false).
      { destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
        apply Z.lt_le_trans with (m := 48); [|lia]. apply Z.log2_lt_pow2; lia. }
      rewrite Tf. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_c_big_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 8 <= n < 2 ^ 40 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x3d71c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d828 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 (n / 8 * 8))) 12 (Z_to_bv 64 0)) 22 (Z_to_bv 64 (n / 8 * 8))) (0x60f78 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_3d71c D_3d71c. rwH. rewrite art_zb_slli by lia.
  stepn F_3d720 D_3d720. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_3d724 D_3d724. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_3d728 D_3d728 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_3d72c D_3d72c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0xd58b8 8 0xddb38) by (recell G48);
    assert (Csb' : cellA X 0xddb38 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_3d730 D_3d730. zld F_3d734 D_3d734 0xd58b8 G48'. zld F_3d738 D_3d738 0xddb38 Csb'. unfold SB.
  stepn F_3d73c D_3d73c. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_3d740 D_3d740.
  zlbu F_3d744 D_3d744 (2147450880 + ab / 8) Csab'.
  zbtk F_3d748 D_3d748.
  zstep F_3d808 D_3d808. zstep F_3d80c D_3d80c.
  stepn F_3d810 D_3d810. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
  zbft F_3d814 D_3d814.
  zstep F_3d818 D_3d818. zstep F_3d81c D_3d81c. zstep F_3d820 D_3d820.
  stepn F_3d824 D_3d824.
  zret.
Qed.

Lemma art_alloc_c_small_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 8 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x3d71c : word) M rom)
               (mkst (regupd (regupd (regupd regs 10 (Z_to_bv 64 281474976710648)) 11 (Z_to_bv 64 (ab / 8))) 22 (Z_to_bv 64 0)) (0x3d828 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_3d71c D_3d71c. rwH. rewrite art_zb_slli by lia.
  stepn F_3d720 D_3d720. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_3d724 D_3d724. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_3d728 D_3d728 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_3d72c D_3d72c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0xd58b8 8 0xddb38) by (recell G48);
    assert (Csb' : cellA X 0xddb38 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_3d730 D_3d730. zld F_3d734 D_3d734 0xd58b8 G48'. zld F_3d738 D_3d738 0xddb38 Csb'. unfold SB.
  stepn F_3d73c D_3d73c. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_3d740 D_3d740.
  zlbu F_3d744 D_3d744 (2147450880 + ab / 8) Csab'.
  zbtk F_3d748 D_3d748.
  zstep F_3d808 D_3d808. zstep F_3d80c D_3d80c.
  stepn F_3d810 D_3d810. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia. rewrite (Z.div_small n 8) by lia.
  zbtk F_3d814 D_3d814.
  zret.
Qed.

Lemma art_alloc_d1_none : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) -> 0 <= n < 2 ^ 40 -> n mod 8 = 0 ->
  msteps ASEGS (mkst regs (0x3d828 : word) M rom) (mkst regs (0x3d8bc : word) M rom).
Proof.
  intros regs M rom n H9 H22 Hn Hn8.
  zbtk F_3d828 D_3d828. apply mst_refl.
Qed.

Lemma art_alloc_d1_part_fn : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 2 ^ 40 -> n mod 8 <> 0 ->
  n + rz <= 65536 ->
  art_layout M -> cellA M (0xdb338 + 85) 1 1 -> wrA M (2147450880 + (ab + rz + n / 8 * 8) / 8) 1 ->
  msteps ASEGS (mkst regs (0x3d828 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d830 : bv 64)%bv) 10 (Z_to_bv 64 (2147450880 + (ab + rz + n / 8 * 8) / 8))) 11 (Z_to_bv 64 (n mod 8))) 12 (Z_to_bv 64 ((ab + rz + n / 8 * 8) / 8))) 13 (Z_to_bv 64 17592186044415)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 17594333495295)) 17 (Z_to_bv 64 140737488355327)) 22 (Z_to_bv 64 (ab + rz + n / 8 * 8))) (0x3d8bc : word) (Wn 1 M (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8)) rom).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hn8 Hprim L Cpp Wsh.
  unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  zbft F_3d828 D_3d828.
  stepn F_3d82c D_3d82c.
  zcall (art_can_poison_fn _ _ _ _).
  zbft F_3d830 D_3d830.
  zstep F_3d834 D_3d834. zld F_3d838 D_3d838 0xd58b8 G48. zld F_3d83c D_3d83c 0xddb38 Csb. unfold SB.
  zstep F_3d840 D_3d840. zstep F_3d844 D_3d844. zstep F_3d848 D_3d848. zstep F_3d84c D_3d84c. zstep F_3d850 D_3d850.
  zbft F_3d854 D_3d854.
  zstep F_3d858 D_3d858. zld F_3d85c D_3d85c 0xd58c0 G50. zstep F_3d860 D_3d860. zld F_3d864 D_3d864 0xd58c8 G58.
  zld F_3d868 D_3d868 0xde828 Cmb. zld F_3d86c D_3d86c 0xde830 Cme.
  zstep F_3d870 D_3d870.
  zbtk F_3d874 D_3d874.
  zstep F_3d87c D_3d87c. zld F_3d880 D_3d880 0xd58d0 G60. zld F_3d884 D_3d884 0xde820 Che. unfold kHighMemEnd.
  zstep F_3d888 D_3d888. zstep F_3d88c D_3d88c.
  zbft F_3d890 D_3d890. zbft F_3d894 D_3d894.
  zstep F_3d898 D_3d898. zld F_3d89c D_3d89c 0xd58b0 G40.
  zlbu F_3d8a0 D_3d8a0 (0xdb338 + 85) Cpp.
  stepn F_3d8a4 D_3d8a4. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_3d8a8 D_3d8a8. zstep F_3d8ac D_3d8ac.
  stepn F_3d8b0 D_3d8b0. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
  stepn F_3d8b4 D_3d8b4. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  zsb F_3d8b8 D_3d8b8 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
  zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
