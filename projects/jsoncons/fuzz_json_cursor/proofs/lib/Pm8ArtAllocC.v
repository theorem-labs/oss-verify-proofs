(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm8ArtLeaf Pm8ArtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_59000_5a000.
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

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_c_big_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 8 <= n < 2 ^ 40 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x59808 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x59914 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 (n / 8 * 8))) 12 (Z_to_bv 64 0)) 22 (Z_to_bv 64 (n / 8 * 8))) (0x81d18 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_597b8 D_597b8. rwH. rewrite art_zb_slli by lia.
  stepn F_597bc D_597bc. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_597c0 D_597c0. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_597c4 D_597c4 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_597c8 D_597c8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x153138 8 0x15c9b8) by (recell G48);
    assert (Csb' : cellA X 0x15c9b8 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_597cc D_597cc. zld F_597d0 D_597d0 0x153138 G48'. zld F_597d4 D_597d4 0x15c9b8 Csb'. unfold SB.
  stepn F_597d8 D_597d8. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_597dc D_597dc.
  zlbu F_597e0 D_597e0 (2147450880 + ab / 8) Csab'.
  zbtk F_597e4 D_597e4.
  zstep F_598a4 D_598a4. zstep F_598a8 D_598a8.
  stepn F_598ac D_598ac. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
  zbft F_598b0 D_598b0.
  zstep F_598b4 D_598b4. zstep F_598b8 D_598b8. zstep F_598bc D_598bc.
  stepn F_598c0 D_598c0.
  zret.
Qed.

Lemma art_alloc_c_small_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 8 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x59808 : word) M rom)
               (mkst (regupd (regupd (regupd regs 10 (Z_to_bv 64 281474976710648)) 11 (Z_to_bv 64 (ab / 8))) 22 (Z_to_bv 64 0)) (0x59914 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_597b8 D_597b8. rwH. rewrite art_zb_slli by lia.
  stepn F_597bc D_597bc. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_597c0 D_597c0. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_597c4 D_597c4 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_597c8 D_597c8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x153138 8 0x15c9b8) by (recell G48);
    assert (Csb' : cellA X 0x15c9b8 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_597cc D_597cc. zld F_597d0 D_597d0 0x153138 G48'. zld F_597d4 D_597d4 0x15c9b8 Csb'. unfold SB.
  stepn F_597d8 D_597d8. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_597dc D_597dc.
  zlbu F_597e0 D_597e0 (2147450880 + ab / 8) Csab'.
  zbtk F_597e4 D_597e4.
  zstep F_598a4 D_598a4. zstep F_598a8 D_598a8.
  stepn F_598ac D_598ac. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia. rewrite (Z.div_small n 8) by lia.
  zbtk F_598b0 D_598b0.
  zret.
Qed.

Lemma art_alloc_d1_none : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) -> 0 <= n < 2 ^ 40 -> n mod 8 = 0 ->
  msteps ASEGS (mkst regs (0x59914 : word) M rom) (mkst regs (0x599a8 : word) M rom).
Proof.
  intros regs M rom n H9 H22 Hn Hn8.
  zbtk F_598c4 D_598c4. apply mst_refl.
Qed.

Lemma art_alloc_d1_part_fn : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 2 ^ 40 -> n mod 8 <> 0 ->
  n + rz <= 65536 ->
  art_layout M -> cellA M (0x15a1b8 + 85) 1 1 -> wrA M (2147450880 + (ab + rz + n / 8 * 8) / 8) 1 ->
  msteps ASEGS (mkst regs (0x59914 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5991c : bv 64)%bv) 10 (Z_to_bv 64 (2147450880 + (ab + rz + n / 8 * 8) / 8))) 11 (Z_to_bv 64 (n mod 8))) 12 (Z_to_bv 64 ((ab + rz + n / 8 * 8) / 8))) 13 (Z_to_bv 64 17592186044415)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 17594333495295)) 17 (Z_to_bv 64 140737488355327)) 22 (Z_to_bv 64 (ab + rz + n / 8 * 8))) (0x599a8 : word) (Wn 1 M (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8)) rom).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hn8 Hprim L Cpp Wsh.
  unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  zbft F_598c4 D_598c4.
  stepn F_598c8 D_598c8.
  zcall (art_can_poison_fn _ _ _ _).
  zbft F_598cc D_598cc.
  zstep F_598d0 D_598d0. zld F_598d4 D_598d4 0x153138 G48. zld F_598d8 D_598d8 0x15c9b8 Csb. unfold SB.
  zstep F_598dc D_598dc. zstep F_598e0 D_598e0. zstep F_598e4 D_598e4. zstep F_598e8 D_598e8. zstep F_598ec D_598ec.
  zbft F_598f0 D_598f0.
  zstep F_598f4 D_598f4. zld F_598f8 D_598f8 0x153140 G50. zstep F_598fc D_598fc. zld F_59900 D_59900 0x153148 G58.
  zld F_59904 D_59904 0x15d6a8 Cmb. zld F_59908 D_59908 0x15d6b0 Cme.
  zstep F_5990c D_5990c.
  zbtk F_59910 D_59910.
  zstep F_59918 D_59918. zld F_5991c D_5991c 0x153150 G60. zld F_59920 D_59920 0x15d6a0 Che. unfold kHighMemEnd.
  zstep F_59924 D_59924. zstep F_59928 D_59928.
  zbft F_5992c D_5992c. zbft F_59930 D_59930.
  zstep F_59934 D_59934. zld F_59938 D_59938 0x153130 G40.
  zlbu F_5993c D_5993c (0x15a1b8 + 85) Cpp.
  stepn F_59940 D_59940. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_59944 D_59944. zstep F_59948 D_59948.
  stepn F_5994c D_5994c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
  stepn F_59950 D_59950. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  zsb F_59954 D_59954 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
  zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
