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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_3d2b4_3e23c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
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
  msteps ASEGS (mkst regs (0x3d99c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x3daa8 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 (n / 8 * 8))) 12 (Z_to_bv 64 0)) 22 (Z_to_bv 64 (n / 8 * 8))) (0x611f8 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_3d99c D_3d99c. rwH. rewrite art_zb_slli by lia.
  stepn F_3d9a0 D_3d9a0. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_3d9a4 D_3d9a4. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_3d9a8 D_3d9a8 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_3d9ac D_3d9ac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0xd64c8 8 0xde738) by (recell G48);
    assert (Csb' : cellA X 0xde738 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_3d9b0 D_3d9b0. zld F_3d9b4 D_3d9b4 0xd64c8 G48'. zld F_3d9b8 D_3d9b8 0xde738 Csb'. unfold SB.
  stepn F_3d9bc D_3d9bc. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_3d9c0 D_3d9c0.
  zlbu F_3d9c4 D_3d9c4 (2147450880 + ab / 8) Csab'.
  zbtk F_3d9c8 D_3d9c8.
  zstep F_3da88 D_3da88. zstep F_3da8c D_3da8c.
  stepn F_3da90 D_3da90. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
  zbft F_3da94 D_3da94.
  zstep F_3da98 D_3da98. zstep F_3da9c D_3da9c. zstep F_3daa0 D_3daa0.
  stepn F_3daa4 D_3daa4.
  zret.
Qed.

Lemma art_alloc_c_small_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 8 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x3d99c : word) M rom)
               (mkst (regupd (regupd (regupd regs 10 (Z_to_bv 64 281474976710648)) 11 (Z_to_bv 64 (ab / 8))) 22 (Z_to_bv 64 0)) (0x3daa8 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_3d99c D_3d99c. rwH. rewrite art_zb_slli by lia.
  stepn F_3d9a0 D_3d9a0. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_3d9a4 D_3d9a4. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_3d9a8 D_3d9a8 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_3d9ac D_3d9ac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0xd64c8 8 0xde738) by (recell G48);
    assert (Csb' : cellA X 0xde738 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_3d9b0 D_3d9b0. zld F_3d9b4 D_3d9b4 0xd64c8 G48'. zld F_3d9b8 D_3d9b8 0xde738 Csb'. unfold SB.
  stepn F_3d9bc D_3d9bc. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_3d9c0 D_3d9c0.
  zlbu F_3d9c4 D_3d9c4 (2147450880 + ab / 8) Csab'.
  zbtk F_3d9c8 D_3d9c8.
  zstep F_3da88 D_3da88. zstep F_3da8c D_3da8c.
  stepn F_3da90 D_3da90. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia. rewrite (Z.div_small n 8) by lia.
  zbtk F_3da94 D_3da94.
  zret.
Qed.

Lemma art_alloc_d1_none : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) -> 0 <= n < 2 ^ 40 -> n mod 8 = 0 ->
  msteps ASEGS (mkst regs (0x3daa8 : word) M rom) (mkst regs (0x3db3c : word) M rom).
Proof.
  intros regs M rom n H9 H22 Hn Hn8.
  zbtk F_3daa8 D_3daa8. apply mst_refl.
Qed.

Lemma art_alloc_d1_part_fn : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 2 ^ 40 -> n mod 8 <> 0 ->
  n + rz <= 65536 ->
  art_layout M -> cellA M (0xdbf38 + 85) 1 1 -> wrA M (2147450880 + (ab + rz + n / 8 * 8) / 8) 1 ->
  msteps ASEGS (mkst regs (0x3daa8 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3dab0 : bv 64)%bv) 10 (Z_to_bv 64 (2147450880 + (ab + rz + n / 8 * 8) / 8))) 11 (Z_to_bv 64 (n mod 8))) 12 (Z_to_bv 64 ((ab + rz + n / 8 * 8) / 8))) 13 (Z_to_bv 64 17592186044415)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 17594333495295)) 17 (Z_to_bv 64 140737488355327)) 22 (Z_to_bv 64 (ab + rz + n / 8 * 8))) (0x3db3c : word) (Wn 1 M (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8)) rom).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hn8 Hprim L Cpp Wsh.
  unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  zbft F_3daa8 D_3daa8.
  stepn F_3daac D_3daac.
  zcall (art_can_poison_fn _ _ _ _).
  zbft F_3dab0 D_3dab0.
  zstep F_3dab4 D_3dab4. zld F_3dab8 D_3dab8 0xd64c8 G48. zld F_3dabc D_3dabc 0xde738 Csb. unfold SB.
  zstep F_3dac0 D_3dac0. zstep F_3dac4 D_3dac4. zstep F_3dac8 D_3dac8. zstep F_3dacc D_3dacc. zstep F_3dad0 D_3dad0.
  zbft F_3dad4 D_3dad4.
  zstep F_3dad8 D_3dad8. zld F_3dadc D_3dadc 0xd64d0 G50. zstep F_3dae0 D_3dae0. zld F_3dae4 D_3dae4 0xd64d8 G58.
  zld F_3dae8 D_3dae8 0xdf428 Cmb. zld F_3daec D_3daec 0xdf430 Cme.
  zstep F_3daf0 D_3daf0.
  zbtk F_3daf4 D_3daf4.
  zstep F_3dafc D_3dafc. zld F_3db00 D_3db00 0xd64e0 G60. zld F_3db04 D_3db04 0xdf420 Che. unfold kHighMemEnd.
  zstep F_3db08 D_3db08. zstep F_3db0c D_3db0c.
  zbft F_3db10 D_3db10. zbft F_3db14 D_3db14.
  zstep F_3db18 D_3db18. zld F_3db1c D_3db1c 0xd64c0 G40.
  zlbu F_3db20 D_3db20 (0xdbf38 + 85) Cpp.
  stepn F_3db24 D_3db24. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_3db28 D_3db28. zstep F_3db2c D_3db2c.
  stepn F_3db30 D_3db30. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
  stepn F_3db34 D_3db34. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  zsb F_3db38 D_3db38 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
  zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
