(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_59000_5a000.
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

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_c_big_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 8 <= n < 2 ^ 40 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x59bc8 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x59cd4 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 (n / 8 * 8))) 12 (Z_to_bv 64 0)) 22 (Z_to_bv 64 (n / 8 * 8))) (0x820d8 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_59b80 D_59b80. rwH. rewrite art_zb_slli by lia.
  stepn F_59b84 D_59b84. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_59b88 D_59b88. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_59b8c D_59b8c (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_59b90 D_59b90.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x154500 8 0x15dcf8) by (recell G48);
    assert (Csb' : cellA X 0x15dcf8 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_59b94 D_59b94. zld F_59b98 D_59b98 0x154500 G48'. zld F_59b9c D_59b9c 0x15dcf8 Csb'. unfold SB.
  stepn F_59ba0 D_59ba0. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_59ba4 D_59ba4.
  zlbu F_59ba8 D_59ba8 (2147450880 + ab / 8) Csab'.
  zbtk F_59bac D_59bac.
  zstep F_59c6c D_59c6c. zstep F_59c70 D_59c70.
  stepn F_59c74 D_59c74. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
  zbft F_59c78 D_59c78.
  zstep F_59c7c D_59c7c. zstep F_59c80 D_59c80. zstep F_59c84 D_59c84.
  stepn F_59c88 D_59c88.
  zret.
Qed.

Lemma art_alloc_c_small_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 8 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x59bc8 : word) M rom)
               (mkst (regupd (regupd (regupd regs 10 (Z_to_bv 64 281474976710648)) 11 (Z_to_bv 64 (ab / 8))) 22 (Z_to_bv 64 0)) (0x59cd4 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_59b80 D_59b80. rwH. rewrite art_zb_slli by lia.
  stepn F_59b84 D_59b84. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_59b88 D_59b88. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_59b8c D_59b8c (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_59b90 D_59b90.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x154500 8 0x15dcf8) by (recell G48);
    assert (Csb' : cellA X 0x15dcf8 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_59b94 D_59b94. zld F_59b98 D_59b98 0x154500 G48'. zld F_59b9c D_59b9c 0x15dcf8 Csb'. unfold SB.
  stepn F_59ba0 D_59ba0. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_59ba4 D_59ba4.
  zlbu F_59ba8 D_59ba8 (2147450880 + ab / 8) Csab'.
  zbtk F_59bac D_59bac.
  zstep F_59c6c D_59c6c. zstep F_59c70 D_59c70.
  stepn F_59c74 D_59c74. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia. rewrite (Z.div_small n 8) by lia.
  zbtk F_59c78 D_59c78.
  zret.
Qed.

Lemma art_alloc_d1_none : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) -> 0 <= n < 2 ^ 40 -> n mod 8 = 0 ->
  msteps ASEGS (mkst regs (0x59cd4 : word) M rom) (mkst regs (0x59d68 : word) M rom).
Proof.
  intros regs M rom n H9 H22 Hn Hn8.
  zbtk F_59c8c D_59c8c. apply mst_refl.
Qed.

Lemma art_alloc_d1_part_fn : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 2 ^ 40 -> n mod 8 <> 0 ->
  n + rz <= 65536 ->
  art_layout M -> cellA M (0x15b4f8 + 85) 1 1 -> wrA M (2147450880 + (ab + rz + n / 8 * 8) / 8) 1 ->
  msteps ASEGS (mkst regs (0x59cd4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x59cdc : bv 64)%bv) 10 (Z_to_bv 64 (2147450880 + (ab + rz + n / 8 * 8) / 8))) 11 (Z_to_bv 64 (n mod 8))) 12 (Z_to_bv 64 ((ab + rz + n / 8 * 8) / 8))) 13 (Z_to_bv 64 17592186044415)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 17594333495295)) 17 (Z_to_bv 64 140737488355327)) 22 (Z_to_bv 64 (ab + rz + n / 8 * 8))) (0x59d68 : word) (Wn 1 M (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8)) rom).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hn8 Hprim L Cpp Wsh.
  unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  zbft F_59c8c D_59c8c.
  stepn F_59c90 D_59c90.
  zcall (art_can_poison_fn _ _ _ _).
  zbft F_59c94 D_59c94.
  zstep F_59c98 D_59c98. zld F_59c9c D_59c9c 0x154500 G48. zld F_59ca0 D_59ca0 0x15dcf8 Csb. unfold SB.
  zstep F_59ca4 D_59ca4. zstep F_59ca8 D_59ca8. zstep F_59cac D_59cac. zstep F_59cb0 D_59cb0. zstep F_59cb4 D_59cb4.
  zbft F_59cb8 D_59cb8.
  zstep F_59cbc D_59cbc. zld F_59cc0 D_59cc0 0x154508 G50. zstep F_59cc4 D_59cc4. zld F_59cc8 D_59cc8 0x154510 G58.
  zld F_59ccc D_59ccc 0x15e9e8 Cmb. zld F_59cd0 D_59cd0 0x15e9f0 Cme.
  zstep F_59cd4 D_59cd4.
  zbtk F_59cd8 D_59cd8.
  zstep F_59ce0 D_59ce0. zld F_59ce4 D_59ce4 0x154518 G60. zld F_59ce8 D_59ce8 0x15e9e0 Che. unfold kHighMemEnd.
  zstep F_59cec D_59cec. zstep F_59cf0 D_59cf0.
  zbft F_59cf4 D_59cf4. zbft F_59cf8 D_59cf8.
  zstep F_59cfc D_59cfc. zld F_59d00 D_59d00 0x1544f8 G40.
  zlbu F_59d04 D_59d04 (0x15b4f8 + 85) Cpp.
  stepn F_59d08 D_59d08. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_59d0c D_59d0c. zstep F_59d10 D_59d10.
  stepn F_59d14 D_59d14. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
  stepn F_59d18 D_59d18. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  zsb F_59d1c D_59d1c (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
  zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
