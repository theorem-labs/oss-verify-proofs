(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
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

#[using="Type"] Lemma art_alloc_c_big_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 8 <= n < 2 ^ 40 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x539a0 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x53aac : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 (n / 8 * 8))) 12 (Z_to_bv 64 0)) 22 (Z_to_bv 64 (n / 8 * 8))) (0x7bce4 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_53950 D_53950. rwH. rewrite art_zb_slli by lia.
  stepn F_53954 D_53954. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_53958 D_53958. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_5395c D_5395c (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_53960 D_53960.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x13d8c8 8 0x1460f8) by (recell G48);
    assert (Csb' : cellA X 0x1460f8 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_53964 D_53964. zld F_53968 D_53968 0x13d8c8 G48'. zld F_5396c D_5396c 0x1460f8 Csb'. unfold SB.
  stepn F_53970 D_53970. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_53974 D_53974.
  zlbu F_53978 D_53978 (2147450880 + ab / 8) Csab'.
  zbtk F_5397c D_5397c.
  zstep F_53a3c D_53a3c. zstep F_53a40 D_53a40.
  stepn F_53a44 D_53a44. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
  zbft F_53a48 D_53a48.
  zstep F_53a4c D_53a4c. zstep F_53a50 D_53a50. zstep F_53a54 D_53a54.
  stepn F_53a58 D_53a58.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_c_small_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 8 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x539a0 : word) M rom)
               (mkst (regupd (regupd (regupd regs 10 (Z_to_bv 64 281474976710648)) 11 (Z_to_bv 64 (ab / 8))) 22 (Z_to_bv 64 0)) (0x53aac : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_53950 D_53950. rwH. rewrite art_zb_slli by lia.
  stepn F_53954 D_53954. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_53958 D_53958. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_5395c D_5395c (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_53960 D_53960.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x13d8c8 8 0x1460f8) by (recell G48);
    assert (Csb' : cellA X 0x1460f8 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_53964 D_53964. zld F_53968 D_53968 0x13d8c8 G48'. zld F_5396c D_5396c 0x1460f8 Csb'. unfold SB.
  stepn F_53970 D_53970. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_53974 D_53974.
  zlbu F_53978 D_53978 (2147450880 + ab / 8) Csab'.
  zbtk F_5397c D_5397c.
  zstep F_53a3c D_53a3c. zstep F_53a40 D_53a40.
  stepn F_53a44 D_53a44. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia. rewrite (Z.div_small n 8) by lia.
  zbtk F_53a48 D_53a48.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_d1_none : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) -> 0 <= n < 2 ^ 40 -> n mod 8 = 0 ->
  msteps ASEGS (mkst regs (0x53aac : word) M rom) (mkst regs (0x53b40 : word) M rom).
Proof.
  intros regs M rom n H9 H22 Hn Hn8.
  zbtk F_53a5c D_53a5c. apply mst_refl.
Qed.

#[using="Type"] Lemma art_alloc_d1_part_fn : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 2 ^ 40 -> n mod 8 <> 0 ->
  n + rz <= 65536 ->
  art_layout M -> cellA M (0x1438f8 + 85) 1 1 -> wrA M (2147450880 + (ab + rz + n / 8 * 8) / 8) 1 ->
  msteps ASEGS (mkst regs (0x53aac : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x53ab4 : bv 64)%bv) 10 (Z_to_bv 64 (2147450880 + (ab + rz + n / 8 * 8) / 8))) 11 (Z_to_bv 64 (n mod 8))) 12 (Z_to_bv 64 ((ab + rz + n / 8 * 8) / 8))) 13 (Z_to_bv 64 17592186044415)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 17594333495295)) 17 (Z_to_bv 64 140737488355327)) 22 (Z_to_bv 64 (ab + rz + n / 8 * 8))) (0x53b40 : word) (Wn 1 M (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8)) rom).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hn8 Hprim L Cpp Wsh.
  unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  zbft F_53a5c D_53a5c.
  stepn F_53a60 D_53a60.
  zcall (art_can_poison_fn _ _ _ _).
  zbft F_53a64 D_53a64.
  zstep F_53a68 D_53a68. zld F_53a6c D_53a6c 0x13d8c8 G48. zld F_53a70 D_53a70 0x1460f8 Csb. unfold SB.
  zstep F_53a74 D_53a74. zstep F_53a78 D_53a78. zstep F_53a7c D_53a7c. zstep F_53a80 D_53a80. zstep F_53a84 D_53a84.
  zbft F_53a88 D_53a88.
  zstep F_53a8c D_53a8c. zld F_53a90 D_53a90 0x13d8d0 G50. zstep F_53a94 D_53a94. zld F_53a98 D_53a98 0x13d8d8 G58.
  zld F_53a9c D_53a9c 0x146de8 Cmb. zld F_53aa0 D_53aa0 0x146df0 Cme.
  zstep F_53aa4 D_53aa4.
  zbtk F_53aa8 D_53aa8.
  zstep F_53ab0 D_53ab0. zld F_53ab4 D_53ab4 0x13d8e0 G60. zld F_53ab8 D_53ab8 0x146de0 Che. unfold kHighMemEnd.
  zstep F_53abc D_53abc. zstep F_53ac0 D_53ac0.
  zbft F_53ac4 D_53ac4. zbft F_53ac8 D_53ac8.
  zstep F_53acc D_53acc. zld F_53ad0 D_53ad0 0x13d8c0 G40.
  zlbu F_53ad4 D_53ad4 (0x1438f8 + 85) Cpp.
  stepn F_53ad8 D_53ad8. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_53adc D_53adc. zstep F_53ae0 D_53ae0.
  stepn F_53ae4 D_53ae4. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
  stepn F_53ae8 D_53ae8. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  zsb F_53aec D_53aec (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
  zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
