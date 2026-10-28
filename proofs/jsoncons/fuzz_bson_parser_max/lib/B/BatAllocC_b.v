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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3cf10_3de98_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
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

#[using="Type"] Lemma art_alloc_c_big_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 8 <= n < 2 ^ 40 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x52990 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x52a9c : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 (n / 8 * 8))) 12 (Z_to_bv 64 0)) 22 (Z_to_bv 64 (n / 8 * 8))) (0x7ab38 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_52578 D_52578. rwH. rewrite art_zb_slli by lia.
  stepn F_5257c D_5257c. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_52580 D_52580. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_52584 D_52584 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_52588 D_52588.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x1374c0 8 0x13fc38) by (recell G48);
    assert (Csb' : cellA X 0x13fc38 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_5258c D_5258c. zld F_52590 D_52590 0x1374c0 G48'. zld F_52594 D_52594 0x13fc38 Csb'. unfold SB.
  stepn F_52598 D_52598. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_5259c D_5259c.
  zlbu F_525a0 D_525a0 (2147450880 + ab / 8) Csab'.
  zbtk F_525a4 D_525a4.
  zstep F_52664 D_52664. zstep F_52668 D_52668.
  stepn F_5266c D_5266c. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
  zbft F_52670 D_52670.
  zstep F_52674 D_52674. zstep F_52678 D_52678. zstep F_5267c D_5267c.
  stepn F_52680 D_52680.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_c_small_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 8 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x52990 : word) M rom)
               (mkst (regupd (regupd (regupd regs 10 (Z_to_bv 64 281474976710648)) 11 (Z_to_bv 64 (ab / 8))) 22 (Z_to_bv 64 0)) (0x52a9c : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_52578 D_52578. rwH. rewrite art_zb_slli by lia.
  stepn F_5257c D_5257c. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_52580 D_52580. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_52584 D_52584 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_52588 D_52588.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x1374c0 8 0x13fc38) by (recell G48);
    assert (Csb' : cellA X 0x13fc38 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_5258c D_5258c. zld F_52590 D_52590 0x1374c0 G48'. zld F_52594 D_52594 0x13fc38 Csb'. unfold SB.
  stepn F_52598 D_52598. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_5259c D_5259c.
  zlbu F_525a0 D_525a0 (2147450880 + ab / 8) Csab'.
  zbtk F_525a4 D_525a4.
  zstep F_52664 D_52664. zstep F_52668 D_52668.
  stepn F_5266c D_5266c. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia. rewrite (Z.div_small n 8) by lia.
  zbtk F_52670 D_52670.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_d1_none : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) -> 0 <= n < 2 ^ 40 -> n mod 8 = 0 ->
  msteps ASEGS (mkst regs (0x52a9c : word) M rom) (mkst regs (0x52b30 : word) M rom).
Proof.
  intros regs M rom n H9 H22 Hn Hn8.
  zbtk F_52684 D_52684. apply mst_refl.
Qed.

#[using="Type"] Lemma art_alloc_d1_part_fn : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 2 ^ 40 -> n mod 8 <> 0 ->
  n + rz <= 65536 ->
  art_layout M -> cellA M (0x13d438 + 85) 1 1 -> wrA M (2147450880 + (ab + rz + n / 8 * 8) / 8) 1 ->
  msteps ASEGS (mkst regs (0x52a9c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52aa4 : bv 64)%bv) 10 (Z_to_bv 64 (2147450880 + (ab + rz + n / 8 * 8) / 8))) 11 (Z_to_bv 64 (n mod 8))) 12 (Z_to_bv 64 ((ab + rz + n / 8 * 8) / 8))) 13 (Z_to_bv 64 17592186044415)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 17594333495295)) 17 (Z_to_bv 64 140737488355327)) 22 (Z_to_bv 64 (ab + rz + n / 8 * 8))) (0x52b30 : word) (Wn 1 M (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8)) rom).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hn8 Hprim L Cpp Wsh.
  unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  zbft F_52684 D_52684.
  stepn F_52688 D_52688.
  zcall (art_can_poison_fn _ _ _ _).
  zbft F_5268c D_5268c.
  zstep F_52690 D_52690. zld F_52694 D_52694 0x1374c0 G48. zld F_52698 D_52698 0x13fc38 Csb. unfold SB.
  zstep F_5269c D_5269c. zstep F_526a0 D_526a0. zstep F_526a4 D_526a4. zstep F_526a8 D_526a8. zstep F_526ac D_526ac.
  zbft F_526b0 D_526b0.
  zstep F_526b4 D_526b4. zld F_526b8 D_526b8 0x1374c8 G50. zstep F_526bc D_526bc. zld F_526c0 D_526c0 0x1374d0 G58.
  zld F_526c4 D_526c4 0x140928 Cmb. zld F_526c8 D_526c8 0x140930 Cme.
  zstep F_526cc D_526cc.
  zbtk F_526d0 D_526d0.
  zstep F_526d8 D_526d8. zld F_526dc D_526dc 0x1374d8 G60. zld F_526e0 D_526e0 0x140920 Che. unfold kHighMemEnd.
  zstep F_526e4 D_526e4. zstep F_526e8 D_526e8.
  zbft F_526ec D_526ec. zbft F_526f0 D_526f0.
  zstep F_526f4 D_526f4. zld F_526f8 D_526f8 0x1374b8 G40.
  zlbu F_526fc D_526fc (0x13d438 + 85) Cpp.
  stepn F_52700 D_52700. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_52704 D_52704. zstep F_52708 D_52708.
  stepn F_5270c D_5270c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
  stepn F_52710 D_52710. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  zsb F_52714 D_52714 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
  zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
