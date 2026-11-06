(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm5ArtLeaf Pm5ArtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_5b000_5c000.
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
  msteps ASEGS (mkst regs (0x5b4a4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x5b5b0 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 (n / 8 * 8))) 12 (Z_to_bv 64 0)) 22 (Z_to_bv 64 (n / 8 * 8))) (0x839b4 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_5b45c D_5b45c. rwH. rewrite art_zb_slli by lia.
  stepn F_5b460 D_5b460. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_5b464 D_5b464. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_5b468 D_5b468 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_5b46c D_5b46c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x164518 8 0x16d7b8) by (recell G48);
    assert (Csb' : cellA X 0x16d7b8 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_5b470 D_5b470. zld F_5b474 D_5b474 0x164518 G48'. zld F_5b478 D_5b478 0x16d7b8 Csb'. unfold SB.
  stepn F_5b47c D_5b47c. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_5b480 D_5b480.
  zlbu F_5b484 D_5b484 (2147450880 + ab / 8) Csab'.
  zbtk F_5b488 D_5b488.
  zstep F_5b548 D_5b548. zstep F_5b54c D_5b54c.
  stepn F_5b550 D_5b550. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia.
  zbft F_5b554 D_5b554.
  zstep F_5b558 D_5b558. zstep F_5b55c D_5b55c. zstep F_5b560 D_5b560.
  stepn F_5b564 D_5b564.
  zret.
Qed.

Lemma art_alloc_c_small_fn : forall regs (M rom : word -> option byte) (ab n rz id sab : Z),
  getr regs 10 = Z_to_bv 64 id -> getr regs 8 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 n -> getr regs 18 = Z_to_bv 64 ab ->
  getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 21 = Z_to_bv 64 (ab + rz - 16) -> getr regs 24 = Z_to_bv 64 0 ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 8 -> 0 <= id < 2 ^ 32 -> 1 <= sab < 256 ->
  wrA M (ab + rz - 16) 16 -> art_layout M -> cellA M (2147450880 + ab / 8) 1 sab ->
  msteps ASEGS (mkst regs (0x5b4a4 : word) M rom)
               (mkst (regupd (regupd (regupd regs 10 (Z_to_bv 64 281474976710648)) 11 (Z_to_bv 64 (ab / 8))) 22 (Z_to_bv 64 0)) (0x5b5b0 : word) (Wn 8 M (ab + rz - 8) id) rom).
Proof.
  intros regs M rom ab n rz id sab H10 H8 H9 H18 H20 H21 H24 Hab Hab' Hab16 Hrz Hrz16 Hn Hid Hsab W L Csab. unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & _).
  stepn F_5b45c D_5b45c. rwH. rewrite art_zb_slli by lia.
  stepn F_5b460 D_5b460. rwH. rewrite (art_zb_srli_exact _ 32 id) by lia.
  stepn F_5b464 D_5b464. rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_l.
  zsd F_5b468 D_5b468 (ab + rz - 16 + 8) id ltac:(rewok W).
  zbft F_5b46c D_5b46c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (G48' : cellA X 0x164518 8 0x16d7b8) by (recell G48);
    assert (Csb' : cellA X 0x16d7b8 8 SB) by (recell Csb);
    assert (Csab' : cellA X (2147450880 + ab / 8) 1 sab) by (recell Csab) end.
  zstep F_5b470 D_5b470. zld F_5b474 D_5b474 0x164518 G48'. zld F_5b478 D_5b478 0x16d7b8 Csb'. unfold SB.
  stepn F_5b47c D_5b47c. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_5b480 D_5b480.
  zlbu F_5b484 D_5b484 (2147450880 + ab / 8) Csab'.
  zbtk F_5b488 D_5b488.
  zstep F_5b548 D_5b548. zstep F_5b54c D_5b54c.
  stepn F_5b550 D_5b550. rwH. rewrite art_zb_and by lia. rewrite art_land_m8_48 by lia. rewrite (Z.div_small n 8) by lia.
  zbtk F_5b554 D_5b554.
  zret.
Qed.

Lemma art_alloc_d1_none : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) -> 0 <= n < 2 ^ 40 -> n mod 8 = 0 ->
  msteps ASEGS (mkst regs (0x5b5b0 : word) M rom) (mkst regs (0x5b644 : word) M rom).
Proof.
  intros regs M rom n H9 H22 Hn Hn8.
  zbtk F_5b568 D_5b568. apply mst_refl.
Qed.

Lemma art_alloc_d1_part_fn : forall regs (M rom : word -> option byte) (ab n rz : Z),
  getr regs 9 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 (ab + rz) -> getr regs 22 = Z_to_bv 64 (n / 8 * 8) ->
  kHighMemBeg <= ab -> ab + 65536 < 2 ^ 47 -> ab mod 16 = 0 -> 16 <= rz <= 2048 -> rz mod 16 = 0 -> 1 <= n < 2 ^ 40 -> n mod 8 <> 0 ->
  n + rz <= 65536 ->
  art_layout M -> cellA M (0x16afb8 + 85) 1 1 -> wrA M (2147450880 + (ab + rz + n / 8 * 8) / 8) 1 ->
  msteps ASEGS (mkst regs (0x5b5b0 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5b5b8 : bv 64)%bv) 10 (Z_to_bv 64 (2147450880 + (ab + rz + n / 8 * 8) / 8))) 11 (Z_to_bv 64 (n mod 8))) 12 (Z_to_bv 64 ((ab + rz + n / 8 * 8) / 8))) 13 (Z_to_bv 64 17592186044415)) 14 (Z_to_bv 64 (2 ^ 64 - 1))) 15 (Z_to_bv 64 0)) 16 (Z_to_bv 64 17594333495295)) 17 (Z_to_bv 64 140737488355327)) 22 (Z_to_bv 64 (ab + rz + n / 8 * 8))) (0x5b644 : word) (Wn 1 M (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8)) rom).
Proof.
  intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hn8 Hprim L Cpp Wsh.
  unfold kHighMemBeg in *.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  zbft F_5b568 D_5b568.
  stepn F_5b56c D_5b56c.
  zcall (art_can_poison_fn _ _ _ _).
  zbft F_5b570 D_5b570.
  zstep F_5b574 D_5b574. zld F_5b578 D_5b578 0x164518 G48. zld F_5b57c D_5b57c 0x16d7b8 Csb. unfold SB.
  zstep F_5b580 D_5b580. zstep F_5b584 D_5b584. zstep F_5b588 D_5b588. zstep F_5b58c D_5b58c. zstep F_5b590 D_5b590.
  zbft F_5b594 D_5b594.
  zstep F_5b598 D_5b598. zld F_5b59c D_5b59c 0x164520 G50. zstep F_5b5a0 D_5b5a0. zld F_5b5a4 D_5b5a4 0x164528 G58.
  zld F_5b5a8 D_5b5a8 0x16e4a8 Cmb. zld F_5b5ac D_5b5ac 0x16e4b0 Cme.
  zstep F_5b5b0 D_5b5b0.
  zbtk F_5b5b4 D_5b5b4.
  zstep F_5b5bc D_5b5bc. zld F_5b5c0 D_5b5c0 0x164530 G60. zld F_5b5c4 D_5b5c4 0x16e4a0 Che. unfold kHighMemEnd.
  zstep F_5b5c8 D_5b5c8. zstep F_5b5cc D_5b5cc.
  zbft F_5b5d0 D_5b5d0. zbft F_5b5d4 D_5b5d4.
  zstep F_5b5d8 D_5b5d8. zld F_5b5dc D_5b5dc 0x164510 G40.
  zlbu F_5b5e0 D_5b5e0 (0x16afb8 + 85) Cpp.
  stepn F_5b5e4 D_5b5e4. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_5b5e8 D_5b5e8. zstep F_5b5ec D_5b5ec.
  stepn F_5b5f0 D_5b5f0. rwH. rewrite art_zb_and by lia. rewrite art_land_full_r by lia.
  stepn F_5b5f4 D_5b5f4. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  zsb F_5b5f8 D_5b5f8 (2147450880 + (ab + rz + n / 8 * 8) / 8) (n mod 8) ltac:(rewok Wsh).
  zret.
Qed.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
