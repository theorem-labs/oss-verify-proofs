(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm4ArtLeaf Pm4ArtRzLog Pm4ArtAllocA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_5a000_5b000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_alloc_memA1_16 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 32).

Lemma art_land_m16 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551600 = x / 16 * 16.
Proof.
  intros x Hx. change 18446744073709551600 with (Z.shiftl (Z.ones 60) 4).
  change 16 with (2 ^ 4). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 4) as [L|G].
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
    replace (i - 4 + 4) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [L2|G2].
    + replace ((0 <=? i - 4) && (i - 4 <? 60))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply Bool.andb_true_r.
    + assert (Tf : Z.testbit x i = false).
      { destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
        apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
      rewrite Tf. reflexivity.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_a1_16_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 16 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x6c0000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x104e0 1 4 -> cellA M 0x16abd8 1 1 -> cellA M 0x1ec162 1 0 ->
  msteps ASEGS (mkst regs (0x5a828 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5a884 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 16)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 32)) 12 (Z_to_bv 64 0x104d8)) 13 (Z_to_bv 64 (2 ^ 64 - 16))) 18 (Z_to_bv 64 16)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 15)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x5a8c0 : word) (art_alloc_memA1_16 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & _ & R3) R2 Ci Cr.
  zstep F_5a7d8 D_5a7d8.
  zsd F_5a7dc D_5a7dc (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_5a7e0 D_5a7e0 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5a7e4 D_5a7e4 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5a7e8 D_5a7e8 (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_5a7ec D_5a7ec (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_5a7f0 D_5a7f0 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_5a7f4 D_5a7f4 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_5a7f8 D_5a7f8 (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_5a7fc D_5a7fc (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_5a800 D_5a800 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_5a804 D_5a804 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_5a808 D_5a808 (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_5a80c D_5a80c (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_5a810 D_5a810. zstep F_5a814 D_5a814. zstep F_5a818 D_5a818. zstep F_5a81c D_5a81c. zstep F_5a820 D_5a820. zstep F_5a824 D_5a824.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x16abd8 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1ec162 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10460 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104e0 1 4) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_5a828 D_5a828.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_5a82c D_5a82c.
  stepn F_5a830 D_5a830.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_5a834 D_5a834.
  zbft F_5a838 D_5a838.
  zstep F_5a83c D_5a83c.
  zbtk F_5a840 D_5a840.
  zstep F_5a87c D_5a87c. zstep F_5a880 D_5a880.
  zbtk F_5a884 D_5a884.
  zstep F_5a88c D_5a88c. zstep F_5a890 D_5a890.
  zbft F_5a894 D_5a894.
  zstep F_5a898 D_5a898. zld F_5a89c D_5a89c 0x10460 R1'.
  zstep F_5a8a0 D_5a8a0. zstep F_5a8a4 D_5a8a4. zstep F_5a8a8 D_5a8a8. zstep F_5a8ac D_5a8ac. zstep F_5a8b0 D_5a8b0. zstep F_5a8b4 D_5a8b4.
  zstep F_5a8b8 D_5a8b8.
  zlbu F_5a8bc D_5a8bc 0x104e0 R2'.
  zstep F_5a8c0 D_5a8c0. zstep F_5a8c4 D_5a8c4. zstep F_5a8c8 D_5a8c8. zstep F_5a8cc D_5a8cc.
  zbft F_5a8d0 D_5a8d0.
  zstep F_5a8d4 D_5a8d4. zstep F_5a854 D_5a854. zstep F_5a858 D_5a858.
  zbft F_5a85c D_5a85c.
  zstep F_5a860 D_5a860. zstep F_5a864 D_5a864.
  zsd F_5a868 D_5a868 (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_5a86c D_5a86c (sp - 128 + 16) 32 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1_16. zret.
Qed.

Lemma art_alloc_a3_16_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 16 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 16 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x6c0000 -> 0x6c0000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 15) / 16 * 16 -> rz = 16 * 2 ^ r -> rs + rz + 16 <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x5a9dc : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5aac8 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + 16 + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + 16 + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 16))) 26 (Z_to_bv 64 t)) (0x5ef80 : word) (Wn 8 M (sp - 8) 0x5aaac) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs16 : exists q16, rs = 16 * q16) by (exists ((Z.max n 8 + 15) / 16); lia). destruct Hrs16 as (q16 & Hrs16).
  assert (Hrs8 : (rs + 16) mod 8 = 0) by (rewrite Hrs16; replace (16 * q16 + 16) with ((2 * q16 + 2) * 8) by lia; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 15) 16 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 15) 16 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_5a98c D_5a98c. zstep F_5a990 D_5a990. zstep F_5a994 D_5a994. zstep F_5a998 D_5a998. zstep F_5a99c D_5a99c.
  stepn F_5a9a0 D_5a9a0. rwH. rewrite art_zb_and by lia. rewrite art_land_m16 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 16 * 16)] => replace (e / 16 * 16) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_5a9a4 D_5a9a4. zstep F_5a9a8 D_5a9a8.
  stepn F_5a9ac D_5a9ac. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_5a9b0 D_5a9b0.
  zstep F_5a9b4 D_5a9b4. zstep F_5a9b8 D_5a9b8. zstep F_5a9bc D_5a9bc.
  stepn F_5a9c0 D_5a9c0. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_5a9c4 D_5a9c4. zstep F_5a9c8 D_5a9c8. zstep F_5a9cc D_5a9cc. zstep F_5a9d0 D_5a9d0. zstep F_5a9d4 D_5a9d4. zstep F_5a9d8 D_5a9d8.
  zstep F_5a9dc D_5a9dc.
  stepn F_5a9e0 D_5a9e0. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_5a9e4 D_5a9e4. zstep F_5a9e8 D_5a9e8.
  zbft F_5a9ec D_5a9ec. zbft F_5a9f0 D_5a9f0.
  zld F_5a9f4 D_5a9f4 (ia + 3616) Cmax.
  zbtk F_5a9f8 D_5a9f8.
  stepn F_5aa58 D_5aa58.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_5aa60 D_5aa60 || (zstep F_5aa5c D_5aa5c; zbft F_5aa60 D_5aa60).
  zstep F_5aa64 D_5aa64. zstep F_5aa68 D_5aa68. zstep F_5aa6c D_5aa6c. zstep F_5aa70 D_5aa70.
  stepn F_5aa74 D_5aa74.
  zret.
Qed.
End FPX.
