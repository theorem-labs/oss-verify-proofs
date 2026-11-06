(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtRzLog Pm9ArtAllocA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_59000_5a000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
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
  wrA M (sp - 256) 256 -> 0x6b4000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x104f8 1 4 -> cellA M 0x15e9d8 1 1 -> cellA M 0x1dff62 1 0 ->
  msteps ASEGS (mkst regs (0x5981c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x59878 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 16)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 32)) 12 (Z_to_bv 64 0x104f0)) 13 (Z_to_bv 64 (2 ^ 64 - 16))) 18 (Z_to_bv 64 16)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 15)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x598b4 : word) (art_alloc_memA1_16 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & _ & R3) R2 Ci Cr.
  zstep F_597d4 D_597d4.
  zsd F_597d8 D_597d8 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_597dc D_597dc (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_597e0 D_597e0 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_597e4 D_597e4 (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_597e8 D_597e8 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_597ec D_597ec (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_597f0 D_597f0 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_597f4 D_597f4 (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_597f8 D_597f8 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_597fc D_597fc (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_59800 D_59800 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_59804 D_59804 (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_59808 D_59808 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_5980c D_5980c. zstep F_59810 D_59810. zstep F_59814 D_59814. zstep F_59818 D_59818. zstep F_5981c D_5981c. zstep F_59820 D_59820.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x15e9d8 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1dff62 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10478 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104f8 1 4) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_59824 D_59824.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_59828 D_59828.
  stepn F_5982c D_5982c.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_59830 D_59830.
  zbft F_59834 D_59834.
  zstep F_59838 D_59838.
  zbtk F_5983c D_5983c.
  zstep F_59878 D_59878. zstep F_5987c D_5987c.
  zbtk F_59880 D_59880.
  zstep F_59888 D_59888. zstep F_5988c D_5988c.
  zbft F_59890 D_59890.
  zstep F_59894 D_59894. zld F_59898 D_59898 0x10478 R1'.
  zstep F_5989c D_5989c. zstep F_598a0 D_598a0. zstep F_598a4 D_598a4. zstep F_598a8 D_598a8. zstep F_598ac D_598ac. zstep F_598b0 D_598b0.
  zstep F_598b4 D_598b4.
  zlbu F_598b8 D_598b8 0x104f8 R2'.
  zstep F_598bc D_598bc. zstep F_598c0 D_598c0. zstep F_598c4 D_598c4. zstep F_598c8 D_598c8.
  zbft F_598cc D_598cc.
  zstep F_598d0 D_598d0. zstep F_59850 D_59850. zstep F_59854 D_59854.
  zbft F_59858 D_59858.
  zstep F_5985c D_5985c. zstep F_59860 D_59860.
  zsd F_59864 D_59864 (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_59868 D_59868 (sp - 128 + 16) 32 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1_16. zret.
Qed.

Lemma art_alloc_a3_16_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 16 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 16 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x6b4000 -> 0x6b4000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 15) / 16 * 16 -> rz = 16 * 2 ^ r -> rs + rz + 16 <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x599d0 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x59abc : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + 16 + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + 16 + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 16))) 26 (Z_to_bv 64 t)) (0x5df74 : word) (Wn 8 M (sp - 8) 0x59aa0) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs16 : exists q16, rs = 16 * q16) by (exists ((Z.max n 8 + 15) / 16); lia). destruct Hrs16 as (q16 & Hrs16).
  assert (Hrs8 : (rs + 16) mod 8 = 0) by (rewrite Hrs16; replace (16 * q16 + 16) with ((2 * q16 + 2) * 8) by lia; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 15) 16 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 15) 16 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_59988 D_59988. zstep F_5998c D_5998c. zstep F_59990 D_59990. zstep F_59994 D_59994. zstep F_59998 D_59998.
  stepn F_5999c D_5999c. rwH. rewrite art_zb_and by lia. rewrite art_land_m16 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 16 * 16)] => replace (e / 16 * 16) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_599a0 D_599a0. zstep F_599a4 D_599a4.
  stepn F_599a8 D_599a8. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_599ac D_599ac.
  zstep F_599b0 D_599b0. zstep F_599b4 D_599b4. zstep F_599b8 D_599b8.
  stepn F_599bc D_599bc. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_599c0 D_599c0. zstep F_599c4 D_599c4. zstep F_599c8 D_599c8. zstep F_599cc D_599cc. zstep F_599d0 D_599d0. zstep F_599d4 D_599d4.
  zstep F_599d8 D_599d8.
  stepn F_599dc D_599dc. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_599e0 D_599e0. zstep F_599e4 D_599e4.
  zbft F_599e8 D_599e8. zbft F_599ec D_599ec.
  zld F_599f0 D_599f0 (ia + 3616) Cmax.
  zbtk F_599f4 D_599f4.
  stepn F_59a54 D_59a54.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_59a5c D_59a5c || (zstep F_59a58 D_59a58; zbft F_59a5c D_59a5c).
  zstep F_59a60 D_59a60. zstep F_59a64 D_59a64. zstep F_59a68 D_59a68. zstep F_59a6c D_59a6c.
  stepn F_59a70 D_59a70.
  zret.
Qed.
End FPX.
