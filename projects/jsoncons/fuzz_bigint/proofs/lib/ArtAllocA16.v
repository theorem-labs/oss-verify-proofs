(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtRzLog ArtAllocA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_3d034_3dfbc.
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
  wrA M (sp - 256) 256 -> 0x633000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x10460 1 4 -> cellA M 0xde818 1 1 -> cellA M 0x15fda2 1 0 ->
  msteps ASEGS (mkst regs (0x3d370 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d3cc : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 16)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 32)) 12 (Z_to_bv 64 0x10458)) 13 (Z_to_bv 64 (2 ^ 64 - 16))) 18 (Z_to_bv 64 16)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 15)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x3d408 : word) (art_alloc_memA1_16 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & _ & R3) R2 Ci Cr.
  zstep F_3d370 D_3d370.
  zsd F_3d374 D_3d374 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_3d378 D_3d378 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_3d37c D_3d37c (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_3d380 D_3d380 (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_3d384 D_3d384 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_3d388 D_3d388 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_3d38c D_3d38c (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_3d390 D_3d390 (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_3d394 D_3d394 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_3d398 D_3d398 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_3d39c D_3d39c (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_3d3a0 D_3d3a0 (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_3d3a4 D_3d3a4 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_3d3a8 D_3d3a8. zstep F_3d3ac D_3d3ac. zstep F_3d3b0 D_3d3b0. zstep F_3d3b4 D_3d3b4. zstep F_3d3b8 D_3d3b8. zstep F_3d3bc D_3d3bc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0xde818 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x15fda2 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x103e8 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x10460 1 4) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_3d3c0 D_3d3c0.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_3d3c4 D_3d3c4.
  stepn F_3d3c8 D_3d3c8.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_3d3cc D_3d3cc.
  zbft F_3d3d0 D_3d3d0.
  zstep F_3d3d4 D_3d3d4.
  zbtk F_3d3d8 D_3d3d8.
  zstep F_3d414 D_3d414. zstep F_3d418 D_3d418.
  zbtk F_3d41c D_3d41c.
  zstep F_3d424 D_3d424. zstep F_3d428 D_3d428.
  zbft F_3d42c D_3d42c.
  zstep F_3d430 D_3d430. zld F_3d434 D_3d434 0x103e8 R1'.
  zstep F_3d438 D_3d438. zstep F_3d43c D_3d43c. zstep F_3d440 D_3d440. zstep F_3d444 D_3d444. zstep F_3d448 D_3d448. zstep F_3d44c D_3d44c.
  zstep F_3d450 D_3d450.
  zlbu F_3d454 D_3d454 0x10460 R2'.
  zstep F_3d458 D_3d458. zstep F_3d45c D_3d45c. zstep F_3d460 D_3d460. zstep F_3d464 D_3d464.
  zbft F_3d468 D_3d468.
  zstep F_3d46c D_3d46c. zstep F_3d3ec D_3d3ec. zstep F_3d3f0 D_3d3f0.
  zbft F_3d3f4 D_3d3f4.
  zstep F_3d3f8 D_3d3f8. zstep F_3d3fc D_3d3fc.
  zsd F_3d400 D_3d400 (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_3d404 D_3d404 (sp - 128 + 16) 32 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1_16. zret.
Qed.

Lemma art_alloc_a3_16_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 16 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 16 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x633000 -> 0x633000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 15) / 16 * 16 -> rz = 16 * 2 ^ r -> rs + rz + 16 <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x3d524 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d610 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + 16 + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + 16 + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 16))) 26 (Z_to_bv 64 t)) (0x41ac8 : word) (Wn 8 M (sp - 8) 0x3d5f4) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs16 : exists q16, rs = 16 * q16) by (exists ((Z.max n 8 + 15) / 16); lia). destruct Hrs16 as (q16 & Hrs16).
  assert (Hrs8 : (rs + 16) mod 8 = 0) by (rewrite Hrs16; replace (16 * q16 + 16) with ((2 * q16 + 2) * 8) by lia; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 15) 16 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 15) 16 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_3d524 D_3d524. zstep F_3d528 D_3d528. zstep F_3d52c D_3d52c. zstep F_3d530 D_3d530. zstep F_3d534 D_3d534.
  stepn F_3d538 D_3d538. rwH. rewrite art_zb_and by lia. rewrite art_land_m16 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 16 * 16)] => replace (e / 16 * 16) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_3d53c D_3d53c. zstep F_3d540 D_3d540.
  stepn F_3d544 D_3d544. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_3d548 D_3d548.
  zstep F_3d54c D_3d54c. zstep F_3d550 D_3d550. zstep F_3d554 D_3d554.
  stepn F_3d558 D_3d558. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_3d55c D_3d55c. zstep F_3d560 D_3d560. zstep F_3d564 D_3d564. zstep F_3d568 D_3d568. zstep F_3d56c D_3d56c. zstep F_3d570 D_3d570.
  zstep F_3d574 D_3d574.
  stepn F_3d578 D_3d578. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_3d57c D_3d57c. zstep F_3d580 D_3d580.
  zbft F_3d584 D_3d584. zbft F_3d588 D_3d588.
  zld F_3d58c D_3d58c (ia + 3616) Cmax.
  zbtk F_3d590 D_3d590.
  stepn F_3d5f0 D_3d5f0.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_3d5f8 D_3d5f8 || (zstep F_3d5f4 D_3d5f4; zbft F_3d5f8 D_3d5f8).
  zstep F_3d5fc D_3d5fc. zstep F_3d600 D_3d600. zstep F_3d604 D_3d604. zstep F_3d608 D_3d608.
  stepn F_3d60c D_3d60c.
  zret.
Qed.
End FPX.
