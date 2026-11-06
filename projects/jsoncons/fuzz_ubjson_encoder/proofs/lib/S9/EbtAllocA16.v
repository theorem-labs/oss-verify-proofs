(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtRzLog EbtAllocA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
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

#[using="Type"] Lemma art_alloc_a1_16_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 16 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x69c000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x104d0 1 4 -> cellA M 0x146dd8 1 1 -> cellA M 0x1c8362 1 0 ->
  msteps ASEGS (mkst regs (0x535f4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x53650 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 16)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 32)) 12 (Z_to_bv 64 0x104c8)) 13 (Z_to_bv 64 (2 ^ 64 - 16))) 18 (Z_to_bv 64 16)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 15)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x5368c : word) (art_alloc_memA1_16 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & _ & R3) R2 Ci Cr.
  zstep F_535a4 D_535a4.
  zsd F_535a8 D_535a8 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_535ac D_535ac (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_535b0 D_535b0 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_535b4 D_535b4 (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_535b8 D_535b8 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_535bc D_535bc (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_535c0 D_535c0 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_535c4 D_535c4 (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_535c8 D_535c8 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_535cc D_535cc (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_535d0 D_535d0 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_535d4 D_535d4 (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_535d8 D_535d8 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_535dc D_535dc. zstep F_535e0 D_535e0. zstep F_535e4 D_535e4. zstep F_535e8 D_535e8. zstep F_535ec D_535ec. zstep F_535f0 D_535f0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x146dd8 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1c8362 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10450 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104d0 1 4) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_535f4 D_535f4.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_535f8 D_535f8.
  stepn F_535fc D_535fc.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_53600 D_53600.
  zbft F_53604 D_53604.
  zstep F_53608 D_53608.
  zbtk F_5360c D_5360c.
  zstep F_53648 D_53648. zstep F_5364c D_5364c.
  zbtk F_53650 D_53650.
  zstep F_53658 D_53658. zstep F_5365c D_5365c.
  zbft F_53660 D_53660.
  zstep F_53664 D_53664. zld F_53668 D_53668 0x10450 R1'.
  zstep F_5366c D_5366c. zstep F_53670 D_53670. zstep F_53674 D_53674. zstep F_53678 D_53678. zstep F_5367c D_5367c. zstep F_53680 D_53680.
  zstep F_53684 D_53684.
  zlbu F_53688 D_53688 0x104d0 R2'.
  zstep F_5368c D_5368c. zstep F_53690 D_53690. zstep F_53694 D_53694. zstep F_53698 D_53698.
  zbft F_5369c D_5369c.
  zstep F_536a0 D_536a0. zstep F_53620 D_53620. zstep F_53624 D_53624.
  zbft F_53628 D_53628.
  zstep F_5362c D_5362c. zstep F_53630 D_53630.
  zsd F_53634 D_53634 (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_53638 D_53638 (sp - 128 + 16) 32 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1_16. zret.
Qed.

#[using="Type"] Lemma art_alloc_a3_16_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 16 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 16 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x69c000 -> 0x69c000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 15) / 16 * 16 -> rz = 16 * 2 ^ r -> rs + rz + 16 <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x537a8 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x53894 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + 16 + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + 16 + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 16))) 26 (Z_to_bv 64 t)) (0x57d4c : word) (Wn 8 M (sp - 8) 0x53878) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs16 : exists q16, rs = 16 * q16) by (exists ((Z.max n 8 + 15) / 16); lia). destruct Hrs16 as (q16 & Hrs16).
  assert (Hrs8 : (rs + 16) mod 8 = 0) by (rewrite Hrs16; replace (16 * q16 + 16) with ((2 * q16 + 2) * 8) by lia; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 15) 16 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 15) 16 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_53758 D_53758. zstep F_5375c D_5375c. zstep F_53760 D_53760. zstep F_53764 D_53764. zstep F_53768 D_53768.
  stepn F_5376c D_5376c. rwH. rewrite art_zb_and by lia. rewrite art_land_m16 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 16 * 16)] => replace (e / 16 * 16) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_53770 D_53770. zstep F_53774 D_53774.
  stepn F_53778 D_53778. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_5377c D_5377c.
  zstep F_53780 D_53780. zstep F_53784 D_53784. zstep F_53788 D_53788.
  stepn F_5378c D_5378c. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_53790 D_53790. zstep F_53794 D_53794. zstep F_53798 D_53798. zstep F_5379c D_5379c. zstep F_537a0 D_537a0. zstep F_537a4 D_537a4.
  zstep F_537a8 D_537a8.
  stepn F_537ac D_537ac. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_537b0 D_537b0. zstep F_537b4 D_537b4.
  zbft F_537b8 D_537b8. zbft F_537bc D_537bc.
  zld F_537c0 D_537c0 (ia + 3616) Cmax.
  zbtk F_537c4 D_537c4.
  stepn F_53824 D_53824.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_5382c D_5382c || (zstep F_53828 D_53828; zbft F_5382c D_5382c).
  zstep F_53830 D_53830. zstep F_53834 D_53834. zstep F_53838 D_53838. zstep F_5383c D_5383c.
  stepn F_53840 D_53840.
  zret.
Qed.
End FPX.
