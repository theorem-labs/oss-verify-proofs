(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatRzLog EatAllocA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
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

#[using="Type"] Lemma art_alloc_a1_16_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 16 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x698000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x104c8 1 4 -> cellA M 0x1426d8 1 1 -> cellA M 0x1c3c62 1 0 ->
  msteps ASEGS (mkst regs (0x52dcc : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52e28 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 16)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 32)) 12 (Z_to_bv 64 0x104c0)) 13 (Z_to_bv 64 (2 ^ 64 - 16))) 18 (Z_to_bv 64 16)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 15)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x52e64 : word) (art_alloc_memA1_16 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & _ & R3) R2 Ci Cr.
  zstep F_52d7c D_52d7c.
  zsd F_52d80 D_52d80 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_52d84 D_52d84 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_52d88 D_52d88 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_52d8c D_52d8c (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_52d90 D_52d90 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_52d94 D_52d94 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_52d98 D_52d98 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_52d9c D_52d9c (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_52da0 D_52da0 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_52da4 D_52da4 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_52da8 D_52da8 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_52dac D_52dac (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_52db0 D_52db0 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_52db4 D_52db4. zstep F_52db8 D_52db8. zstep F_52dbc D_52dbc. zstep F_52dc0 D_52dc0. zstep F_52dc4 D_52dc4. zstep F_52dc8 D_52dc8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x1426d8 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1c3c62 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10448 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104c8 1 4) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_52dcc D_52dcc.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_52dd0 D_52dd0.
  stepn F_52dd4 D_52dd4.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_52dd8 D_52dd8.
  zbft F_52ddc D_52ddc.
  zstep F_52de0 D_52de0.
  zbtk F_52de4 D_52de4.
  zstep F_52e20 D_52e20. zstep F_52e24 D_52e24.
  zbtk F_52e28 D_52e28.
  zstep F_52e30 D_52e30. zstep F_52e34 D_52e34.
  zbft F_52e38 D_52e38.
  zstep F_52e3c D_52e3c. zld F_52e40 D_52e40 0x10448 R1'.
  zstep F_52e44 D_52e44. zstep F_52e48 D_52e48. zstep F_52e4c D_52e4c. zstep F_52e50 D_52e50. zstep F_52e54 D_52e54. zstep F_52e58 D_52e58.
  zstep F_52e5c D_52e5c.
  zlbu F_52e60 D_52e60 0x104c8 R2'.
  zstep F_52e64 D_52e64. zstep F_52e68 D_52e68. zstep F_52e6c D_52e6c. zstep F_52e70 D_52e70.
  zbft F_52e74 D_52e74.
  zstep F_52e78 D_52e78. zstep F_52df8 D_52df8. zstep F_52dfc D_52dfc.
  zbft F_52e00 D_52e00.
  zstep F_52e04 D_52e04. zstep F_52e08 D_52e08.
  zsd F_52e0c D_52e0c (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_52e10 D_52e10 (sp - 128 + 16) 32 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1_16. zret.
Qed.

#[using="Type"] Lemma art_alloc_a3_16_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 16 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 16 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x698000 -> 0x698000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 15) / 16 * 16 -> rz = 16 * 2 ^ r -> rs + rz + 16 <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x52f80 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5306c : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + 16 + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + 16 + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 16))) 26 (Z_to_bv 64 t)) (0x57524 : word) (Wn 8 M (sp - 8) 0x53050) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs16 : exists q16, rs = 16 * q16) by (exists ((Z.max n 8 + 15) / 16); lia). destruct Hrs16 as (q16 & Hrs16).
  assert (Hrs8 : (rs + 16) mod 8 = 0) by (rewrite Hrs16; replace (16 * q16 + 16) with ((2 * q16 + 2) * 8) by lia; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 15) 16 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 15) 16 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_52f30 D_52f30. zstep F_52f34 D_52f34. zstep F_52f38 D_52f38. zstep F_52f3c D_52f3c. zstep F_52f40 D_52f40.
  stepn F_52f44 D_52f44. rwH. rewrite art_zb_and by lia. rewrite art_land_m16 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 16 * 16)] => replace (e / 16 * 16) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_52f48 D_52f48. zstep F_52f4c D_52f4c.
  stepn F_52f50 D_52f50. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_52f54 D_52f54.
  zstep F_52f58 D_52f58. zstep F_52f5c D_52f5c. zstep F_52f60 D_52f60.
  stepn F_52f64 D_52f64. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_52f68 D_52f68. zstep F_52f6c D_52f6c. zstep F_52f70 D_52f70. zstep F_52f74 D_52f74. zstep F_52f78 D_52f78. zstep F_52f7c D_52f7c.
  zstep F_52f80 D_52f80.
  stepn F_52f84 D_52f84. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_52f88 D_52f88. zstep F_52f8c D_52f8c.
  zbft F_52f90 D_52f90. zbft F_52f94 D_52f94.
  zld F_52f98 D_52f98 (ia + 3616) Cmax.
  zbtk F_52f9c D_52f9c.
  stepn F_52ffc D_52ffc.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_53004 D_53004 || (zstep F_53000 D_53000; zbft F_53004 D_53004).
  zstep F_53008 D_53008. zstep F_5300c D_5300c. zstep F_53010 D_53010. zstep F_53014 D_53014.
  stepn F_53018 D_53018.
  zret.
Qed.
End FPX.
