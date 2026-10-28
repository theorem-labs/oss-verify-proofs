(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatAllocA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3cf10_3de98_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
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
  wrA M (sp - 256) 256 -> 0x696000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x104c0 1 4 -> cellA M 0x140918 1 1 -> cellA M 0x1c1ea2 1 0 ->
  msteps ASEGS (mkst regs (0x525e4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52640 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 16)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 32)) 12 (Z_to_bv 64 0x104b8)) 13 (Z_to_bv 64 (2 ^ 64 - 16))) 18 (Z_to_bv 64 16)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 15)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x5267c : word) (art_alloc_memA1_16 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & _ & R3) R2 Ci Cr.
  zstep F_521cc D_521cc.
  zsd F_521d0 D_521d0 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_521d4 D_521d4 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_521d8 D_521d8 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_521dc D_521dc (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_521e0 D_521e0 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_521e4 D_521e4 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_521e8 D_521e8 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_521ec D_521ec (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_521f0 D_521f0 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_521f4 D_521f4 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_521f8 D_521f8 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_521fc D_521fc (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_52200 D_52200 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_52204 D_52204. zstep F_52208 D_52208. zstep F_5220c D_5220c. zstep F_52210 D_52210. zstep F_52214 D_52214. zstep F_52218 D_52218.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x140918 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1c1ea2 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10438 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104c0 1 4) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_5221c D_5221c.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_52220 D_52220.
  stepn F_52224 D_52224.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_52228 D_52228.
  zbft F_5222c D_5222c.
  zstep F_52230 D_52230.
  zbtk F_52234 D_52234.
  zstep F_52270 D_52270. zstep F_52274 D_52274.
  zbtk F_52278 D_52278.
  zstep F_52280 D_52280. zstep F_52284 D_52284.
  zbft F_52288 D_52288.
  zstep F_5228c D_5228c. zld F_52290 D_52290 0x10438 R1'.
  zstep F_52294 D_52294. zstep F_52298 D_52298. zstep F_5229c D_5229c. zstep F_522a0 D_522a0. zstep F_522a4 D_522a4. zstep F_522a8 D_522a8.
  zstep F_522ac D_522ac.
  zlbu F_522b0 D_522b0 0x104c0 R2'.
  zstep F_522b4 D_522b4. zstep F_522b8 D_522b8. zstep F_522bc D_522bc. zstep F_522c0 D_522c0.
  zbft F_522c4 D_522c4.
  zstep F_522c8 D_522c8. zstep F_52248 D_52248. zstep F_5224c D_5224c.
  zbft F_52250 D_52250.
  zstep F_52254 D_52254. zstep F_52258 D_52258.
  zsd F_5225c D_5225c (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_52260 D_52260 (sp - 128 + 16) 32 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1_16. zret.
Qed.

#[using="Type"] Lemma art_alloc_a3_16_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 16 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 16 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x696000 -> 0x696000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 15) / 16 * 16 -> rz = 16 * 2 ^ r -> rs + rz + 16 <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x52798 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52884 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + 16 + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + 16 + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 16))) 26 (Z_to_bv 64 t)) (0x56d3c : word) (Wn 8 M (sp - 8) 0x52868) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs16 : exists q16, rs = 16 * q16) by (exists ((Z.max n 8 + 15) / 16); lia). destruct Hrs16 as (q16 & Hrs16).
  assert (Hrs8 : (rs + 16) mod 8 = 0) by (rewrite Hrs16; replace (16 * q16 + 16) with ((2 * q16 + 2) * 8) by lia; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 15) 16 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 15) 16 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_52380 D_52380. zstep F_52384 D_52384. zstep F_52388 D_52388. zstep F_5238c D_5238c. zstep F_52390 D_52390.
  stepn F_52394 D_52394. rwH. rewrite art_zb_and by lia. rewrite art_land_m16 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 16 * 16)] => replace (e / 16 * 16) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_52398 D_52398. zstep F_5239c D_5239c.
  stepn F_523a0 D_523a0. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_523a4 D_523a4.
  zstep F_523a8 D_523a8. zstep F_523ac D_523ac. zstep F_523b0 D_523b0.
  stepn F_523b4 D_523b4. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_523b8 D_523b8. zstep F_523bc D_523bc. zstep F_523c0 D_523c0. zstep F_523c4 D_523c4. zstep F_523c8 D_523c8. zstep F_523cc D_523cc.
  zstep F_523d0 D_523d0.
  stepn F_523d4 D_523d4. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_523d8 D_523d8. zstep F_523dc D_523dc.
  zbft F_523e0 D_523e0. zbft F_523e4 D_523e4.
  zld F_523e8 D_523e8 (ia + 3616) Cmax.
  zbtk F_523ec D_523ec.
  stepn F_5244c D_5244c.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_52454 D_52454 || (zstep F_52450 D_52450; zbft F_52454 D_52454).
  zstep F_52458 D_52458. zstep F_5245c D_5245c. zstep F_52460 D_52460. zstep F_52464 D_52464.
  stepn F_52468 D_52468.
  zret.
Qed.
End FPX.
