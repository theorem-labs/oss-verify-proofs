(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatPoison.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_d2a_fn : forall regs (M rom : word -> option byte) (sp n rs rz tp key tsd ctx t mc mb mr : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (rs + rz) ->
  32 <= sp -> sp < 2 ^ 64 -> 0x698000 + 32 <= sp -> 1 <= n <= rs -> rs + rz <= 65536 -> 0 <= rz ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 ->
  apart (sp - 32) 32 0x141260 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 32 (t + 2800) 24 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> wrA M (t + 2800) 24 ->
  msteps ASEGS (mkst regs (0x53318 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5331c : bv 64)%bv) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800 + 112))) 11 (Z_to_bv 64 512)) 12 (Z_to_bv 64 (mc + 1))) 13 (Z_to_bv 64 (mb + n))) 14 (Z_to_bv 64 65537)) (0x53370 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x5331c) (sp - 24) 0x83440) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (rs + rz - n))) rom).
Proof.
  intros regs M rom sp n rs rz tp key tsd ctx t mc mb mr H2 H4 H9 H19 Hsp Hsp' IMG Hn Hprim Hrz Hmc Hmb Hmr W TSD Ht Ht' A1 A2 A3 A4 A5
         Cmc Cmb Cmr Wts.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_532c8 D_532c8.
  zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
    assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
    assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
    assert (Wts' : wrA X (t + 2800) 24) by (repeat apply wr_Wn; exact Wts) end.
  zld F_532cc D_532cc (t + 2800 + 16) Cmr'.
  zld F_532d0 D_532d0 (t + 2800) Cmc'.
  zld F_532d4 D_532d4 (t + 2800 + 8) Cmb'.
  zstep F_532d8 D_532d8. zstep F_532dc D_532dc. zstep F_532e0 D_532e0. zstep F_532e4 D_532e4. zstep F_532e8 D_532e8. zstep F_532ec D_532ec.
  zsd F_532f0 D_532f0 (t + 2800) (mc + 1) ltac:(rewok Wts').
  zsd F_532f4 D_532f4 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
  zsd F_532f8 D_532f8 (t + 2800 + 16) (mr + (rs + rz - n)) ltac:(rewok Wts').
  zbtk F_532fc D_532fc.
  zstep F_53318 D_53318. zstep F_5331c D_5331c.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_d2b_small_fn : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 1 <= rs + rz <= 512 ->
  msteps ASEGS (mkst regs (0x53370 : word) M rom) (mkst (regupd regs 11 (Z_to_bv 64 ((rs + rz + 31) / 32))) (0x5345c : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbft F_53320 D_53320.
  zstep F_53324 D_53324.
  stepn F_53328 D_53328. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
  stepn F_5332c D_5332c.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_d2b_big : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 513 <= rs + rz <= 65536 ->
  msteps ASEGS (mkst regs (0x53370 : word) M rom) (mkst regs (0x53380 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbtk F_53320 D_53320. apply mst_refl.
Qed.

#[using="Type"] Lemma art_alloc_d2c_fn : forall regs (M rom : word -> option byte) (sp ab n rz c t mbs : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 (t + 2800 + 112) -> getr regs 11 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 (ab + rz) ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 0x698000 <= sp -> 1 <= n < 2 ^ 40 -> 1 <= c <= 52 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= mbs < 2 ^ 64 ->
  0 <= ab + rz < 2 ^ 64 ->
  cellA M (t + 2800 + 112 + 8 * c) 8 mbs -> wrA M (t + 2800 + 112 + 8 * c) 8 -> apart (t + 2800 + 112 + 8 * c) 8 sp 128 -> t + 4096 <= 0x10000 \/ 0x698000 <= t ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x13f1f8 + 44) 4 4096 -> cellA M (0x13f1f8 + 52) 4 190 ->
  msteps ASEGS (mkst regs (0x5345c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x534ac : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 190)) 12 (Z_to_bv 64 (Z.min n 4096))) 13 (Z_to_bv 64 0x12b88c)) (0x12b88c : word) (Wn 8 M (t + 2800 + 112 + 8 * c) (mbs + 1)) rom).
Proof.
  intros regs M rom sp ab n rz c t mbs H2 H9 H10 H11 H20 Hsp Hsp' IMG Hn Hc Ht Ht' Hmbs Hub Cmbs Wmbs A1 Timg Ccf L Cmax Cfb.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_5340c D_5340c. rwH. rewrite art_zb_slli by lia. change (2 ^ 3) with 8.
  zstep F_53410 D_53410.
  zld F_53414 D_53414 (t + 2800 + 112 + 8 * c) Cmbs.
  zstep F_53418 D_53418.
  zsd F_5341c D_5341c (t + 2800 + 112 + 8 * c) (mbs + 1) ltac:(rewok Wmbs).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
    assert (G40' : cellA X 0x1391b0 8 0x13f1f8) by (unfold apart in *; recell G40);
    assert (Cmax' : cellA X (0x13f1f8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
    assert (G68' : cellA X 0x1391d8 8 0x13b1c8) by (unfold apart in *; recell G68);
    assert (Crm' : cellA X 0x13b1c8 8 0x12b88c) by (unfold apart in *; recell Crm);
    assert (Cfb' : cellA X (0x13f1f8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
  zld F_53420 D_53420 (sp + 8) Ccf'.
  zbft F_53424 D_53424.
  zstep F_53428 D_53428. zld F_5342c D_5342c 0x1391b0 G40'.
  zlw F_53430 D_53430 (0x13f1f8 + 44) Cmax'.
  zbft F_53434 D_53434.
  zstep F_53438 D_53438.
  destruct (Z.lt_ge_cases n 4096) as [Sm|Bg].
  - zbtk F_5343c D_5343c.
    zstep F_53444 D_53444. zld F_53448 D_53448 0x1391d8 G68'. zld F_5344c D_5344c 0x13b1c8 Crm'.
    zlw F_53450 D_53450 (0x13f1f8 + 52) Cfb'.
    zstep F_53454 D_53454.
    stepjr F_53458 D_53458 (0x12b88c : bv 64)%bv ltac:(gres; bveq).
    zret.
  - zbft F_5343c D_5343c.
    zstep F_53440 D_53440.
    zstep F_53444 D_53444. zld F_53448 D_53448 0x1391d8 G68'. zld F_5344c D_5344c 0x13b1c8 Crm'.
    zlw F_53450 D_53450 (0x13f1f8 + 52) Cfb'.
    zstep F_53454 D_53454.
    stepjr F_53458 D_53458 (0x12b88c : bv 64)%bv ltac:(gres; bveq).
    zret.
Qed.
End FPX.
