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
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_d2a_fn : forall regs (M rom : word -> option byte) (sp n rs rz tp key tsd ctx t mc mb mr : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (rs + rz) ->
  32 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 32 <= sp -> 1 <= n <= rs -> rs + rz <= 65536 -> 0 <= rz ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 ->
  apart (sp - 32) 32 0x145960 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 32 (t + 2800) 24 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> wrA M (t + 2800) 24 ->
  msteps ASEGS (mkst regs (0x53b40 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x53b44 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800 + 112))) 11 (Z_to_bv 64 512)) 12 (Z_to_bv 64 (mc + 1))) 13 (Z_to_bv 64 (mb + n))) 14 (Z_to_bv 64 65537)) (0x53b98 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x53b44) (sp - 24) 0x83c68) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (rs + rz - n))) rom).
Proof.
  intros regs M rom sp n rs rz tp key tsd ctx t mc mb mr H2 H4 H9 H19 Hsp Hsp' IMG Hn Hprim Hrz Hmc Hmb Hmr W TSD Ht Ht' A1 A2 A3 A4 A5
         Cmc Cmb Cmr Wts.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_53af0 D_53af0.
  zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
    assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
    assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
    assert (Wts' : wrA X (t + 2800) 24) by (repeat apply wr_Wn; exact Wts) end.
  zld F_53af4 D_53af4 (t + 2800 + 16) Cmr'.
  zld F_53af8 D_53af8 (t + 2800) Cmc'.
  zld F_53afc D_53afc (t + 2800 + 8) Cmb'.
  zstep F_53b00 D_53b00. zstep F_53b04 D_53b04. zstep F_53b08 D_53b08. zstep F_53b0c D_53b0c. zstep F_53b10 D_53b10. zstep F_53b14 D_53b14.
  zsd F_53b18 D_53b18 (t + 2800) (mc + 1) ltac:(rewok Wts').
  zsd F_53b1c D_53b1c (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
  zsd F_53b20 D_53b20 (t + 2800 + 16) (mr + (rs + rz - n)) ltac:(rewok Wts').
  zbtk F_53b24 D_53b24.
  zstep F_53b40 D_53b40. zstep F_53b44 D_53b44.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_d2b_small_fn : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 1 <= rs + rz <= 512 ->
  msteps ASEGS (mkst regs (0x53b98 : word) M rom) (mkst (regupd regs 11 (Z_to_bv 64 ((rs + rz + 31) / 32))) (0x53c84 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbft F_53b48 D_53b48.
  zstep F_53b4c D_53b4c.
  stepn F_53b50 D_53b50. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
  stepn F_53b54 D_53b54.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_d2b_big : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 513 <= rs + rz <= 65536 ->
  msteps ASEGS (mkst regs (0x53b98 : word) M rom) (mkst regs (0x53ba8 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbtk F_53b48 D_53b48. apply mst_refl.
Qed.

#[using="Type"] Lemma art_alloc_d2c_fn : forall regs (M rom : word -> option byte) (sp ab n rz c t mbs : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 (t + 2800 + 112) -> getr regs 11 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 (ab + rz) ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 0x69c000 <= sp -> 1 <= n < 2 ^ 40 -> 1 <= c <= 52 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= mbs < 2 ^ 64 ->
  0 <= ab + rz < 2 ^ 64 ->
  cellA M (t + 2800 + 112 + 8 * c) 8 mbs -> wrA M (t + 2800 + 112 + 8 * c) 8 -> apart (t + 2800 + 112 + 8 * c) 8 sp 128 -> t + 4096 <= 0x10000 \/ 0x69c000 <= t ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x1438f8 + 44) 4 4096 -> cellA M (0x1438f8 + 52) 4 190 ->
  msteps ASEGS (mkst regs (0x53c84 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x53cd4 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 190)) 12 (Z_to_bv 64 (Z.min n 4096))) 13 (Z_to_bv 64 0x130034)) (0x130034 : word) (Wn 8 M (t + 2800 + 112 + 8 * c) (mbs + 1)) rom).
Proof.
  intros regs M rom sp ab n rz c t mbs H2 H9 H10 H11 H20 Hsp Hsp' IMG Hn Hc Ht Ht' Hmbs Hub Cmbs Wmbs A1 Timg Ccf L Cmax Cfb.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_53c34 D_53c34. rwH. rewrite art_zb_slli by lia. change (2 ^ 3) with 8.
  zstep F_53c38 D_53c38.
  zld F_53c3c D_53c3c (t + 2800 + 112 + 8 * c) Cmbs.
  zstep F_53c40 D_53c40.
  zsd F_53c44 D_53c44 (t + 2800 + 112 + 8 * c) (mbs + 1) ltac:(rewok Wmbs).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
    assert (G40' : cellA X 0x13d8c0 8 0x1438f8) by (unfold apart in *; recell G40);
    assert (Cmax' : cellA X (0x1438f8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
    assert (G68' : cellA X 0x13d8e8 8 0x13f8d8) by (unfold apart in *; recell G68);
    assert (Crm' : cellA X 0x13f8d8 8 0x130034) by (unfold apart in *; recell Crm);
    assert (Cfb' : cellA X (0x1438f8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
  zld F_53c48 D_53c48 (sp + 8) Ccf'.
  zbft F_53c4c D_53c4c.
  zstep F_53c50 D_53c50. zld F_53c54 D_53c54 0x13d8c0 G40'.
  zlw F_53c58 D_53c58 (0x1438f8 + 44) Cmax'.
  zbft F_53c5c D_53c5c.
  zstep F_53c60 D_53c60.
  destruct (Z.lt_ge_cases n 4096) as [Sm|Bg].
  - zbtk F_53c64 D_53c64.
    zstep F_53c6c D_53c6c. zld F_53c70 D_53c70 0x13d8e8 G68'. zld F_53c74 D_53c74 0x13f8d8 Crm'.
    zlw F_53c78 D_53c78 (0x1438f8 + 52) Cfb'.
    zstep F_53c7c D_53c7c.
    stepjr F_53c80 D_53c80 (0x130034 : bv 64)%bv ltac:(gres; bveq).
    zret.
  - zbft F_53c64 D_53c64.
    zstep F_53c68 D_53c68.
    zstep F_53c6c D_53c6c. zld F_53c70 D_53c70 0x13d8e8 G68'. zld F_53c74 D_53c74 0x13f8d8 Crm'.
    zlw F_53c78 D_53c78 (0x1438f8 + 52) Cfb'.
    zstep F_53c7c D_53c7c.
    stepjr F_53c80 D_53c80 (0x130034 : bv 64)%bv ltac:(gres; bveq).
    zret.
Qed.
End FPX.
