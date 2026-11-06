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

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_alloc_d2a_fn : forall regs (M rom : word -> option byte) (sp n rs rz tp key tsd ctx t mc mb mr : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (rs + rz) ->
  32 <= sp -> sp < 2 ^ 64 -> 0x6c4000 + 32 <= sp -> 1 <= n <= rs -> rs + rz <= 65536 -> 0 <= rz ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 ->
  apart (sp - 32) 32 0x16d020 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 32 (t + 2800) 24 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> wrA M (t + 2800) 24 ->
  msteps ASEGS (mkst regs (0x5b644 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5b648 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800 + 112))) 11 (Z_to_bv 64 512)) 12 (Z_to_bv 64 (mc + 1))) 13 (Z_to_bv 64 (mb + n))) 14 (Z_to_bv 64 65537)) (0x5b69c : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x5b648) (sp - 24) 0x8b938) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (rs + rz - n))) rom).
Proof.
  intros regs M rom sp n rs rz tp key tsd ctx t mc mb mr H2 H4 H9 H19 Hsp Hsp' IMG Hn Hprim Hrz Hmc Hmb Hmr W TSD Ht Ht' A1 A2 A3 A4 A5
         Cmc Cmb Cmr Wts.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_5b5fc D_5b5fc.
  zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
    assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
    assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
    assert (Wts' : wrA X (t + 2800) 24) by (repeat apply wr_Wn; exact Wts) end.
  zld F_5b600 D_5b600 (t + 2800 + 16) Cmr'.
  zld F_5b604 D_5b604 (t + 2800) Cmc'.
  zld F_5b608 D_5b608 (t + 2800 + 8) Cmb'.
  zstep F_5b60c D_5b60c. zstep F_5b610 D_5b610. zstep F_5b614 D_5b614. zstep F_5b618 D_5b618. zstep F_5b61c D_5b61c. zstep F_5b620 D_5b620.
  zsd F_5b624 D_5b624 (t + 2800) (mc + 1) ltac:(rewok Wts').
  zsd F_5b628 D_5b628 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
  zsd F_5b62c D_5b62c (t + 2800 + 16) (mr + (rs + rz - n)) ltac:(rewok Wts').
  zbtk F_5b630 D_5b630.
  zstep F_5b64c D_5b64c. zstep F_5b650 D_5b650.
  zret.
Qed.

Lemma art_alloc_d2b_small_fn : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 1 <= rs + rz <= 512 ->
  msteps ASEGS (mkst regs (0x5b69c : word) M rom) (mkst (regupd regs 11 (Z_to_bv 64 ((rs + rz + 31) / 32))) (0x5b788 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbft F_5b654 D_5b654.
  zstep F_5b658 D_5b658.
  stepn F_5b65c D_5b65c. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
  stepn F_5b660 D_5b660.
  zret.
Qed.

Lemma art_alloc_d2b_big : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 513 <= rs + rz <= 65536 ->
  msteps ASEGS (mkst regs (0x5b69c : word) M rom) (mkst regs (0x5b6ac : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbtk F_5b654 D_5b654. apply mst_refl.
Qed.

Lemma art_alloc_d2c_fn : forall regs (M rom : word -> option byte) (sp ab n rz c t mbs : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 (t + 2800 + 112) -> getr regs 11 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 (ab + rz) ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 0x6c4000 <= sp -> 1 <= n < 2 ^ 40 -> 1 <= c <= 52 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= mbs < 2 ^ 64 ->
  0 <= ab + rz < 2 ^ 64 ->
  cellA M (t + 2800 + 112 + 8 * c) 8 mbs -> wrA M (t + 2800 + 112 + 8 * c) 8 -> apart (t + 2800 + 112 + 8 * c) 8 sp 128 -> t + 4096 <= 0x10000 \/ 0x6c4000 <= t ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x16afb8 + 44) 4 4096 -> cellA M (0x16afb8 + 52) 4 190 ->
  msteps ASEGS (mkst regs (0x5b788 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x5b7d8 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 190)) 12 (Z_to_bv 64 (Z.min n 4096))) 13 (Z_to_bv 64 0x1568bc)) (0x1568bc : word) (Wn 8 M (t + 2800 + 112 + 8 * c) (mbs + 1)) rom).
Proof.
  intros regs M rom sp ab n rz c t mbs H2 H9 H10 H11 H20 Hsp Hsp' IMG Hn Hc Ht Ht' Hmbs Hub Cmbs Wmbs A1 Timg Ccf L Cmax Cfb.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_5b740 D_5b740. rwH. rewrite art_zb_slli by lia. change (2 ^ 3) with 8.
  zstep F_5b744 D_5b744.
  zld F_5b748 D_5b748 (t + 2800 + 112 + 8 * c) Cmbs.
  zstep F_5b74c D_5b74c.
  zsd F_5b750 D_5b750 (t + 2800 + 112 + 8 * c) (mbs + 1) ltac:(rewok Wmbs).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
    assert (G40' : cellA X 0x164510 8 0x16afb8) by (unfold apart in *; recell G40);
    assert (Cmax' : cellA X (0x16afb8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
    assert (G68' : cellA X 0x164538 8 0x166550) by (unfold apart in *; recell G68);
    assert (Crm' : cellA X 0x166550 8 0x1568bc) by (unfold apart in *; recell Crm);
    assert (Cfb' : cellA X (0x16afb8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
  zld F_5b754 D_5b754 (sp + 8) Ccf'.
  zbft F_5b758 D_5b758.
  zstep F_5b75c D_5b75c. zld F_5b760 D_5b760 0x164510 G40'.
  zlw F_5b764 D_5b764 (0x16afb8 + 44) Cmax'.
  zbft F_5b768 D_5b768.
  zstep F_5b76c D_5b76c.
  destruct (Z.lt_ge_cases n 4096) as [Sm|Bg].
  - zbtk F_5b770 D_5b770.
    zstep F_5b778 D_5b778. zld F_5b77c D_5b77c 0x164538 G68'. zld F_5b780 D_5b780 0x166550 Crm'.
    zlw F_5b784 D_5b784 (0x16afb8 + 52) Cfb'.
    zstep F_5b788 D_5b788.
    stepjr F_5b78c D_5b78c (0x1568bc : bv 64)%bv ltac:(gres; bveq).
    zret.
  - zbft F_5b770 D_5b770.
    zstep F_5b774 D_5b774.
    zstep F_5b778 D_5b778. zld F_5b77c D_5b77c 0x164538 G68'. zld F_5b780 D_5b780 0x166550 Crm'.
    zlw F_5b784 D_5b784 (0x16afb8 + 52) Cfb'.
    zstep F_5b788 D_5b788.
    stepjr F_5b78c D_5b78c (0x1568bc : bv 64)%bv ltac:(gres; bveq).
    zret.
Qed.
End FPX.
