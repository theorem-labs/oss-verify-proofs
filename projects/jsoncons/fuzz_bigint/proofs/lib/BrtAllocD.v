(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_3d2b4_3e23c.
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
  32 <= sp -> sp < 2 ^ 64 -> 0x634000 + 32 <= sp -> 1 <= n <= rs -> rs + rz <= 65536 -> 0 <= rz ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 ->
  apart (sp - 32) 32 0xddfa0 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 32 (t + 2800) 24 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> wrA M (t + 2800) 24 ->
  msteps ASEGS (mkst regs (0x3db3c : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3db40 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800 + 112))) 11 (Z_to_bv 64 512)) 12 (Z_to_bv 64 (mc + 1))) 13 (Z_to_bv 64 (mb + n))) 14 (Z_to_bv 64 65537)) (0x3db94 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x3db40) (sp - 24) 0x68c3c) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (rs + rz - n))) rom).
Proof.
  intros regs M rom sp n rs rz tp key tsd ctx t mc mb mr H2 H4 H9 H19 Hsp Hsp' IMG Hn Hprim Hrz Hmc Hmb Hmr W TSD Ht Ht' A1 A2 A3 A4 A5
         Cmc Cmb Cmr Wts.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_3db3c D_3db3c.
  zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
    assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
    assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
    assert (Wts' : wrA X (t + 2800) 24) by (repeat apply wr_Wn; exact Wts) end.
  zld F_3db40 D_3db40 (t + 2800 + 16) Cmr'.
  zld F_3db44 D_3db44 (t + 2800) Cmc'.
  zld F_3db48 D_3db48 (t + 2800 + 8) Cmb'.
  zstep F_3db4c D_3db4c. zstep F_3db50 D_3db50. zstep F_3db54 D_3db54. zstep F_3db58 D_3db58. zstep F_3db5c D_3db5c. zstep F_3db60 D_3db60.
  zsd F_3db64 D_3db64 (t + 2800) (mc + 1) ltac:(rewok Wts').
  zsd F_3db68 D_3db68 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
  zsd F_3db6c D_3db6c (t + 2800 + 16) (mr + (rs + rz - n)) ltac:(rewok Wts').
  zbtk F_3db70 D_3db70.
  zstep F_3db8c D_3db8c. zstep F_3db90 D_3db90.
  zret.
Qed.

Lemma art_alloc_d2b_small_fn : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 1 <= rs + rz <= 512 ->
  msteps ASEGS (mkst regs (0x3db94 : word) M rom) (mkst (regupd regs 11 (Z_to_bv 64 ((rs + rz + 31) / 32))) (0x3dc80 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbft F_3db94 D_3db94.
  zstep F_3db98 D_3db98.
  stepn F_3db9c D_3db9c. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
  stepn F_3dba0 D_3dba0.
  zret.
Qed.

Lemma art_alloc_d2b_big : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 513 <= rs + rz <= 65536 ->
  msteps ASEGS (mkst regs (0x3db94 : word) M rom) (mkst regs (0x3dba4 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbtk F_3db94 D_3db94. apply mst_refl.
Qed.

Lemma art_alloc_d2c_fn : forall regs (M rom : word -> option byte) (sp ab n rz c t mbs : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 (t + 2800 + 112) -> getr regs 11 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 (ab + rz) ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 0x634000 <= sp -> 1 <= n < 2 ^ 40 -> 1 <= c <= 52 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= mbs < 2 ^ 64 ->
  0 <= ab + rz < 2 ^ 64 ->
  cellA M (t + 2800 + 112 + 8 * c) 8 mbs -> wrA M (t + 2800 + 112 + 8 * c) 8 -> apart (t + 2800 + 112 + 8 * c) 8 sp 128 -> t + 4096 <= 0x10000 \/ 0x634000 <= t ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0xdbf38 + 44) 4 4096 -> cellA M (0xdbf38 + 52) 4 190 ->
  msteps ASEGS (mkst regs (0x3dc80 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x3dcd0 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 190)) 12 (Z_to_bv 64 (Z.min n 4096))) 13 (Z_to_bv 64 0xcc740)) (0xcc740 : word) (Wn 8 M (t + 2800 + 112 + 8 * c) (mbs + 1)) rom).
Proof.
  intros regs M rom sp ab n rz c t mbs H2 H9 H10 H11 H20 Hsp Hsp' IMG Hn Hc Ht Ht' Hmbs Hub Cmbs Wmbs A1 Timg Ccf L Cmax Cfb.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_3dc80 D_3dc80. rwH. rewrite art_zb_slli by lia. change (2 ^ 3) with 8.
  zstep F_3dc84 D_3dc84.
  zld F_3dc88 D_3dc88 (t + 2800 + 112 + 8 * c) Cmbs.
  zstep F_3dc8c D_3dc8c.
  zsd F_3dc90 D_3dc90 (t + 2800 + 112 + 8 * c) (mbs + 1) ltac:(rewok Wmbs).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
    assert (G40' : cellA X 0xd64c0 8 0xdbf38) by (unfold apart in *; recell G40);
    assert (Cmax' : cellA X (0xdbf38 + 44) 4 4096) by (unfold apart in *; recell Cmax);
    assert (G68' : cellA X 0xd64e8 8 0xd8428) by (unfold apart in *; recell G68);
    assert (Crm' : cellA X 0xd8428 8 0xcc740) by (unfold apart in *; recell Crm);
    assert (Cfb' : cellA X (0xdbf38 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
  zld F_3dc94 D_3dc94 (sp + 8) Ccf'.
  zbft F_3dc98 D_3dc98.
  zstep F_3dc9c D_3dc9c. zld F_3dca0 D_3dca0 0xd64c0 G40'.
  zlw F_3dca4 D_3dca4 (0xdbf38 + 44) Cmax'.
  zbft F_3dca8 D_3dca8.
  zstep F_3dcac D_3dcac.
  destruct (Z.lt_ge_cases n 4096) as [Sm|Bg].
  - zbtk F_3dcb0 D_3dcb0.
    zstep F_3dcb8 D_3dcb8. zld F_3dcbc D_3dcbc 0xd64e8 G68'. zld F_3dcc0 D_3dcc0 0xd8428 Crm'.
    zlw F_3dcc4 D_3dcc4 (0xdbf38 + 52) Cfb'.
    zstep F_3dcc8 D_3dcc8.
    stepjr F_3dccc D_3dccc (0xcc740 : bv 64)%bv ltac:(gres; bveq).
    zret.
  - zbft F_3dcb0 D_3dcb0.
    zstep F_3dcb4 D_3dcb4.
    zstep F_3dcb8 D_3dcb8. zld F_3dcbc D_3dcbc 0xd64e8 G68'. zld F_3dcc0 D_3dcc0 0xd8428 Crm'.
    zlw F_3dcc4 D_3dcc4 (0xdbf38 + 52) Cfb'.
    zstep F_3dcc8 D_3dcc8.
    stepjr F_3dccc D_3dccc (0xcc740 : bv 64)%bv ltac:(gres; bveq).
    zret.
Qed.
End FPX.
