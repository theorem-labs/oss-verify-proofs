(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtPoison.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_59000_5a000.
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
  32 <= sp -> sp < 2 ^ 64 -> 0x6b4000 + 32 <= sp -> 1 <= n <= rs -> rs + rz <= 65536 -> 0 <= rz ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 ->
  apart (sp - 32) 32 0x15d560 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 32 (t + 2800) 24 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> wrA M (t + 2800) 24 ->
  msteps ASEGS (mkst regs (0x59d68 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x59d6c : bv 64)%bv) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800 + 112))) 11 (Z_to_bv 64 512)) 12 (Z_to_bv 64 (mc + 1))) 13 (Z_to_bv 64 (mb + n))) 14 (Z_to_bv 64 65537)) (0x59dc0 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x59d6c) (sp - 24) 0x8a05c) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (rs + rz - n))) rom).
Proof.
  intros regs M rom sp n rs rz tp key tsd ctx t mc mb mr H2 H4 H9 H19 Hsp Hsp' IMG Hn Hprim Hrz Hmc Hmb Hmr W TSD Ht Ht' A1 A2 A3 A4 A5
         Cmc Cmb Cmr Wts.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_59d20 D_59d20.
  zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
    assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
    assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
    assert (Wts' : wrA X (t + 2800) 24) by (repeat apply wr_Wn; exact Wts) end.
  zld F_59d24 D_59d24 (t + 2800 + 16) Cmr'.
  zld F_59d28 D_59d28 (t + 2800) Cmc'.
  zld F_59d2c D_59d2c (t + 2800 + 8) Cmb'.
  zstep F_59d30 D_59d30. zstep F_59d34 D_59d34. zstep F_59d38 D_59d38. zstep F_59d3c D_59d3c. zstep F_59d40 D_59d40. zstep F_59d44 D_59d44.
  zsd F_59d48 D_59d48 (t + 2800) (mc + 1) ltac:(rewok Wts').
  zsd F_59d4c D_59d4c (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
  zsd F_59d50 D_59d50 (t + 2800 + 16) (mr + (rs + rz - n)) ltac:(rewok Wts').
  zbtk F_59d54 D_59d54.
  zstep F_59d70 D_59d70. zstep F_59d74 D_59d74.
  zret.
Qed.

Lemma art_alloc_d2b_small_fn : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 1 <= rs + rz <= 512 ->
  msteps ASEGS (mkst regs (0x59dc0 : word) M rom) (mkst (regupd regs 11 (Z_to_bv 64 ((rs + rz + 31) / 32))) (0x59eac : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbft F_59d78 D_59d78.
  zstep F_59d7c D_59d7c.
  stepn F_59d80 D_59d80. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
  stepn F_59d84 D_59d84.
  zret.
Qed.

Lemma art_alloc_d2b_big : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 513 <= rs + rz <= 65536 ->
  msteps ASEGS (mkst regs (0x59dc0 : word) M rom) (mkst regs (0x59dd0 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbtk F_59d78 D_59d78. apply mst_refl.
Qed.

Lemma art_alloc_d2c_fn : forall regs (M rom : word -> option byte) (sp ab n rz c t mbs : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 (t + 2800 + 112) -> getr regs 11 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 (ab + rz) ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 0x6b4000 <= sp -> 1 <= n < 2 ^ 40 -> 1 <= c <= 52 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= mbs < 2 ^ 64 ->
  0 <= ab + rz < 2 ^ 64 ->
  cellA M (t + 2800 + 112 + 8 * c) 8 mbs -> wrA M (t + 2800 + 112 + 8 * c) 8 -> apart (t + 2800 + 112 + 8 * c) 8 sp 128 -> t + 4096 <= 0x10000 \/ 0x6b4000 <= t ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x15b4f8 + 44) 4 4096 -> cellA M (0x15b4f8 + 52) 4 190 ->
  msteps ASEGS (mkst regs (0x59eac : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x59efc : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 190)) 12 (Z_to_bv 64 (Z.min n 4096))) 13 (Z_to_bv 64 0x1468c4)) (0x1468c4 : word) (Wn 8 M (t + 2800 + 112 + 8 * c) (mbs + 1)) rom).
Proof.
  intros regs M rom sp ab n rz c t mbs H2 H9 H10 H11 H20 Hsp Hsp' IMG Hn Hc Ht Ht' Hmbs Hub Cmbs Wmbs A1 Timg Ccf L Cmax Cfb.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_59e64 D_59e64. rwH. rewrite art_zb_slli by lia. change (2 ^ 3) with 8.
  zstep F_59e68 D_59e68.
  zld F_59e6c D_59e6c (t + 2800 + 112 + 8 * c) Cmbs.
  zstep F_59e70 D_59e70.
  zsd F_59e74 D_59e74 (t + 2800 + 112 + 8 * c) (mbs + 1) ltac:(rewok Wmbs).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
    assert (G40' : cellA X 0x1544f8 8 0x15b4f8) by (unfold apart in *; recell G40);
    assert (Cmax' : cellA X (0x15b4f8 + 44) 4 4096) by (unfold apart in *; recell Cmax);
    assert (G68' : cellA X 0x154520 8 0x156528) by (unfold apart in *; recell G68);
    assert (Crm' : cellA X 0x156528 8 0x1468c4) by (unfold apart in *; recell Crm);
    assert (Cfb' : cellA X (0x15b4f8 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
  zld F_59e78 D_59e78 (sp + 8) Ccf'.
  zbft F_59e7c D_59e7c.
  zstep F_59e80 D_59e80. zld F_59e84 D_59e84 0x1544f8 G40'.
  zlw F_59e88 D_59e88 (0x15b4f8 + 44) Cmax'.
  zbft F_59e8c D_59e8c.
  zstep F_59e90 D_59e90.
  destruct (Z.lt_ge_cases n 4096) as [Sm|Bg].
  - zbtk F_59e94 D_59e94.
    zstep F_59e9c D_59e9c. zld F_59ea0 D_59ea0 0x154520 G68'. zld F_59ea4 D_59ea4 0x156528 Crm'.
    zlw F_59ea8 D_59ea8 (0x15b4f8 + 52) Cfb'.
    zstep F_59eac D_59eac.
    stepjr F_59eb0 D_59eb0 (0x1468c4 : bv 64)%bv ltac:(gres; bveq).
    zret.
  - zbft F_59e94 D_59e94.
    zstep F_59e98 D_59e98.
    zstep F_59e9c D_59e9c. zld F_59ea0 D_59ea0 0x154520 G68'. zld F_59ea4 D_59ea4 0x156528 Crm'.
    zlw F_59ea8 D_59ea8 (0x15b4f8 + 52) Cfb'.
    zstep F_59eac D_59eac.
    stepjr F_59eb0 D_59eb0 (0x1468c4 : bv 64)%bv ltac:(gres; bveq).
    zret.
Qed.
End FPX.
