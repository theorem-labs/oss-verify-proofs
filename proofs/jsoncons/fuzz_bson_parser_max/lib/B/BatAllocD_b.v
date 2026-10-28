(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3cf10_3de98_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_d2a_fn : forall regs (M rom : word -> option byte) (sp n rs rz tp key tsd ctx t mc mb mr : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 (rs + rz) ->
  32 <= sp -> sp < 2 ^ 64 -> 0x696000 + 32 <= sp -> 1 <= n <= rs -> rs + rz <= 65536 -> 0 <= rz ->
  0 <= mc < 2 ^ 64 -> 0 <= mb < 2 ^ 64 -> 0 <= mr < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 < 2 ^ 64 ->
  apart (sp - 32) 32 0x13f4a0 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 32 (t + 2800) 24 ->
  cellA M (t + 2800) 8 mc -> cellA M (t + 2800 + 8) 8 mb -> cellA M (t + 2800 + 16) 8 mr -> wrA M (t + 2800) 24 ->
  msteps ASEGS (mkst regs (0x52b30 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52b34 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800 + 112))) 11 (Z_to_bv 64 512)) 12 (Z_to_bv 64 (mc + 1))) 13 (Z_to_bv 64 (mb + n))) 14 (Z_to_bv 64 65537)) (0x52b88 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 0x52b34) (sp - 24) 0x82abc) (t + 2800) (mc + 1)) (t + 2800 + 8) (mb + n)) (t + 2800 + 16) (mr + (rs + rz - n))) rom).
Proof.
  intros regs M rom sp n rs rz tp key tsd ctx t mc mb mr H2 H4 H9 H19 Hsp Hsp' IMG Hn Hprim Hrz Hmc Hmb Hmr W TSD Ht Ht' A1 A2 A3 A4 A5
         Cmc Cmb Cmr Wts.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_52718 D_52718.
  zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cmc' : cellA X (t + 2800) 8 mc) by (unfold apart in *; recell Cmc);
    assert (Cmb' : cellA X (t + 2800 + 8) 8 mb) by (unfold apart in *; recell Cmb);
    assert (Cmr' : cellA X (t + 2800 + 16) 8 mr) by (unfold apart in *; recell Cmr);
    assert (Wts' : wrA X (t + 2800) 24) by (repeat apply wr_Wn; exact Wts) end.
  zld F_5271c D_5271c (t + 2800 + 16) Cmr'.
  zld F_52720 D_52720 (t + 2800) Cmc'.
  zld F_52724 D_52724 (t + 2800 + 8) Cmb'.
  zstep F_52728 D_52728. zstep F_5272c D_5272c. zstep F_52730 D_52730. zstep F_52734 D_52734. zstep F_52738 D_52738. zstep F_5273c D_5273c.
  zsd F_52740 D_52740 (t + 2800) (mc + 1) ltac:(rewok Wts').
  zsd F_52744 D_52744 (t + 2800 + 8) (mb + n) ltac:(rewok Wts').
  zsd F_52748 D_52748 (t + 2800 + 16) (mr + (rs + rz - n)) ltac:(rewok Wts').
  zbtk F_5274c D_5274c.
  zstep F_52768 D_52768. zstep F_5276c D_5276c.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_d2b_small_fn : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 1 <= rs + rz <= 512 ->
  msteps ASEGS (mkst regs (0x52b88 : word) M rom) (mkst (regupd regs 11 (Z_to_bv 64 ((rs + rz + 31) / 32))) (0x52c74 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbft F_52770 D_52770.
  zstep F_52774 D_52774.
  stepn F_52778 D_52778. rwH. rewrite art_zb_srli by lia. change (2 ^ 5) with 32.
  stepn F_5277c D_5277c.
  zret.
Qed.

#[using="Type"] Lemma art_alloc_d2b_big : forall regs (M rom : word -> option byte) (rs rz : Z),
  getr regs 11 = Z_to_bv 64 512 -> getr regs 19 = Z_to_bv 64 (rs + rz) -> 513 <= rs + rz <= 65536 ->
  msteps ASEGS (mkst regs (0x52b88 : word) M rom) (mkst regs (0x52b98 : word) M rom).
Proof.
  intros regs M rom rs rz H11 H19 Hs.
  zbtk F_52770 D_52770. apply mst_refl.
Qed.

#[using="Type"] Lemma art_alloc_d2c_fn : forall regs (M rom : word -> option byte) (sp ab n rz c t mbs : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 n -> getr regs 10 = Z_to_bv 64 (t + 2800 + 112) -> getr regs 11 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 (ab + rz) ->
  0 <= sp -> sp + 128 < 2 ^ 64 -> 0x696000 <= sp -> 1 <= n < 2 ^ 40 -> 1 <= c <= 52 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= mbs < 2 ^ 64 ->
  0 <= ab + rz < 2 ^ 64 ->
  cellA M (t + 2800 + 112 + 8 * c) 8 mbs -> wrA M (t + 2800 + 112 + 8 * c) 8 -> apart (t + 2800 + 112 + 8 * c) 8 sp 128 -> t + 4096 <= 0x10000 \/ 0x696000 <= t ->
  cellA M (sp + 8) 8 1 -> art_layout M -> cellA M (0x13d438 + 44) 4 4096 -> cellA M (0x13d438 + 52) 4 190 ->
  msteps ASEGS (mkst regs (0x52c74 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x52cc4 : bv 64)%bv) 10 (Z_to_bv 64 (ab + rz))) 11 (Z_to_bv 64 190)) 12 (Z_to_bv 64 (Z.min n 4096))) 13 (Z_to_bv 64 0x129d04)) (0x129d04 : word) (Wn 8 M (t + 2800 + 112 + 8 * c) (mbs + 1)) rom).
Proof.
  intros regs M rom sp ab n rz c t mbs H2 H9 H10 H11 H20 Hsp Hsp' IMG Hn Hc Ht Ht' Hmbs Hub Cmbs Wmbs A1 Timg Ccf L Cmax Cfb.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_5285c D_5285c. rwH. rewrite art_zb_slli by lia. change (2 ^ 3) with 8.
  zstep F_52860 D_52860.
  zld F_52864 D_52864 (t + 2800 + 112 + 8 * c) Cmbs.
  zstep F_52868 D_52868.
  zsd F_5286c D_5286c (t + 2800 + 112 + 8 * c) (mbs + 1) ltac:(rewok Wmbs).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ccf' : cellA X (sp + 8) 8 1) by (unfold apart in *; recell Ccf);
    assert (G40' : cellA X 0x1374b8 8 0x13d438) by (unfold apart in *; recell G40);
    assert (Cmax' : cellA X (0x13d438 + 44) 4 4096) by (unfold apart in *; recell Cmax);
    assert (G68' : cellA X 0x1374e0 8 0x1394d0) by (unfold apart in *; recell G68);
    assert (Crm' : cellA X 0x1394d0 8 0x129d04) by (unfold apart in *; recell Crm);
    assert (Cfb' : cellA X (0x13d438 + 52) 4 190) by (unfold apart in *; recell Cfb) end.
  zld F_52870 D_52870 (sp + 8) Ccf'.
  zbft F_52874 D_52874.
  zstep F_52878 D_52878. zld F_5287c D_5287c 0x1374b8 G40'.
  zlw F_52880 D_52880 (0x13d438 + 44) Cmax'.
  zbft F_52884 D_52884.
  zstep F_52888 D_52888.
  destruct (Z.lt_ge_cases n 4096) as [Sm|Bg].
  - zbtk F_5288c D_5288c.
    zstep F_52894 D_52894. zld F_52898 D_52898 0x1374e0 G68'. zld F_5289c D_5289c 0x1394d0 Crm'.
    zlw F_528a0 D_528a0 (0x13d438 + 52) Cfb'.
    zstep F_528a4 D_528a4.
    stepjr F_528a8 D_528a8 (0x129d04 : bv 64)%bv ltac:(gres; bveq).
    zret.
  - zbft F_5288c D_5288c.
    zstep F_52890 D_52890.
    zstep F_52894 D_52894. zld F_52898 D_52898 0x1374e0 G68'. zld F_5289c D_5289c 0x1394d0 Crm'.
    zlw F_528a0 D_528a0 (0x13d438 + 52) Cfb'.
    zstep F_528a4 D_528a4.
    stepjr F_528a8 D_528a8 (0x129d04 : bv 64)%bv ltac:(gres; bveq).
    zret.
Qed.
End FPX.
