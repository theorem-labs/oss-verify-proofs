(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac Pm5ArtLeaf Pm5ArtPoison Pm5ArtAllocG Pm5ArtUnwind Pm5ArtFree1 Pm5ArtFxPut Pm5ArtBig.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5_code_5f000_60000  Pm5X_code_5f000_60000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_fx_fq1p_fn : forall regs (M rom : word -> option byte) (S p b1 nl nh n t id f22 spb : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 8 = Z_to_bv 64 (p - 16) -> getr regs 9 = Z_to_bv 64 (S - 2128) -> getr regs 10 = Z_to_bv 64 id ->
  getr regs 18 = Z_to_bv 64 0x16a158 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 t -> getr regs 21 = Z_to_bv 64 (S - 81) -> getr regs 22 = Z_to_bv 64 f22 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x6c4000 + 16 <= p -> p + 8 < 2 ^ 47 -> 0 <= b1 < 256 -> 0 <= nl < 2 ^ 32 -> 0 <= nh < 2 ^ 7 -> n = nl + 2 ^ 32 * nh -> 2 ^ 28 < n ->
  0 <= id < 2 ^ 32 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart (p - 16) 24 (S - 4096) 8192 -> 0 <= f22 < 2 ^ 64 ->
  0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> (p < spb \/ spb + 2 ^ 37 <= p - 16) ->
  wrA M (S - 4096) 4096 -> wrA M (p - 16) 24 -> art_layout M ->
  cellA M (S - 2136) 8 (U (0x82848 : bv 64)%bv) -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x827d8 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) ->
  cellA M (p - 16) 4 (3 + 256 * b1 + 65536 * nh) -> cellA M (p - 12) 4 nl ->
  cellA M (0x16a430 + 80) 8 (2 ^ 20) -> cellA M (0x16a430 + 64) 8 (2 ^ 28) -> cellA M (1483096 + 32) 8 spb ->
  msteps ASEGS (mkst regs (0x5f39c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (0x5f57c : bv 64)%bv) 2 (Z_to_bv 64 (S - 2208))) 8 (Z_to_bv 64 0x16a430)) 9 (Z_to_bv 64 (t + 80))) 10 (Z_to_bv 64 (S - 2208))) 11 (Z_to_bv 64 (p - 16)))
             12 (Z_to_bv 64 (t + 208))) 13 (Z_to_bv 64 (S - 2128))) 14 (Z_to_bv 64 (p - 16))) 15 (Z_to_bv 64 n)) 18 (Z_to_bv 64 (U (0x827d8 : bv 64)%bv))) 19 (Z_to_bv 64 1))
             20 (Z_to_bv 64 (S - 2128))) 22 (Z_to_bv 64 (2 ^ 20)))
          (0x5d408 : word) (art_fx_fq1_mem M S p t id f22) rom).
Proof.
  intros regs M rom S p b1 nl nh n t id f22 spb H2 H8 H9 H10 H18 H19 H20 H21 H22 HS HS' Hp Hp' Hb1 Hnl Hnh En Hn Hid Ht Ht' Apsp Hf22 Hspb Hspb' OFF W Wp L C36 C44 C52 C60 C68 C76 Chw Cn Cqc Cqm Cspb.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  assert (Hhi : (3 + 256 * b1 + 65536 * nh) / 65536 = nh). { rewrite Z.add_comm. rewrite Z.mul_comm. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (Hor : Z.lor (nh * 2 ^ 32) nl = n) by (rewrite art_lor_hi_lo by lia; lia).
  stepn F_5f354 D_5f354. rwH. try rewrite art_zb_slli by lia.
  stepn F_5f358 D_5f358. rwH. try rewrite art_zb_slli by lia.
  stepn F_5f35c D_5f35c. rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
  stepn F_5f360 D_5f360. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zsd F_5f364 D_5f364 (p - 16 + 16) id ltac:(rewok Wp).
  zstep F_5f368 D_5f368.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1 + 65536 * nh)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1 + 65536 * nh) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
    rewrite Hhi in Chi;
    assert (Cn' : cellA X (p - 16 + 4) 4 nl) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_5f36c D_5f36c (p - 16 + 2) Chi.
  zlwu F_5f370 D_5f370 (p - 16 + 4) Cn'.
  zstep F_5f374 D_5f374. zstep F_5f378 D_5f378.
  stepn F_5f37c D_5f37c. rwH. try rewrite art_zb_slli by lia.
  stepn F_5f380 D_5f380. rwH. rewrite art_fx_zb_or2 by lia. rewrite Hor.
  zstep F_5f384 D_5f384. zstep F_5f388 D_5f388.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x82848 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x827d8 : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
  zld F_5f38c D_5f38c (S - 2136) E36. zld F_5f390 D_5f390 (S - 2144) E44. zld F_5f394 D_5f394 (S - 2152) E52.
  zld F_5f398 D_5f398 (S - 2160) E60. zld F_5f39c D_5f39c (S - 2168) E68. zld F_5f3a0 D_5f3a0 (S - 2176) E76.
  zstep F_5f3a4 D_5f3a4.
  stepn F_5f3a8 D_5f3a8.
  (* [comment removed for export] *)
  zstep F_5f474 D_5f474.
  zsd F_5f478 D_5f478 (S - 2136) (U (0x82848 : bv 64)%bv) ltac:(rewok W). zsd F_5f47c D_5f47c (S - 2144) S ltac:(rewok W). zsd F_5f480 D_5f480 (S - 2152) p ltac:(rewok W).
  zsd F_5f484 D_5f484 (S - 2160) (U (0x827d8 : bv 64)%bv) ltac:(rewok W). zsd F_5f488 D_5f488 (S - 2168) 1 ltac:(rewok W). zsd F_5f48c D_5f48c (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_5f490 D_5f490 (S - 2184) (S - 81) ltac:(rewok W). zsd F_5f494 D_5f494 (S - 2192) f22 ltac:(rewok W).
  zstep F_5f498 D_5f498.
  zsd F_5f49c D_5f49c (S - 2208) (t + 208) ltac:(rewok W). zsd F_5f4a0 D_5f4a0 (S - 2208 + 8) (S - 2128) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0x16a430 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0x16a430 + 64) 8 (2 ^ 28)) by zcell;
    assert (Cspb' : cellA X (1483096 + 32) 8 spb) by zcell end.
  zld F_5f4a4 D_5f4a4 (0x16a430 + 80) Cqc'.
  zstep F_5f4a8 D_5f4a8.
  zbft F_5f4ac D_5f4ac.
  zld F_5f4b0 D_5f4b0 (0x16a430 + 64) Cqm'.
  zbft F_5f4b4 D_5f4b4.
  (* [comment removed for export] *)
  zstep F_5f4b8 D_5f4b8.
  zld F_5f4bc D_5f4bc (1483096 + 32) Cspb'.
  destruct OFF as [OFF|OFF].
  - zbtk F_5f4c0 D_5f4c0.
    zstep F_5f528 D_5f528. zstep F_5f52c D_5f52c.
    stepn F_5f530 D_5f530.
    unfold art_fx_fq1_mem. zret.
  - zbft F_5f4c0 D_5f4c0.
    zstep F_5f4c4 D_5f4c4.
    stepn F_5f4c8 D_5f4c8. rwH. try rewrite art_zb_slli by lia.
    zstep F_5f4cc D_5f4cc.
    zbtk F_5f4d0 D_5f4d0.
    zstep F_5f528 D_5f528. zstep F_5f52c D_5f52c.
    stepn F_5f530 D_5f530.
    unfold art_fx_fq1_mem. zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq1pb_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p c csz f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= csz <= 2 ^ 20 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (c + 24) 8 csz ->
  cellA M (S - 2136) 8 0x82848 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x827d8 -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x5f57c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 10 (Z_to_bv 64 csz)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p c csz f22 g16 g24 g32 g40 g48 g56 H2 H9 H22 Hret HS HS' Hp Hf22 Hc Hc' Hcsz Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Ccsz E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_5f534 D_5f534 (c + 24) Ccsz.
  zbtk F_5f538 D_5f538.
  zcall (art_fx_fq2e_fn _ _ _ raw0 S p f22 g16 g24 g32 g40 g48 g56).
  zret.
Qed.

End FPX.
