(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac Pm4ArtLeaf Pm4ArtPoison Pm4ArtAllocG Pm4ArtUnwind Pm4ArtFree1 Pm4ArtFxPut Pm4ArtBig.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_5e000_5f000 Pm4_code_81000_82000 Pm4X_code_5e000_5f000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_fx_fq1p_fn : forall regs (M rom : word -> option byte) (S p b1 nl nh n t id f22 spb : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 8 = Z_to_bv 64 (p - 16) -> getr regs 9 = Z_to_bv 64 (S - 2128) -> getr regs 10 = Z_to_bv 64 id ->
  getr regs 18 = Z_to_bv 64 0x166898 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 t -> getr regs 21 = Z_to_bv 64 (S - 81) -> getr regs 22 = Z_to_bv 64 f22 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x6c0000 + 16 <= p -> p + 8 < 2 ^ 47 -> 0 <= b1 < 256 -> 0 <= nl < 2 ^ 32 -> 0 <= nh < 2 ^ 7 -> n = nl + 2 ^ 32 * nh -> 2 ^ 28 < n ->
  0 <= id < 2 ^ 32 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart (p - 16) 24 (S - 4096) 8192 -> 0 <= f22 < 2 ^ 64 ->
  0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> (p < spb \/ spb + 2 ^ 37 <= p - 16) ->
  wrA M (S - 4096) 4096 -> wrA M (p - 16) 24 -> art_layout M ->
  cellA M (S - 2136) 8 (U (0x81f78 : bv 64)%bv) -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x81f08 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) ->
  cellA M (p - 16) 4 (3 + 256 * b1 + 65536 * nh) -> cellA M (p - 12) 4 nl ->
  cellA M (0x166b70 + 80) 8 (2 ^ 20) -> cellA M (0x166b70 + 64) 8 (2 ^ 28) -> cellA M (1468568 + 32) 8 spb ->
  msteps ASEGS (mkst regs (0x5eacc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (0x5ecac : bv 64)%bv) 2 (Z_to_bv 64 (S - 2208))) 8 (Z_to_bv 64 0x166b70)) 9 (Z_to_bv 64 (t + 80))) 10 (Z_to_bv 64 (S - 2208))) 11 (Z_to_bv 64 (p - 16)))
             12 (Z_to_bv 64 (t + 208))) 13 (Z_to_bv 64 (S - 2128))) 14 (Z_to_bv 64 (p - 16))) 15 (Z_to_bv 64 n)) 18 (Z_to_bv 64 (U (0x81f08 : bv 64)%bv))) 19 (Z_to_bv 64 1))
             20 (Z_to_bv 64 (S - 2128))) 22 (Z_to_bv 64 (2 ^ 20)))
          (0x5cb38 : word) (art_fx_fq1_mem M S p t id f22) rom).
Proof.
  intros regs M rom S p b1 nl nh n t id f22 spb H2 H8 H9 H10 H18 H19 H20 H21 H22 HS HS' Hp Hp' Hb1 Hnl Hnh En Hn Hid Ht Ht' Apsp Hf22 Hspb Hspb' OFF W Wp L C36 C44 C52 C60 C68 C76 Chw Cn Cqc Cqm Cspb.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  assert (Hhi : (3 + 256 * b1 + 65536 * nh) / 65536 = nh). { rewrite Z.add_comm. rewrite Z.mul_comm. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (Hor : Z.lor (nh * 2 ^ 32) nl = n) by (rewrite art_lor_hi_lo by lia; lia).
  stepn F_5ea7c D_5ea7c. rwH. try rewrite art_zb_slli by lia.
  stepn F_5ea80 D_5ea80. rwH. try rewrite art_zb_slli by lia.
  stepn F_5ea84 D_5ea84. rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
  stepn F_5ea88 D_5ea88. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zsd F_5ea8c D_5ea8c (p - 16 + 16) id ltac:(rewok Wp).
  zstep F_5ea90 D_5ea90.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1 + 65536 * nh)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1 + 65536 * nh) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
    rewrite Hhi in Chi;
    assert (Cn' : cellA X (p - 16 + 4) 4 nl) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_5ea94 D_5ea94 (p - 16 + 2) Chi.
  zlwu F_5ea98 D_5ea98 (p - 16 + 4) Cn'.
  zstep F_5ea9c D_5ea9c. zstep F_5eaa0 D_5eaa0.
  stepn F_5eaa4 D_5eaa4. rwH. try rewrite art_zb_slli by lia.
  stepn F_5eaa8 D_5eaa8. rwH. rewrite art_fx_zb_or2 by lia. rewrite Hor.
  zstep F_5eaac D_5eaac. zstep F_5eab0 D_5eab0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x81f78 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x81f08 : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
  zld F_5eab4 D_5eab4 (S - 2136) E36. zld F_5eab8 D_5eab8 (S - 2144) E44. zld F_5eabc D_5eabc (S - 2152) E52.
  zld F_5eac0 D_5eac0 (S - 2160) E60. zld F_5eac4 D_5eac4 (S - 2168) E68. zld F_5eac8 D_5eac8 (S - 2176) E76.
  zstep F_5eacc D_5eacc.
  stepn F_5ead0 D_5ead0.
  (* [comment removed for export] *)
  zstep F_5eb9c D_5eb9c.
  zsd F_5eba0 D_5eba0 (S - 2136) (U (0x81f78 : bv 64)%bv) ltac:(rewok W). zsd F_5eba4 D_5eba4 (S - 2144) S ltac:(rewok W). zsd F_5eba8 D_5eba8 (S - 2152) p ltac:(rewok W).
  zsd F_5ebac D_5ebac (S - 2160) (U (0x81f08 : bv 64)%bv) ltac:(rewok W). zsd F_5ebb0 D_5ebb0 (S - 2168) 1 ltac:(rewok W). zsd F_5ebb4 D_5ebb4 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_5ebb8 D_5ebb8 (S - 2184) (S - 81) ltac:(rewok W). zsd F_5ebbc D_5ebbc (S - 2192) f22 ltac:(rewok W).
  zstep F_5ebc0 D_5ebc0.
  zsd F_5ebc4 D_5ebc4 (S - 2208) (t + 208) ltac:(rewok W). zsd F_5ebc8 D_5ebc8 (S - 2208 + 8) (S - 2128) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0x166b70 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0x166b70 + 64) 8 (2 ^ 28)) by zcell;
    assert (Cspb' : cellA X (1468568 + 32) 8 spb) by zcell end.
  zld F_5ebcc D_5ebcc (0x166b70 + 80) Cqc'.
  zstep F_5ebd0 D_5ebd0.
  zbft F_5ebd4 D_5ebd4.
  zld F_5ebd8 D_5ebd8 (0x166b70 + 64) Cqm'.
  zbft F_5ebdc D_5ebdc.
  (* [comment removed for export] *)
  zstep F_5ebe0 D_5ebe0.
  zld F_5ebe4 D_5ebe4 (1468568 + 32) Cspb'.
  destruct OFF as [OFF|OFF].
  - zbtk F_5ebe8 D_5ebe8.
    zstep F_5ec50 D_5ec50. zstep F_5ec54 D_5ec54.
    stepn F_5ec58 D_5ec58.
    unfold art_fx_fq1_mem. zret.
  - zbft F_5ebe8 D_5ebe8.
    zstep F_5ebec D_5ebec.
    stepn F_5ebf0 D_5ebf0. rwH. try rewrite art_zb_slli by lia.
    zstep F_5ebf4 D_5ebf4.
    zbtk F_5ebf8 D_5ebf8.
    zstep F_5ec50 D_5ec50. zstep F_5ec54 D_5ec54.
    stepn F_5ec58 D_5ec58.
    unfold art_fx_fq1_mem. zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq1pb_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p c csz f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= csz <= 2 ^ 20 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (c + 24) 8 csz ->
  cellA M (S - 2136) 8 0x81f78 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x81f08 -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x5ecac : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 10 (Z_to_bv 64 csz)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p c csz f22 g16 g24 g32 g40 g48 g56 H2 H9 H22 Hret HS HS' Hp Hf22 Hc Hc' Hcsz Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Ccsz E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_5ec5c D_5ec5c (c + 24) Ccsz.
  zbtk F_5ec60 D_5ec60.
  zcall (art_fx_fq2e_fn _ _ _ raw0 S p f22 g16 g24 g32 g40 g48 g56).
  zret.
Qed.

End FPX.
