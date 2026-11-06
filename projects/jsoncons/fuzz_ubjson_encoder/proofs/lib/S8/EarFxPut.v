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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac EatLeaf EatPoison EatAllocG EatUnwind EatFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r5fac4_60344 Ea0_code_r67bcc_67d3c Ea0_code_r3cf10_3de98 Ea0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000080. Set Printing Width 10000.

Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Lemma art_fx_zb_or2 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

Definition art_fx_fq1_mem (M : word -> option byte) (S p t id f22 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M p id) (S - 2136) 0x7a350) (S - 2144) S) (S - 2152) p) (S - 2160) 0x7a2e0) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2208) (t + 208)) (S - 2200) (S - 2128)).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_fx_fq1_fn : forall regs (M rom : word -> option byte) (S p b1 n t id f22 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 8 = Z_to_bv 64 (p - 16) -> getr regs 9 = Z_to_bv 64 (S - 2128) -> getr regs 10 = Z_to_bv 64 id ->
  getr regs 18 = Z_to_bv 64 0x13e398 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 t -> getr regs 21 = Z_to_bv 64 (S - 81) -> getr regs 22 = Z_to_bv 64 f22 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x698000 + 16 <= p -> p + 8 < 2 ^ 47 -> 0 <= b1 < 256 -> 1 <= n <= 2 ^ 28 -> 0 <= id < 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart (p - 16) 24 (S - 4096) 8192 -> 0 <= f22 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M (p - 16) 24 -> art_layout M ->
  cellA M (S - 2136) 8 (U (0x7a350 : bv 64)%bv) -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) ->
  cellA M (p - 16) 4 (3 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M (0x13e670 + 80) 8 (2 ^ 20) -> cellA M (0x13e670 + 64) 8 (2 ^ 28) -> cellA M (0x13f1f8 + 48) 4 0 ->
  msteps ASEGS (mkst regs (0x57070 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5731c : bv 64)%bv) 2 (Z_to_bv 64 (S - 2208))) 8 (Z_to_bv 64 0x13e670)) 9 (Z_to_bv 64 (t + 80))) 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 ((n + 7) / 8 * 8))) 12 (Z_to_bv 64 253)) 13 (Z_to_bv 64 0)) 14 (Z_to_bv 64 (p - 16))) 15 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 19 (Z_to_bv 64 (S - 2128))) 20 (Z_to_bv 64 (t + 208))) 21 (Z_to_bv 64 (p - 16))) 22 (Z_to_bv 64 (2 ^ 20))) (0x7b4bc : word) (art_fx_fq1_mem M S p t id f22) rom).
Proof.
  intros regs M rom S p b1 n t id f22 H2 H8 H9 H10 H18 H19 H20 H21 H22 HS HS' Hp Hp' Hb1 Hn Hid Ht Ht' Apsp Hf22 W Wp L C36 C44 C52 C60 C68 C76 Chw Cn Cqc Cqm Cff.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_57020 D_57020. rwH. try rewrite art_zb_slli by lia.
  stepn F_57024 D_57024. rwH. try rewrite art_zb_slli by lia.
  stepn F_57028 D_57028. rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
  stepn F_5702c D_5702c. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zsd F_57030 D_57030 (p - 16 + 16) id ltac:(rewok Wp).
  zstep F_57034 D_57034.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
    replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia);
    assert (Cn' : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_57038 D_57038 (p - 16 + 2) Chi.
  zlwu F_5703c D_5703c (p - 16 + 4) Cn'.
  zstep F_57040 D_57040. zstep F_57044 D_57044.
  stepn F_57048 D_57048. rwH. try rewrite art_zb_slli by lia.
  stepn F_5704c D_5704c. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zstep F_57050 D_57050. zstep F_57054 D_57054.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x7a350 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
  zld F_57058 D_57058 (S - 2136) E36. zld F_5705c D_5705c (S - 2144) E44. zld F_57060 D_57060 (S - 2152) E52.
  zld F_57064 D_57064 (S - 2160) E60. zld F_57068 D_57068 (S - 2168) E68. zld F_5706c D_5706c (S - 2176) E76.
  zstep F_57070 D_57070.
  stepn F_57074 D_57074.

  zstep F_57140 D_57140.
  zsd F_57144 D_57144 (S - 2136) (U (0x7a350 : bv 64)%bv) ltac:(rewok W). zsd F_57148 D_57148 (S - 2144) S ltac:(rewok W). zsd F_5714c D_5714c (S - 2152) p ltac:(rewok W).
  zsd F_57150 D_57150 (S - 2160) (U (0x7a2e0 : bv 64)%bv) ltac:(rewok W). zsd F_57154 D_57154 (S - 2168) 1 ltac:(rewok W). zsd F_57158 D_57158 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_5715c D_5715c (S - 2184) (S - 81) ltac:(rewok W). zsd F_57160 D_57160 (S - 2192) f22 ltac:(rewok W).
  zstep F_57164 D_57164.
  zsd F_57168 D_57168 (S - 2208) (t + 208) ltac:(rewok W). zsd F_5716c D_5716c (S - 2208 + 8) (S - 2128) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0x13e670 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0x13e670 + 64) 8 (2 ^ 28)) by zcell end.
  zld F_57170 D_57170 (0x13e670 + 80) Cqc'.
  zstep F_57174 D_57174.
  zbft F_57178 D_57178.
  zld F_5717c D_5717c (0x13e670 + 64) Cqm'.
  zbtk F_57180 D_57180.
  zstep F_57244 D_57244. zstep F_57248 D_57248. zstep F_5724c D_5724c. zstep F_57250 D_57250.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G40' : cellA X 0x1391b0 8 0x13f1f8) by zcell; assert (Cff' : cellA X (0x13f1f8 + 48) 4 0) by zcell end.
  zld F_57254 D_57254 0x1391b0 G40'.
  zlw F_57258 D_57258 (0x13f1f8 + 48) Cff'.
  zbtk F_5725c D_5725c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi2);
    replace ((3 + 256 * b1) / 65536) with 0 in Chi2 by (symmetry; apply Z.div_small; lia);
    assert (Cn2 : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_572a4 D_572a4 (p - 16 + 2) Chi2.
  zlwu F_572a8 D_572a8 (p - 16 + 4) Cn2.
  zstep F_572ac D_572ac.
  stepn F_572b0 D_572b0. rwH. try rewrite art_zb_slli by lia.
  stepn F_572b4 D_572b4. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zstep F_572b8 D_572b8.
  stepn F_572bc D_572bc. rwH. unfold v_andi. rewrite (art_u_lit (n + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
  zstep F_572c0 D_572c0. zstep F_572c4 D_572c4.
  stepn F_572c8 D_572c8.
  unfold art_fx_fq1_mem. zret.
Qed.

#[using="Type"] Lemma art_fx_fq2a_fn : forall regs (M rom : word -> option byte) (c ca st m n : Z),
  getr regs 9 = Z_to_bv 64 c -> getr regs 20 = Z_to_bv 64 ca -> getr regs 19 = Z_to_bv 64 st -> getr regs 21 = Z_to_bv 64 m -> getr regs 18 = Z_to_bv 64 n ->
  msteps ASEGS (mkst regs (0x5731c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x57334)) 10 (Z_to_bv 64 c)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 st)) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 n))
          (0x57340 : word) M rom).
Proof.
  intros regs M rom c ca st m n H9 H20 H19 H21 H18.
  zstep F_572cc D_572cc. zstep F_572d0 D_572d0. zstep F_572d4 D_572d4. zstep F_572d8 D_572d8. zstep F_572dc D_572dc.
  stepn F_572e0 D_572e0.
  zret.
Qed.

#[using="Type"] Lemma art_fx_fq2e_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (S - 2136) 8 0x7a350 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x7a2e0 -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x5726c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p f22 g16 g24 g32 g40 g48 g56 H2 Hret HS HS' Hp Hf22 Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_5721c D_5721c (S - 2136) E36. zld F_57220 D_57220 (S - 2144) E44. zld F_57224 D_57224 (S - 2152) E52. zld F_57228 D_57228 (S - 2160) E60.
  zld F_5722c D_5722c (S - 2168) E68. zld F_57230 D_57230 (S - 2176) E76. zld F_57234 D_57234 (S - 2184) E84. zld F_57238 D_57238 (S - 2192) E92.
  zstep F_5723c D_5723c.
  stepjr F_57240 D_57240 (0x7a350 : bv 64)%bv ltac:(gres; bveq).
  zstep F_7a300 D_7a300.
  zld F_7a304 D_7a304 (S - 8) F8. rewrite Z_to_bv_bv_unsigned.
  zld F_7a308 D_7a308 (S - 16) F16. zld F_7a30c D_7a30c (S - 24) F24. zld F_7a310 D_7a310 (S - 32) F32.
  zld F_7a314 D_7a314 (S - 40) F40. zld F_7a318 D_7a318 (S - 48) F48. zld F_7a31c D_7a31c (S - 56) F56.
  zstep F_7a320 D_7a320.
  stepret F_7a324 D_7a324 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_fx_fq2n_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p c csz f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= csz <= 2 ^ 20 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (c + 24) 8 csz ->
  cellA M (S - 2136) 8 0x7a350 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x7a2e0 -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x57334 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 10 (Z_to_bv 64 csz)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p c csz f22 g16 g24 g32 g40 g48 g56 H2 H9 H22 Hret HS HS' Hp Hf22 Hc Hc' Hcsz Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Ccsz E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_572e4 D_572e4 (c + 24) Ccsz.
  zbft F_572e8 D_572e8.
  stepn F_572ec D_572ec.
  zcall (art_fx_fq2e_fn _ _ _ raw0 S p f22 g16 g24 g32 g40 g48 g56).
  zret.
Qed.

#[using="Type"] Lemma art_fx_fq2d_fn : forall regs (M rom : word -> option byte) (S c q csz cbc cbs : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 8 = Z_to_bv 64 q -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= c -> c + 32 < 2 ^ 64 -> 2 ^ 20 < csz < 2 ^ 64 ->
  cellA M (c + 24) 8 csz -> cellA M (S - 2208) 8 cbc -> cellA M (S - 2200) 8 cbs ->
  msteps ASEGS (mkst regs (0x57334 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x5726c)) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 c)) 12 (Z_to_bv 64 cbc)) 13 (Z_to_bv 64 cbs)) (0x54a98 : word) M rom).
Proof.
  intros regs M rom S c q csz cbc cbs H2 H8 H9 H22 HS HS' Hc Hc' Hcsz Ccsz Ccbc Ccbs.
  zld F_572e4 D_572e4 (c + 24) Ccsz.
  zbtk F_572e8 D_572e8.
  zld F_57208 D_57208 (S - 2208) Ccbc.
  zld F_5720c D_5720c (S - 2200) Ccbs.
  zstep F_57210 D_57210. zstep F_57214 D_57214.
  stepn F_57218 D_57218.
  zret.
Qed.
End FPX.
