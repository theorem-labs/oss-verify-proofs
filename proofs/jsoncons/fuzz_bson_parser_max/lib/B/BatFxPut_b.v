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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatAllocG_b BatUnwind_b BatFree1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r5fac4_60344_b Ba0_code_r67bcc_67d3c_b Ba0_code_r3cf10_3de98_b Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.


Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Lemma art_fx_zb_or2 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_fx_fq1_mem (M : word -> option byte) (S p t id f22 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M p id) (S - 2136) 0x799cc) (S - 2144) S) (S - 2152) p) (S - 2160) 0x7995c) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2208) (t + 208)) (S - 2200) (S - 2128)).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_fx_fq1_fn : forall regs (M rom : word -> option byte) (S p b1 n t id f22 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 8 = Z_to_bv 64 (p - 16) -> getr regs 9 = Z_to_bv 64 (S - 2128) -> getr regs 10 = Z_to_bv 64 id ->
  getr regs 18 = Z_to_bv 64 0x13c5d8 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 t -> getr regs 21 = Z_to_bv 64 (S - 81) -> getr regs 22 = Z_to_bv 64 f22 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x696000 + 16 <= p -> p + 8 < 2 ^ 47 -> 0 <= b1 < 256 -> 1 <= n < 2 ^ 28 -> 0 <= id < 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart (p - 16) 24 (S - 4096) 8192 -> 0 <= f22 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M (p - 16) 24 -> art_layout M ->
  cellA M (S - 2136) 8 (U (0x799cc : bv 64)%bv) -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x7995c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) ->
  cellA M (p - 16) 4 (3 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M (0x13c8b0 + 80) 8 (2 ^ 20) -> cellA M (0x13c8b0 + 64) 8 (2 ^ 28) -> cellA M (0x13d438 + 48) 4 0 ->
  msteps ASEGS (mkst regs (0x56888 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x56b34 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2208))) 8 (Z_to_bv 64 0x13c8b0)) 9 (Z_to_bv 64 (t + 80))) 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 ((n + 7) / 8 * 8))) 12 (Z_to_bv 64 253)) 13 (Z_to_bv 64 0)) 14 (Z_to_bv 64 (p - 16))) 15 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 19 (Z_to_bv 64 (S - 2128))) 20 (Z_to_bv 64 (t + 208))) 21 (Z_to_bv 64 (p - 16))) 22 (Z_to_bv 64 (2 ^ 20))) (0x7ab38 : word) (art_fx_fq1_mem M S p t id f22) rom).
Proof.
  intros regs M rom S p b1 n t id f22 H2 H8 H9 H10 H18 H19 H20 H21 H22 HS HS' Hp Hp' Hb1 Hn Hid Ht Ht' Apsp Hf22 W Wp L C36 C44 C52 C60 C68 C76 Chw Cn Cqc Cqm Cff.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_56470 D_56470. rwH. try rewrite art_zb_slli by lia.
  stepn F_56474 D_56474. rwH. try rewrite art_zb_slli by lia.
  stepn F_56478 D_56478. rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
  stepn F_5647c D_5647c. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zsd F_56480 D_56480 (p - 16 + 16) id ltac:(rewok Wp).
  zstep F_56484 D_56484.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
    replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia);
    assert (Cn' : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_56488 D_56488 (p - 16 + 2) Chi.
  zlwu F_5648c D_5648c (p - 16 + 4) Cn'.
  zstep F_56490 D_56490. zstep F_56494 D_56494.
  stepn F_56498 D_56498. rwH. try rewrite art_zb_slli by lia.
  stepn F_5649c D_5649c. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zstep F_564a0 D_564a0. zstep F_564a4 D_564a4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x799cc : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x7995c : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
  zld F_564a8 D_564a8 (S - 2136) E36. zld F_564ac D_564ac (S - 2144) E44. zld F_564b0 D_564b0 (S - 2152) E52.
  zld F_564b4 D_564b4 (S - 2160) E60. zld F_564b8 D_564b8 (S - 2168) E68. zld F_564bc D_564bc (S - 2176) E76.
  zstep F_564c0 D_564c0.
  stepn F_564c4 D_564c4.
  (* [comment removed for export] *)
  zstep F_56590 D_56590.
  zsd F_56594 D_56594 (S - 2136) (U (0x799cc : bv 64)%bv) ltac:(rewok W). zsd F_56598 D_56598 (S - 2144) S ltac:(rewok W). zsd F_5659c D_5659c (S - 2152) p ltac:(rewok W).
  zsd F_565a0 D_565a0 (S - 2160) (U (0x7995c : bv 64)%bv) ltac:(rewok W). zsd F_565a4 D_565a4 (S - 2168) 1 ltac:(rewok W). zsd F_565a8 D_565a8 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_565ac D_565ac (S - 2184) (S - 81) ltac:(rewok W). zsd F_565b0 D_565b0 (S - 2192) f22 ltac:(rewok W).
  zstep F_565b4 D_565b4.
  zsd F_565b8 D_565b8 (S - 2208) (t + 208) ltac:(rewok W). zsd F_565bc D_565bc (S - 2208 + 8) (S - 2128) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0x13c8b0 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0x13c8b0 + 64) 8 (2 ^ 28)) by zcell end.
  zld F_565c0 D_565c0 (0x13c8b0 + 80) Cqc'.
  zstep F_565c4 D_565c4.
  zbft F_565c8 D_565c8.
  zld F_565cc D_565cc (0x13c8b0 + 64) Cqm'.
  zbtk F_565d0 D_565d0.
  zstep F_56694 D_56694. zstep F_56698 D_56698. zstep F_5669c D_5669c. zstep F_566a0 D_566a0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G40' : cellA X 0x1374b8 8 0x13d438) by zcell; assert (Cff' : cellA X (0x13d438 + 48) 4 0) by zcell end.
  zld F_566a4 D_566a4 0x1374b8 G40'.
  zlw F_566a8 D_566a8 (0x13d438 + 48) Cff'.
  zbtk F_566ac D_566ac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi2);
    replace ((3 + 256 * b1) / 65536) with 0 in Chi2 by (symmetry; apply Z.div_small; lia);
    assert (Cn2 : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_566f4 D_566f4 (p - 16 + 2) Chi2.
  zlwu F_566f8 D_566f8 (p - 16 + 4) Cn2.
  zstep F_566fc D_566fc.
  stepn F_56700 D_56700. rwH. try rewrite art_zb_slli by lia.
  stepn F_56704 D_56704. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zstep F_56708 D_56708.
  stepn F_5670c D_5670c. rwH. unfold v_andi. rewrite (art_u_lit (n + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
  zstep F_56710 D_56710. zstep F_56714 D_56714.
  stepn F_56718 D_56718.
  unfold art_fx_fq1_mem. zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_fx_fq2a_fn : forall regs (M rom : word -> option byte) (c ca st m n : Z),
  getr regs 9 = Z_to_bv 64 c -> getr regs 20 = Z_to_bv 64 ca -> getr regs 19 = Z_to_bv 64 st -> getr regs 21 = Z_to_bv 64 m -> getr regs 18 = Z_to_bv 64 n ->
  msteps ASEGS (mkst regs (0x56b34 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x56b4c)) 10 (Z_to_bv 64 c)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 st)) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 n))
          (0x56b58 : word) M rom).
Proof.
  intros regs M rom c ca st m n H9 H20 H19 H21 H18.
  zstep F_5671c D_5671c. zstep F_56720 D_56720. zstep F_56724 D_56724. zstep F_56728 D_56728. zstep F_5672c D_5672c.
  stepn F_56730 D_56730.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_fx_fq2e_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (S - 2136) 8 0x799cc -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x7995c -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x56a84 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p f22 g16 g24 g32 g40 g48 g56 H2 Hret HS HS' Hp Hf22 Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_5666c D_5666c (S - 2136) E36. zld F_56670 D_56670 (S - 2144) E44. zld F_56674 D_56674 (S - 2152) E52. zld F_56678 D_56678 (S - 2160) E60.
  zld F_5667c D_5667c (S - 2168) E68. zld F_56680 D_56680 (S - 2176) E76. zld F_56684 D_56684 (S - 2184) E84. zld F_56688 D_56688 (S - 2192) E92.
  zstep F_5668c D_5668c.
  stepjr F_56690 D_56690 (0x799cc : bv 64)%bv ltac:(gres; bveq).
  zstep F_795b4 D_795b4.
  zld F_795b8 D_795b8 (S - 8) F8. rewrite Z_to_bv_bv_unsigned.
  zld F_795bc D_795bc (S - 16) F16. zld F_795c0 D_795c0 (S - 24) F24. zld F_795c4 D_795c4 (S - 32) F32.
  zld F_795c8 D_795c8 (S - 40) F40. zld F_795cc D_795cc (S - 48) F48. zld F_795d0 D_795d0 (S - 56) F56.
  zstep F_795d4 D_795d4.
  stepret F_795d8 D_795d8 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_fx_fq2n_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p c csz f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= csz <= 2 ^ 20 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (c + 24) 8 csz ->
  cellA M (S - 2136) 8 0x799cc -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x7995c -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x56b4c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 10 (Z_to_bv 64 csz)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p c csz f22 g16 g24 g32 g40 g48 g56 H2 H9 H22 Hret HS HS' Hp Hf22 Hc Hc' Hcsz Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Ccsz E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_56734 D_56734 (c + 24) Ccsz.
  zbft F_56738 D_56738.
  stepn F_5673c D_5673c.
  zcall (art_fx_fq2e_fn _ _ _ raw0 S p f22 g16 g24 g32 g40 g48 g56).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_fx_fq2d_fn : forall regs (M rom : word -> option byte) (S c q csz cbc cbs : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 8 = Z_to_bv 64 q -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= c -> c + 32 < 2 ^ 64 -> 2 ^ 20 < csz < 2 ^ 64 ->
  cellA M (c + 24) 8 csz -> cellA M (S - 2208) 8 cbc -> cellA M (S - 2200) 8 cbs ->
  msteps ASEGS (mkst regs (0x56b4c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x56a84)) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 c)) 12 (Z_to_bv 64 cbc)) 13 (Z_to_bv 64 cbs)) (0x542b0 : word) M rom).
Proof.
  intros regs M rom S c q csz cbc cbs H2 H8 H9 H22 HS HS' Hc Hc' Hcsz Ccsz Ccbc Ccbs.
  zld F_56734 D_56734 (c + 24) Ccsz.
  zbtk F_56738 D_56738.
  zld F_56658 D_56658 (S - 2208) Ccbc.
  zld F_5665c D_5665c (S - 2200) Ccbs.
  zstep F_56660 D_56660. zstep F_56664 D_56664.
  stepn F_56668 D_56668.
  zret.
Qed.
End FPX.
