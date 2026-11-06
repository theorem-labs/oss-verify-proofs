(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac BrtLeaf BrtPoison BrtAllocG BrtUnwind BrtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_5fed4_60754 Bo0_code_67fdc_6814c Bo0_code_3d2b4_3e23c Bo0_code_4183c_42d28.
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

Lemma art_fx_zb_or2 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_fx_fq1_mem (M : word -> option byte) (S p t id f22 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M p id) (S - 2136) 0x6008c) (S - 2144) S) (S - 2152) p) (S - 2160) 0x6001c) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2208) (t + 208)) (S - 2200) (S - 2128)).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_fx_fq1_fn : forall regs (M rom : word -> option byte) (S p b1 n t id f22 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 8 = Z_to_bv 64 (p - 16) -> getr regs 9 = Z_to_bv 64 (S - 2128) -> getr regs 10 = Z_to_bv 64 id ->
  getr regs 18 = Z_to_bv 64 0xdb0d8 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 t -> getr regs 21 = Z_to_bv 64 (S - 81) -> getr regs 22 = Z_to_bv 64 f22 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x634000 + 16 <= p -> p + 8 < 2 ^ 47 -> 0 <= b1 < 256 -> 1 <= n < 2 ^ 28 -> 0 <= id < 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart (p - 16) 24 (S - 4096) 8192 -> 0 <= f22 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M (p - 16) 24 -> art_layout M ->
  cellA M (S - 2136) 8 (U (0x6008c : bv 64)%bv) -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x6001c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) ->
  cellA M (p - 16) 4 (3 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M (0xdb3b0 + 80) 8 (2 ^ 20) -> cellA M (0xdb3b0 + 64) 8 (2 ^ 28) -> cellA M (0xdbf38 + 48) 4 0 ->
  msteps ASEGS (mkst regs (0x41894 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x41b40 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2208))) 8 (Z_to_bv 64 0xdb3b0)) 9 (Z_to_bv 64 (t + 80))) 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 ((n + 7) / 8 * 8))) 12 (Z_to_bv 64 253)) 13 (Z_to_bv 64 0)) 14 (Z_to_bv 64 (p - 16))) 15 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 19 (Z_to_bv 64 (S - 2128))) 20 (Z_to_bv 64 (t + 208))) 21 (Z_to_bv 64 (p - 16))) 22 (Z_to_bv 64 (2 ^ 20))) (0x611f8 : word) (art_fx_fq1_mem M S p t id f22) rom).
Proof.
  intros regs M rom S p b1 n t id f22 H2 H8 H9 H10 H18 H19 H20 H21 H22 HS HS' Hp Hp' Hb1 Hn Hid Ht Ht' Apsp Hf22 W Wp L C36 C44 C52 C60 C68 C76 Chw Cn Cqc Cqm Cff.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_41894 D_41894. rwH. try rewrite art_zb_slli by lia.
  stepn F_41898 D_41898. rwH. try rewrite art_zb_slli by lia.
  stepn F_4189c D_4189c. rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
  stepn F_418a0 D_418a0. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zsd F_418a4 D_418a4 (p - 16 + 16) id ltac:(rewok Wp).
  zstep F_418a8 D_418a8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
    replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia);
    assert (Cn' : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_418ac D_418ac (p - 16 + 2) Chi.
  zlwu F_418b0 D_418b0 (p - 16 + 4) Cn'.
  zstep F_418b4 D_418b4. zstep F_418b8 D_418b8.
  stepn F_418bc D_418bc. rwH. try rewrite art_zb_slli by lia.
  stepn F_418c0 D_418c0. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zstep F_418c4 D_418c4. zstep F_418c8 D_418c8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x6008c : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x6001c : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
  zld F_418cc D_418cc (S - 2136) E36. zld F_418d0 D_418d0 (S - 2144) E44. zld F_418d4 D_418d4 (S - 2152) E52.
  zld F_418d8 D_418d8 (S - 2160) E60. zld F_418dc D_418dc (S - 2168) E68. zld F_418e0 D_418e0 (S - 2176) E76.
  zstep F_418e4 D_418e4.
  stepn F_418e8 D_418e8.
  (* [comment removed for export] *)
  zstep F_419b4 D_419b4.
  zsd F_419b8 D_419b8 (S - 2136) (U (0x6008c : bv 64)%bv) ltac:(rewok W). zsd F_419bc D_419bc (S - 2144) S ltac:(rewok W). zsd F_419c0 D_419c0 (S - 2152) p ltac:(rewok W).
  zsd F_419c4 D_419c4 (S - 2160) (U (0x6001c : bv 64)%bv) ltac:(rewok W). zsd F_419c8 D_419c8 (S - 2168) 1 ltac:(rewok W). zsd F_419cc D_419cc (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_419d0 D_419d0 (S - 2184) (S - 81) ltac:(rewok W). zsd F_419d4 D_419d4 (S - 2192) f22 ltac:(rewok W).
  zstep F_419d8 D_419d8.
  zsd F_419dc D_419dc (S - 2208) (t + 208) ltac:(rewok W). zsd F_419e0 D_419e0 (S - 2208 + 8) (S - 2128) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0xdb3b0 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0xdb3b0 + 64) 8 (2 ^ 28)) by zcell end.
  zld F_419e4 D_419e4 (0xdb3b0 + 80) Cqc'.
  zstep F_419e8 D_419e8.
  zbft F_419ec D_419ec.
  zld F_419f0 D_419f0 (0xdb3b0 + 64) Cqm'.
  zbtk F_419f4 D_419f4.
  zstep F_41ab8 D_41ab8. zstep F_41abc D_41abc. zstep F_41ac0 D_41ac0. zstep F_41ac4 D_41ac4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G40' : cellA X 0xd64c0 8 0xdbf38) by zcell; assert (Cff' : cellA X (0xdbf38 + 48) 4 0) by zcell end.
  zld F_41ac8 D_41ac8 0xd64c0 G40'.
  zlw F_41acc D_41acc (0xdbf38 + 48) Cff'.
  zbtk F_41ad0 D_41ad0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi2);
    replace ((3 + 256 * b1) / 65536) with 0 in Chi2 by (symmetry; apply Z.div_small; lia);
    assert (Cn2 : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_41b18 D_41b18 (p - 16 + 2) Chi2.
  zlwu F_41b1c D_41b1c (p - 16 + 4) Cn2.
  zstep F_41b20 D_41b20.
  stepn F_41b24 D_41b24. rwH. try rewrite art_zb_slli by lia.
  stepn F_41b28 D_41b28. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zstep F_41b2c D_41b2c.
  stepn F_41b30 D_41b30. rwH. unfold v_andi. rewrite (art_u_lit (n + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
  zstep F_41b34 D_41b34. zstep F_41b38 D_41b38.
  stepn F_41b3c D_41b3c.
  unfold art_fx_fq1_mem. zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq2a_fn : forall regs (M rom : word -> option byte) (c ca st m n : Z),
  getr regs 9 = Z_to_bv 64 c -> getr regs 20 = Z_to_bv 64 ca -> getr regs 19 = Z_to_bv 64 st -> getr regs 21 = Z_to_bv 64 m -> getr regs 18 = Z_to_bv 64 n ->
  msteps ASEGS (mkst regs (0x41b40 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x41b58)) 10 (Z_to_bv 64 c)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 st)) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 n))
          (0x41b64 : word) M rom).
Proof.
  intros regs M rom c ca st m n H9 H20 H19 H21 H18.
  zstep F_41b40 D_41b40. zstep F_41b44 D_41b44. zstep F_41b48 D_41b48. zstep F_41b4c D_41b4c. zstep F_41b50 D_41b50.
  stepn F_41b54 D_41b54.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq2e_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (S - 2136) 8 0x6008c -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x6001c -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x41a90 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p f22 g16 g24 g32 g40 g48 g56 H2 Hret HS HS' Hp Hf22 Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_41a90 D_41a90 (S - 2136) E36. zld F_41a94 D_41a94 (S - 2144) E44. zld F_41a98 D_41a98 (S - 2152) E52. zld F_41a9c D_41a9c (S - 2160) E60.
  zld F_41aa0 D_41aa0 (S - 2168) E68. zld F_41aa4 D_41aa4 (S - 2176) E76. zld F_41aa8 D_41aa8 (S - 2184) E84. zld F_41aac D_41aac (S - 2192) E92.
  zstep F_41ab0 D_41ab0.
  stepjr F_41ab4 D_41ab4 (0x6008c : bv 64)%bv ltac:(gres; bveq).
  zstep F_6008c D_6008c.
  zld F_60090 D_60090 (S - 8) F8. rewrite Z_to_bv_bv_unsigned.
  zld F_60094 D_60094 (S - 16) F16. zld F_60098 D_60098 (S - 24) F24. zld F_6009c D_6009c (S - 32) F32.
  zld F_600a0 D_600a0 (S - 40) F40. zld F_600a4 D_600a4 (S - 48) F48. zld F_600a8 D_600a8 (S - 56) F56.
  zstep F_600ac D_600ac.
  stepret F_600b0 D_600b0 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq2n_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p c csz f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= csz <= 2 ^ 20 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (c + 24) 8 csz ->
  cellA M (S - 2136) 8 0x6008c -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x6001c -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x41b58 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 10 (Z_to_bv 64 csz)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p c csz f22 g16 g24 g32 g40 g48 g56 H2 H9 H22 Hret HS HS' Hp Hf22 Hc Hc' Hcsz Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Ccsz E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_41b58 D_41b58 (c + 24) Ccsz.
  zbft F_41b5c D_41b5c.
  stepn F_41b60 D_41b60.
  zcall (art_fx_fq2e_fn _ _ _ raw0 S p f22 g16 g24 g32 g40 g48 g56).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq2d_fn : forall regs (M rom : word -> option byte) (S c q csz cbc cbs : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 8 = Z_to_bv 64 q -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= c -> c + 32 < 2 ^ 64 -> 2 ^ 20 < csz < 2 ^ 64 ->
  cellA M (c + 24) 8 csz -> cellA M (S - 2208) 8 cbc -> cellA M (S - 2200) 8 cbs ->
  msteps ASEGS (mkst regs (0x41b58 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x41a90)) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 c)) 12 (Z_to_bv 64 cbc)) 13 (Z_to_bv 64 cbs)) (0x3f2bc : word) M rom).
Proof.
  intros regs M rom S c q csz cbc cbs H2 H8 H9 H22 HS HS' Hc Hc' Hcsz Ccsz Ccbc Ccbs.
  zld F_41b58 D_41b58 (c + 24) Ccsz.
  zbtk F_41b5c D_41b5c.
  zld F_41a7c D_41a7c (S - 2208) Ccbc.
  zld F_41a80 D_41a80 (S - 2200) Ccbs.
  zstep F_41a84 D_41a84. zstep F_41a88 D_41a88.
  stepn F_41a8c D_41a8c.
  zret.
Qed.
End FPX.
