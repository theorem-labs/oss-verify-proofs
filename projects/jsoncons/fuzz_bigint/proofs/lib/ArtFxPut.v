(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac ArtLeaf ArtPoison ArtAllocG ArtUnwind ArtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_5fc54_604d4 As0_code_67d5c_67ecc As0_code_3d034_3dfbc As0_code_415bc_42aa8.
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

Lemma art_fx_zb_or2 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_fx_fq1_mem (M : word -> option byte) (S p t id f22 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M p id) (S - 2136) 0x5fe0c) (S - 2144) S) (S - 2152) p) (S - 2160) 0x5fd9c) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2208) (t + 208)) (S - 2200) (S - 2128)).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_fx_fq1_fn : forall regs (M rom : word -> option byte) (S p b1 n t id f22 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 8 = Z_to_bv 64 (p - 16) -> getr regs 9 = Z_to_bv 64 (S - 2128) -> getr regs 10 = Z_to_bv 64 id ->
  getr regs 18 = Z_to_bv 64 0xda4d8 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 t -> getr regs 21 = Z_to_bv 64 (S - 81) -> getr regs 22 = Z_to_bv 64 f22 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x633000 + 16 <= p -> p + 8 < 2 ^ 47 -> 0 <= b1 < 256 -> 1 <= n < 2 ^ 28 -> 0 <= id < 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart (p - 16) 24 (S - 4096) 8192 -> 0 <= f22 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M (p - 16) 24 -> art_layout M ->
  cellA M (S - 2136) 8 (U (0x5fe0c : bv 64)%bv) -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x5fd9c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) ->
  cellA M (p - 16) 4 (3 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M (0xda7b0 + 80) 8 (2 ^ 20) -> cellA M (0xda7b0 + 64) 8 (2 ^ 28) -> cellA M (0xdb338 + 48) 4 0 ->
  msteps ASEGS (mkst regs (0x41614 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x418c0 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2208))) 8 (Z_to_bv 64 0xda7b0)) 9 (Z_to_bv 64 (t + 80))) 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 ((n + 7) / 8 * 8))) 12 (Z_to_bv 64 253)) 13 (Z_to_bv 64 0)) 14 (Z_to_bv 64 (p - 16))) 15 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 19 (Z_to_bv 64 (S - 2128))) 20 (Z_to_bv 64 (t + 208))) 21 (Z_to_bv 64 (p - 16))) 22 (Z_to_bv 64 (2 ^ 20))) (0x60f78 : word) (art_fx_fq1_mem M S p t id f22) rom).
Proof.
  intros regs M rom S p b1 n t id f22 H2 H8 H9 H10 H18 H19 H20 H21 H22 HS HS' Hp Hp' Hb1 Hn Hid Ht Ht' Apsp Hf22 W Wp L C36 C44 C52 C60 C68 C76 Chw Cn Cqc Cqm Cff.
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_41614 D_41614. rwH. try rewrite art_zb_slli by lia.
  stepn F_41618 D_41618. rwH. try rewrite art_zb_slli by lia.
  stepn F_4161c D_4161c. rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
  stepn F_41620 D_41620. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zsd F_41624 D_41624 (p - 16 + 16) id ltac:(rewok Wp).
  zstep F_41628 D_41628.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
    replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia);
    assert (Cn' : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_4162c D_4162c (p - 16 + 2) Chi.
  zlwu F_41630 D_41630 (p - 16 + 4) Cn'.
  zstep F_41634 D_41634. zstep F_41638 D_41638.
  stepn F_4163c D_4163c. rwH. try rewrite art_zb_slli by lia.
  stepn F_41640 D_41640. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zstep F_41644 D_41644. zstep F_41648 D_41648.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x5fe0c : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x5fd9c : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
  zld F_4164c D_4164c (S - 2136) E36. zld F_41650 D_41650 (S - 2144) E44. zld F_41654 D_41654 (S - 2152) E52.
  zld F_41658 D_41658 (S - 2160) E60. zld F_4165c D_4165c (S - 2168) E68. zld F_41660 D_41660 (S - 2176) E76.
  zstep F_41664 D_41664.
  stepn F_41668 D_41668.
  (* [comment removed for export] *)
  zstep F_41734 D_41734.
  zsd F_41738 D_41738 (S - 2136) (U (0x5fe0c : bv 64)%bv) ltac:(rewok W). zsd F_4173c D_4173c (S - 2144) S ltac:(rewok W). zsd F_41740 D_41740 (S - 2152) p ltac:(rewok W).
  zsd F_41744 D_41744 (S - 2160) (U (0x5fd9c : bv 64)%bv) ltac:(rewok W). zsd F_41748 D_41748 (S - 2168) 1 ltac:(rewok W). zsd F_4174c D_4174c (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_41750 D_41750 (S - 2184) (S - 81) ltac:(rewok W). zsd F_41754 D_41754 (S - 2192) f22 ltac:(rewok W).
  zstep F_41758 D_41758.
  zsd F_4175c D_4175c (S - 2208) (t + 208) ltac:(rewok W). zsd F_41760 D_41760 (S - 2208 + 8) (S - 2128) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0xda7b0 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0xda7b0 + 64) 8 (2 ^ 28)) by zcell end.
  zld F_41764 D_41764 (0xda7b0 + 80) Cqc'.
  zstep F_41768 D_41768.
  zbft F_4176c D_4176c.
  zld F_41770 D_41770 (0xda7b0 + 64) Cqm'.
  zbtk F_41774 D_41774.
  zstep F_41838 D_41838. zstep F_4183c D_4183c. zstep F_41840 D_41840. zstep F_41844 D_41844.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G40' : cellA X 0xd58b0 8 0xdb338) by zcell; assert (Cff' : cellA X (0xdb338 + 48) 4 0) by zcell end.
  zld F_41848 D_41848 0xd58b0 G40'.
  zlw F_4184c D_4184c (0xdb338 + 48) Cff'.
  zbtk F_41850 D_41850.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi2);
    replace ((3 + 256 * b1) / 65536) with 0 in Chi2 by (symmetry; apply Z.div_small; lia);
    assert (Cn2 : cellA X (p - 16 + 4) 4 n) by (replace (p - 16 + 4) with (p - 12) by lia; zcell) end.
  zlhu F_41898 D_41898 (p - 16 + 2) Chi2.
  zlwu F_4189c D_4189c (p - 16 + 4) Cn2.
  zstep F_418a0 D_418a0.
  stepn F_418a4 D_418a4. rwH. try rewrite art_zb_slli by lia.
  stepn F_418a8 D_418a8. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zstep F_418ac D_418ac.
  stepn F_418b0 D_418b0. rwH. unfold v_andi. rewrite (art_u_lit (n + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
  zstep F_418b4 D_418b4. zstep F_418b8 D_418b8.
  stepn F_418bc D_418bc.
  unfold art_fx_fq1_mem. zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq2a_fn : forall regs (M rom : word -> option byte) (c ca st m n : Z),
  getr regs 9 = Z_to_bv 64 c -> getr regs 20 = Z_to_bv 64 ca -> getr regs 19 = Z_to_bv 64 st -> getr regs 21 = Z_to_bv 64 m -> getr regs 18 = Z_to_bv 64 n ->
  msteps ASEGS (mkst regs (0x418c0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x418d8)) 10 (Z_to_bv 64 c)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 st)) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 n))
          (0x418e4 : word) M rom).
Proof.
  intros regs M rom c ca st m n H9 H20 H19 H21 H18.
  zstep F_418c0 D_418c0. zstep F_418c4 D_418c4. zstep F_418c8 D_418c8. zstep F_418cc D_418cc. zstep F_418d0 D_418d0.
  stepn F_418d4 D_418d4.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq2e_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (S - 2136) 8 0x5fe0c -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x5fd9c -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x41810 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p f22 g16 g24 g32 g40 g48 g56 H2 Hret HS HS' Hp Hf22 Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_41810 D_41810 (S - 2136) E36. zld F_41814 D_41814 (S - 2144) E44. zld F_41818 D_41818 (S - 2152) E52. zld F_4181c D_4181c (S - 2160) E60.
  zld F_41820 D_41820 (S - 2168) E68. zld F_41824 D_41824 (S - 2176) E76. zld F_41828 D_41828 (S - 2184) E84. zld F_4182c D_4182c (S - 2192) E92.
  zstep F_41830 D_41830.
  stepjr F_41834 D_41834 (0x5fe0c : bv 64)%bv ltac:(gres; bveq).
  zstep F_5fe0c D_5fe0c.
  zld F_5fe10 D_5fe10 (S - 8) F8. rewrite Z_to_bv_bv_unsigned.
  zld F_5fe14 D_5fe14 (S - 16) F16. zld F_5fe18 D_5fe18 (S - 24) F24. zld F_5fe1c D_5fe1c (S - 32) F32.
  zld F_5fe20 D_5fe20 (S - 40) F40. zld F_5fe24 D_5fe24 (S - 48) F48. zld F_5fe28 D_5fe28 (S - 56) F56.
  zstep F_5fe2c D_5fe2c.
  stepret F_5fe30 D_5fe30 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq2n_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p c csz f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= csz <= 2 ^ 20 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (c + 24) 8 csz ->
  cellA M (S - 2136) 8 0x5fe0c -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x5fd9c -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x418d8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 10 (Z_to_bv 64 csz)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p c csz f22 g16 g24 g32 g40 g48 g56 H2 H9 H22 Hret HS HS' Hp Hf22 Hc Hc' Hcsz Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Ccsz E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_418d8 D_418d8 (c + 24) Ccsz.
  zbft F_418dc D_418dc.
  stepn F_418e0 D_418e0.
  zcall (art_fx_fq2e_fn _ _ _ raw0 S p f22 g16 g24 g32 g40 g48 g56).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_fx_fq2d_fn : forall regs (M rom : word -> option byte) (S c q csz cbc cbs : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 8 = Z_to_bv 64 q -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= c -> c + 32 < 2 ^ 64 -> 2 ^ 20 < csz < 2 ^ 64 ->
  cellA M (c + 24) 8 csz -> cellA M (S - 2208) 8 cbc -> cellA M (S - 2200) 8 cbs ->
  msteps ASEGS (mkst regs (0x418d8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x41810)) 10 (Z_to_bv 64 q)) 11 (Z_to_bv 64 c)) 12 (Z_to_bv 64 cbc)) 13 (Z_to_bv 64 cbs)) (0x3f03c : word) M rom).
Proof.
  intros regs M rom S c q csz cbc cbs H2 H8 H9 H22 HS HS' Hc Hc' Hcsz Ccsz Ccbc Ccbs.
  zld F_418d8 D_418d8 (c + 24) Ccsz.
  zbtk F_418dc D_418dc.
  zld F_417fc D_417fc (S - 2208) Ccbc.
  zld F_41800 D_41800 (S - 2200) Ccbs.
  zstep F_41804 D_41804. zstep F_41808 D_41808.
  stepn F_4180c D_4180c.
  zret.
Qed.
End FPX.
