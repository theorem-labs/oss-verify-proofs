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
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtPoison BrtAllocG BrtUnwind BrtFree1 BrtFree2.
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
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".


Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Lemma art_fx_zb_or : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_fx_fcu2_mem (M : word -> option byte) (S p b1 n sz t fr1 fr2 f22 f23 f24 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) 393356) (S - 2144) S) (S - 2152) p) (S - 2160) 393244) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2192 - 8) 250664) (S - 2192 - 16) (S - 2128)) (S - 2192 - 24) p) (p - 16) (3 + 256 * b1)) (p - 16 + 16) (2 ^ 64 - 2 ^ 32)) (S - 2192 - 8) 251156) (S - 2192 - 24) 429116) (t + 2800 + 24) (fr1 + 1)) (t + 2800 + 32) (n + fr2)) (S - 2136) 393356) (S - 2144) S) (S - 2152) p) (S - 2160) 393244) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2176 - 8) 268404).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_fx_fcu2_fn : forall regs (M rom : word -> option byte) (S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> getr regs 4 = Z_to_bv 64 tp ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x634000 + 16 <= p -> p + 8 < 2 ^ 47 -> p mod 16 = 0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 -> 1 <= n < 2 ^ 32 -> 1 <= sz <= 30 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> apart (p - 16) 24 (S - 4096) 8192 -> apart (p - 16) 24 t 4096 ->
  apart ctx 4096 (S - 4096) 8192 -> apart t 4096 ctx 4096 -> apart (p - 16) 24 ctx 4096 -> hid (ctx + 4096 <= 0x10000 \/ 0x634000 <= ctx) -> hid (t + 4096 <= 0x10000 \/ 0x634000 <= t) ->
  0x10100 <= tp -> tp + 8 <= 0x634000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x634000 ->
  0 <= fr1 < 2 ^ 64 -> 0 <= fr2 < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> wrA M (p - 16) 24 -> art_tsd M tp key tsd ctx t ->
  cellA M (S - 2136) 8 0x60078 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x6001c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 2128) 8 (S - 2112) -> cellA M (S - 2120) 8 sz ->
  cellA M (p - 16) 4 (2 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M 0x170208 8 0 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M (t + 2824) 8 fr1 -> cellA M (t + 2832) 8 fr2 ->
  msteps ASEGS (mkst regs (0x68118 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x41894 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (p - 16))) 9 (Z_to_bv 64 (S - 2128))) 10 (Z_to_bv 64 (S - 2112))) 11 (Z_to_bv 64 sz)) 12 (Z_to_bv 64 (S - 2112))) 13 (Z_to_bv 64 ctx)) 14 (Z_to_bv 64 (fr1 + 1))) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 897240)) 19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 t)) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x80128 : word) (art_fx_fcu2_mem M S p b1 n sz t fr1 fr2 f22 f23 f24) rom).
Proof.
  intros regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 Hb1 Hb14 Hn Hsz Ht Ht' Atsp Apsp Apt Actx Atctx Apctx Cimg Timg
         Htp0 Htp1 Htsd0 Htsd Hfr1 Hfr2 Hf22 Hf23 Hf24 W Wt Wp TSD C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 C28 C20 Chw Cn Cfh Ctctx Ctid Cfr1 Cfr2.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR). pose proof Timg as Timg'; unfold hid in Timg'.
  (* [comment removed for export] *)
  zsb F_68118 D_68118 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D36 : cellA X (S - 2136) 8 0x60078) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 p) by zcell;
    assert (D60 : cellA X (S - 2160) 8 (U (0x6001c : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
    assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
  zld F_6811c D_6811c (S - 2136) D36. zld F_68120 D_68120 (S - 2144) D44. zld F_68124 D_68124 (S - 2152) D52. zld F_68128 D_68128 (S - 2160) D60.
  zld F_6812c D_6812c (S - 2168) D68. zld F_68130 D_68130 (S - 2176) D76. zld F_68134 D_68134 (S - 2184) D84. zld F_68138 D_68138 (S - 2192) D92.
  zld F_6813c D_6813c (S - 2200) D00. zld F_68140 D_68140 (S - 2208) D08.
  zstep F_68144 D_68144.
  stepjr F_68148 D_68148 (0x60078 : bv 64)%bv ltac:(gres; bveq).
  (* [comment removed for export] *)
  zstep F_60078 D_60078. zstep F_6007c D_6007c. zstep F_60080 D_60080. zstep F_60084 D_60084.
  stepn F_60088 D_60088.
  zstep F_3d2b4 D_3d2b4. zstep F_3d2b8 D_3d2b8. zstep F_3d2bc D_3d2bc. zstep F_3d2c0 D_3d2c0. zstep F_3d2c4 D_3d2c4. zstep F_3d2c8 D_3d2c8.
  zstep F_3d2cc D_3d2cc. zstep F_3d2d0 D_3d2d0. zstep F_3d2d4 D_3d2d4.
  stepn F_3d2d8 D_3d2d8.
  (* [comment removed for export] *)
  zstep F_3d2dc D_3d2dc.
  zsd F_3d2e0 D_3d2e0 (S - 2136) (U (0x6008c : bv 64)%bv) ltac:(rewok W). zsd F_3d2e4 D_3d2e4 (S - 2144) S ltac:(rewok W). zsd F_3d2e8 D_3d2e8 (S - 2152) p ltac:(rewok W).
  zsd F_3d2ec D_3d2ec (S - 2160) (U (0x6001c : bv 64)%bv) ltac:(rewok W). zsd F_3d2f0 D_3d2f0 (S - 2168) 1 ltac:(rewok W). zsd F_3d2f4 D_3d2f4 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_3d2f8 D_3d2f8 (S - 2184) (S - 81) ltac:(rewok W). zsd F_3d2fc D_3d2fc (S - 2192) f22 ltac:(rewok W).
  zbft F_3d300 D_3d300.
  zstep F_3d304 D_3d304. zstep F_3d308 D_3d308. zstep F_3d30c D_3d30c. zstep F_3d310 D_3d310. zstep F_3d314 D_3d314. zstep F_3d318 D_3d318. zstep F_3d31c D_3d31c. zstep F_3d320 D_3d320.
  stepn F_3d324 D_3d324.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cfh' : cellA X 0x170208 8 0) by (unfold hid in Timg; zcell) end.
  zcall (art_run_free_hooks_fn _ _ _ _ (S - 2192)).
  zbtk F_3d328 D_3d328.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chw' : cellA X (p - 16) 4 (2 + 256 * b1)) by zcell; assert (Wp' : wrA X (p - 16) 24) by zwr end.
  assert (Hm16 : (p - 16) mod 16 = 0) by (replace (p - 16) with (p + (-1) * 16) by lia; rewrite Z_mod_plus_full; exact Hp16).
  zcall (art_cas23_fn _ _ _ (p - 16) b1).
  zstep F_3d3a4 D_3d3a4. zstep F_3d3a8 D_3d3a8.
  zsd F_3d3ac D_3d3ac (p - 16 + 16) (2 ^ 64 - 2 ^ 32) ltac:(rewok Wp).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (Cst & Cb1 & Chi) end.
  replace ((3 + 256 * b1) mod 256) with 3 in Cst by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity).
  replace ((3 + 256 * b1) / 256 mod 256) with b1 in Cb1 by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_div_plus_full, (Z.div_small 3) by lia; rewrite Z.mod_small by lia; lia).
  replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia).
  zlbu F_3d3b0 D_3d3b0 (p - 16 + 1) Cb1.
  stepn F_3d3b4 D_3d3b4. rwH. rewrite art_zb_andi by lia. replace (Z.land b1 3) with 1 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia).
  zbft F_3d3b8 D_3d3b8.
  stepn F_3d3bc D_3d3bc. rwH. unfold v_andi. rewrite art_u_lit by lia. change (Z_to_bv 64 (Z.land 1 (bv_wrap 64 (-2)))) with (Z_to_bv 64 0 : word).
  zstep F_3d3c0 D_3d3c0.
  zbtk F_3d3c4 D_3d3c4.
  stepn F_3d510 D_3d510.
  zcall (art_thread_stats_fn _ _ _ _ (S - 2192) tp key tsd ctx t).
  { unfold art_tsd. repeat split; try lia; zcell. }
  all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi');
    replace ((3 + 256 * b1) / 65536) with 0 in Chi' by (symmetry; apply Z.div_small; lia); replace (p - 16 + 2) with (p - 14) in Chi' by lia;
    assert (Cn' : cellA X (p - 12) 4 n) by zcell;
    assert (Cfr1' : cellA X (t + 2800 + 24) 8 fr1) by (replace (t + 2800 + 24) with (t + 2824) by lia; zcell);
    assert (Cfr2' : cellA X (t + 2800 + 32) 8 fr2) by (replace (t + 2800 + 32) with (t + 2832) by lia; zcell) end.
  zlhu F_3d514 D_3d514 (p - 14) Chi'.
  zlwu F_3d518 D_3d518 (p - 12) Cn'.
  zld F_3d51c D_3d51c (t + 2800 + 32) Cfr2'. zld F_3d520 D_3d520 (t + 2800 + 24) Cfr1'.
  zstep F_3d524 D_3d524.
  stepn F_3d528 D_3d528. rwH. rewrite art_fx_zb_or by lia. rewrite Z.lor_0_l.
  zstep F_3d52c D_3d52c. zstep F_3d530 D_3d530.
  zsd F_3d534 D_3d534 (t + 2800 + 24) (fr1 + 1) ltac:(rewok Wt).
  zsd F_3d538 D_3d538 (t + 2800 + 32) (n + fr2) ltac:(rewok Wt).
  zstep F_3d53c D_3d53c. zstep F_3d540 D_3d540. zstep F_3d544 D_3d544. zstep F_3d548 D_3d548.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x6008c : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x6001c : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell;
    assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell end.
  zld F_3d54c D_3d54c (S - 2136) E36. zld F_3d550 D_3d550 (S - 2144) E44. zld F_3d554 D_3d554 (S - 2152) E52. zld F_3d558 D_3d558 (S - 2160) E60.
  zld F_3d55c D_3d55c (S - 2168) E68. zld F_3d560 D_3d560 (S - 2176) E76. zld F_3d564 D_3d564 (S - 2184) E84. zld F_3d568 D_3d568 (S - 2192) E92.
  zstep F_3d56c D_3d56c.
  stepn F_3d570 D_3d570.
  (* [comment removed for export] *)
  zstep F_4183c D_4183c.
  zsd F_41840 D_41840 (S - 2136) (U (0x6008c : bv 64)%bv) ltac:(rewok W). zsd F_41844 D_41844 (S - 2144) S ltac:(rewok W). zsd F_41848 D_41848 (S - 2152) p ltac:(rewok W).
  zsd F_4184c D_4184c (S - 2160) (U (0x6001c : bv 64)%bv) ltac:(rewok W). zsd F_41850 D_41850 (S - 2168) 1 ltac:(rewok W). zsd F_41854 D_41854 (S - 2176) (S - 2128) ltac:(rewok W).
  zstep F_41858 D_41858.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw3 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw3) as (Cst' & _ & _);
    replace ((3 + 256 * b1) mod 256) with 3 in Cst' by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity) end.
  zlb F_4185c D_4185c (p - 16) Cst'.
  zstep F_41860 D_41860.
  zbft F_41864 D_41864.
  zstep F_41868 D_41868. zstep F_4186c D_4186c.
  stepn F_41870 D_41870.
  zcall (art_cur_thread_fn _ _ _ _ (S - 2176) tp key tsd ctx t).
  { unfold art_tsd. repeat split; try lia; zcell. }
  all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
  zbft F_41874 D_41874.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ctctx' : cellA X t 8 ctx) by zcell;
    assert (C28' : cellA X (S - 2128) 8 (S - 2112)) by zcell;
    assert (C20' : cellA X (S - 2128 + 8) 8 sz) by (replace (S - 2128 + 8) with (S - 2120) by lia; zcell);
    assert (Ctid' : cellA X (ctx + 8) 4 0) by zcell end.
  zld F_41878 D_41878 t Ctctx'. zld F_4187c D_4187c (S - 2128) C28'. zld F_41880 D_41880 (S - 2128 + 8) C20'.
  zlw F_41884 D_41884 (ctx + 8) Ctid'.
  zstep F_41888 D_41888. zstep F_4188c D_4188c.
  stepn F_41890 D_41890.
  unfold art_fx_fcu2_mem. zret.
Qed.
End FPX.
