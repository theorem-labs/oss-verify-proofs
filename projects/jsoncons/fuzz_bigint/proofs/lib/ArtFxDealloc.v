(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtPoison ArtAllocG ArtUnwind ArtFree1 ArtFree2.
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
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".


Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Lemma art_fx_zb_or : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_fx_fcu2_mem (M : word -> option byte) (S p b1 n sz t fr1 fr2 f22 f23 f24 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) 392716) (S - 2144) S) (S - 2152) p) (S - 2160) 392604) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2192 - 8) 250024) (S - 2192 - 16) (S - 2128)) (S - 2192 - 24) p) (p - 16) (3 + 256 * b1)) (p - 16 + 16) (2 ^ 64 - 2 ^ 32)) (S - 2192 - 8) 250516) (S - 2192 - 24) 428476) (t + 2800 + 24) (fr1 + 1)) (t + 2800 + 32) (n + fr2)) (S - 2136) 392716) (S - 2144) S) (S - 2152) p) (S - 2160) 392604) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2176 - 8) 267764).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_fx_fcu2_fn : forall regs (M rom : word -> option byte) (S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> getr regs 4 = Z_to_bv 64 tp ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x633000 + 16 <= p -> p + 8 < 2 ^ 47 -> p mod 16 = 0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 -> 1 <= n < 2 ^ 32 -> 1 <= sz <= 30 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> apart (p - 16) 24 (S - 4096) 8192 -> apart (p - 16) 24 t 4096 ->
  apart ctx 4096 (S - 4096) 8192 -> apart t 4096 ctx 4096 -> apart (p - 16) 24 ctx 4096 -> hid (ctx + 4096 <= 0x10000 \/ 0x633000 <= ctx) -> hid (t + 4096 <= 0x10000 \/ 0x633000 <= t) ->
  0x10100 <= tp -> tp + 8 <= 0x633000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x633000 ->
  0 <= fr1 < 2 ^ 64 -> 0 <= fr2 < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> wrA M (p - 16) 24 -> art_tsd M tp key tsd ctx t ->
  cellA M (S - 2136) 8 0x5fdf8 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x5fd9c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 2128) 8 (S - 2112) -> cellA M (S - 2120) 8 sz ->
  cellA M (p - 16) 4 (2 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M 0x16f608 8 0 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M (t + 2824) 8 fr1 -> cellA M (t + 2832) 8 fr2 ->
  msteps ASEGS (mkst regs (0x67e98 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x41614 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (p - 16))) 9 (Z_to_bv 64 (S - 2128))) 10 (Z_to_bv 64 (S - 2112))) 11 (Z_to_bv 64 sz)) 12 (Z_to_bv 64 (S - 2112))) 13 (Z_to_bv 64 ctx)) 14 (Z_to_bv 64 (fr1 + 1))) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 894168)) 19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 t)) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x7fea8 : word) (art_fx_fcu2_mem M S p b1 n sz t fr1 fr2 f22 f23 f24) rom).
Proof.
  intros regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 Hb1 Hb14 Hn Hsz Ht Ht' Atsp Apsp Apt Actx Atctx Apctx Cimg Timg
         Htp0 Htp1 Htsd0 Htsd Hfr1 Hfr2 Hf22 Hf23 Hf24 W Wt Wp TSD C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 C28 C20 Chw Cn Cfh Ctctx Ctid Cfr1 Cfr2.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR). pose proof Timg as Timg'; unfold hid in Timg'.
  (* [comment removed for export] *)
  zsb F_67e98 D_67e98 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D36 : cellA X (S - 2136) 8 0x5fdf8) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 p) by zcell;
    assert (D60 : cellA X (S - 2160) 8 (U (0x5fd9c : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
    assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
  zld F_67e9c D_67e9c (S - 2136) D36. zld F_67ea0 D_67ea0 (S - 2144) D44. zld F_67ea4 D_67ea4 (S - 2152) D52. zld F_67ea8 D_67ea8 (S - 2160) D60.
  zld F_67eac D_67eac (S - 2168) D68. zld F_67eb0 D_67eb0 (S - 2176) D76. zld F_67eb4 D_67eb4 (S - 2184) D84. zld F_67eb8 D_67eb8 (S - 2192) D92.
  zld F_67ebc D_67ebc (S - 2200) D00. zld F_67ec0 D_67ec0 (S - 2208) D08.
  zstep F_67ec4 D_67ec4.
  stepjr F_67ec8 D_67ec8 (0x5fdf8 : bv 64)%bv ltac:(gres; bveq).
  (* [comment removed for export] *)
  zstep F_5fdf8 D_5fdf8. zstep F_5fdfc D_5fdfc. zstep F_5fe00 D_5fe00. zstep F_5fe04 D_5fe04.
  stepn F_5fe08 D_5fe08.
  zstep F_3d034 D_3d034. zstep F_3d038 D_3d038. zstep F_3d03c D_3d03c. zstep F_3d040 D_3d040. zstep F_3d044 D_3d044. zstep F_3d048 D_3d048.
  zstep F_3d04c D_3d04c. zstep F_3d050 D_3d050. zstep F_3d054 D_3d054.
  stepn F_3d058 D_3d058.
  (* [comment removed for export] *)
  zstep F_3d05c D_3d05c.
  zsd F_3d060 D_3d060 (S - 2136) (U (0x5fe0c : bv 64)%bv) ltac:(rewok W). zsd F_3d064 D_3d064 (S - 2144) S ltac:(rewok W). zsd F_3d068 D_3d068 (S - 2152) p ltac:(rewok W).
  zsd F_3d06c D_3d06c (S - 2160) (U (0x5fd9c : bv 64)%bv) ltac:(rewok W). zsd F_3d070 D_3d070 (S - 2168) 1 ltac:(rewok W). zsd F_3d074 D_3d074 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_3d078 D_3d078 (S - 2184) (S - 81) ltac:(rewok W). zsd F_3d07c D_3d07c (S - 2192) f22 ltac:(rewok W).
  zbft F_3d080 D_3d080.
  zstep F_3d084 D_3d084. zstep F_3d088 D_3d088. zstep F_3d08c D_3d08c. zstep F_3d090 D_3d090. zstep F_3d094 D_3d094. zstep F_3d098 D_3d098. zstep F_3d09c D_3d09c. zstep F_3d0a0 D_3d0a0.
  stepn F_3d0a4 D_3d0a4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cfh' : cellA X 0x16f608 8 0) by (unfold hid in Timg; zcell) end.
  zcall (art_run_free_hooks_fn _ _ _ _ (S - 2192)).
  zbtk F_3d0a8 D_3d0a8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chw' : cellA X (p - 16) 4 (2 + 256 * b1)) by zcell; assert (Wp' : wrA X (p - 16) 24) by zwr end.
  assert (Hm16 : (p - 16) mod 16 = 0) by (replace (p - 16) with (p + (-1) * 16) by lia; rewrite Z_mod_plus_full; exact Hp16).
  zcall (art_cas23_fn _ _ _ (p - 16) b1).
  zstep F_3d124 D_3d124. zstep F_3d128 D_3d128.
  zsd F_3d12c D_3d12c (p - 16 + 16) (2 ^ 64 - 2 ^ 32) ltac:(rewok Wp).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (Cst & Cb1 & Chi) end.
  replace ((3 + 256 * b1) mod 256) with 3 in Cst by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity).
  replace ((3 + 256 * b1) / 256 mod 256) with b1 in Cb1 by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_div_plus_full, (Z.div_small 3) by lia; rewrite Z.mod_small by lia; lia).
  replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia).
  zlbu F_3d130 D_3d130 (p - 16 + 1) Cb1.
  stepn F_3d134 D_3d134. rwH. rewrite art_zb_andi by lia. replace (Z.land b1 3) with 1 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia).
  zbft F_3d138 D_3d138.
  stepn F_3d13c D_3d13c. rwH. unfold v_andi. rewrite art_u_lit by lia. change (Z_to_bv 64 (Z.land 1 (bv_wrap 64 (-2)))) with (Z_to_bv 64 0 : word).
  zstep F_3d140 D_3d140.
  zbtk F_3d144 D_3d144.
  stepn F_3d290 D_3d290.
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
  zlhu F_3d294 D_3d294 (p - 14) Chi'.
  zlwu F_3d298 D_3d298 (p - 12) Cn'.
  zld F_3d29c D_3d29c (t + 2800 + 32) Cfr2'. zld F_3d2a0 D_3d2a0 (t + 2800 + 24) Cfr1'.
  zstep F_3d2a4 D_3d2a4.
  stepn F_3d2a8 D_3d2a8. rwH. rewrite art_fx_zb_or by lia. rewrite Z.lor_0_l.
  zstep F_3d2ac D_3d2ac. zstep F_3d2b0 D_3d2b0.
  zsd F_3d2b4 D_3d2b4 (t + 2800 + 24) (fr1 + 1) ltac:(rewok Wt).
  zsd F_3d2b8 D_3d2b8 (t + 2800 + 32) (n + fr2) ltac:(rewok Wt).
  zstep F_3d2bc D_3d2bc. zstep F_3d2c0 D_3d2c0. zstep F_3d2c4 D_3d2c4. zstep F_3d2c8 D_3d2c8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x5fe0c : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x5fd9c : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell;
    assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell end.
  zld F_3d2cc D_3d2cc (S - 2136) E36. zld F_3d2d0 D_3d2d0 (S - 2144) E44. zld F_3d2d4 D_3d2d4 (S - 2152) E52. zld F_3d2d8 D_3d2d8 (S - 2160) E60.
  zld F_3d2dc D_3d2dc (S - 2168) E68. zld F_3d2e0 D_3d2e0 (S - 2176) E76. zld F_3d2e4 D_3d2e4 (S - 2184) E84. zld F_3d2e8 D_3d2e8 (S - 2192) E92.
  zstep F_3d2ec D_3d2ec.
  stepn F_3d2f0 D_3d2f0.
  (* [comment removed for export] *)
  zstep F_415bc D_415bc.
  zsd F_415c0 D_415c0 (S - 2136) (U (0x5fe0c : bv 64)%bv) ltac:(rewok W). zsd F_415c4 D_415c4 (S - 2144) S ltac:(rewok W). zsd F_415c8 D_415c8 (S - 2152) p ltac:(rewok W).
  zsd F_415cc D_415cc (S - 2160) (U (0x5fd9c : bv 64)%bv) ltac:(rewok W). zsd F_415d0 D_415d0 (S - 2168) 1 ltac:(rewok W). zsd F_415d4 D_415d4 (S - 2176) (S - 2128) ltac:(rewok W).
  zstep F_415d8 D_415d8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw3 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw3) as (Cst' & _ & _);
    replace ((3 + 256 * b1) mod 256) with 3 in Cst' by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity) end.
  zlb F_415dc D_415dc (p - 16) Cst'.
  zstep F_415e0 D_415e0.
  zbft F_415e4 D_415e4.
  zstep F_415e8 D_415e8. zstep F_415ec D_415ec.
  stepn F_415f0 D_415f0.
  zcall (art_cur_thread_fn _ _ _ _ (S - 2176) tp key tsd ctx t).
  { unfold art_tsd. repeat split; try lia; zcell. }
  all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
  zbft F_415f4 D_415f4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ctctx' : cellA X t 8 ctx) by zcell;
    assert (C28' : cellA X (S - 2128) 8 (S - 2112)) by zcell;
    assert (C20' : cellA X (S - 2128 + 8) 8 sz) by (replace (S - 2128 + 8) with (S - 2120) by lia; zcell);
    assert (Ctid' : cellA X (ctx + 8) 4 0) by zcell end.
  zld F_415f8 D_415f8 t Ctctx'. zld F_415fc D_415fc (S - 2128) C28'. zld F_41600 D_41600 (S - 2128 + 8) C20'.
  zlw F_41604 D_41604 (ctx + 8) Ctid'.
  zstep F_41608 D_41608. zstep F_4160c D_4160c.
  stepn F_41610 D_41610.
  unfold art_fx_fcu2_mem. zret.
Qed.
End FPX.
