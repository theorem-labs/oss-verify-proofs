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
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatAllocG_b BatUnwind_b BatFree1_b.
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
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".


Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Lemma art_fx_zb_or : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_fx_fcu2_mem (M : word -> option byte) (S p b1 n sz t fr1 fr2 f22 f23 f24 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) 498124) (S - 2144) S) (S - 2152) p) (S - 2160) 498012) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2192 - 8) 336668) (S - 2192 - 16) (S - 2128)) (S - 2192 - 24) p) (p - 16) (3 + 256 * b1)) (p - 16 + 16) (2 ^ 64 - 2 ^ 32)) (S - 2192 - 8) 337160) (S - 2192 - 24) 535228) (t + 2800 + 24) (fr1 + 1)) (t + 2800 + 32) (n + fr2)) (S - 2136) 498124) (S - 2144) S) (S - 2152) p) (S - 2160) 498012) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2176 - 8) 354408).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_fx_fcu2_fn : forall regs (M rom : word -> option byte) (S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> getr regs 4 = Z_to_bv 64 tp ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x696000 + 16 <= p -> p + 8 < 2 ^ 47 -> p mod 16 = 0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 -> 1 <= n < 2 ^ 32 -> 1 <= sz <= 30 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> apart (p - 16) 24 (S - 4096) 8192 -> apart (p - 16) 24 t 4096 ->
  apart ctx 4096 (S - 4096) 8192 -> apart t 4096 ctx 4096 -> apart (p - 16) 24 ctx 4096 -> hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) -> hid (t + 4096 <= 0x10000 \/ 0x696000 <= t) ->
  0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 ->
  0 <= fr1 < 2 ^ 64 -> 0 <= fr2 < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> wrA M (p - 16) 24 -> art_tsd M tp key tsd ctx t ->
  cellA M (S - 2136) 8 0x799b8 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x7995c : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 2128) 8 (S - 2112) -> cellA M (S - 2120) 8 sz ->
  cellA M (p - 16) 4 (2 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M 0x1d1708 8 0 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M (t + 2824) 8 fr1 -> cellA M (t + 2832) 8 fr2 ->
  msteps ASEGS (mkst regs (0x81f98 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x56888 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (p - 16))) 9 (Z_to_bv 64 (S - 2128))) 10 (Z_to_bv 64 (S - 2112))) 11 (Z_to_bv 64 sz)) 12 (Z_to_bv 64 (S - 2112))) 13 (Z_to_bv 64 ctx)) 14 (Z_to_bv 64 (fr1 + 1))) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 1295832)) 19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 t)) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x99fc4 : word) (art_fx_fcu2_mem M S p b1 n sz t fr1 fr2 f22 f23 f24) rom).
Proof.
  intros regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 Hb1 Hb14 Hn Hsz Ht Ht' Atsp Apsp Apt Actx Atctx Apctx Cimg Timg
         Htp0 Htp1 Htsd0 Htsd Hfr1 Hfr2 Hf22 Hf23 Hf24 W Wt Wp TSD C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 C28 C20 Chw Cn Cfh Ctctx Ctid Cfr1 Cfr2.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR). pose proof Timg as Timg'; unfold hid in Timg'.
  (* [comment removed for export] *)
  zsb F_81b80 D_81b80 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D36 : cellA X (S - 2136) 8 0x799b8) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 p) by zcell;
    assert (D60 : cellA X (S - 2160) 8 (U (0x7995c : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
    assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
  zld F_81b84 D_81b84 (S - 2136) D36. zld F_81b88 D_81b88 (S - 2144) D44. zld F_81b8c D_81b8c (S - 2152) D52. zld F_81b90 D_81b90 (S - 2160) D60.
  zld F_81b94 D_81b94 (S - 2168) D68. zld F_81b98 D_81b98 (S - 2176) D76. zld F_81b9c D_81b9c (S - 2184) D84. zld F_81ba0 D_81ba0 (S - 2192) D92.
  zld F_81ba4 D_81ba4 (S - 2200) D00. zld F_81ba8 D_81ba8 (S - 2208) D08.
  zstep F_81bac D_81bac.
  stepjr F_81bb0 D_81bb0 (0x799b8 : bv 64)%bv ltac:(gres; bveq).
  (* [comment removed for export] *)
  zstep F_795a0 D_795a0. zstep F_795a4 D_795a4. zstep F_795a8 D_795a8. zstep F_795ac D_795ac.
  stepn F_795b0 D_795b0.
  zstep F_51e90 D_51e90. zstep F_51e94 D_51e94. zstep F_51e98 D_51e98. zstep F_51e9c D_51e9c. zstep F_51ea0 D_51ea0. zstep F_51ea4 D_51ea4.
  zstep F_51ea8 D_51ea8. zstep F_51eac D_51eac. zstep F_51eb0 D_51eb0.
  stepn F_51eb4 D_51eb4.
  (* [comment removed for export] *)
  zstep F_51eb8 D_51eb8.
  zsd F_51ebc D_51ebc (S - 2136) (U (0x799cc : bv 64)%bv) ltac:(rewok W). zsd F_51ec0 D_51ec0 (S - 2144) S ltac:(rewok W). zsd F_51ec4 D_51ec4 (S - 2152) p ltac:(rewok W).
  zsd F_51ec8 D_51ec8 (S - 2160) (U (0x7995c : bv 64)%bv) ltac:(rewok W). zsd F_51ecc D_51ecc (S - 2168) 1 ltac:(rewok W). zsd F_51ed0 D_51ed0 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_51ed4 D_51ed4 (S - 2184) (S - 81) ltac:(rewok W). zsd F_51ed8 D_51ed8 (S - 2192) f22 ltac:(rewok W).
  zbft F_51edc D_51edc.
  zstep F_51ee0 D_51ee0. zstep F_51ee4 D_51ee4. zstep F_51ee8 D_51ee8. zstep F_51eec D_51eec. zstep F_51ef0 D_51ef0. zstep F_51ef4 D_51ef4. zstep F_51ef8 D_51ef8. zstep F_51efc D_51efc.
  stepn F_51f00 D_51f00.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cfh' : cellA X 0x1d1708 8 0) by (unfold hid in Timg; zcell) end.
  zcall (art_run_free_hooks_fn _ _ _ _ (S - 2192)).
  zbtk F_51f04 D_51f04.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chw' : cellA X (p - 16) 4 (2 + 256 * b1)) by zcell; assert (Wp' : wrA X (p - 16) 24) by zwr end.
  assert (Hm16 : (p - 16) mod 16 = 0) by (replace (p - 16) with (p + (-1) * 16) by lia; rewrite Z_mod_plus_full; exact Hp16).
  zcall (art_cas23_fn _ _ _ (p - 16) b1).
  zstep F_51f80 D_51f80. zstep F_51f84 D_51f84.
  zsd F_51f88 D_51f88 (p - 16 + 16) (2 ^ 64 - 2 ^ 32) ltac:(rewok Wp).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (Cst & Cb1 & Chi) end.
  replace ((3 + 256 * b1) mod 256) with 3 in Cst by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity).
  replace ((3 + 256 * b1) / 256 mod 256) with b1 in Cb1 by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_div_plus_full, (Z.div_small 3) by lia; rewrite Z.mod_small by lia; lia).
  replace ((3 + 256 * b1) / 65536) with 0 in Chi by (symmetry; apply Z.div_small; lia).
  zlbu F_51f8c D_51f8c (p - 16 + 1) Cb1.
  stepn F_51f90 D_51f90. rwH. rewrite art_zb_andi by lia. replace (Z.land b1 3) with 1 by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia).
  zbft F_51f94 D_51f94.
  stepn F_51f98 D_51f98. rwH. unfold v_andi. rewrite art_u_lit by lia. change (Z_to_bv 64 (Z.land 1 (bv_wrap 64 (-2)))) with (Z_to_bv 64 0 : word).
  zstep F_51f9c D_51f9c.
  zbtk F_51fa0 D_51fa0.
  stepn F_520ec D_520ec.
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
  zlhu F_520f0 D_520f0 (p - 14) Chi'.
  zlwu F_520f4 D_520f4 (p - 12) Cn'.
  zld F_520f8 D_520f8 (t + 2800 + 32) Cfr2'. zld F_520fc D_520fc (t + 2800 + 24) Cfr1'.
  zstep F_52100 D_52100.
  stepn F_52104 D_52104. rwH. rewrite art_fx_zb_or by lia. rewrite Z.lor_0_l.
  zstep F_52108 D_52108. zstep F_5210c D_5210c.
  zsd F_52110 D_52110 (t + 2800 + 24) (fr1 + 1) ltac:(rewok Wt).
  zsd F_52114 D_52114 (t + 2800 + 32) (n + fr2) ltac:(rewok Wt).
  zstep F_52118 D_52118. zstep F_5211c D_5211c. zstep F_52120 D_52120. zstep F_52124 D_52124.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x799cc : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x7995c : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell;
    assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell end.
  zld F_52128 D_52128 (S - 2136) E36. zld F_5212c D_5212c (S - 2144) E44. zld F_52130 D_52130 (S - 2152) E52. zld F_52134 D_52134 (S - 2160) E60.
  zld F_52138 D_52138 (S - 2168) E68. zld F_5213c D_5213c (S - 2176) E76. zld F_52140 D_52140 (S - 2184) E84. zld F_52144 D_52144 (S - 2192) E92.
  zstep F_52148 D_52148.
  stepn F_5214c D_5214c.
  (* [comment removed for export] *)
  zstep F_56418 D_56418.
  zsd F_5641c D_5641c (S - 2136) (U (0x799cc : bv 64)%bv) ltac:(rewok W). zsd F_56420 D_56420 (S - 2144) S ltac:(rewok W). zsd F_56424 D_56424 (S - 2152) p ltac:(rewok W).
  zsd F_56428 D_56428 (S - 2160) (U (0x7995c : bv 64)%bv) ltac:(rewok W). zsd F_5642c D_5642c (S - 2168) 1 ltac:(rewok W). zsd F_56430 D_56430 (S - 2176) (S - 2128) ltac:(rewok W).
  zstep F_56434 D_56434.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw3 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw3) as (Cst' & _ & _);
    replace ((3 + 256 * b1) mod 256) with 3 in Cst' by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity) end.
  zlb F_56438 D_56438 (p - 16) Cst'.
  zstep F_5643c D_5643c.
  zbft F_56440 D_56440.
  zstep F_56444 D_56444. zstep F_56448 D_56448.
  stepn F_5644c D_5644c.
  zcall (art_cur_thread_fn _ _ _ _ (S - 2176) tp key tsd ctx t).
  { unfold art_tsd. repeat split; try lia; zcell. }
  all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
  zbft F_56450 D_56450.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ctctx' : cellA X t 8 ctx) by zcell;
    assert (C28' : cellA X (S - 2128) 8 (S - 2112)) by zcell;
    assert (C20' : cellA X (S - 2128 + 8) 8 sz) by (replace (S - 2128 + 8) with (S - 2120) by lia; zcell);
    assert (Ctid' : cellA X (ctx + 8) 4 0) by zcell end.
  zld F_56454 D_56454 t Ctctx'. zld F_56458 D_56458 (S - 2128) C28'. zld F_5645c D_5645c (S - 2128 + 8) C20'.
  zlw F_56460 D_56460 (ctx + 8) Ctid'.
  zstep F_56464 D_56464. zstep F_56468 D_56468.
  stepn F_5646c D_5646c.
  unfold art_fx_fcu2_mem. zret.
Qed.
End FPX.
