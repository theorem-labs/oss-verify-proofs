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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatPoison EatAllocG EatUnwind EatFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EatHdrW.
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
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Lemma art_fx_zb_or : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

Definition art_fx_fcu2_mem (M : word -> option byte) (S p b1 n sz t fr1 fr2 f22 f23 f24 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) 500560) (S - 2144) S) (S - 2152) p) (S - 2160) 500448) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2192 - 8) 338692) (S - 2192 - 16) (S - 2128)) (S - 2192 - 24) p) (p - 16) (3 + 256 * b1)) (p - 16 + 16) (2 ^ 64 - 2 ^ 32)) (S - 2192 - 8) 339184) (S - 2192 - 24) 537664) (t + 2800 + 24) (fr1 + 1)) (t + 2800 + 32) (n + fr2)) (S - 2136) 500560) (S - 2144) S) (S - 2152) p) (S - 2160) 500448) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2176 - 8) 356432).

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

#[using="Type"] Lemma art_cas23W_fn : forall regs (M rom : word -> option byte) (m b1 : Z),
  getr regs 18 = Z_to_bv 64 m -> 16 <= m -> m + 16 < 2 ^ 47 -> m mod 16 = 0 -> 0 <= b1 < 2 ^ 23 ->
  cellA M m 4 (2 + 256 * b1) -> wrA M m 4 ->
  msteps ASEGS (mkst regs (0x52b40 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (m * 2 ^ 3))) 11 (Z_to_bv 64 3)) 12 (Z_to_bv 64 (2 + 256 * b1))) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 2)) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0))
          (0x52b80 : word) (Wn 4 M m (3 + 256 * b1)) rom).
Proof.
  intros regs M rom m b1 H18 Hm Hm' Hm16 Hb1 Chw Whw.
  assert (Hm4 : m mod 4 = 0). { pose proof (Z.div_mod m 16 ltac:(lia)) as E. rewrite Hm16 in E. rewrite E. replace (16 * (m / 16) + 0) with ((4 * (m / 16)) * 4) by lia. apply Z_mod_mult. }
  stepn F_52af0 D_52af0. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612. rewrite art_land_m4 by lia.
  replace (m / 4 * 4) with m by (pose proof (Z.div_mod m 4 ltac:(lia)); lia).
  stepn F_52af4 D_52af4. rwH. rewrite art_zb_slli by lia.
  zstep F_52af8 D_52af8. zstep F_52afc D_52afc. zstep F_52b00 D_52b00.
  stepn F_52b04 D_52b04. rwH. rewrite art_sllw_0 by lia.
  stepn F_52b08 D_52b08. rwH. rewrite art_sllw_0 by lia.
  stepn F_52b0c D_52b0c. rwH. rewrite art_sllw_0 by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Whw' : wok Asan.M.loaded_segments X m 4) by (rewok Whw) end.

  chain_step; [reflexivity
    | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m) _ (Z_to_bv 64 (2 + 256 * b1)));
      [exact F_52b10 | reflexivity | exact D_52b10 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4
      | exact Chw | apply art_bytes4; lia ]
    | ]. wpc. rewrite art_v_lw_small by lia.

  chain_step; [reflexivity | eapply art_step_and_r; [exact F_52b14 | reflexivity | exact D_52b14 | reflexivity] | ]. wpc.
  gres. rewrite (art_zb_and (2 + 256 * b1) 255) by lia.
  replace (Z.land (2 + 256 * b1) 255) with 2.
  2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. replace (2 + 256 * b1) with (2 + b1 * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_52b18 | reflexivity | exact D_52b18 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.

  chain_step; [reflexivity | eapply art_step_xor_r; [exact F_52b1c | reflexivity | exact D_52b1c | reflexivity] | ]. wpc.
  chain_step; [reflexivity | eapply art_step_and_r; [exact F_52b20 | reflexivity | exact D_52b20 | reflexivity] | ]. wpc.
  chain_step; [reflexivity | eapply art_step_xor_r; [exact F_52b24 | reflexivity | exact D_52b24 | reflexivity] | ]. wpc.
  gres.
  rewrite (art_casw_xor 2 3 b1) by lia.

  chain_step; [reflexivity
    | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m));
      [exact F_52b28 | reflexivity | exact D_52b28 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4 | gres; rwH; reflexivity
      | exact Whw' ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 m) (word_to_le_bytes 4 (Z_to_bv 64 (3 + 256 * b1)))) with (Wn 4 M0 m (3 + 256 * b1)).
  zbft F_52b2c D_52b2c.
  zret.
Qed.

#[using="Type"] Lemma art_fx_fcu2W_fn : forall regs (M rom : word -> option byte) (S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> getr regs 4 = Z_to_bv 64 tp ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x698000 + 16 <= p -> p + 8 < 2 ^ 47 -> p mod 16 = 0 -> 0 <= b1 < 2 ^ 24 -> b1 mod 4 = 1 -> 1 <= n < 2 ^ 40 -> b1 / 256 = n / 2 ^ 32 -> 1 <= sz <= 30 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> apart (p - 16) 24 (S - 4096) 8192 -> apart (p - 16) 24 t 4096 ->
  apart ctx 4096 (S - 4096) 8192 -> apart t 4096 ctx 4096 -> apart (p - 16) 24 ctx 4096 -> hid (ctx + 4096 <= 0x10000 \/ 0x698000 <= ctx) -> hid (t + 4096 <= 0x10000 \/ 0x698000 <= t) ->
  0x10100 <= tp -> tp + 8 <= 0x698000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x698000 ->
  0 <= fr1 < 2 ^ 64 -> 0 <= fr2 < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> wrA M (p - 16) 24 -> art_tsd M tp key tsd ctx t ->
  cellA M (S - 2136) 8 0x7a33c -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 2128) 8 (S - 2112) -> cellA M (S - 2120) 8 sz ->
  cellA M (p - 16) 4 (2 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M 0x1d34c8 8 0 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M (t + 2824) 8 fr1 -> cellA M (t + 2832) 8 fr2 ->
  msteps ASEGS (mkst regs (0x8291c : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x57070 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (p - 16))) 9 (Z_to_bv 64 (S - 2128))) 10 (Z_to_bv 64 (S - 2112))) 11 (Z_to_bv 64 sz)) 12 (Z_to_bv 64 (S - 2112))) 13 (Z_to_bv 64 ctx)) 14 (Z_to_bv 64 (fr1 + 1))) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 1303448)) 19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 t)) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x9a948 : word) (art_fx_fcu2_mem M S p b1 n sz t fr1 fr2 f22 f23 f24) rom).
Proof.
  intros regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 Hb1 Hb14 Hn Hlink Hsz Ht Ht' Atsp Apsp Apt Actx Atctx Apctx Cimg Timg
         Htp0 Htp1 Htsd0 Htsd Hfr1 Hfr2 Hf22 Hf23 Hf24 W Wt Wp TSD C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 C28 C20 Chw Cn Cfh Ctctx Ctid Cfr1 Cfr2.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR). pose proof Timg as Timg'; unfold hid in Timg'.
  assert (Hb1w := Hb1). clear Hb1. assert (Hb1 : 0 <= b1 < 2 ^ 16) by (apply (art_b1_bound b1 n (proj1 Hb1w) Hlink); clear - Hn; lia). clear Hb1w.
  assert (Hhi : 0 <= b1 / 256 < 2 ^ 15) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (Hlo : 0 <= n mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia). assert (Htb : 0 <= b1 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Hhi32 : 0 <= b1 / 256 * 2 ^ 32 < 2 ^ 47) by lia.

  zsb F_828cc D_828cc (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D36 : cellA X (S - 2136) 8 0x7a33c) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 p) by zcell;
    assert (D60 : cellA X (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
    assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
  zld F_828d0 D_828d0 (S - 2136) D36. zld F_828d4 D_828d4 (S - 2144) D44. zld F_828d8 D_828d8 (S - 2152) D52. zld F_828dc D_828dc (S - 2160) D60.
  zld F_828e0 D_828e0 (S - 2168) D68. zld F_828e4 D_828e4 (S - 2176) D76. zld F_828e8 D_828e8 (S - 2184) D84. zld F_828ec D_828ec (S - 2192) D92.
  zld F_828f0 D_828f0 (S - 2200) D00. zld F_828f4 D_828f4 (S - 2208) D08.
  zstep F_828f8 D_828f8.
  stepjr F_828fc D_828fc (0x7a33c : bv 64)%bv ltac:(gres; bveq).

  zstep F_7a2ec D_7a2ec. zstep F_7a2f0 D_7a2f0. zstep F_7a2f4 D_7a2f4. zstep F_7a2f8 D_7a2f8.
  stepn F_7a2fc D_7a2fc.
  zstep F_52a40 D_52a40. zstep F_52a44 D_52a44. zstep F_52a48 D_52a48. zstep F_52a4c D_52a4c. zstep F_52a50 D_52a50. zstep F_52a54 D_52a54.
  zstep F_52a58 D_52a58. zstep F_52a5c D_52a5c. zstep F_52a60 D_52a60.
  stepn F_52a64 D_52a64.

  zstep F_52a68 D_52a68.
  zsd F_52a6c D_52a6c (S - 2136) (U (0x7a350 : bv 64)%bv) ltac:(rewok W). zsd F_52a70 D_52a70 (S - 2144) S ltac:(rewok W). zsd F_52a74 D_52a74 (S - 2152) p ltac:(rewok W).
  zsd F_52a78 D_52a78 (S - 2160) (U (0x7a2e0 : bv 64)%bv) ltac:(rewok W). zsd F_52a7c D_52a7c (S - 2168) 1 ltac:(rewok W). zsd F_52a80 D_52a80 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_52a84 D_52a84 (S - 2184) (S - 81) ltac:(rewok W). zsd F_52a88 D_52a88 (S - 2192) f22 ltac:(rewok W).
  zbft F_52a8c D_52a8c.
  zstep F_52a90 D_52a90. zstep F_52a94 D_52a94. zstep F_52a98 D_52a98. zstep F_52a9c D_52a9c. zstep F_52aa0 D_52aa0. zstep F_52aa4 D_52aa4. zstep F_52aa8 D_52aa8. zstep F_52aac D_52aac.
  stepn F_52ab0 D_52ab0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cfh' : cellA X 0x1d34c8 8 0) by (unfold hid in Timg; zcell) end.
  zcall (art_run_free_hooks_fn _ _ _ _ (S - 2192)).
  zbtk F_52ab4 D_52ab4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chw' : cellA X (p - 16) 4 (2 + 256 * b1)) by zcell; assert (Wp' : wrA X (p - 16) 24) by zwr end.
  assert (Hm16 : (p - 16) mod 16 = 0) by (replace (p - 16) with (p + (-1) * 16) by lia; rewrite Z_mod_plus_full; exact Hp16).
  zcall (art_cas23W_fn _ _ _ (p - 16) b1).
  zstep F_52b30 D_52b30. zstep F_52b34 D_52b34.
  zsd F_52b38 D_52b38 (p - 16 + 16) (2 ^ 64 - 2 ^ 32) ltac:(rewok Wp).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (Cst & Cb1 & Chi) end.
  replace ((3 + 256 * b1) mod 256) with 3 in Cst by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity).
  rewrite (art_hdrw_tb 3 b1) in Cb1 by lia.
  rewrite (art_hdrw_hi 3 b1) in Chi by lia.
  zlbu F_52b3c D_52b3c (p - 16 + 1) Cb1.
  stepn F_52b40 D_52b40. rwH. rewrite art_zb_andi by lia. replace (Z.land (b1 mod 256) 3) with 1 by (rewrite art_land3_mod256 by lia; symmetry; exact Hb14).
  zbft F_52b44 D_52b44.
  stepn F_52b48 D_52b48. rwH. unfold v_andi. rewrite art_u_lit by lia. change (Z_to_bv 64 (Z.land 1 (bv_wrap 64 (-2)))) with (Z_to_bv 64 0 : word).
  zstep F_52b4c D_52b4c.
  zbtk F_52b50 D_52b50.
  stepn F_52c9c D_52c9c.
  zcall (art_thread_stats_fn _ _ _ _ (S - 2192) tp key tsd ctx t).
  { unfold art_tsd. repeat split; try lia; zcell. }
  all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi');
    rewrite (art_hdrw_hi 3 b1) in Chi' by lia; replace (p - 16 + 2) with (p - 14) in Chi' by lia;
    assert (Cn' : cellA X (p - 12) 4 (n mod 2 ^ 32)) by (apply cell4_mod; zcell);
    assert (Cfr1' : cellA X (t + 2800 + 24) 8 fr1) by (replace (t + 2800 + 24) with (t + 2824) by lia; zcell);
    assert (Cfr2' : cellA X (t + 2800 + 32) 8 fr2) by (replace (t + 2800 + 32) with (t + 2832) by lia; zcell) end.
  zlhu F_52ca0 D_52ca0 (p - 14) Chi'.
  zlwu F_52ca4 D_52ca4 (p - 12) Cn'.
  zld F_52ca8 D_52ca8 (t + 2800 + 32) Cfr2'. zld F_52cac D_52cac (t + 2800 + 24) Cfr1'.
  zstep F_52cb0 D_52cb0.
  stepn F_52cb4 D_52cb4. rwH. rewrite art_fx_zb_or by lia. rewrite (art_or_b1lo b1 n) by lia.
  zstep F_52cb8 D_52cb8. zstep F_52cbc D_52cbc.
  zsd F_52cc0 D_52cc0 (t + 2800 + 24) (fr1 + 1) ltac:(rewok Wt).
  zsd F_52cc4 D_52cc4 (t + 2800 + 32) (n + fr2) ltac:(rewok Wt).
  zstep F_52cc8 D_52cc8. zstep F_52ccc D_52ccc. zstep F_52cd0 D_52cd0. zstep F_52cd4 D_52cd4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x7a350 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell;
    assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell end.
  zld F_52cd8 D_52cd8 (S - 2136) E36. zld F_52cdc D_52cdc (S - 2144) E44. zld F_52ce0 D_52ce0 (S - 2152) E52. zld F_52ce4 D_52ce4 (S - 2160) E60.
  zld F_52ce8 D_52ce8 (S - 2168) E68. zld F_52cec D_52cec (S - 2176) E76. zld F_52cf0 D_52cf0 (S - 2184) E84. zld F_52cf4 D_52cf4 (S - 2192) E92.
  zstep F_52cf8 D_52cf8.
  stepn F_52cfc D_52cfc.

  zstep F_56fc8 D_56fc8.
  zsd F_56fcc D_56fcc (S - 2136) (U (0x7a350 : bv 64)%bv) ltac:(rewok W). zsd F_56fd0 D_56fd0 (S - 2144) S ltac:(rewok W). zsd F_56fd4 D_56fd4 (S - 2152) p ltac:(rewok W).
  zsd F_56fd8 D_56fd8 (S - 2160) (U (0x7a2e0 : bv 64)%bv) ltac:(rewok W). zsd F_56fdc D_56fdc (S - 2168) 1 ltac:(rewok W). zsd F_56fe0 D_56fe0 (S - 2176) (S - 2128) ltac:(rewok W).
  zstep F_56fe4 D_56fe4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw3 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw3) as (Cst' & _ & _);
    replace ((3 + 256 * b1) mod 256) with 3 in Cst' by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity) end.
  zlb F_56fe8 D_56fe8 (p - 16) Cst'.
  zstep F_56fec D_56fec.
  zbft F_56ff0 D_56ff0.
  zstep F_56ff4 D_56ff4. zstep F_56ff8 D_56ff8.
  stepn F_56ffc D_56ffc.
  zcall (art_cur_thread_fn _ _ _ _ (S - 2176) tp key tsd ctx t).
  { unfold art_tsd. repeat split; try lia; zcell. }
  all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
  zbft F_57000 D_57000.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ctctx' : cellA X t 8 ctx) by zcell;
    assert (C28' : cellA X (S - 2128) 8 (S - 2112)) by zcell;
    assert (C20' : cellA X (S - 2128 + 8) 8 sz) by (replace (S - 2128 + 8) with (S - 2120) by lia; zcell);
    assert (Ctid' : cellA X (ctx + 8) 4 0) by zcell end.
  zld F_57004 D_57004 t Ctctx'. zld F_57008 D_57008 (S - 2128) C28'. zld F_5700c D_5700c (S - 2128 + 8) C20'.
  zlw F_57010 D_57010 (ctx + 8) Ctid'.
  zstep F_57014 D_57014. zstep F_57018 D_57018.
  stepn F_5701c D_5701c.
  unfold art_fx_fcu2_mem. zret.
Qed.

#[using="Type"] Lemma art_fx_fcu2_fn : forall regs (M rom : word -> option byte) (S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> getr regs 4 = Z_to_bv 64 tp ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x698000 + 16 <= p -> p + 8 < 2 ^ 47 -> p mod 16 = 0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 -> 1 <= n < 2 ^ 32 -> 1 <= sz <= 30 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> apart (p - 16) 24 (S - 4096) 8192 -> apart (p - 16) 24 t 4096 ->
  apart ctx 4096 (S - 4096) 8192 -> apart t 4096 ctx 4096 -> apart (p - 16) 24 ctx 4096 -> hid (ctx + 4096 <= 0x10000 \/ 0x698000 <= ctx) -> hid (t + 4096 <= 0x10000 \/ 0x698000 <= t) ->
  0x10100 <= tp -> tp + 8 <= 0x698000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x698000 ->
  0 <= fr1 < 2 ^ 64 -> 0 <= fr2 < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> wrA M (p - 16) 24 -> art_tsd M tp key tsd ctx t ->
  cellA M (S - 2136) 8 0x7a33c -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 2128) 8 (S - 2112) -> cellA M (S - 2120) 8 sz ->
  cellA M (p - 16) 4 (2 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M 0x1d34c8 8 0 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M (t + 2824) 8 fr1 -> cellA M (t + 2832) 8 fr2 ->
  msteps ASEGS (mkst regs (0x8291c : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x57070 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (p - 16))) 9 (Z_to_bv 64 (S - 2128))) 10 (Z_to_bv 64 (S - 2112))) 11 (Z_to_bv 64 sz)) 12 (Z_to_bv 64 (S - 2112))) 13 (Z_to_bv 64 ctx)) 14 (Z_to_bv 64 (fr1 + 1))) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 1303448)) 19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 t)) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x9a948 : word) (art_fx_fcu2_mem M S p b1 n sz t fr1 fr2 f22 f23 f24) rom).
Proof.
  intros regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 Hb1 Hb14 Hn.
  apply (art_fx_fcu2W_fn regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 ltac:(lia) Hb14 ltac:(lia)).
  rewrite (Z.div_small b1), (Z.div_small n) by lia. reflexivity.
Qed.
End FPX.
