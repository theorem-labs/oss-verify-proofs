(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1BootCode U1BootDefs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Img.
  Variable SEGS : list Segment.
  Hypothesis HX : u1b_ok SEGS = true.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0xe311c : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  -
    stepb_ft (F_e30e8 _ HX) D_e30e8 ltac:(pin; cond_compute).
    stw (F_e30ec _ HX) D_e30ec (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv (F_e30f0 _ HX) D_e30f0 (Z_to_bv 64 (bv_unsigned d + 304)).
    sn (F_e30f4 _ HX) D_e30f4.
    stw (F_e30f8 _ HX) D_e30f8 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft (F_e30fc _ HX) D_e30fc ltac:(pin; cond_compute).
    stw (F_e3100 _ HX) D_e3100 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e3104 _ HX) D_e3104 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e3108 _ HX) D_e3108.
    stw (F_e310c _ HX) D_e310c (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e3110 _ HX) D_e3110 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft (F_e3114 _ HX) D_e3114 ltac:(pin; cond_compute).
    stw (F_e3118 _ HX) D_e3118 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e311c _ HX) D_e311c.
    stw (F_e3120 _ HX) D_e3120 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft (F_e3124 _ HX) D_e3124 ltac:(pin; cond_compute).
    sn (F_e3128 _ HX) D_e3128.
    sn (F_e312c _ HX) D_e312c.
    sn (F_e3130 _ HX) D_e3130.
    stepiv (F_e3134 _ HX) D_e3134 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn (F_e3138 _ HX) D_e3138.
    sn (F_e313c _ HX) D_e313c.
    sv (F_e3140 _ HX) D_e3140 (d).
    sn (F_e3144 _ HX) D_e3144.
    sn (F_e3148 _ HX) D_e3148.
    sn (F_e314c _ HX) D_e314c.
    stw (F_e3150 _ HX) D_e3150 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv (F_e3154 _ HX) D_e3154 (Z_to_bv 64 (bv_unsigned d + 304)).
    stw (F_e3158 _ HX) D_e3158 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft (F_e315c _ HX) D_e315c ltac:(pin; cond_compute).
    stw (F_e3160 _ HX) D_e3160 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e3164 _ HX) D_e3164 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e3168 _ HX) D_e3168.
    stw (F_e316c _ HX) D_e316c (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e3170 _ HX) D_e3170 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft (F_e3174 _ HX) D_e3174 ltac:(pin; cond_compute).
    stw (F_e3178 _ HX) D_e3178 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e317c _ HX) D_e317c (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e3180 _ HX) D_e3180 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e3184 _ HX) D_e3184 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv (F_e3188 _ HX) D_e3188 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn (F_e318c _ HX) D_e318c.
    sn (F_e3190 _ HX) D_e3190.
    sn (F_e3194 _ HX) D_e3194.
    stw (F_e3198 _ HX) D_e3198 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e319c _ HX) D_e319c (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31a0 _ HX) D_e31a0 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31a4 _ HX) D_e31a4 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft (F_e31a8 _ HX) D_e31a8 ltac:(pin; cond_compute).
    sn (F_e31ac _ HX) D_e31ac.
    sv (F_e31b0 _ HX) D_e31b0 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn (F_e31b4 _ HX) D_e31b4.
    sn (F_e31b8 _ HX) D_e31b8.
    sn (F_e31bc _ HX) D_e31bc.
    stw (F_e31c0 _ HX) D_e31c0 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c4 _ HX) D_e31c4 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c8 _ HX) D_e31c8 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31cc _ HX) D_e31cc (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e31d0 _ HX) D_e31d0.
    sv (F_e31d4 _ HX) D_e31d4 (Z_to_bv 64 (bv_unsigned d + 56)).
    stepb_tk (F_e31d8 _ HX) D_e31d8 ltac:(pin; cond_compute).
    stw (F_e31c0 _ HX) D_e31c0 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c4 _ HX) D_e31c4 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c8 _ HX) D_e31c8 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31cc _ HX) D_e31cc (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e31d0 _ HX) D_e31d0.
    sv (F_e31d4 _ HX) D_e31d4 (Z_to_bv 64 (bv_unsigned d + 88)).
    stepb_tk (F_e31d8 _ HX) D_e31d8 ltac:(pin; cond_compute).
    stw (F_e31c0 _ HX) D_e31c0 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c4 _ HX) D_e31c4 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c8 _ HX) D_e31c8 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31cc _ HX) D_e31cc (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e31d0 _ HX) D_e31d0.
    sv (F_e31d4 _ HX) D_e31d4 (Z_to_bv 64 (bv_unsigned d + 120)).
    stepb_tk (F_e31d8 _ HX) D_e31d8 ltac:(pin; cond_compute).
    stw (F_e31c0 _ HX) D_e31c0 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c4 _ HX) D_e31c4 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c8 _ HX) D_e31c8 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31cc _ HX) D_e31cc (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e31d0 _ HX) D_e31d0.
    sv (F_e31d4 _ HX) D_e31d4 (Z_to_bv 64 (bv_unsigned d + 152)).
    stepb_tk (F_e31d8 _ HX) D_e31d8 ltac:(pin; cond_compute).
    stw (F_e31c0 _ HX) D_e31c0 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c4 _ HX) D_e31c4 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c8 _ HX) D_e31c8 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31cc _ HX) D_e31cc (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e31d0 _ HX) D_e31d0.
    sv (F_e31d4 _ HX) D_e31d4 (Z_to_bv 64 (bv_unsigned d + 184)).
    stepb_tk (F_e31d8 _ HX) D_e31d8 ltac:(pin; cond_compute).
    stw (F_e31c0 _ HX) D_e31c0 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c4 _ HX) D_e31c4 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c8 _ HX) D_e31c8 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31cc _ HX) D_e31cc (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e31d0 _ HX) D_e31d0.
    sv (F_e31d4 _ HX) D_e31d4 (Z_to_bv 64 (bv_unsigned d + 216)).
    stepb_tk (F_e31d8 _ HX) D_e31d8 ltac:(pin; cond_compute).
    stw (F_e31c0 _ HX) D_e31c0 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c4 _ HX) D_e31c4 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c8 _ HX) D_e31c8 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31cc _ HX) D_e31cc (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e31d0 _ HX) D_e31d0.
    sv (F_e31d4 _ HX) D_e31d4 (Z_to_bv 64 (bv_unsigned d + 248)).
    stepb_tk (F_e31d8 _ HX) D_e31d8 ltac:(pin; cond_compute).
    stw (F_e31c0 _ HX) D_e31c0 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c4 _ HX) D_e31c4 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31c8 _ HX) D_e31c8 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw (F_e31cc _ HX) D_e31cc (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn (F_e31d0 _ HX) D_e31d0.
    sv (F_e31d4 _ HX) D_e31d4 (Z_to_bv 64 (bv_unsigned d + 280)).
    stepb_ft (F_e31d8 _ HX) D_e31d8 ltac:(pin; cond_compute).
    stepret (F_e31dc _ HX) D_e31dc ret ltac:(pin; reflexivity).
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

End Img.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
