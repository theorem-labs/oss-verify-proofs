(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import StartupTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6_code_ba000_bb000_u5 .
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.


Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0xbe5c8 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret ra_is_ret ret_fine a0_is_d a1_zero a2_len d_al8 d_fit d_wok.
  pose proof (u64_range d) as d_rng.
  assert (d_al4 : (bv_unsigned d mod 4 = 0)%Z).
  { pose proof (proj1 (Z.mod_divide _ 8 ltac:(discriminate)) d_al8) as [q d_by8].
    apply Z.mod_divide; [discriminate |]. exists (2 * q)%Z. lia. }
  eexists; eexists; refine (conj _ (conj _ _)).
  - (* head: n = 304 skips every short-length exit *)
    stepb_ft F_baba0 D_baba0 ltac:(pin; cond_compute).
    stw F_baba4 D_baba4 (Z_to_bv 64 (bv_unsigned d + 0)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sv F_baba8 D_baba8 (Z_to_bv 64 (bv_unsigned d + 304)%Z).
    sn F_babac D_babac.
    stw F_babb0 D_babb0 (Z_to_bv 64 (bv_unsigned d + 303)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stepb_ft F_babb4 D_babb4 ltac:(pin; cond_compute).
    stw F_babb8 D_babb8 (Z_to_bv 64 (bv_unsigned d + 1)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_babbc D_babbc (Z_to_bv 64 (bv_unsigned d + 2)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_babc0 D_babc0.
    stw F_babc4 D_babc4 (Z_to_bv 64 (bv_unsigned d + 301)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_babc8 D_babc8 (Z_to_bv 64 (bv_unsigned d + 302)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stepb_ft F_babcc D_babcc ltac:(pin; cond_compute).
    stw F_babd0 D_babd0 (Z_to_bv 64 (bv_unsigned d + 3)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_babd4 D_babd4.
    stw F_babd8 D_babd8 (Z_to_bv 64 (bv_unsigned d + 300)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stepb_ft F_babdc D_babdc ltac:(pin; cond_compute).
    (* alignment: d is 8-aligned, so the head adjustment is zero *)
    sn F_babe0 D_babe0.
    sn F_babe4 D_babe4.
    sn F_babe8 D_babe8.
    stepiv F_babec D_babec (Z_to_bv 64 0)
      ltac:(gres; imm_norm; apply negw_and3_aligned; exact d_al4).
    sn F_babf0 D_babf0.
    sv F_babf4 D_babf4 (Z_to_bv 64 304).
    sv F_babf8 D_babf8 d.
    sn F_babfc D_babfc.
    sn F_bac00 D_bac00.
    sn F_bac04 D_bac04.
    stw F_bac08 D_bac08 (Z_to_bv 64 (bv_unsigned d + 0)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sv F_bac0c D_bac0c (Z_to_bv 64 (bv_unsigned d + 304)%Z).
    stw F_bac10 D_bac10 (Z_to_bv 64 (bv_unsigned d + 300)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stepb F_bac14 D_bac14.
    stw F_bac18 D_bac18 (Z_to_bv 64 (bv_unsigned d + 4)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac1c D_bac1c (Z_to_bv 64 (bv_unsigned d + 8)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac20 D_bac20.
    stw F_bac24 D_bac24 (Z_to_bv 64 (bv_unsigned d + 292)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac28 D_bac28 (Z_to_bv 64 (bv_unsigned d + 296)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stepb F_bac2c D_bac2c.
    stw F_bac30 D_bac30 (Z_to_bv 64 (bv_unsigned d + 12)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac34 D_bac34 (Z_to_bv 64 (bv_unsigned d + 16)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac38 D_bac38 (Z_to_bv 64 (bv_unsigned d + 20)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac3c D_bac3c (Z_to_bv 64 (bv_unsigned d + 24)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stepiv F_bac40 D_bac40 (Z_to_bv 64 0)
      ltac:(gres; imm_norm; apply v_andi_4_aligned8; exact d_al8).
    sn F_bac44 D_bac44.
    sn F_bac48 D_bac48.
    sn F_bac4c D_bac4c.
    stw F_bac50 D_bac50 (Z_to_bv 64 (bv_unsigned d + 276)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac54 D_bac54 (Z_to_bv 64 (bv_unsigned d + 280)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac58 D_bac58 (Z_to_bv 64 (bv_unsigned d + 284)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac5c D_bac5c (Z_to_bv 64 (bv_unsigned d + 288)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stepb F_bac60 D_bac60.
    sn F_bac64 D_bac64.
    sv F_bac68 D_bac68 (Z_to_bv 64 (bv_unsigned d + 24)%Z).
    sn F_bac6c D_bac6c.
    sn F_bac70 D_bac70.
    sn F_bac74 D_bac74.
    (* eight laps of the 32-byte body *)
    stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + 24)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + 32)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + 40)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + 48)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac88 D_bac88.
    sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + 56)%Z).
    stepb F_bac90 D_bac90.
    stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + 56)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + 64)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + 72)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + 80)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac88 D_bac88.
    sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + 88)%Z).
    stepb F_bac90 D_bac90.
    stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + 88)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + 96)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + 104)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + 112)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac88 D_bac88.
    sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + 120)%Z).
    stepb F_bac90 D_bac90.
    stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + 120)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + 128)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + 136)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + 144)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac88 D_bac88.
    sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + 152)%Z).
    stepb F_bac90 D_bac90.
    stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + 152)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + 160)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + 168)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + 176)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac88 D_bac88.
    sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + 184)%Z).
    stepb F_bac90 D_bac90.
    stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + 184)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + 192)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + 200)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + 208)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac88 D_bac88.
    sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + 216)%Z).
    stepb F_bac90 D_bac90.
    stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + 216)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + 224)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + 232)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + 240)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac88 D_bac88.
    sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + 248)%Z).
    stepb F_bac90 D_bac90.
    stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + 248)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + 256)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + 264)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + 272)%Z) (Z_to_bv 64 0) ltac:(ok_sub d_wok).
    sn F_bac88 D_bac88.
    sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + 280)%Z).
    stepb F_bac90 D_bac90.
    stepret F_bac94 D_bac94 ret ltac:(exact ra_is_ret).
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 d_fit memset304_ws mem 304 eq_refl
                 memset304_ws_inb memset304_ws_cover).
    unfold memset304_ws; cbn [zstores]. reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
