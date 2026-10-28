(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import StartupTac HU_code_276000_277000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
    msteps SEGS (mkst regs (0x2bc5a4 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_2769b8 D_2769b8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2769bc D_2769bc (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_2769c0 D_2769c0 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_2769c4 D_2769c4.  (* [comment removed for export] *)
    stw F_2769c8 D_2769c8 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2769cc D_2769cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2769d0 D_2769d0 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2769d4 D_2769d4 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2769d8 D_2769d8.  (* [comment removed for export] *)
    stw F_2769dc D_2769dc (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2769e0 D_2769e0 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2769e4 D_2769e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2769e8 D_2769e8 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2769ec D_2769ec.  (* [comment removed for export] *)
    stw F_2769f0 D_2769f0 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2769f4 D_2769f4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_2769f8 D_2769f8.  (* [comment removed for export] *)
    sn F_2769fc D_2769fc.  (* [comment removed for export] *)
    sn F_276a00 D_276a00.  (* [comment removed for export] *)
    stepiv F_276a04 D_276a04 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_276a08 D_276a08.  (* [comment removed for export] *)
    sn F_276a0c D_276a0c.  (* [comment removed for export] *)
    sv F_276a10 D_276a10 (d).  (* [comment removed for export] *)
    sn F_276a14 D_276a14.  (* [comment removed for export] *)
    sn F_276a18 D_276a18.  (* [comment removed for export] *)
    sn F_276a1c D_276a1c.  (* [comment removed for export] *)
    stw F_276a20 D_276a20 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_276a24 D_276a24 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_276a28 D_276a28 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_276a2c D_276a2c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a30 D_276a30 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a34 D_276a34 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276a38 D_276a38.  (* [comment removed for export] *)
    stw F_276a3c D_276a3c (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a40 D_276a40 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_276a44 D_276a44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a48 D_276a48 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a4c D_276a4c (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a50 D_276a50 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a54 D_276a54 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepiv F_276a58 D_276a58 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_276a5c D_276a5c.  (* [comment removed for export] *)
    sn F_276a60 D_276a60.  (* [comment removed for export] *)
    sn F_276a64 D_276a64.  (* [comment removed for export] *)
    stw F_276a68 D_276a68 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a6c D_276a6c (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a70 D_276a70 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a74 D_276a74 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_276a78 D_276a78 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_276a7c D_276a7c.  (* [comment removed for export] *)
    sv F_276a80 D_276a80 (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_276a84 D_276a84.  (* [comment removed for export] *)
    sn F_276a88 D_276a88.  (* [comment removed for export] *)
    sn F_276a8c D_276a8c.  (* [comment removed for export] *)
    stw F_276a90 D_276a90 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a94 D_276a94 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a98 D_276a98 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a9c D_276a9c (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276aa0 D_276aa0.  (* [comment removed for export] *)
    sv F_276aa4 D_276aa4 (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_276aa8 D_276aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a90 D_276a90 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a94 D_276a94 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a98 D_276a98 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a9c D_276a9c (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276aa0 D_276aa0.  (* [comment removed for export] *)
    sv F_276aa4 D_276aa4 (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_276aa8 D_276aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a90 D_276a90 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a94 D_276a94 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a98 D_276a98 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a9c D_276a9c (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276aa0 D_276aa0.  (* [comment removed for export] *)
    sv F_276aa4 D_276aa4 (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_276aa8 D_276aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a90 D_276a90 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a94 D_276a94 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a98 D_276a98 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a9c D_276a9c (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276aa0 D_276aa0.  (* [comment removed for export] *)
    sv F_276aa4 D_276aa4 (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_276aa8 D_276aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a90 D_276a90 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a94 D_276a94 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a98 D_276a98 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a9c D_276a9c (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276aa0 D_276aa0.  (* [comment removed for export] *)
    sv F_276aa4 D_276aa4 (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_276aa8 D_276aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a90 D_276a90 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a94 D_276a94 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a98 D_276a98 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a9c D_276a9c (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276aa0 D_276aa0.  (* [comment removed for export] *)
    sv F_276aa4 D_276aa4 (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_276aa8 D_276aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a90 D_276a90 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a94 D_276a94 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a98 D_276a98 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a9c D_276a9c (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276aa0 D_276aa0.  (* [comment removed for export] *)
    sv F_276aa4 D_276aa4 (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_276aa8 D_276aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_276a90 D_276a90 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a94 D_276a94 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a98 D_276a98 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_276a9c D_276a9c (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_276aa0 D_276aa0.  (* [comment removed for export] *)
    sv F_276aa4 D_276aa4 (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_276aa8 D_276aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_276aac D_276aac ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
