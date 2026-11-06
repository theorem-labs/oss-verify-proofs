(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import StartupTac Ub_code_2c03b8_2c0b2c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
    msteps SEGS (mkst regs (0x2c0a70 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_2c0a34 D_2c0a34 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0a38 D_2c0a38 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_2c0a3c D_2c0a3c (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_2c0a40 D_2c0a40.  (* [comment removed for export] *)
    stw F_2c0a44 D_2c0a44 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2c0a48 D_2c0a48 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0a4c D_2c0a4c (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0a50 D_2c0a50 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0a54 D_2c0a54.  (* [comment removed for export] *)
    stw F_2c0a58 D_2c0a58 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0a5c D_2c0a5c (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2c0a60 D_2c0a60 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0a64 D_2c0a64 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0a68 D_2c0a68.  (* [comment removed for export] *)
    stw F_2c0a6c D_2c0a6c (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2c0a70 D_2c0a70 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_2c0a74 D_2c0a74.  (* [comment removed for export] *)
    sn F_2c0a78 D_2c0a78.  (* [comment removed for export] *)
    sn F_2c0a7c D_2c0a7c.  (* [comment removed for export] *)
    stepiv F_2c0a80 D_2c0a80 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_2c0a84 D_2c0a84.  (* [comment removed for export] *)
    sn F_2c0a88 D_2c0a88.  (* [comment removed for export] *)
    sv F_2c0a8c D_2c0a8c (d).  (* [comment removed for export] *)
    sn F_2c0a90 D_2c0a90.  (* [comment removed for export] *)
    sn F_2c0a94 D_2c0a94.  (* [comment removed for export] *)
    sn F_2c0a98 D_2c0a98.  (* [comment removed for export] *)
    stw F_2c0a9c D_2c0a9c (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_2c0aa0 D_2c0aa0 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_2c0aa4 D_2c0aa4 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2c0aa8 D_2c0aa8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0aac D_2c0aac (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0ab0 D_2c0ab0 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0ab4 D_2c0ab4.  (* [comment removed for export] *)
    stw F_2c0ab8 D_2c0ab8 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0abc D_2c0abc (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2c0ac0 D_2c0ac0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0ac4 D_2c0ac4 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0ac8 D_2c0ac8 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0acc D_2c0acc (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0ad0 D_2c0ad0 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepiv F_2c0ad4 D_2c0ad4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_2c0ad8 D_2c0ad8.  (* [comment removed for export] *)
    sn F_2c0adc D_2c0adc.  (* [comment removed for export] *)
    sn F_2c0ae0 D_2c0ae0.  (* [comment removed for export] *)
    stw F_2c0ae4 D_2c0ae4 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0ae8 D_2c0ae8 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0aec D_2c0aec (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0af0 D_2c0af0 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_2c0af4 D_2c0af4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_2c0af8 D_2c0af8.  (* [comment removed for export] *)
    sv F_2c0afc D_2c0afc (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_2c0b00 D_2c0b00.  (* [comment removed for export] *)
    sn F_2c0b04 D_2c0b04.  (* [comment removed for export] *)
    sn F_2c0b08 D_2c0b08.  (* [comment removed for export] *)
    stw F_2c0b0c D_2c0b0c (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b10 D_2c0b10 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b14 D_2c0b14 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b18 D_2c0b18 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0b1c D_2c0b1c.  (* [comment removed for export] *)
    sv F_2c0b20 D_2c0b20 (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_2c0b24 D_2c0b24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0b0c D_2c0b0c (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b10 D_2c0b10 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b14 D_2c0b14 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b18 D_2c0b18 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0b1c D_2c0b1c.  (* [comment removed for export] *)
    sv F_2c0b20 D_2c0b20 (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_2c0b24 D_2c0b24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0b0c D_2c0b0c (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b10 D_2c0b10 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b14 D_2c0b14 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b18 D_2c0b18 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0b1c D_2c0b1c.  (* [comment removed for export] *)
    sv F_2c0b20 D_2c0b20 (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_2c0b24 D_2c0b24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0b0c D_2c0b0c (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b10 D_2c0b10 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b14 D_2c0b14 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b18 D_2c0b18 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0b1c D_2c0b1c.  (* [comment removed for export] *)
    sv F_2c0b20 D_2c0b20 (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_2c0b24 D_2c0b24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0b0c D_2c0b0c (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b10 D_2c0b10 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b14 D_2c0b14 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b18 D_2c0b18 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0b1c D_2c0b1c.  (* [comment removed for export] *)
    sv F_2c0b20 D_2c0b20 (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_2c0b24 D_2c0b24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0b0c D_2c0b0c (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b10 D_2c0b10 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b14 D_2c0b14 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b18 D_2c0b18 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0b1c D_2c0b1c.  (* [comment removed for export] *)
    sv F_2c0b20 D_2c0b20 (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_2c0b24 D_2c0b24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0b0c D_2c0b0c (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b10 D_2c0b10 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b14 D_2c0b14 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b18 D_2c0b18 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0b1c D_2c0b1c.  (* [comment removed for export] *)
    sv F_2c0b20 D_2c0b20 (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_2c0b24 D_2c0b24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_2c0b0c D_2c0b0c (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b10 D_2c0b10 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b14 D_2c0b14 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_2c0b18 D_2c0b18 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_2c0b1c D_2c0b1c.  (* [comment removed for export] *)
    sv F_2c0b20 D_2c0b20 (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_2c0b24 D_2c0b24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_2c0b28 D_2c0b28 ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
