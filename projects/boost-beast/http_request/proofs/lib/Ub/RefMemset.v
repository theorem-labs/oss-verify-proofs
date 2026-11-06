(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import StartupTac Ub_code_79454_79c00.
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
    msteps SEGS (mkst regs (0x79ad0 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_79ad0 D_79ad0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ad4 D_79ad4 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_79ad8 D_79ad8 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_79adc D_79adc.  (* [comment removed for export] *)
    stw F_79ae0 D_79ae0 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_79ae4 D_79ae4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ae8 D_79ae8 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79aec D_79aec (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79af0 D_79af0.  (* [comment removed for export] *)
    stw F_79af4 D_79af4 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79af8 D_79af8 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_79afc D_79afc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79b00 D_79b00 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79b04 D_79b04.  (* [comment removed for export] *)
    stw F_79b08 D_79b08 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_79b0c D_79b0c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_79b10 D_79b10.  (* [comment removed for export] *)
    sn F_79b14 D_79b14.  (* [comment removed for export] *)
    sn F_79b18 D_79b18.  (* [comment removed for export] *)
    stepiv F_79b1c D_79b1c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_79b20 D_79b20.  (* [comment removed for export] *)
    sn F_79b24 D_79b24.  (* [comment removed for export] *)
    sv F_79b28 D_79b28 (d).  (* [comment removed for export] *)
    sn F_79b2c D_79b2c.  (* [comment removed for export] *)
    sn F_79b30 D_79b30.  (* [comment removed for export] *)
    sn F_79b34 D_79b34.  (* [comment removed for export] *)
    stw F_79b38 D_79b38 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_79b3c D_79b3c (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_79b40 D_79b40 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_79b44 D_79b44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79b48 D_79b48 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79b4c D_79b4c (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79b50 D_79b50.  (* [comment removed for export] *)
    stw F_79b54 D_79b54 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79b58 D_79b58 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_79b5c D_79b5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79b60 D_79b60 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79b64 D_79b64 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79b68 D_79b68 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79b6c D_79b6c (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepiv F_79b70 D_79b70 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_79b74 D_79b74.  (* [comment removed for export] *)
    sn F_79b78 D_79b78.  (* [comment removed for export] *)
    sn F_79b7c D_79b7c.  (* [comment removed for export] *)
    stw F_79b80 D_79b80 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79b84 D_79b84 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79b88 D_79b88 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79b8c D_79b8c (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_79b90 D_79b90 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_79b94 D_79b94.  (* [comment removed for export] *)
    sv F_79b98 D_79b98 (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_79b9c D_79b9c.  (* [comment removed for export] *)
    sn F_79ba0 D_79ba0.  (* [comment removed for export] *)
    sn F_79ba4 D_79ba4.  (* [comment removed for export] *)
    stw F_79ba8 D_79ba8 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bac D_79bac (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb0 D_79bb0 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb4 D_79bb4 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79bb8 D_79bb8.  (* [comment removed for export] *)
    sv F_79bbc D_79bbc (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_79bc0 D_79bc0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ba8 D_79ba8 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bac D_79bac (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb0 D_79bb0 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb4 D_79bb4 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79bb8 D_79bb8.  (* [comment removed for export] *)
    sv F_79bbc D_79bbc (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_79bc0 D_79bc0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ba8 D_79ba8 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bac D_79bac (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb0 D_79bb0 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb4 D_79bb4 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79bb8 D_79bb8.  (* [comment removed for export] *)
    sv F_79bbc D_79bbc (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_79bc0 D_79bc0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ba8 D_79ba8 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bac D_79bac (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb0 D_79bb0 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb4 D_79bb4 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79bb8 D_79bb8.  (* [comment removed for export] *)
    sv F_79bbc D_79bbc (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_79bc0 D_79bc0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ba8 D_79ba8 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bac D_79bac (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb0 D_79bb0 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb4 D_79bb4 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79bb8 D_79bb8.  (* [comment removed for export] *)
    sv F_79bbc D_79bbc (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_79bc0 D_79bc0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ba8 D_79ba8 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bac D_79bac (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb0 D_79bb0 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb4 D_79bb4 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79bb8 D_79bb8.  (* [comment removed for export] *)
    sv F_79bbc D_79bbc (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_79bc0 D_79bc0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ba8 D_79ba8 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bac D_79bac (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb0 D_79bb0 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb4 D_79bb4 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79bb8 D_79bb8.  (* [comment removed for export] *)
    sv F_79bbc D_79bbc (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_79bc0 D_79bc0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_79ba8 D_79ba8 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bac D_79bac (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb0 D_79bb0 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_79bb4 D_79bb4 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_79bb8 D_79bb8.  (* [comment removed for export] *)
    sv F_79bbc D_79bbc (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_79bc0 D_79bc0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_79bc4 D_79bc4 ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
