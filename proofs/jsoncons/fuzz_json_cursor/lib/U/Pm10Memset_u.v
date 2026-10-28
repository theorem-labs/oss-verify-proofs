(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import StartupTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10_code_b5000_b6000_u Pm10_code_b6000_b7000_u .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.

Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vmc_refl. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vmc_refl. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0xb7e14 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  -
    stepb_ft F_b5f84 D_b5f84 ltac:(pin; cond_compute).
    stw F_b5f88 D_b5f88 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_b5f8c D_b5f8c (Z_to_bv 64 (bv_unsigned d + 304)).
    sn F_b5f90 D_b5f90.
    stw F_b5f94 D_b5f94 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b5f98 D_b5f98 ltac:(pin; cond_compute).
    stw F_b5f9c D_b5f9c (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b5fa0 D_b5fa0 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b5fa4 D_b5fa4.
    stw F_b5fa8 D_b5fa8 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b5fac D_b5fac (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b5fb0 D_b5fb0 ltac:(pin; cond_compute).
    stw F_b5fb4 D_b5fb4 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b5fb8 D_b5fb8.
    stw F_b5fbc D_b5fbc (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b5fc0 D_b5fc0 ltac:(pin; cond_compute).
    sn F_b5fc4 D_b5fc4.
    sn F_b5fc8 D_b5fc8.
    sn F_b5fcc D_b5fcc.
    stepiv F_b5fd0 D_b5fd0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_b5fd4 D_b5fd4.
    sn F_b5fd8 D_b5fd8.
    sv F_b5fdc D_b5fdc (d).
    sn F_b5fe0 D_b5fe0.
    sn F_b5fe4 D_b5fe4.
    sn F_b5fe8 D_b5fe8.
    stw F_b5fec D_b5fec (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_b5ff0 D_b5ff0 (Z_to_bv 64 (bv_unsigned d + 304)).
    stw F_b5ff4 D_b5ff4 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b5ff8 D_b5ff8 ltac:(pin; cond_compute).
    stw F_b5ffc D_b5ffc (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6000 D_b6000 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b6004 D_b6004.
    stw F_b6008 D_b6008 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b600c D_b600c (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b6010 D_b6010 ltac:(pin; cond_compute).
    stw F_b6014 D_b6014 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6018 D_b6018 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b601c D_b601c (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6020 D_b6020 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_b6024 D_b6024 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_b6028 D_b6028.
    sn F_b602c D_b602c.
    sn F_b6030 D_b6030.
    stw F_b6034 D_b6034 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6038 D_b6038 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b603c D_b603c (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6040 D_b6040 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b6044 D_b6044 ltac:(pin; cond_compute).
    sn F_b6048 D_b6048.
    sv F_b604c D_b604c (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_b6050 D_b6050.
    sn F_b6054 D_b6054.
    sn F_b6058 D_b6058.
    stw F_b605c D_b605c (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6060 D_b6060 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6064 D_b6064 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6068 D_b6068 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b606c D_b606c.
    sv F_b6070 D_b6070 (Z_to_bv 64 (bv_unsigned d + 56)).
    stepb_tk F_b6074 D_b6074 ltac:(pin; cond_compute).
    stw F_b605c D_b605c (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6060 D_b6060 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6064 D_b6064 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6068 D_b6068 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b606c D_b606c.
    sv F_b6070 D_b6070 (Z_to_bv 64 (bv_unsigned d + 88)).
    stepb_tk F_b6074 D_b6074 ltac:(pin; cond_compute).
    stw F_b605c D_b605c (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6060 D_b6060 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6064 D_b6064 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6068 D_b6068 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b606c D_b606c.
    sv F_b6070 D_b6070 (Z_to_bv 64 (bv_unsigned d + 120)).
    stepb_tk F_b6074 D_b6074 ltac:(pin; cond_compute).
    stw F_b605c D_b605c (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6060 D_b6060 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6064 D_b6064 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6068 D_b6068 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b606c D_b606c.
    sv F_b6070 D_b6070 (Z_to_bv 64 (bv_unsigned d + 152)).
    stepb_tk F_b6074 D_b6074 ltac:(pin; cond_compute).
    stw F_b605c D_b605c (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6060 D_b6060 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6064 D_b6064 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6068 D_b6068 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b606c D_b606c.
    sv F_b6070 D_b6070 (Z_to_bv 64 (bv_unsigned d + 184)).
    stepb_tk F_b6074 D_b6074 ltac:(pin; cond_compute).
    stw F_b605c D_b605c (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6060 D_b6060 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6064 D_b6064 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6068 D_b6068 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b606c D_b606c.
    sv F_b6070 D_b6070 (Z_to_bv 64 (bv_unsigned d + 216)).
    stepb_tk F_b6074 D_b6074 ltac:(pin; cond_compute).
    stw F_b605c D_b605c (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6060 D_b6060 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6064 D_b6064 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6068 D_b6068 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b606c D_b606c.
    sv F_b6070 D_b6070 (Z_to_bv 64 (bv_unsigned d + 248)).
    stepb_tk F_b6074 D_b6074 ltac:(pin; cond_compute).
    stw F_b605c D_b605c (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6060 D_b6060 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6064 D_b6064 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b6068 D_b6068 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b606c D_b606c.
    sv F_b6070 D_b6070 (Z_to_bv 64 (bv_unsigned d + 280)).
    stepb_ft F_b6074 D_b6074 ltac:(pin; cond_compute).
    stepret F_b6078 D_b6078 ret ltac:(pin; reflexivity).
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
