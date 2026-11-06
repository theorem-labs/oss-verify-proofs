(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_1c000_1d000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := rl_segs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memset232_ws : list (Z * nat) := [(0,1%nat); (231,1%nat); (1,1%nat); (2,1%nat); (229,1%nat); (230,1%nat); (3,1%nat); (228,1%nat); (0,4%nat); (228,4%nat); (4,4%nat); (8,4%nat); (220,4%nat); (224,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (204,4%nat); (208,4%nat); (212,4%nat); (216,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat)]%Z.

Section VP1. Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.   (* [comment removed for export] *)
Lemma memset232_ws_inb : ws_inb memset232_ws 232 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset232_ws_cover : ws_cover memset232_ws 232 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset232_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

Lemma memset232_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 232 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 232 < 2^64)%Z ->
  store_ok SEGS mem d 232 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdb8) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 232)
    /\ regs_agree (fun r => In r memset232_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  -
    stepb_ft F_1cdb8 D_1cdb8 ltac:(pin; cond_compute).
    stw F_1cdbc D_1cdbc (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_1cdc0 D_1cdc0 (Z_to_bv 64 (bv_unsigned d + 232)).
    sn F_1cdc4 D_1cdc4.
    stw F_1cdc8 D_1cdc8 (Z_to_bv 64 (bv_unsigned d + 231)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1cdcc D_1cdcc ltac:(pin; cond_compute).
    stw F_1cdd0 D_1cdd0 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1cdd4 D_1cdd4 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1cdd8 D_1cdd8.
    stw F_1cddc D_1cddc (Z_to_bv 64 (bv_unsigned d + 229)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1cde0 D_1cde0 (Z_to_bv 64 (bv_unsigned d + 230)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1cde4 D_1cde4 ltac:(pin; cond_compute).
    stw F_1cde8 D_1cde8 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1cdec D_1cdec.
    stw F_1cdf0 D_1cdf0 (Z_to_bv 64 (bv_unsigned d + 228)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1cdf4 D_1cdf4 ltac:(pin; cond_compute).
    sn F_1cdf8 D_1cdf8.
    sn F_1cdfc D_1cdfc.
    sn F_1ce00 D_1ce00.
    stepiv F_1ce04 D_1ce04 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_1ce08 D_1ce08.
    sn F_1ce0c D_1ce0c.
    sv F_1ce10 D_1ce10 (d).
    sn F_1ce14 D_1ce14.
    sn F_1ce18 D_1ce18.
    sn F_1ce1c D_1ce1c.
    stw F_1ce20 D_1ce20 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_1ce24 D_1ce24 (Z_to_bv 64 (bv_unsigned d + 232)).
    stw F_1ce28 D_1ce28 (Z_to_bv 64 (bv_unsigned d + 228)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1ce2c D_1ce2c ltac:(pin; cond_compute).
    stw F_1ce30 D_1ce30 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce34 D_1ce34 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1ce38 D_1ce38.
    stw F_1ce3c D_1ce3c (Z_to_bv 64 (bv_unsigned d + 220)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce40 D_1ce40 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1ce44 D_1ce44 ltac:(pin; cond_compute).
    stw F_1ce48 D_1ce48 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce4c D_1ce4c (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce50 D_1ce50 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce54 D_1ce54 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_1ce58 D_1ce58 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_1ce5c D_1ce5c.
    sn F_1ce60 D_1ce60.
    sn F_1ce64 D_1ce64.
    stw F_1ce68 D_1ce68 (Z_to_bv 64 (bv_unsigned d + 204)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce6c D_1ce6c (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce70 D_1ce70 (Z_to_bv 64 (bv_unsigned d + 212)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce74 D_1ce74 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1ce78 D_1ce78 ltac:(pin; cond_compute).
    sn F_1ce7c D_1ce7c.
    sv F_1ce80 D_1ce80 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_1ce84 D_1ce84.
    sn F_1ce88 D_1ce88.
    sn F_1ce8c D_1ce8c.
    stw F_1ce90 D_1ce90 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce94 D_1ce94 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce98 D_1ce98 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce9c D_1ce9c (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1cea0 D_1cea0.
    sv F_1cea4 D_1cea4 (Z_to_bv 64 (bv_unsigned d + 56)).
    stepb_tk F_1cea8 D_1cea8 ltac:(pin; cond_compute).
    stw F_1ce90 D_1ce90 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce94 D_1ce94 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce98 D_1ce98 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce9c D_1ce9c (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1cea0 D_1cea0.
    sv F_1cea4 D_1cea4 (Z_to_bv 64 (bv_unsigned d + 88)).
    stepb_tk F_1cea8 D_1cea8 ltac:(pin; cond_compute).
    stw F_1ce90 D_1ce90 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce94 D_1ce94 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce98 D_1ce98 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce9c D_1ce9c (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1cea0 D_1cea0.
    sv F_1cea4 D_1cea4 (Z_to_bv 64 (bv_unsigned d + 120)).
    stepb_tk F_1cea8 D_1cea8 ltac:(pin; cond_compute).
    stw F_1ce90 D_1ce90 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce94 D_1ce94 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce98 D_1ce98 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce9c D_1ce9c (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1cea0 D_1cea0.
    sv F_1cea4 D_1cea4 (Z_to_bv 64 (bv_unsigned d + 152)).
    stepb_tk F_1cea8 D_1cea8 ltac:(pin; cond_compute).
    stw F_1ce90 D_1ce90 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce94 D_1ce94 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce98 D_1ce98 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce9c D_1ce9c (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1cea0 D_1cea0.
    sv F_1cea4 D_1cea4 (Z_to_bv 64 (bv_unsigned d + 184)).
    stepb_tk F_1cea8 D_1cea8 ltac:(pin; cond_compute).
    stw F_1ce90 D_1ce90 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce94 D_1ce94 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce98 D_1ce98 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1ce9c D_1ce9c (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1cea0 D_1cea0.
    sv F_1cea4 D_1cea4 (Z_to_bv 64 (bv_unsigned d + 216)).
    stepb_ft F_1cea8 D_1cea8 ltac:(pin; cond_compute).
    stepret F_1ceac D_1ceac ret ltac:(pin; reflexivity).
    apply mst_refl.
  - rewrite <- (zstores_cover d 232 Hnw memset232_ws mem 232%nat eq_refl memset232_ws_inb memset232_ws_cover).
    reflexivity.
  - unfold memset232_clob. solve_regs_agree.
Qed.
End VP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
