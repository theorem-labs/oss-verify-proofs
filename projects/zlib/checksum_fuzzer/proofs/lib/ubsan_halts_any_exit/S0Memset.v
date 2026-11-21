(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import StartupTac S0_code_1d000_1d640.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require L10Walk.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_chain_step.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_peel; OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.ZStores.length_zeros; OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StartupTac.unorm; Stdlib.micromega.Lia.lia.

Abbreviation SEGS := Src_zlib_checksum_fuzzer_repro.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

Lemma memset304_run {RCa1 : RunCtx}  : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok (run_segments SEGS rc_inp rc_sp rc_mb) mem d 304 = true ->
  exists regs' mem',
    msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d108 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_1d068 D_1d068 ltac:(pin; cond_compute).
    stw F_1d06c D_1d06c (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_1d070 D_1d070 (Z_to_bv 64 (bv_unsigned d + 304)).
    sn F_1d074 D_1d074.
    stw F_1d078 D_1d078 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d07c D_1d07c ltac:(pin; cond_compute).
    stw F_1d080 D_1d080 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d084 D_1d084 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d088 D_1d088.
    stw F_1d08c D_1d08c (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d090 D_1d090 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d094 D_1d094 ltac:(pin; cond_compute).
    stw F_1d098 D_1d098 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d09c D_1d09c.
    stw F_1d0a0 D_1d0a0 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d0a4 D_1d0a4 ltac:(pin; cond_compute).
    sn F_1d0a8 D_1d0a8.
    sn F_1d0ac D_1d0ac.
    sn F_1d0b0 D_1d0b0.
    stepiv F_1d0b4 D_1d0b4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_1d0b8 D_1d0b8.
    sn F_1d0bc D_1d0bc.
    sv F_1d0c0 D_1d0c0 (d).
    sn F_1d0c4 D_1d0c4.
    sn F_1d0c8 D_1d0c8.
    sn F_1d0cc D_1d0cc.
    stw F_1d0d0 D_1d0d0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_1d0d4 D_1d0d4 (Z_to_bv 64 (bv_unsigned d + 304)).
    stw F_1d0d8 D_1d0d8 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d0dc D_1d0dc ltac:(pin; cond_compute).
    stw F_1d0e0 D_1d0e0 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d0e4 D_1d0e4 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d0e8 D_1d0e8.
    stw F_1d0ec D_1d0ec (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d0f0 D_1d0f0 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d0f4 D_1d0f4 ltac:(pin; cond_compute).
    stw F_1d0f8 D_1d0f8 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d0fc D_1d0fc (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d100 D_1d100 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d104 D_1d104 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_1d108 D_1d108 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_1d10c D_1d10c.
    sn F_1d110 D_1d110.
    sn F_1d114 D_1d114.
    stw F_1d118 D_1d118 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d11c D_1d11c (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d120 D_1d120 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d124 D_1d124 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d128 D_1d128 ltac:(pin; cond_compute).
    sn F_1d12c D_1d12c.
    sv F_1d130 D_1d130 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_1d134 D_1d134.
    sn F_1d138 D_1d138.
    sn F_1d13c D_1d13c.
    stw F_1d140 D_1d140 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d144 D_1d144 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d148 D_1d148 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d14c D_1d14c (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d150 D_1d150.
    sv F_1d154 D_1d154 (Z_to_bv 64 (bv_unsigned d + 56)).
    stepb_tk F_1d158 D_1d158 ltac:(pin; cond_compute).
    stw F_1d140 D_1d140 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d144 D_1d144 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d148 D_1d148 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d14c D_1d14c (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d150 D_1d150.
    sv F_1d154 D_1d154 (Z_to_bv 64 (bv_unsigned d + 88)).
    stepb_tk F_1d158 D_1d158 ltac:(pin; cond_compute).
    stw F_1d140 D_1d140 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d144 D_1d144 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d148 D_1d148 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d14c D_1d14c (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d150 D_1d150.
    sv F_1d154 D_1d154 (Z_to_bv 64 (bv_unsigned d + 120)).
    stepb_tk F_1d158 D_1d158 ltac:(pin; cond_compute).
    stw F_1d140 D_1d140 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d144 D_1d144 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d148 D_1d148 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d14c D_1d14c (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d150 D_1d150.
    sv F_1d154 D_1d154 (Z_to_bv 64 (bv_unsigned d + 152)).
    stepb_tk F_1d158 D_1d158 ltac:(pin; cond_compute).
    stw F_1d140 D_1d140 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d144 D_1d144 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d148 D_1d148 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d14c D_1d14c (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d150 D_1d150.
    sv F_1d154 D_1d154 (Z_to_bv 64 (bv_unsigned d + 184)).
    stepb_tk F_1d158 D_1d158 ltac:(pin; cond_compute).
    stw F_1d140 D_1d140 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d144 D_1d144 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d148 D_1d148 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d14c D_1d14c (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d150 D_1d150.
    sv F_1d154 D_1d154 (Z_to_bv 64 (bv_unsigned d + 216)).
    stepb_tk F_1d158 D_1d158 ltac:(pin; cond_compute).
    stw F_1d140 D_1d140 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d144 D_1d144 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d148 D_1d148 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d14c D_1d14c (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d150 D_1d150.
    sv F_1d154 D_1d154 (Z_to_bv 64 (bv_unsigned d + 248)).
    stepb_tk F_1d158 D_1d158 ltac:(pin; cond_compute).
    stw F_1d140 D_1d140 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d144 D_1d144 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d148 D_1d148 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d14c D_1d14c (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d150 D_1d150.
    sv F_1d154 D_1d154 (Z_to_bv 64 (bv_unsigned d + 280)).
    stepb_ft F_1d158 D_1d158 ltac:(pin; cond_compute).
    stepret F_1d15c D_1d15c ret ltac:(pin; reflexivity).
    OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_chain_step_kit.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.ZStores.length_zeros; OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StartupTac.unorm; Stdlib.micromega.Lia.lia.
