(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import StartupTac U0_code_1d000_1d8c4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require L10Walk.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_chain_step.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_peel; OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.ZStores.length_zeros; OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StartupTac.unorm; Stdlib.micromega.Lia.lia.

Abbreviation SEGS := Tgt_checksum_fuzzer_ubsan.M.loaded_segments.

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
    msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst regs (0x1d38c : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_1d2ec D_1d2ec ltac:(pin; cond_compute).
    stw F_1d2f0 D_1d2f0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_1d2f4 D_1d2f4 (Z_to_bv 64 (bv_unsigned d + 304)).
    sn F_1d2f8 D_1d2f8.
    stw F_1d2fc D_1d2fc (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d300 D_1d300 ltac:(pin; cond_compute).
    stw F_1d304 D_1d304 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d308 D_1d308 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d30c D_1d30c.
    stw F_1d310 D_1d310 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d314 D_1d314 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d318 D_1d318 ltac:(pin; cond_compute).
    stw F_1d31c D_1d31c (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d320 D_1d320.
    stw F_1d324 D_1d324 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d328 D_1d328 ltac:(pin; cond_compute).
    sn F_1d32c D_1d32c.
    sn F_1d330 D_1d330.
    sn F_1d334 D_1d334.
    stepiv F_1d338 D_1d338 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_1d33c D_1d33c.
    sn F_1d340 D_1d340.
    sv F_1d344 D_1d344 (d).
    sn F_1d348 D_1d348.
    sn F_1d34c D_1d34c.
    sn F_1d350 D_1d350.
    stw F_1d354 D_1d354 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_1d358 D_1d358 (Z_to_bv 64 (bv_unsigned d + 304)).
    stw F_1d35c D_1d35c (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d360 D_1d360 ltac:(pin; cond_compute).
    stw F_1d364 D_1d364 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d368 D_1d368 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d36c D_1d36c.
    stw F_1d370 D_1d370 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d374 D_1d374 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d378 D_1d378 ltac:(pin; cond_compute).
    stw F_1d37c D_1d37c (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d380 D_1d380 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d384 D_1d384 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d388 D_1d388 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_1d38c D_1d38c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_1d390 D_1d390.
    sn F_1d394 D_1d394.
    sn F_1d398 D_1d398.
    stw F_1d39c D_1d39c (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3a0 D_1d3a0 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3a4 D_1d3a4 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3a8 D_1d3a8 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_1d3ac D_1d3ac ltac:(pin; cond_compute).
    sn F_1d3b0 D_1d3b0.
    sv F_1d3b4 D_1d3b4 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_1d3b8 D_1d3b8.
    sn F_1d3bc D_1d3bc.
    sn F_1d3c0 D_1d3c0.
    stw F_1d3c4 D_1d3c4 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3c8 D_1d3c8 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3cc D_1d3cc (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3d0 D_1d3d0 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d3d4 D_1d3d4.
    sv F_1d3d8 D_1d3d8 (Z_to_bv 64 (bv_unsigned d + 56)).
    stepb_tk F_1d3dc D_1d3dc ltac:(pin; cond_compute).
    stw F_1d3c4 D_1d3c4 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3c8 D_1d3c8 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3cc D_1d3cc (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3d0 D_1d3d0 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d3d4 D_1d3d4.
    sv F_1d3d8 D_1d3d8 (Z_to_bv 64 (bv_unsigned d + 88)).
    stepb_tk F_1d3dc D_1d3dc ltac:(pin; cond_compute).
    stw F_1d3c4 D_1d3c4 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3c8 D_1d3c8 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3cc D_1d3cc (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3d0 D_1d3d0 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d3d4 D_1d3d4.
    sv F_1d3d8 D_1d3d8 (Z_to_bv 64 (bv_unsigned d + 120)).
    stepb_tk F_1d3dc D_1d3dc ltac:(pin; cond_compute).
    stw F_1d3c4 D_1d3c4 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3c8 D_1d3c8 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3cc D_1d3cc (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3d0 D_1d3d0 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d3d4 D_1d3d4.
    sv F_1d3d8 D_1d3d8 (Z_to_bv 64 (bv_unsigned d + 152)).
    stepb_tk F_1d3dc D_1d3dc ltac:(pin; cond_compute).
    stw F_1d3c4 D_1d3c4 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3c8 D_1d3c8 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3cc D_1d3cc (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3d0 D_1d3d0 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d3d4 D_1d3d4.
    sv F_1d3d8 D_1d3d8 (Z_to_bv 64 (bv_unsigned d + 184)).
    stepb_tk F_1d3dc D_1d3dc ltac:(pin; cond_compute).
    stw F_1d3c4 D_1d3c4 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3c8 D_1d3c8 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3cc D_1d3cc (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3d0 D_1d3d0 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d3d4 D_1d3d4.
    sv F_1d3d8 D_1d3d8 (Z_to_bv 64 (bv_unsigned d + 216)).
    stepb_tk F_1d3dc D_1d3dc ltac:(pin; cond_compute).
    stw F_1d3c4 D_1d3c4 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3c8 D_1d3c8 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3cc D_1d3cc (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3d0 D_1d3d0 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d3d4 D_1d3d4.
    sv F_1d3d8 D_1d3d8 (Z_to_bv 64 (bv_unsigned d + 248)).
    stepb_tk F_1d3dc D_1d3dc ltac:(pin; cond_compute).
    stw F_1d3c4 D_1d3c4 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3c8 D_1d3c8 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3cc D_1d3cc (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_1d3d0 D_1d3d0 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_1d3d4 D_1d3d4.
    sv F_1d3d8 D_1d3d8 (Z_to_bv 64 (bv_unsigned d + 280)).
    stepb_ft F_1d3dc D_1d3dc ltac:(pin; cond_compute).
    stepret F_1d3e0 D_1d3e0 ret ltac:(pin; reflexivity).
    OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_chain_step_kit.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.ZStores.length_zeros; OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StartupTac.unorm; Stdlib.micromega.Lia.lia.
