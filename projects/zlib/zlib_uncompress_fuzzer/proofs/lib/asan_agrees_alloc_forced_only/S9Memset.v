(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.GcF06.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import StartupTac S9_code_20000_20a74.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require L10Walk.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.L10Walk.l10_peel; OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ZStores.length_zeros; OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StartupTac.unorm; Stdlib.micromega.Lia.lia.

Abbreviation SEGS := Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.

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
    msteps SEGS (mkst regs (0x2056c : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_2049c D_2049c ltac:(pin; cond_compute).
    stw F_204a0 D_204a0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_204a4 D_204a4 (Z_to_bv 64 (bv_unsigned d + 304)).
    sn F_204a8 D_204a8.
    stw F_204ac D_204ac (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_204b0 D_204b0 ltac:(pin; cond_compute).
    stw F_204b4 D_204b4 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204b8 D_204b8 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_204bc D_204bc.
    stw F_204c0 D_204c0 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204c4 D_204c4 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_204c8 D_204c8 ltac:(pin; cond_compute).
    stw F_204cc D_204cc (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_204d0 D_204d0.
    stw F_204d4 D_204d4 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_204d8 D_204d8 ltac:(pin; cond_compute).
    sn F_204dc D_204dc.
    sn F_204e0 D_204e0.
    sn F_204e4 D_204e4.
    stepiv F_204e8 D_204e8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_204ec D_204ec.
    sn F_204f0 D_204f0.
    sv F_204f4 D_204f4 (d).
    sn F_204f8 D_204f8.
    sn F_204fc D_204fc.
    sn F_20500 D_20500.
    stw F_20504 D_20504 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_20508 D_20508 (Z_to_bv 64 (bv_unsigned d + 304)).
    stw F_2050c D_2050c (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_20510 D_20510 ltac:(pin; cond_compute).
    stw F_20514 D_20514 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20518 D_20518 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_2051c D_2051c.
    stw F_20520 D_20520 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20524 D_20524 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_20528 D_20528 ltac:(pin; cond_compute).
    stw F_2052c D_2052c (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20530 D_20530 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20534 D_20534 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20538 D_20538 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_2053c D_2053c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_20540 D_20540.
    sn F_20544 D_20544.
    sn F_20548 D_20548.
    stw F_2054c D_2054c (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20550 D_20550 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20554 D_20554 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20558 D_20558 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_2055c D_2055c ltac:(pin; cond_compute).
    sn F_20560 D_20560.
    sv F_20564 D_20564 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_20568 D_20568.
    sn F_2056c D_2056c.
    sn F_20570 D_20570.
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 56)).
    stepb_tk F_2058c D_2058c ltac:(pin; cond_compute).
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 88)).
    stepb_tk F_2058c D_2058c ltac:(pin; cond_compute).
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 120)).
    stepb_tk F_2058c D_2058c ltac:(pin; cond_compute).
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 152)).
    stepb_tk F_2058c D_2058c ltac:(pin; cond_compute).
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 184)).
    stepb_tk F_2058c D_2058c ltac:(pin; cond_compute).
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 216)).
    stepb_tk F_2058c D_2058c ltac:(pin; cond_compute).
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 248)).
    stepb_tk F_2058c D_2058c ltac:(pin; cond_compute).
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 280)).
    stepb_ft F_2058c D_2058c ltac:(pin; cond_compute).
    stepret F_20590 D_20590 ret ltac:(pin; reflexivity).
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.L10Walk.l10_mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ZStores.length_zeros; OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StartupTac.unorm; Stdlib.micromega.Lia.lia.
End FXG.
