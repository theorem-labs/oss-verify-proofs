(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress3_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac U8_code_21000_21d90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_peel; OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ZStores.length_zeros; OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac.unorm; Stdlib.micromega.Lia.lia.

Abbreviation SEGS := Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments.

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
    msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst regs (0x21904 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_217b8 D_217b8 ltac:(pin; cond_compute).
    stw F_217bc D_217bc (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_217c0 D_217c0 (Z_to_bv 64 (bv_unsigned d + 304)).
    sn F_217c4 D_217c4.
    stw F_217c8 D_217c8 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_217cc D_217cc ltac:(pin; cond_compute).
    stw F_217d0 D_217d0 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217d4 D_217d4 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_217d8 D_217d8.
    stw F_217dc D_217dc (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217e0 D_217e0 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_217e4 D_217e4 ltac:(pin; cond_compute).
    stw F_217e8 D_217e8 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_217ec D_217ec.
    stw F_217f0 D_217f0 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_217f4 D_217f4 ltac:(pin; cond_compute).
    sn F_217f8 D_217f8.
    sn F_217fc D_217fc.
    sn F_21800 D_21800.
    stepiv F_21804 D_21804 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_21808 D_21808.
    sn F_2180c D_2180c.
    sv F_21810 D_21810 (d).
    sn F_21814 D_21814.
    sn F_21818 D_21818.
    sn F_2181c D_2181c.
    stw F_21820 D_21820 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_21824 D_21824 (Z_to_bv 64 (bv_unsigned d + 304)).
    stw F_21828 D_21828 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_2182c D_2182c ltac:(pin; cond_compute).
    stw F_21830 D_21830 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21834 D_21834 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_21838 D_21838.
    stw F_2183c D_2183c (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21840 D_21840 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_21844 D_21844 ltac:(pin; cond_compute).
    stw F_21848 D_21848 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2184c D_2184c (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21850 D_21850 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21854 D_21854 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_21858 D_21858 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_2185c D_2185c.
    sn F_21860 D_21860.
    sn F_21864 D_21864.
    stw F_21868 D_21868 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2186c D_2186c (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21870 D_21870 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21874 D_21874 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_21878 D_21878 ltac:(pin; cond_compute).
    sn F_2187c D_2187c.
    sv F_21880 D_21880 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_21884 D_21884.
    sn F_21888 D_21888.
    sn F_2188c D_2188c.
    stw F_21890 D_21890 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21894 D_21894 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21898 D_21898 (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2189c D_2189c (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_218a0 D_218a0.
    sv F_218a4 D_218a4 (Z_to_bv 64 (bv_unsigned d + 56)).
    stepb_tk F_218a8 D_218a8 ltac:(pin; cond_compute).
    stw F_21890 D_21890 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21894 D_21894 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21898 D_21898 (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2189c D_2189c (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_218a0 D_218a0.
    sv F_218a4 D_218a4 (Z_to_bv 64 (bv_unsigned d + 88)).
    stepb_tk F_218a8 D_218a8 ltac:(pin; cond_compute).
    stw F_21890 D_21890 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21894 D_21894 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21898 D_21898 (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2189c D_2189c (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_218a0 D_218a0.
    sv F_218a4 D_218a4 (Z_to_bv 64 (bv_unsigned d + 120)).
    stepb_tk F_218a8 D_218a8 ltac:(pin; cond_compute).
    stw F_21890 D_21890 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21894 D_21894 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21898 D_21898 (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2189c D_2189c (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_218a0 D_218a0.
    sv F_218a4 D_218a4 (Z_to_bv 64 (bv_unsigned d + 152)).
    stepb_tk F_218a8 D_218a8 ltac:(pin; cond_compute).
    stw F_21890 D_21890 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21894 D_21894 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21898 D_21898 (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2189c D_2189c (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_218a0 D_218a0.
    sv F_218a4 D_218a4 (Z_to_bv 64 (bv_unsigned d + 184)).
    stepb_tk F_218a8 D_218a8 ltac:(pin; cond_compute).
    stw F_21890 D_21890 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21894 D_21894 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21898 D_21898 (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2189c D_2189c (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_218a0 D_218a0.
    sv F_218a4 D_218a4 (Z_to_bv 64 (bv_unsigned d + 216)).
    stepb_tk F_218a8 D_218a8 ltac:(pin; cond_compute).
    stw F_21890 D_21890 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21894 D_21894 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21898 D_21898 (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2189c D_2189c (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_218a0 D_218a0.
    sv F_218a4 D_218a4 (Z_to_bv 64 (bv_unsigned d + 248)).
    stepb_tk F_218a8 D_218a8 ltac:(pin; cond_compute).
    stw F_21890 D_21890 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21894 D_21894 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21898 D_21898 (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2189c D_2189c (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_218a0 D_218a0.
    sv F_218a4 D_218a4 (Z_to_bv 64 (bv_unsigned d + 280)).
    stepb_ft F_218a8 D_218a8 ltac:(pin; cond_compute).
    stepret F_218ac D_218ac ret ltac:(pin; reflexivity).
    OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.ZStores.length_zeros; OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac.unorm; Stdlib.micromega.Lia.lia.
