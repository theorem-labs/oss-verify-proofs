(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* memset(d, 0, 7168): the opening steps (memset304_run's, offsets moved) and
   the whole run, over S7Memset7168's loop. Split from S7Memset7168.v (one file went over 300 s). *)

Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.GcF06.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import StartupTac S7_code_20000_20a30 S7Memset S7Memset7168.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.L10Walk.l10_peel; OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ZStores.length_zeros; OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.StartupTac.unorm; Stdlib.micromega.Lia.lia.

Abbreviation SEGS := Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac gfin := gres; pin; first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition memset7168_ws_pro : list (Z * nat) :=
  [(0,1%nat); (7167,1%nat); (1,1%nat); (2,1%nat); (7165,1%nat); (7166,1%nat); (3,1%nat); (7164,1%nat);
   (0,4%nat); (7164,4%nat); (4,4%nat); (8,4%nat); (7156,4%nat); (7160,4%nat); (12,4%nat); (16,4%nat); (20,4%nat);
   (24,4%nat); (7140,4%nat); (7144,4%nat); (7148,4%nat); (7152,4%nat)]%Z.
Definition memset7168_ws : list (Z * nat) := memset7168_ws_pro ++ [(24%Z, (32 * 223)%nat)].

Lemma memset7168_ws_inb : ws_inb memset7168_ws 7168 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset7168_ws_cover : ws_cover memset7168_ws 7168 = true.
Proof. vm_compute. reflexivity. Qed.

(* memset's opening steps for n = 7168 (memset304_run's, offsets moved), up to the loop head *)
Lemma memset7168_pro : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 7168 ->
  (bv_unsigned d mod 8 = 0)%Z -> (bv_unsigned d + 7168 < 2^64)%Z ->
  store_ok SEGS mem d (7 * 1024) = true ->
  exists regs1 mem1,
    msteps SEGS (mkst regs (0x20588 : word) mem rom) (mkst regs1 (0x20660 : word) mem1 rom)
    /\ mem1 = zstores mem d memset7168_ws_pro
    /\ getr regs1 1 = ret
    /\ getr regs1 11 = Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat 223))
    /\ getr regs1 12 = Z_to_bv 64 0 /\ getr regs1 13 = Z_to_bv 64 31
    /\ getr regs1 14 = Z_to_bv 64 (32 * Z.of_nat 223 + 8)
    /\ regs_agree (fun r => In r memset_clob) regs regs1.
Proof.
  intros regs mem rom d ret Hra Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - stepb_ft F_20458 D_20458 ltac:(pin; cond_compute).
    stw F_2045c D_2045c (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_20460 D_20460 (Z_to_bv 64 (bv_unsigned d + 7168)).
    sn F_20464 D_20464.
    stw F_20468 D_20468 (Z_to_bv 64 (bv_unsigned d + 7167)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_2046c D_2046c ltac:(pin; cond_compute).
    stw F_20470 D_20470 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20474 D_20474 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20478 D_20478.
    stw F_2047c D_2047c (Z_to_bv 64 (bv_unsigned d + 7165)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20480 D_20480 (Z_to_bv 64 (bv_unsigned d + 7166)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_20484 D_20484 ltac:(pin; cond_compute).
    stw F_20488 D_20488 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_2048c D_2048c.
    stw F_20490 D_20490 (Z_to_bv 64 (bv_unsigned d + 7164)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_20494 D_20494 ltac:(pin; cond_compute).
    sn F_20498 D_20498.
    sn F_2049c D_2049c.
    sn F_204a0 D_204a0.
    stepiv F_204a4 D_204a4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_204a8 D_204a8.
    sn F_204ac D_204ac.
    sv F_204b0 D_204b0 (d).
    sn F_204b4 D_204b4.
    sn F_204b8 D_204b8.
    sn F_204bc D_204bc.
    stw F_204c0 D_204c0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_204c4 D_204c4 (Z_to_bv 64 (bv_unsigned d + 7168)).
    stw F_204c8 D_204c8 (Z_to_bv 64 (bv_unsigned d + 7164)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_204cc D_204cc ltac:(pin; cond_compute).
    stw F_204d0 D_204d0 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204d4 D_204d4 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_204d8 D_204d8.
    stw F_204dc D_204dc (Z_to_bv 64 (bv_unsigned d + 7156)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204e0 D_204e0 (Z_to_bv 64 (bv_unsigned d + 7160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_204e4 D_204e4 ltac:(pin; cond_compute).
    stw F_204e8 D_204e8 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204ec D_204ec (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204f0 D_204f0 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204f4 D_204f4 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_204f8 D_204f8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_204fc D_204fc.
    sn F_20500 D_20500.
    sn F_20504 D_20504.
    stw F_20508 D_20508 (Z_to_bv 64 (bv_unsigned d + 7140)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2050c D_2050c (Z_to_bv 64 (bv_unsigned d + 7144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20510 D_20510 (Z_to_bv 64 (bv_unsigned d + 7148)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20514 D_20514 (Z_to_bv 64 (bv_unsigned d + 7152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_20518 D_20518 ltac:(pin; cond_compute).
    sn F_2051c D_2051c.
    sv F_20520 D_20520 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_20524 D_20524.
    sn F_20528 D_20528.
    sn F_2052c D_2052c.
    OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl.
  - reflexivity.
  - gfin.
  - gfin.
  - gfin.
  - gfin.
  - gfin.
  - unfold memset_clob. solve_regs_agree.
Qed.

Theorem memset7168_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 7168 ->
  (bv_unsigned d mod 8 = 0)%Z -> (bv_unsigned d + 7168 < 2^64)%Z ->
  store_ok SEGS mem d (7 * 1024) = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0x20588 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 7168)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  destruct (memset7168_pro regs mem rom d ret Hra Hd H11 H12 Hal Hnw Hok)
    as (r1 & m1 & RUN1 & EQ1 & G1 & G11 & G12 & G13 & G14 & AG1).
  destruct (memset7168_loop 223 r1 m1 rom d ret ltac:(lia) ltac:(lia) G1 Hret G11 G12 G13 G14 Hnw)
    as (r2 & m2 & RUN2 & EQ2 & AG2).
  { subst m1. unfold memset7168_ws_pro. cbn [zstores]. ok_sub Hok. }
  exists r2, m2. split; [eapply msteps_trans; eassumption|]. split; [| eapply regs_agree_trans; eassumption].
  rewrite EQ2, EQ1.
  rewrite <- (zstores_cover d 7168 Hnw memset7168_ws mem 7168%nat eq_refl memset7168_ws_inb memset7168_ws_cover).
  unfold memset7168_ws. rewrite zstores_app. cbn [zstores].
  replace (7160 - 32 * Z.of_nat 223)%Z with 24%Z by lia. reflexivity.
Qed.
End FXG.
