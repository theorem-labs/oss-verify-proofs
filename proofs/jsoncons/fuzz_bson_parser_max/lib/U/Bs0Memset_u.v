(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import StartupTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0_code_r58000_59000_u .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require PropExec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


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
    msteps SEGS (mkst regs (0xaba00 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_aa3cc D_aa3cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa3d0 D_aa3d0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_aa3d4 D_aa3d4 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    sn F_aa3d8 D_aa3d8.  (* [comment removed for export] *)
    stw F_aa3dc D_aa3dc (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_aa3e0 D_aa3e0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa3e4 D_aa3e4 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa3e8 D_aa3e8 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa3ec D_aa3ec.  (* [comment removed for export] *)
    stw F_aa3f0 D_aa3f0 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa3f4 D_aa3f4 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_aa3f8 D_aa3f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa3fc D_aa3fc (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa400 D_aa400.  (* [comment removed for export] *)
    stw F_aa404 D_aa404 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_aa408 D_aa408 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_aa40c D_aa40c.  (* [comment removed for export] *)
    sn F_aa410 D_aa410.  (* [comment removed for export] *)
    sn F_aa414 D_aa414.  (* [comment removed for export] *)
    stepiv F_aa418 D_aa418 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).  (* [comment removed for export] *)
    sn F_aa41c D_aa41c.  (* [comment removed for export] *)
    sn F_aa420 D_aa420.  (* [comment removed for export] *)
    sv F_aa424 D_aa424 (d).  (* [comment removed for export] *)
    sn F_aa428 D_aa428.  (* [comment removed for export] *)
    sn F_aa42c D_aa42c.  (* [comment removed for export] *)
    sn F_aa430 D_aa430.  (* [comment removed for export] *)
    stw F_aa434 D_aa434 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sv F_aa438 D_aa438 (Z_to_bv 64 (bv_unsigned d + 304)).  (* [comment removed for export] *)
    stw F_aa43c D_aa43c (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_aa440 D_aa440 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa444 D_aa444 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa448 D_aa448 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa44c D_aa44c.  (* [comment removed for export] *)
    stw F_aa450 D_aa450 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa454 D_aa454 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_aa458 D_aa458 ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa45c D_aa45c (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa460 D_aa460 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa464 D_aa464 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa468 D_aa468 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepiv F_aa46c D_aa46c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).  (* [comment removed for export] *)
    sn F_aa470 D_aa470.  (* [comment removed for export] *)
    sn F_aa474 D_aa474.  (* [comment removed for export] *)
    sn F_aa478 D_aa478.  (* [comment removed for export] *)
    stw F_aa47c D_aa47c (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa480 D_aa480 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa484 D_aa484 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa488 D_aa488 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stepb_ft F_aa48c D_aa48c ltac:(pin; cond_compute).  (* [comment removed for export] *)
    sn F_aa490 D_aa490.  (* [comment removed for export] *)
    sv F_aa494 D_aa494 (Z_to_bv 64 (bv_unsigned d + 24)).  (* [comment removed for export] *)
    sn F_aa498 D_aa498.  (* [comment removed for export] *)
    sn F_aa49c D_aa49c.  (* [comment removed for export] *)
    sn F_aa4a0 D_aa4a0.  (* [comment removed for export] *)
    stw F_aa4a4 D_aa4a4 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4a8 D_aa4a8 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4ac D_aa4ac (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4b0 D_aa4b0 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa4b4 D_aa4b4.  (* [comment removed for export] *)
    sv F_aa4b8 D_aa4b8 (Z_to_bv 64 (bv_unsigned d + 56)).  (* [comment removed for export] *)
    stepb_tk F_aa4bc D_aa4bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa4a4 D_aa4a4 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4a8 D_aa4a8 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4ac D_aa4ac (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4b0 D_aa4b0 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa4b4 D_aa4b4.  (* [comment removed for export] *)
    sv F_aa4b8 D_aa4b8 (Z_to_bv 64 (bv_unsigned d + 88)).  (* [comment removed for export] *)
    stepb_tk F_aa4bc D_aa4bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa4a4 D_aa4a4 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4a8 D_aa4a8 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4ac D_aa4ac (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4b0 D_aa4b0 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa4b4 D_aa4b4.  (* [comment removed for export] *)
    sv F_aa4b8 D_aa4b8 (Z_to_bv 64 (bv_unsigned d + 120)).  (* [comment removed for export] *)
    stepb_tk F_aa4bc D_aa4bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa4a4 D_aa4a4 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4a8 D_aa4a8 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4ac D_aa4ac (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4b0 D_aa4b0 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa4b4 D_aa4b4.  (* [comment removed for export] *)
    sv F_aa4b8 D_aa4b8 (Z_to_bv 64 (bv_unsigned d + 152)).  (* [comment removed for export] *)
    stepb_tk F_aa4bc D_aa4bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa4a4 D_aa4a4 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4a8 D_aa4a8 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4ac D_aa4ac (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4b0 D_aa4b0 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa4b4 D_aa4b4.  (* [comment removed for export] *)
    sv F_aa4b8 D_aa4b8 (Z_to_bv 64 (bv_unsigned d + 184)).  (* [comment removed for export] *)
    stepb_tk F_aa4bc D_aa4bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa4a4 D_aa4a4 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4a8 D_aa4a8 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4ac D_aa4ac (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4b0 D_aa4b0 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa4b4 D_aa4b4.  (* [comment removed for export] *)
    sv F_aa4b8 D_aa4b8 (Z_to_bv 64 (bv_unsigned d + 216)).  (* [comment removed for export] *)
    stepb_tk F_aa4bc D_aa4bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa4a4 D_aa4a4 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4a8 D_aa4a8 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4ac D_aa4ac (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4b0 D_aa4b0 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa4b4 D_aa4b4.  (* [comment removed for export] *)
    sv F_aa4b8 D_aa4b8 (Z_to_bv 64 (bv_unsigned d + 248)).  (* [comment removed for export] *)
    stepb_tk F_aa4bc D_aa4bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stw F_aa4a4 D_aa4a4 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4a8 D_aa4a8 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4ac D_aa4ac (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    stw F_aa4b0 D_aa4b0 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).  (* [comment removed for export] *)
    sn F_aa4b4 D_aa4b4.  (* [comment removed for export] *)
    sv F_aa4b8 D_aa4b8 (Z_to_bv 64 (bv_unsigned d + 280)).  (* [comment removed for export] *)
    stepb_ft F_aa4bc D_aa4bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
    stepret F_aa4c0 D_aa4c0 ret ltac:(pin; reflexivity).  (* [comment removed for export] *)
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
