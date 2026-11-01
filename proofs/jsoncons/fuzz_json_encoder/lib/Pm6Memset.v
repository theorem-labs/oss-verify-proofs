(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import StartupTac Pm6_code_ba000_bb000 .
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.


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
    msteps SEGS (mkst regs (0xbabdc : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret x1_ret ret_good x10_dst x11_byte x12_len dst_al8 dst_room dst_ok.
  pose proof (u64_range d) as dst_rng.
  assert (dst_al4 : (bv_unsigned d mod 4 = 0)%Z).
  { pose proof (Z.mod_mod_divide (bv_unsigned d) 8 4 (ex_intro _ 2%Z eq_refl)) as fold4.
    rewrite dst_al8 in fold4. exact (eq_sym fold4). }
  assert (fill_eq : zstores mem d memset304_ws = wbytes mem d (zeros 304)).
  { apply (zstores_cover d 304 dst_room);
      [ reflexivity | exact memset304_ws_inb | exact memset304_ws_cover ]. }
  do 2 eexists. split; [| split].
  - stepb_ft F_baba0 D_baba0 ltac:(pin; cond_compute).
    stw F_baba4 D_baba4 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    sv F_baba8 D_baba8 (Z_to_bv 64 (bv_unsigned d + 304)).
    sn F_babac D_babac.
    stw F_babb0 D_babb0 (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stepb_ft F_babb4 D_babb4 ltac:(pin; cond_compute).
    stw F_babb8 D_babb8 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_babbc D_babbc (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    sn F_babc0 D_babc0.
    stw F_babc4 D_babc4 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_babc8 D_babc8 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stepb_ft F_babcc D_babcc ltac:(pin; cond_compute).
    stw F_babd0 D_babd0 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    sn F_babd4 D_babd4.
    stw F_babd8 D_babd8 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stepb_ft F_babdc D_babdc ltac:(pin; cond_compute).
    sn F_babe0 D_babe0.
    sn F_babe4 D_babe4.
    sn F_babe8 D_babe8.
    stepiv F_babec D_babec (Z_to_bv 64 0)
      ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact dst_al4).
    sn F_babf0 D_babf0.
    sn F_babf4 D_babf4.
    sv F_babf8 D_babf8 d.
    sn F_babfc D_babfc.
    sn F_bac00 D_bac00.
    sn F_bac04 D_bac04.
    stw F_bac08 D_bac08 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    sv F_bac0c D_bac0c (Z_to_bv 64 (bv_unsigned d + 304)).
    stw F_bac10 D_bac10 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stepb_ft F_bac14 D_bac14 ltac:(pin; cond_compute).
    stw F_bac18 D_bac18 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_bac1c D_bac1c (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    sn F_bac20 D_bac20.
    stw F_bac24 D_bac24 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_bac28 D_bac28 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stepb_ft F_bac2c D_bac2c ltac:(pin; cond_compute).
    stw F_bac30 D_bac30 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_bac34 D_bac34 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_bac38 D_bac38 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_bac3c D_bac3c (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stepiv F_bac40 D_bac40 (Z_to_bv 64 0)
      ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact dst_al8).
    sn F_bac44 D_bac44.
    sn F_bac48 D_bac48.
    sn F_bac4c D_bac4c.
    stw F_bac50 D_bac50 (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_bac54 D_bac54 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_bac58 D_bac58 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stw F_bac5c D_bac5c (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok).
    stepb_ft F_bac60 D_bac60 ltac:(pin; cond_compute).
    sn F_bac64 D_bac64.
    sv F_bac68 D_bac68 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_bac6c D_bac6c.
    sn F_bac70 D_bac70.
    sn F_bac74 D_bac74.
    do 8 (
      lazymatch goal with
      | |- msteps _ (mkst ?rs _ _ _) _ =>
          lazymatch wf_find rs (11 : reg) with
          | Z_to_bv 64 (bv_unsigned d + ?at0) =>
              let at1 := eval vm_compute in (at0 + 8)%Z in
              let at2 := eval vm_compute in (at0 + 16)%Z in
              let at3 := eval vm_compute in (at0 + 24)%Z in
              let nxt := eval vm_compute in (at0 + 32)%Z in
              stw F_bac78 D_bac78 (Z_to_bv 64 (bv_unsigned d + at0)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok);
              stw F_bac7c D_bac7c (Z_to_bv 64 (bv_unsigned d + at1)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok);
              stw F_bac80 D_bac80 (Z_to_bv 64 (bv_unsigned d + at2)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok);
              stw F_bac84 D_bac84 (Z_to_bv 64 (bv_unsigned d + at3)) (Z_to_bv 64 0) ltac:(ok_sub dst_ok);
              sn F_bac88 D_bac88;
              sv F_bac8c D_bac8c (Z_to_bv 64 (bv_unsigned d + nxt));
              stepb F_bac90 D_bac90
          end
      end).
    stepret F_bac94 D_bac94 ret ltac:(exact x1_ret).
    apply mst_refl.
  - rewrite <- fill_eq. reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
