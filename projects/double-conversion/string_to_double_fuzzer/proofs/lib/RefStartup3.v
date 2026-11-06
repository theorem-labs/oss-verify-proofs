(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg RefImgTls RefStartupDefs Ref_code_95a4c_95cfc Ref_code_a8d50_a8d5c.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := ImgP.M.loaded_segments.
Abbreviation RPH := ImgP.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPW_1. Context {fx : PropExec.FPState}.


Section P4.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

#[using="Hlo Hhi"] Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 612412 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 936872 ->
getr regs 19 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 936872) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 936224) ->
getr regs' 13 = (Z_to_bv 64 10) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65600) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
G (mkst regs' (0x95ad4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x95a4c : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_95a4c D_95a4c (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_95a50 D_95a50 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 612412) ltac:(ok_win HJ).
stw F_95a54 D_95a54 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_95a58 D_95a58 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_95a5c D_95a5c (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 936872) ltac:(ok_win HJ).
stw F_95a60 D_95a60 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_95a64 D_95a64 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_95a68 D_95a68 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_95a6c D_95a6c (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_95a70 D_95a70.
sn F_95a74 D_95a74.
sn F_95a78 D_95a78.
sn F_95a7c D_95a7c.
stepb_ft F_95a80 D_95a80 ltac:(pin; cond_compute).
sn F_95a84 D_95a84.
sn F_95a88 D_95a88.
sn F_95a8c D_95a8c.
ld_step F_95a90 D_95a90 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95a94 D_95a94 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_95a98 D_95a98.
sn F_95a9c D_95a9c.
ld_step F_95aa0 D_95aa0 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_b2e80_4) ltac:(vm_compute; reflexivity).
ld_step F_95aa4 D_95aa4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b1a48_8) ltac:(apply bytes_le_to_Z_8).
sn F_95aa8 D_95aa8.
sn F_95aac D_95aac.
sn F_95ab0 D_95ab0.
sn F_95ab4 D_95ab4.
sn F_95ab8 D_95ab8.
sn F_95abc D_95abc.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 936872 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 936224 ->
getr regs 13 = Z_to_bv 64 10 ->
getr regs 15 = Z_to_bv 64 65600 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65600 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 936872) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 936224) ->
getr regs' 13 = (Z_to_bv 64 5) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65880) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x95ad4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x95ad4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_95ad8 D_95ad8 ltac:(pin; cond_compute).
ld_step F_95ac0 D_95ac0 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_95ac4 D_95ac4.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_tk F_95afc D_95afc ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_tk F_95afc D_95afc ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_tk F_95afc D_95afc ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_tk F_95afc D_95afc ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 936872 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 936224 ->
getr regs 13 = Z_to_bv 64 5 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65880 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 9 = (Z_to_bv 64 936872) ->
getr regs' 11 = (Z_to_bv 64 936224) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x95b24 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x95ad4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_tk F_95afc D_95afc ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_tk F_95afc D_95afc ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_ft F_95afc D_95afc ltac:(pin; cond_compute).
ld_step F_95b00 D_95b00 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_95b04 D_95b04 ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_tk F_95afc D_95afc ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_ft F_95ad0 D_95ad0 ltac:(pin; cond_compute).
ld_step F_95ad4 D_95ad4 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_95ad8 D_95ad8 ltac:(pin; cond_compute).
stepb_tk F_95adc D_95adc ltac:(pin; cond_compute).
sn F_95af0 D_95af0.
stepb_ft F_95af4 D_95af4 ltac:(pin; cond_compute).
sn F_95af8 D_95af8.
stepb_tk F_95afc D_95afc ltac:(pin; cond_compute).
sn F_95b1c D_95b1c.
sn F_95b20 D_95b20.
sn F_95ac8 D_95ac8.
sn F_95acc D_95acc.
stepb_tk F_95ad0 D_95ad0 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo"] Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 936872 ->
getr regs 11 = Z_to_bv 64 936224 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 805144) ->
getr regs' 10 = (Z_to_bv 64 936224) ->
getr regs' 11 = (Z_to_bv 64 936928) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 804936) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073708746472) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 804944) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x95ca8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x95b24 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_95b24 D_95b24 ltac:(pin; cond_compute).
ld_step F_95b5c D_95b5c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e4930_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95b60 D_95b60 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e4940_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95b64 D_95b64 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e4948_8) ltac:(apply bytes_le_to_Z_8).
sn F_95b68 D_95b68.
sn F_95b6c D_95b6c.
sn F_95b70 D_95b70.
sn F_95b74 D_95b74.
sn F_95b78 D_95b78.
sn F_95b7c D_95b7c.
sn F_95b80 D_95b80.
stw F_95b84 D_95b84 (Z_to_bv 64 936256) (Z_to_bv 64 0) ltac:(ok_data).
stw F_95b88 D_95b88 (Z_to_bv 64 936272) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_95b8c D_95b8c ltac:(pin; cond_compute).
sn F_95b90 D_95b90.
stw F_95b94 D_95b94 (Z_to_bv 64 936264) (Z_to_bv 64 8) ltac:(ok_data).
sn F_95b98 D_95b98.
sn F_95b9c D_95b9c.
sn F_95ba0 D_95ba0.
sn F_95ba4 D_95ba4.
sn F_95ba8 D_95ba8.
sn F_95bac D_95bac.
stw F_95bb0 D_95bb0 (Z_to_bv 64 936896) (Z_to_bv 64 224) ltac:(ok_data).
stw F_95bb4 D_95bb4 (Z_to_bv 64 936904) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_95bb8 D_95bb8 ltac:(pin; cond_compute).
sn F_95bec D_95bec.
ld_step F_95bf0 D_95bf0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e4bb8_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95bf4 D_95bf4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e4bd0_8) ltac:(apply bytes_le_to_Z_8).
sn F_95bf8 D_95bf8.
sn F_95bfc D_95bfc.
sn F_95c00 D_95c00.
sn F_95c04 D_95c04.
sn F_95c08 D_95c08.
sn F_95c0c D_95c0c.
sn F_95c10 D_95c10.
sn F_95c14 D_95c14.
sn F_95c18 D_95c18.
sn F_95c1c D_95c1c.
sn F_95c20 D_95c20.
stepb_tk F_95c24 D_95c24 ltac:(pin; cond_compute).
stw F_95c6c D_95c6c (Z_to_bv 64 805160) (Z_to_bv 64 0) ltac:(ok_data).
stw F_95c70 D_95c70 (Z_to_bv 64 805136) (Z_to_bv 64 805160) ltac:(ok_data).
stw F_95c74 D_95c74 (Z_to_bv 64 804944) (Z_to_bv 64 804944) ltac:(ok_data).
sn F_95c78 D_95c78.
sn F_95c7c D_95c7c.
sn F_a8d50 D_a8d50.
sn F_a8d54 D_a8d54.
stepret F_a8d58 D_a8d58 (0x95c80 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_95c80 D_95c80 ltac:(pin; cond_compute).
stepb_ft F_95c84 D_95c84 ltac:(pin; cond_compute).
sn F_95c88 D_95c88.
stw F_95c8c D_95c8c (Z_to_bv 64 936872) (Z_to_bv 64 1) ltac:(ok_data).
sn F_95c90 D_95c90.
sn F_95c94 D_95c94.
stw F_95c98 D_95c98 (Z_to_bv 64 804984) (Z_to_bv 64 2) ltac:(ok_data).
sn F_95c9c D_95c9c.
sn F_95ca0 D_95ca0.
sn F_95ca4 D_95ca4.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

#[using="Hlo Hhi"] Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 805144 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 936928 ->
getr regs 18 = Z_to_bv 64 804944 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 805144) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x9583c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x95cac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_95cac D_95cac.
stw F_95cb0 D_95cb0 (Z_to_bv 64 804976) tid ltac:(ok_data).
stw F_95cb4 D_95cb4 (Z_to_bv 64 805096) (Z_to_bv 64 936928) ltac:(ok_data).
stw F_95cb8 D_95cb8 (Z_to_bv 64 805064) (Z_to_bv 64 805064) ltac:(ok_data).
sn F_95cbc D_95cbc.
ld_step F_95cc0 D_95cc0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e4b90_8) ltac:(apply bytes_le_to_Z_8).
stw F_95cc4 D_95cc4 (Z_to_bv 64 804952) (Z_to_bv 64 804944) ltac:(ok_data).
stw F_95cc8 D_95cc8 (Z_to_bv 64 804960) (Z_to_bv 64 804944) ltac:(ok_data).
stw F_95ccc D_95ccc (Z_to_bv 64 804968) (Z_to_bv 64 0) ltac:(ok_data).
sn F_95cd0 D_95cd0.
ld_step F_95cd8 D_95cd8 (word_to_le_bytes 8 (Z_to_bv 64 612412)) (Z_to_bv 64 612412) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95cdc D_95cdc (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95ce0 D_95ce0 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95ce4 D_95ce4 (word_to_le_bytes 8 (Z_to_bv 64 936872)) (Z_to_bv 64 936872) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95ce8 D_95ce8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95cec D_95cec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_95cf0 D_95cf0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_95cf4 D_95cf4 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_95cf8 D_95cf8 (0x9583c : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P4.
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
