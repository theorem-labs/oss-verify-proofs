(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ArgvEnv RefLayout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1BootCode S1BootDefs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Img.
  Variable SEGS : list Segment.
  Hypothesis HX : s1b_ok SEGS = true.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 850084 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 8 = pn_w sp0 av ev ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = Z_to_bv 64 1182024 ->
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
        getr regs' 9 = (Z_to_bv 64 1182024) ->
        getr regs' 10 = (Z_to_bv 64 56) ->
        getr regs' 11 = (Z_to_bv 64 1181376) ->
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
        G (mkst regs' (0xcfb3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xcfab4 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv (F_cfab4 _ HX) D_cfab4 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
      stw (F_cfab8 _ HX) D_cfab8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 850084) ltac:(ok_win HJ).
      stw (F_cfabc _ HX) D_cfabc (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
      stw (F_cfac0 _ HX) D_cfac0 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
      stw (F_cfac4 _ HX) D_cfac4 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 1182024) ltac:(ok_win HJ).
      stw (F_cfac8 _ HX) D_cfac8 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_cfacc _ HX) D_cfacc (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_cfad0 _ HX) D_cfad0 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      ld_step (F_cfad4 _ HX) D_cfad4 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn (F_cfad8 _ HX) D_cfad8.
      sn (F_cfadc _ HX) D_cfadc.
      sn (F_cfae0 _ HX) D_cfae0.
      sn (F_cfae4 _ HX) D_cfae4.
      stepb_ft (F_cfae8 _ HX) D_cfae8 ltac:(pin; cond_compute).
      sn (F_cfaec _ HX) D_cfaec.
      sn (F_cfaf0 _ HX) D_cfaf0.
      sn (F_cfaf4 _ HX) D_cfaf4.
      ld_step (F_cfaf8 _ HX) D_cfaf8 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfafc _ HX) D_cfafc (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn (F_cfb00 _ HX) D_cfb00.
      sn (F_cfb04 _ HX) D_cfb04.
      ld_step (F_cfb08 _ HX) D_cfb08 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img (img_ee450_4 _ HX)) ltac:(vm_compute; reflexivity).
      ld_step (F_cfb0c _ HX) D_cfb0c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_ece98_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      sn (F_cfb10 _ HX) D_cfb10.
      sn (F_cfb14 _ HX) D_cfb14.
      sn (F_cfb18 _ HX) D_cfb18.
      sn (F_cfb1c _ HX) D_cfb1c.
      sn (F_cfb20 _ HX) D_cfb20.
      sn (F_cfb24 _ HX) D_cfb24.
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = Z_to_bv 64 1182024 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 1181376 ->
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
        getr regs' 9 = (Z_to_bv 64 1182024) ->
        getr regs' 10 = (Z_to_bv 64 56) ->
        getr regs' 11 = (Z_to_bv 64 1181376) ->
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
        G (mkst regs' (0xcfb3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xcfb3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img (img_10040_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_tk (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      ld_step (F_cfb28 _ HX) D_cfb28 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img (img_10050_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      sn (F_cfb2c _ HX) D_cfb2c.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img (img_10078_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_tk (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img (img_100b0_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_tk (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img (img_100e8_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_tk (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img (img_10120_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_tk (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = Z_to_bv 64 1182024 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 1181376 ->
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
        getr regs' 9 = (Z_to_bv 64 1182024) ->
        getr regs' 11 = (Z_to_bv 64 1181376) ->
        getr regs' 17 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0xcfb8c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xcfb3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img (img_10158_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_tk (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img (img_10190_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_tk (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img (img_101c8_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_ft (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      ld_step (F_cfb68 _ HX) D_cfb68 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_101f0_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stepb_tk (F_cfb6c _ HX) D_cfb6c ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img (img_10200_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_tk (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_ft (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      ld_step (F_cfb3c _ HX) D_cfb3c (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img (img_10238_4 _ HX)) ltac:(vm_compute; reflexivity).
      stepb_ft (F_cfb40 _ HX) D_cfb40 ltac:(pin; cond_compute).
      stepb_tk (F_cfb44 _ HX) D_cfb44 ltac:(pin; cond_compute).
      sn (F_cfb58 _ HX) D_cfb58.
      stepb_ft (F_cfb5c _ HX) D_cfb5c ltac:(pin; cond_compute).
      sn (F_cfb60 _ HX) D_cfb60.
      stepb_tk (F_cfb64 _ HX) D_cfb64 ltac:(pin; cond_compute).
      sn (F_cfb84 _ HX) D_cfb84.
      sn (F_cfb88 _ HX) D_cfb88.
      sn (F_cfb30 _ HX) D_cfb30.
      sn (F_cfb34 _ HX) D_cfb34.
      stepb_tk (F_cfb38 _ HX) D_cfb38 ltac:(pin; cond_compute).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P4.

End Img.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
