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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1BootCode U1BootDefs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Img.
  Variable SEGS : list Segment.
  Hypothesis HX : u1b_ok SEGS = true.

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

  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = Z_to_bv 64 1189544 ->
    getr regs 11 = Z_to_bv 64 1188896 ->
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
        getr regs' 4 = (Z_to_bv 64 1057816) ->
        getr regs' 10 = (Z_to_bv 64 1188896) ->
        getr regs' 11 = (Z_to_bv 64 1189600) ->
        getr regs' 12 = (Z_to_bv 64 0) ->
        getr regs' 13 = (Z_to_bv 64 1057608) ->
        getr regs' 14 = (Z_to_bv 64 0) ->
        getr regs' 15 = (Z_to_bv 64 18446744073708493800) ->
        getr regs' 17 = (Z_to_bv 64 96) ->
        getr regs' 18 = (Z_to_bv 64 1057616) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (0xd1a68 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (0xd18e4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { stepb_tk (F_d18e4 _ HX) D_d18e4 ltac:(pin; cond_compute).
      ld_step (F_d191c _ HX) D_d191c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_102330_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1920 _ HX) D_d1920 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_102340_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1924 _ HX) D_d1924 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_102348_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      sn (F_d1928 _ HX) D_d1928.
      sn (F_d192c _ HX) D_d192c.
      sn (F_d1930 _ HX) D_d1930.
      sn (F_d1934 _ HX) D_d1934.
      sn (F_d1938 _ HX) D_d1938.
      sn (F_d193c _ HX) D_d193c.
      sn (F_d1940 _ HX) D_d1940.
      stw (F_d1944 _ HX) D_d1944 (Z_to_bv 64 1188928) (Z_to_bv 64 0) ltac:(ok_dat HX).
      stw (F_d1948 _ HX) D_d1948 (Z_to_bv 64 1188944) (Z_to_bv 64 0) ltac:(ok_dat HX).
      stepb_ft (F_d194c _ HX) D_d194c ltac:(pin; cond_compute).
      sn (F_d1950 _ HX) D_d1950.
      stw (F_d1954 _ HX) D_d1954 (Z_to_bv 64 1188936) (Z_to_bv 64 8) ltac:(ok_dat HX).
      sn (F_d1958 _ HX) D_d1958.
      sn (F_d195c _ HX) D_d195c.
      sn (F_d1960 _ HX) D_d1960.
      sn (F_d1964 _ HX) D_d1964.
      sn (F_d1968 _ HX) D_d1968.
      sn (F_d196c _ HX) D_d196c.
      stw (F_d1970 _ HX) D_d1970 (Z_to_bv 64 1189568) (Z_to_bv 64 224) ltac:(ok_dat HX).
      stw (F_d1974 _ HX) D_d1974 (Z_to_bv 64 1189576) (Z_to_bv 64 8) ltac:(ok_dat HX).
      stepb_tk (F_d1978 _ HX) D_d1978 ltac:(pin; cond_compute).
      sn (F_d19ac _ HX) D_d19ac.
      ld_step (F_d19b0 _ HX) D_d19b0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_102708_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d19b4 _ HX) D_d19b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_102720_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      sn (F_d19b8 _ HX) D_d19b8.
      sn (F_d19bc _ HX) D_d19bc.
      sn (F_d19c0 _ HX) D_d19c0.
      sn (F_d19c4 _ HX) D_d19c4.
      sn (F_d19c8 _ HX) D_d19c8.
      sn (F_d19cc _ HX) D_d19cc.
      sn (F_d19d0 _ HX) D_d19d0.
      sn (F_d19d4 _ HX) D_d19d4.
      sn (F_d19d8 _ HX) D_d19d8.
      sn (F_d19dc _ HX) D_d19dc.
      sn (F_d19e0 _ HX) D_d19e0.
      stepb_tk (F_d19e4 _ HX) D_d19e4 ltac:(pin; cond_compute).
      stw (F_d1a2c _ HX) D_d1a2c (Z_to_bv 64 1057832) (Z_to_bv 64 0) ltac:(ok_dat HX).
      stw (F_d1a30 _ HX) D_d1a30 (Z_to_bv 64 1057808) (Z_to_bv 64 1057832) ltac:(ok_dat HX).
      stw (F_d1a34 _ HX) D_d1a34 (Z_to_bv 64 1057616) (Z_to_bv 64 1057616) ltac:(ok_dat HX).
      sn (F_d1a38 _ HX) D_d1a38.
      sn (F_d1a3c _ HX) D_d1a3c.
      sn (F_e5288 _ HX) D_e5288.
      sn (F_e528c _ HX) D_e528c.
      stepret (F_e5290 _ HX) D_e5290 (0xd1a40 : word) ltac:(pin; first [reflexivity | bveq]).
      stepb_ft (F_d1a40 _ HX) D_d1a40 ltac:(pin; cond_compute).
      stepb_ft (F_d1a44 _ HX) D_d1a44 ltac:(pin; cond_compute).
      sn (F_d1a48 _ HX) D_d1a48.
      stw (F_d1a4c _ HX) D_d1a4c (Z_to_bv 64 1189544) (Z_to_bv 64 1) ltac:(ok_dat HX).
      sn (F_d1a50 _ HX) D_d1a50.
      sn (F_d1a54 _ HX) D_d1a54.
      stw (F_d1a58 _ HX) D_d1a58 (Z_to_bv 64 1057656) (Z_to_bv 64 2) ltac:(ok_dat HX).
      sn (F_d1a5c _ HX) D_d1a5c.
      sn (F_d1a60 _ HX) D_d1a60.
      sn (F_d1a64 _ HX) D_d1a64.
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 1057816 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 1189600 ->
    getr regs 18 = Z_to_bv 64 1057616 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 1057816) ->
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
        G (mkst regs' (0xd15fc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1057648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1057768) (word_to_le_bytes 8 (Z_to_bv 64 1189600))) (Z_to_bv 64 1057736) (word_to_le_bytes 8 (Z_to_bv 64 1057736))) (Z_to_bv 64 1057624) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057632) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057640) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (0xd1a6c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn (F_d1a6c _ HX) D_d1a6c.
      stw (F_d1a70 _ HX) D_d1a70 (Z_to_bv 64 1057648) tid ltac:(ok_dat HX).
      stw (F_d1a74 _ HX) D_d1a74 (Z_to_bv 64 1057768) (Z_to_bv 64 1189600) ltac:(ok_dat HX).
      stw (F_d1a78 _ HX) D_d1a78 (Z_to_bv 64 1057736) (Z_to_bv 64 1057736) ltac:(ok_dat HX).
      sn (F_d1a7c _ HX) D_d1a7c.
      ld_step (F_d1a80 _ HX) D_d1a80 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_1026e0_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stw (F_d1a84 _ HX) D_d1a84 (Z_to_bv 64 1057624) (Z_to_bv 64 1057616) ltac:(ok_dat HX).
      stw (F_d1a88 _ HX) D_d1a88 (Z_to_bv 64 1057632) (Z_to_bv 64 1057616) ltac:(ok_dat HX).
      stw (F_d1a8c _ HX) D_d1a8c (Z_to_bv 64 1057640) (Z_to_bv 64 0) ltac:(ok_dat HX).
      sn (F_d1a90 _ HX) D_d1a90.
      ld_step (F_d1a98 _ HX) D_d1a98 (word_to_le_bytes 8 (Z_to_bv 64 857596)) (Z_to_bv 64 857596) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1a9c _ HX) D_d1a9c (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1aa0 _ HX) D_d1aa0 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1aa4 _ HX) D_d1aa4 (word_to_le_bytes 8 (Z_to_bv 64 1189544)) (Z_to_bv 64 1189544) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1aa8 _ HX) D_d1aa8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1aac _ HX) D_d1aac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1ab0 _ HX) D_d1ab0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv (F_d1ab4 _ HX) D_d1ab4 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret (F_d1ab8 _ HX) D_d1ab8 (0xd15fc : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P4.

End Img.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
