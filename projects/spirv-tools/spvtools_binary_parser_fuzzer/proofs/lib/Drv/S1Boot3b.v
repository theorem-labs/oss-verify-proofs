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

  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = Z_to_bv 64 1182024 ->
    getr regs 11 = Z_to_bv 64 1181376 ->
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
        getr regs' 4 = (Z_to_bv 64 1050296) ->
        getr regs' 10 = (Z_to_bv 64 1181376) ->
        getr regs' 11 = (Z_to_bv 64 1182080) ->
        getr regs' 12 = (Z_to_bv 64 0) ->
        getr regs' 13 = (Z_to_bv 64 1050088) ->
        getr regs' 14 = (Z_to_bv 64 0) ->
        getr regs' 15 = (Z_to_bv 64 18446744073708501320) ->
        getr regs' 17 = (Z_to_bv 64 96) ->
        getr regs' 18 = (Z_to_bv 64 1050096) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (0xcfd10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (0xcfb8c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { stepb_tk (F_cfb8c _ HX) D_cfb8c ltac:(pin; cond_compute).
      ld_step (F_cfbc4 _ HX) D_cfbc4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_1005d0_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfbc8 _ HX) D_cfbc8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_1005e0_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfbcc _ HX) D_cfbcc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_1005e8_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      sn (F_cfbd0 _ HX) D_cfbd0.
      sn (F_cfbd4 _ HX) D_cfbd4.
      sn (F_cfbd8 _ HX) D_cfbd8.
      sn (F_cfbdc _ HX) D_cfbdc.
      sn (F_cfbe0 _ HX) D_cfbe0.
      sn (F_cfbe4 _ HX) D_cfbe4.
      sn (F_cfbe8 _ HX) D_cfbe8.
      stw (F_cfbec _ HX) D_cfbec (Z_to_bv 64 1181408) (Z_to_bv 64 0) ltac:(ok_dat HX).
      stw (F_cfbf0 _ HX) D_cfbf0 (Z_to_bv 64 1181424) (Z_to_bv 64 0) ltac:(ok_dat HX).
      stepb_ft (F_cfbf4 _ HX) D_cfbf4 ltac:(pin; cond_compute).
      sn (F_cfbf8 _ HX) D_cfbf8.
      stw (F_cfbfc _ HX) D_cfbfc (Z_to_bv 64 1181416) (Z_to_bv 64 8) ltac:(ok_dat HX).
      sn (F_cfc00 _ HX) D_cfc00.
      sn (F_cfc04 _ HX) D_cfc04.
      sn (F_cfc08 _ HX) D_cfc08.
      sn (F_cfc0c _ HX) D_cfc0c.
      sn (F_cfc10 _ HX) D_cfc10.
      sn (F_cfc14 _ HX) D_cfc14.
      stw (F_cfc18 _ HX) D_cfc18 (Z_to_bv 64 1182048) (Z_to_bv 64 224) ltac:(ok_dat HX).
      stw (F_cfc1c _ HX) D_cfc1c (Z_to_bv 64 1182056) (Z_to_bv 64 8) ltac:(ok_dat HX).
      stepb_tk (F_cfc20 _ HX) D_cfc20 ltac:(pin; cond_compute).
      sn (F_cfc54 _ HX) D_cfc54.
      ld_step (F_cfc58 _ HX) D_cfc58 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_1009a8_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfc5c _ HX) D_cfc5c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_1009c0_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      sn (F_cfc60 _ HX) D_cfc60.
      sn (F_cfc64 _ HX) D_cfc64.
      sn (F_cfc68 _ HX) D_cfc68.
      sn (F_cfc6c _ HX) D_cfc6c.
      sn (F_cfc70 _ HX) D_cfc70.
      sn (F_cfc74 _ HX) D_cfc74.
      sn (F_cfc78 _ HX) D_cfc78.
      sn (F_cfc7c _ HX) D_cfc7c.
      sn (F_cfc80 _ HX) D_cfc80.
      sn (F_cfc84 _ HX) D_cfc84.
      sn (F_cfc88 _ HX) D_cfc88.
      stepb_tk (F_cfc8c _ HX) D_cfc8c ltac:(pin; cond_compute).
      stw (F_cfcd4 _ HX) D_cfcd4 (Z_to_bv 64 1050312) (Z_to_bv 64 0) ltac:(ok_dat HX).
      stw (F_cfcd8 _ HX) D_cfcd8 (Z_to_bv 64 1050288) (Z_to_bv 64 1050312) ltac:(ok_dat HX).
      stw (F_cfcdc _ HX) D_cfcdc (Z_to_bv 64 1050096) (Z_to_bv 64 1050096) ltac:(ok_dat HX).
      sn (F_cfce0 _ HX) D_cfce0.
      sn (F_cfce4 _ HX) D_cfce4.
      sn (F_e3530 _ HX) D_e3530.
      sn (F_e3534 _ HX) D_e3534.
      stepret (F_e3538 _ HX) D_e3538 (0xcfce8 : word) ltac:(pin; first [reflexivity | bveq]).
      stepb_ft (F_cfce8 _ HX) D_cfce8 ltac:(pin; cond_compute).
      stepb_ft (F_cfcec _ HX) D_cfcec ltac:(pin; cond_compute).
      sn (F_cfcf0 _ HX) D_cfcf0.
      stw (F_cfcf4 _ HX) D_cfcf4 (Z_to_bv 64 1182024) (Z_to_bv 64 1) ltac:(ok_dat HX).
      sn (F_cfcf8 _ HX) D_cfcf8.
      sn (F_cfcfc _ HX) D_cfcfc.
      stw (F_cfd00 _ HX) D_cfd00 (Z_to_bv 64 1050136) (Z_to_bv 64 2) ltac:(ok_dat HX).
      sn (F_cfd04 _ HX) D_cfd04.
      sn (F_cfd08 _ HX) D_cfd08.
      sn (F_cfd0c _ HX) D_cfd0c.
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 1050296 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 1182080 ->
    getr regs 18 = Z_to_bv 64 1050096 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 1050296) ->
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
        G (mkst regs' (0xcf8a4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1050128) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1050248) (word_to_le_bytes 8 (Z_to_bv 64 1182080))) (Z_to_bv 64 1050216) (word_to_le_bytes 8 (Z_to_bv 64 1050216))) (Z_to_bv 64 1050104) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050112) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050120) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (0xcfd14 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn (F_cfd14 _ HX) D_cfd14.
      stw (F_cfd18 _ HX) D_cfd18 (Z_to_bv 64 1050128) tid ltac:(ok_dat HX).
      stw (F_cfd1c _ HX) D_cfd1c (Z_to_bv 64 1050248) (Z_to_bv 64 1182080) ltac:(ok_dat HX).
      stw (F_cfd20 _ HX) D_cfd20 (Z_to_bv 64 1050216) (Z_to_bv 64 1050216) ltac:(ok_dat HX).
      sn (F_cfd24 _ HX) D_cfd24.
      ld_step (F_cfd28 _ HX) D_cfd28 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img (img_100980_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stw (F_cfd2c _ HX) D_cfd2c (Z_to_bv 64 1050104) (Z_to_bv 64 1050096) ltac:(ok_dat HX).
      stw (F_cfd30 _ HX) D_cfd30 (Z_to_bv 64 1050112) (Z_to_bv 64 1050096) ltac:(ok_dat HX).
      stw (F_cfd34 _ HX) D_cfd34 (Z_to_bv 64 1050120) (Z_to_bv 64 0) ltac:(ok_dat HX).
      sn (F_cfd38 _ HX) D_cfd38.
      ld_step (F_cfd40 _ HX) D_cfd40 (word_to_le_bytes 8 (Z_to_bv 64 850084)) (Z_to_bv 64 850084) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfd44 _ HX) D_cfd44 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfd48 _ HX) D_cfd48 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfd4c _ HX) D_cfd4c (word_to_le_bytes 8 (Z_to_bv 64 1182024)) (Z_to_bv 64 1182024) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfd50 _ HX) D_cfd50 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfd54 _ HX) D_cfd54 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfd58 _ HX) D_cfd58 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv (F_cfd5c _ HX) D_cfd5c (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret (F_cfd60 _ HX) D_cfd60 (0xcf8a4 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P4.

End Img.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
