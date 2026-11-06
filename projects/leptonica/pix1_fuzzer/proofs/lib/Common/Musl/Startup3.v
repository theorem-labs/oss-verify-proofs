(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_15000_16000 RCode_1d000_1d348.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Musl Require Import StartupBase StartupDefs.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := rl_segs.
Abbreviation RPH := RPH0.

(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P4.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variables (hw : word) (drw : EntryDraw).   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw drw)) (only parsing).

  Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = rl dF_15170 0x15280 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 8 = pn_w sp0 av ev ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = rl dA_2f848 0x2f868 ->
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
        getr regs' 9 = (rl dA_2f848 0x2f868) ->
        getr regs' 10 = (Z_to_bv 64 56) ->
        getr regs' 11 = (rl dA_2f6b8s 0x2f6b8) ->
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
        G (mkst regs' (rl dF_15490 0x15518) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (rl dF_15490 0x15490) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_15490 D_15490 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
      stw F_15494 D_15494 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (rl dF_15170 0x15280) ltac:(ok_win HJ).
      stw F_15498 D_15498 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
      stw F_1549c D_1549c (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
      stw F_154a0 D_154a0 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (rl dA_2f848 0x2f868) ltac:(ok_win HJ).
      stw F_154a4 D_154a4 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_154a8 D_154a8 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_154ac D_154ac (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      ld_step F_154b0 D_154b0 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_154b4 D_154b4.
      sn F_154b8 D_154b8.
      sn F_154bc D_154bc.
      sn F_154c0 D_154c0.
      stepb_ft F_154c4 D_154c4 ltac:(pin; rl_cond).
      sn F_154c8 D_154c8.
      sn F_154cc D_154cc.
      sn F_154d0 D_154d0.
      ld_step F_154d4 D_154d4 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_154d8 D_154d8 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_154dc D_154dc.
      sn F_154e0 D_154e0.
      ld_step F_154e4 D_154e4 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_1f620_4) ltac:(vm_compute; reflexivity).
      ld_step F_154e8 D_154e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_1e368_8) ltac:(apply bytes_le_to_Z_8).
      sn F_154ec D_154ec.
      sn F_154f0 D_154f0.
      sn F_154f4 D_154f4.
      sn F_154f8 D_154f8.
      sn F_154fc D_154fc.
      sn F_15500 D_15500.
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = rl dA_2f848 0x2f868 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = rl dA_2f6b8s 0x2f6b8 ->
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
        getr regs' 9 = (rl dA_2f848 0x2f868) ->
        getr regs' 10 = (Z_to_bv 64 56) ->
        getr regs' 11 = (rl dA_2f6b8s 0x2f6b8) ->
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
        G (mkst regs' (rl dF_15490 0x15518) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (rl dF_15490 0x15518) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img imgL_10040_4) ltac:(vm_compute; reflexivity).
      stepb_tk F_1551c D_1551c ltac:(pin; rl_cond).
      ld_step F_15504 D_15504 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img imgL_10050_8) ltac:(apply bytes_le_to_Z_8).
      sn F_15508 D_15508.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img imgL_10078_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_tk F_15540 D_15540 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img imgL_100b0_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_tk F_15540 D_15540 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img imgL_100e8_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_tk F_15540 D_15540 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img imgL_10120_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_tk F_15540 D_15540 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = rl dA_2f848 0x2f868 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = rl dA_2f6b8s 0x2f6b8 ->
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
        getr regs' 9 = (rl dA_2f848 0x2f868) ->
        getr regs' 11 = (rl dA_2f6b8s 0x2f6b8) ->
        getr regs' 17 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (rl dF_15490 0x15568) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (rl dF_15490 0x15518) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img imgL_10158_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_tk F_15540 D_15540 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img imgL_10190_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_tk F_15540 D_15540 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img imgL_101c8_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_ft F_15540 D_15540 ltac:(pin; rl_cond).
      ld_step F_15544 D_15544 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img imgL_101f0_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_15548 D_15548 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img imgL_10200_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_tk F_15540 D_15540 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_ft F_15514 D_15514 ltac:(pin; rl_cond).
      ld_step F_15518 D_15518 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img imgL_10238_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_1551c D_1551c ltac:(pin; rl_cond).
      stepb_tk F_15520 D_15520 ltac:(pin; rl_cond).
      sn F_15534 D_15534.
      stepb_ft F_15538 D_15538 ltac:(pin; rl_cond).
      sn F_1553c D_1553c.
      stepb_tk F_15540 D_15540 ltac:(pin; rl_cond).
      sn F_15560 D_15560.
      sn F_15564 D_15564.
      sn F_1550c D_1550c.
      sn F_15510 D_15510.
      stepb_tk F_15514 D_15514 ltac:(pin; rl_cond).
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
