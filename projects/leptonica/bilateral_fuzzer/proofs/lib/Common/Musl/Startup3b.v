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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_15000_16000 RCode_1d000_1d348.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import StartupBase StartupDefs.
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

  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = rl dA_2f848 0x2f868 ->
    getr regs 11 = rl dA_2f6b8 0x2f6b8 ->
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
        getr regs' 4 = (rl dA_2f6b0 0x2f7b8) ->
        getr regs' 10 = (rl dA_2f6b8 0x2f6b8) ->
        getr regs' 11 = (rl dA_2f848 0x2f8a0) ->
        getr regs' 12 = (Z_to_bv 64 0) ->
        getr regs' 13 = (rl dA_2f6b0 0x2f6e8) ->
        getr regs' 14 = (Z_to_bv 64 0) ->
        getr regs' 15 = v_sub (Z_to_bv 64 18446744073709551416) (rl dA_2f6b0 0x2f6f0) ->  (* [comment removed for export] *)
        getr regs' 17 = (Z_to_bv 64 96) ->
        getr regs' 18 = (rl dA_2f6b0 0x2f6f0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (rl dF_15490 0x156ec) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (rl dF_15490 0x15568) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { stepb_tk F_15568 D_15568 ltac:(pin; rl_cond).
      ld_step F_155a0 D_155a0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2f6c8_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_155a4 D_155a4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2f6d8_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_155a8 D_155a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2f6e0_8) ltac:(apply bytes_le_to_Z_8).
      sn F_155ac D_155ac.
      sn F_155b0 D_155b0.
      sn F_155b4 D_155b4.
      sn F_155b8 D_155b8.
      sn F_155bc D_155bc.
      sn F_155c0 D_155c0.
      sn F_155c4 D_155c4.
      stw F_155c8 D_155c8 (rl dA_2f6b8 0x2f6d8) (Z_to_bv 64 0) ltac:(ok_data).
      stw F_155cc D_155cc (rl dA_2f6b8 0x2f6e8) (Z_to_bv 64 0) ltac:(ok_data).
      stepb_ft F_155d0 D_155d0 ltac:(pin; rl_cond).
      sn F_155d4 D_155d4.
      stw F_155d8 D_155d8 (rl dA_2f6b8 0x2f6e0) (Z_to_bv 64 8) ltac:(ok_data).
      sn F_155dc D_155dc.
      sn F_155e0 D_155e0.
      sn F_155e4 D_155e4.
      sn F_155e8 D_155e8.
      sn F_155ec D_155ec.
      sn F_155f0 D_155f0.
      stw F_155f4 D_155f4 (rl dA_2f848 0x2f880) (Z_to_bv 64 224) ltac:(ok_data).
      stw F_155f8 D_155f8 (rl dA_2f848 0x2f888) (Z_to_bv 64 8) ltac:(ok_data).
      stepb_tk F_155fc D_155fc ltac:(pin; rl_cond).
      sn F_15630 D_15630.
      ld_step F_15634 D_15634 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2f878_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15638 D_15638 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2f890_8) ltac:(apply bytes_le_to_Z_8).
      sn F_1563c D_1563c.
      sn F_15640 D_15640.
      sn F_15644 D_15644.
      sn F_15648 D_15648.
      sn F_1564c D_1564c.
      rl_and7.
      sn F_15650 D_15650.
      sn F_15654 D_15654.
      sn F_15658 D_15658.
      sn F_1565c D_1565c.
      sn F_15660 D_15660.
      MuslTac.rl_addfold.
      MuslTac.rl_wrap.
      sn F_15664 D_15664.
      stepb_tk F_15668 D_15668 ltac:(pin; rl_cond).
      stw F_156b0 D_156b0 (rl dA_2f6b0 0x2f7c8) (Z_to_bv 64 0) ltac:(ok_data).
      stw F_156b4 D_156b4 (rl dA_2f6b0 0x2f7b0) (rl dA_2f6b0 0x2f7c8) ltac:(ok_data).
      stw F_156b8 D_156b8 (rl dA_2f6b0 0x2f6f0) (rl dA_2f6b0 0x2f6f0) ltac:(ok_data).
      sn F_156bc D_156bc.
      sn F_156c0 D_156c0.
      sn F_1d2a8 D_1d2a8.
      sn F_1d2ac D_1d2ac.
      stepretK F_1d2b0 D_1d2b0 F_156c4 ltac:(pin; first [reflexivity | bveq]).
      stepb_ft F_156c4 D_156c4 ltac:(pin; rl_cond).
      stepb_ft F_156c8 D_156c8 ltac:(pin; rl_cond).
      sn F_156cc D_156cc.
      stw F_156d0 D_156d0 (rl dA_2f848 0x2f868) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_156d4 D_156d4.
      sn F_156d8 D_156d8.
      stw F_156dc D_156dc (rl dA_2f6b0 0x2f718) (Z_to_bv 64 2) ltac:(ok_data).
      sn F_156e0 D_156e0.
      sn F_156e4 D_156e4.
      sn F_156e8 D_156e8.
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
    getr regs 10 = tid ->
    getr regs 11 = rl dA_2f848 0x2f8a0 ->
    getr regs 18 = rl dA_2f6b0 0x2f6f0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (rl dA_2f6b0 0x2f7b8) ->
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
        G (mkst regs' (rl dF_15170 0x15280) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (rl dF_15490 0x156f0) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_156f0 D_156f0.
      stw F_156f4 D_156f4 (rl dA_2f6b0 0x2f710) tid ltac:(ok_data).
      stw F_156f8 D_156f8 (rl dA_2f6b0 0x2f788) (rl dA_2f848 0x2f8a0) ltac:(ok_data).
      stw F_156fc D_156fc (rl dA_2f6b0 0x2f768) (rl dA_2f6b0 0x2f768) ltac:(ok_data).
      sn F_15700 D_15700.
      ld_step F_15704 D_15704 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2f850_8) ltac:(apply bytes_le_to_Z_8).
      stw F_15708 D_15708 (rl dA_2f6b0 0x2f6f8) (rl dA_2f6b0 0x2f6f0) ltac:(ok_data).
      stw F_1570c D_1570c (rl dA_2f6b0 0x2f700) (rl dA_2f6b0 0x2f6f0) ltac:(ok_data).
      stw F_15710 D_15710 (rl dA_2f6b0 0x2f708) (Z_to_bv 64 0) ltac:(ok_data).
      sn F_15714 D_15714.
      ld_step F_1571c D_1571c (word_to_le_bytes 8 (rl dF_15170 0x15280)) (rl dF_15170 0x15280) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15720 D_15720 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15724 D_15724 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15728 D_15728 (word_to_le_bytes 8 (rl dA_2f848 0x2f868)) (rl dA_2f848 0x2f868) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1572c D_1572c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15730 D_15730 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15734 D_15734 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15738 D_15738 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepretK F_1573c D_1573c F_15280 ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
