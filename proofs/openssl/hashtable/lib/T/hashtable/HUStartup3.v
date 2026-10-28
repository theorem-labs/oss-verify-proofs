(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  StartupTac ArgvEnv RefLayout HUImg HUStartupDefs HU_code_26b000_26c000 HU_code_27a000_27b000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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

  Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 2821964 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 8 = pn_w sp0 av ev ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = Z_to_bv 64 3480952 ->
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
        getr regs' 9 = (Z_to_bv 64 3480952) ->
        getr regs' 10 = (Z_to_bv 64 56) ->
        getr regs' 11 = (Z_to_bv 64 3480304) ->
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
        G (mkst regs' (0x2b12bc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x2b1234 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_26b63c D_26b63c (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
      stw F_26b640 D_26b640 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 2821964) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b644 D_26b644 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b648 D_26b648 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b64c D_26b64c (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 3480952) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b650 D_26b650 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b654 D_26b654 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_26b658 D_26b658 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      ld_step F_26b65c D_26b65c (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26b660 D_26b660.  (* [comment removed for export] *)
      sn F_26b664 D_26b664.  (* [comment removed for export] *)
      sn F_26b668 D_26b668.  (* [comment removed for export] *)
      sn F_26b66c D_26b66c.  (* [comment removed for export] *)
      stepb_ft F_26b670 D_26b670 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b674 D_26b674.  (* [comment removed for export] *)
      sn F_26b678 D_26b678.  (* [comment removed for export] *)
      sn F_26b67c D_26b67c.  (* [comment removed for export] *)
      ld_step F_26b680 D_26b680 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b684 D_26b684 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26b688 D_26b688.  (* [comment removed for export] *)
      sn F_26b68c D_26b68c.  (* [comment removed for export] *)
      ld_step F_26b690 D_26b690 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_2d92d0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      ld_step F_26b694 D_26b694 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2d7580_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26b698 D_26b698.  (* [comment removed for export] *)
      sn F_26b69c D_26b69c.  (* [comment removed for export] *)
      sn F_26b6a0 D_26b6a0.  (* [comment removed for export] *)
      sn F_26b6a4 D_26b6a4.  (* [comment removed for export] *)
      sn F_26b6a8 D_26b6a8.  (* [comment removed for export] *)
      sn F_26b6ac D_26b6ac.  (* [comment removed for export] *)
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
    getr regs 9 = Z_to_bv 64 3480952 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 3480304 ->
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
        getr regs' 9 = (Z_to_bv 64 3480952) ->
        getr regs' 10 = (Z_to_bv 64 56) ->
        getr regs' 11 = (Z_to_bv 64 3480304) ->
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
        G (mkst regs' (0x2b12bc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x2b12bc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6b0 D_26b6b0 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26b6b4 D_26b6b4.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_tk F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_tk F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_tk F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_tk F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
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
    getr regs 9 = Z_to_bv 64 3480952 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 3480304 ->
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
        getr regs' 9 = (Z_to_bv 64 3480952) ->
        getr regs' 11 = (Z_to_bv 64 3480304) ->
        getr regs' 17 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0x2b130c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x2b12bc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_tk F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_tk F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_ft F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6f0 D_26b6f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_26b6f4 D_26b6f4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_tk F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_ft F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b6c4 D_26b6c4 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_26b6c8 D_26b6c8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_26b6cc D_26b6cc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e0 D_26b6e0.  (* [comment removed for export] *)
      stepb_ft F_26b6e4 D_26b6e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b6e8 D_26b6e8.  (* [comment removed for export] *)
      stepb_tk F_26b6ec D_26b6ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b70c D_26b70c.  (* [comment removed for export] *)
      sn F_26b710 D_26b710.  (* [comment removed for export] *)
      sn F_26b6b8 D_26b6b8.  (* [comment removed for export] *)
      sn F_26b6bc D_26b6bc.  (* [comment removed for export] *)
      stepb_tk F_26b6c0 D_26b6c0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = Z_to_bv 64 3480952 ->
    getr regs 11 = Z_to_bv 64 3480304 ->
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
        getr regs' 4 = (Z_to_bv 64 3349224) ->
        getr regs' 10 = (Z_to_bv 64 3480304) ->
        getr regs' 11 = (Z_to_bv 64 3481008) ->
        getr regs' 12 = (Z_to_bv 64 0) ->
        getr regs' 13 = (Z_to_bv 64 3349016) ->
        getr regs' 15 = (Z_to_bv 64 18446744073706202392) ->
        getr regs' 17 = (Z_to_bv 64 96) ->
        getr regs' 18 = (Z_to_bv 64 3349024) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 3349240) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (0x2b1490 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (0x2b130c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { stepb_tk F_26b714 D_26b714 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26b74c D_26b74c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ebe60_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b750 D_26b750 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ebe70_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b754 D_26b754 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ebe78_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26b758 D_26b758.  (* [comment removed for export] *)
      sn F_26b75c D_26b75c.  (* [comment removed for export] *)
      sn F_26b760 D_26b760.  (* [comment removed for export] *)
      sn F_26b764 D_26b764.  (* [comment removed for export] *)
      sn F_26b768 D_26b768.  (* [comment removed for export] *)
      sn F_26b76c D_26b76c.  (* [comment removed for export] *)
      sn F_26b770 D_26b770.  (* [comment removed for export] *)
      stw F_26b774 D_26b774 (Z_to_bv 64 3480336) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_26b778 D_26b778 (Z_to_bv 64 3480352) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_ft F_26b77c D_26b77c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b780 D_26b780.  (* [comment removed for export] *)
      stw F_26b784 D_26b784 (Z_to_bv 64 3480344) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_26b788 D_26b788.  (* [comment removed for export] *)
      sn F_26b78c D_26b78c.  (* [comment removed for export] *)
      sn F_26b790 D_26b790.  (* [comment removed for export] *)
      sn F_26b794 D_26b794.  (* [comment removed for export] *)
      sn F_26b798 D_26b798.  (* [comment removed for export] *)
      sn F_26b79c D_26b79c.  (* [comment removed for export] *)
      stw F_26b7a0 D_26b7a0 (Z_to_bv 64 3480976) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_26b7a4 D_26b7a4 (Z_to_bv 64 3480984) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_tk F_26b7e4 D_26b7e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b7e8 D_26b7e8.  (* [comment removed for export] *)
      ld_step F_26b7ec D_26b7ec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ec238_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b7f0 D_26b7f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ec250_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_26b7f4 D_26b7f4.  (* [comment removed for export] *)
      sn F_26b7f8 D_26b7f8.  (* [comment removed for export] *)
      sn F_26b7fc D_26b7fc.  (* [comment removed for export] *)
      sn F_26b800 D_26b800.  (* [comment removed for export] *)
      sn F_26b804 D_26b804.  (* [comment removed for export] *)
      sn F_26b808 D_26b808.  (* [comment removed for export] *)
      sn F_26b80c D_26b80c.  (* [comment removed for export] *)
      sn F_26b810 D_26b810.  (* [comment removed for export] *)
      sn F_26b814 D_26b814.  (* [comment removed for export] *)
      sn F_26b818 D_26b818.  (* [comment removed for export] *)
      sn F_26b81c D_26b81c.  (* [comment removed for export] *)
      stepb_tk F_26b820 D_26b820 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stw F_26b868 D_26b868 (Z_to_bv 64 3349240) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_26b86c D_26b86c (Z_to_bv 64 3349216) (Z_to_bv 64 3349240) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_26b870 D_26b870 (Z_to_bv 64 3349024) (Z_to_bv 64 3349024) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_26b874 D_26b874.  (* [comment removed for export] *)
      sn F_26b878 D_26b878.  (* [comment removed for export] *)
      sn F_27a36c D_27a36c.  (* [comment removed for export] *)
      sn F_27a370 D_27a370.  (* [comment removed for export] *)
      stepret F_27a374 D_27a374 (0x2b1468 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      stepb_ft F_26b87c D_26b87c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_ft F_26b880 D_26b880 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26b884 D_26b884.  (* [comment removed for export] *)
      stw F_26b888 D_26b888 (Z_to_bv 64 3480952) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_26b88c D_26b88c.  (* [comment removed for export] *)
      sn F_26b890 D_26b890.  (* [comment removed for export] *)
      stw F_26b894 D_26b894 (Z_to_bv 64 3349064) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_26b898 D_26b898.  (* [comment removed for export] *)
      sn F_26b89c D_26b89c.  (* [comment removed for export] *)
      sn F_26b8a0 D_26b8a0.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 3349224 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 3481008 ->
    getr regs 18 = Z_to_bv 64 3349024 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 3349224) ->
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
        G (mkst regs' (0x2b0f4c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 3349056) (word_to_le_bytes 4 tid)) (Z_to_bv 64 3349176) (word_to_le_bytes 8 (Z_to_bv 64 3481008))) (Z_to_bv 64 3349144) (word_to_le_bytes 8 (Z_to_bv 64 3349144))) (Z_to_bv 64 3349032) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349040) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3349048) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (0x2b1494 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 2821964))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 3480952))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 3480336) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480352) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3480344) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3480976) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 3480984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 3349240) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 3349216) (word_to_le_bytes 8 (Z_to_bv 64 3349240))) (Z_to_bv 64 3349024) (word_to_le_bytes 8 (Z_to_bv 64 3349024))) (Z_to_bv 64 3480952) ([Z_to_bv 8 1])) (Z_to_bv 64 3349064) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_26b8a8 D_26b8a8.  (* [comment removed for export] *)
      stw F_26b8ac D_26b8ac (Z_to_bv 64 3349056) tid ltac:(ok_data).  (* [comment removed for export] *)
      stw F_26b8b0 D_26b8b0 (Z_to_bv 64 3349176) (Z_to_bv 64 3481008) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_26b8b4 D_26b8b4 (Z_to_bv 64 3349144) (Z_to_bv 64 3349144) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_26b8b8 D_26b8b8.  (* [comment removed for export] *)
      ld_step F_26b8bc D_26b8bc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_2ec210_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_26b8c0 D_26b8c0 (Z_to_bv 64 3349032) (Z_to_bv 64 3349024) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_26b8c4 D_26b8c4 (Z_to_bv 64 3349040) (Z_to_bv 64 3349024) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_26b8c8 D_26b8c8 (Z_to_bv 64 3349048) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_26b8cc D_26b8cc.  (* [comment removed for export] *)
      ld_step F_26b8d4 D_26b8d4 (word_to_le_bytes 8 (Z_to_bv 64 2821964)) (Z_to_bv 64 2821964) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b8d8 D_26b8d8 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b8dc D_26b8dc (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b8e0 D_26b8e0 (word_to_le_bytes 8 (Z_to_bv 64 3480952)) (Z_to_bv 64 3480952) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b8e4 D_26b8e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b8e8 D_26b8e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_26b8ec D_26b8ec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_26b8f0 D_26b8f0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_26b8f4 D_26b8f4 (0x2b0f4c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P4.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
