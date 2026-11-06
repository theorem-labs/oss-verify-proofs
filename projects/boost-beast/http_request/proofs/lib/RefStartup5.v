(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg RefImgX RefStartupDefs RefMemcpyLib StepFence
  Ref_code_2ab1c_2b108 Ref_code_2b290_2b3e0 Ref_code_2b3e0_2c4d8 Ref_code_3bdf0_3c70c
  Ref_code_66e58_6717c Ref_code_6717c_678ec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P7.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rnd : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rnd)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 rnd av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma fin_c9a : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = (Z_to_bv 64 422072) ->
    getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
    getr regs 3 = (Z_to_bv 64 67584) ->
    getr regs 4 = (Z_to_bv 64 599632) ->
    getr regs 8 = (Z_to_bv 64 500088) ->
    getr regs 9 = (Z_to_bv 64 500008) ->
    getr regs 18 = (Z_to_bv 64 175208) ->
    getr regs 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
    getr regs 20 = (Z_to_bv 64 0) ->
    getr regs 21 = (Z_to_bv 64 0) ->
    getr regs 22 = (Z_to_bv 64 0) ->
    getr regs 23 = (Z_to_bv 64 0) ->
    getr regs 24 = (Z_to_bv 64 0) ->
    getr regs 25 = (Z_to_bv 64 0) ->
    getr regs 26 = (Z_to_bv 64 0) ->
    getr regs 27 = (Z_to_bv 64 0) ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 422072) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 599632) ->
        getr regs' 8 = (Z_to_bv 64 500088) ->
        getr regs' 9 = (Z_to_bv 64 500016) ->
        getr regs' 10 = (Z_to_bv 64 176784) ->
        getr regs' 11 = (Z_to_bv 64 527392) ->
        getr regs' 18 = (Z_to_bv 64 175208) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs' ->
        G (mkst regs' (0x2b290 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 500088))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 527392) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x2ab64 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_2ab64 D_2ab64 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2ab68 D_2ab68 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 422072) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2ab6c D_2ab6c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 500088) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_2ab70 D_2ab70 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_2ab74 D_2ab74.  (* [comment removed for export] *)
      sn F_2ab78 D_2ab78.  (* [comment removed for export] *)
      lb_step F_2ab7c D_2ab7c (Z_to_bv 8 0) ltac:(rd_img img_80c20_1).  (* [comment removed for export] *)
      sn F_2ab80 D_2ab80.  (* [comment removed for export] *)
      stepb_tk F_2ab84 D_2ab84 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2ab90 D_2ab90.  (* [comment removed for export] *)
      sn F_2ab94 D_2ab94.  (* [comment removed for export] *)
      sn F_2ab98 D_2ab98.  (* [comment removed for export] *)
      stw F_2ab9c D_2ab9c (Z_to_bv 64 527392) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2aba0 D_2aba0.  (* [comment removed for export] *)
      ld_step F_2aba4 D_2aba4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_7f6f8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_2aba8 D_2aba8 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_2abc8 D_2abc8 (word_to_le_bytes 8 (Z_to_bv 64 422072)) (Z_to_bv 64 422072) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2abcc D_2abcc (word_to_le_bytes 8 (Z_to_bv 64 500088)) (Z_to_bv 64 500088) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2abd0 D_2abd0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_2abd4 D_2abd4 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 176784)) (Z_to_bv 64 176784) ltac:(rd_img img_7a130_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2b290 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9b : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = (Z_to_bv 64 422072) ->
    getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
    getr regs 3 = (Z_to_bv 64 67584) ->
    getr regs 4 = (Z_to_bv 64 599632) ->
    getr regs 8 = (Z_to_bv 64 500088) ->
    getr regs 9 = (Z_to_bv 64 500016) ->
    getr regs 10 = (Z_to_bv 64 176784) ->
    getr regs 11 = (Z_to_bv 64 527392) ->
    getr regs 18 = (Z_to_bv 64 175208) ->
    getr regs 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
    getr regs 20 = (Z_to_bv 64 0) ->
    getr regs 21 = (Z_to_bv 64 0) ->
    getr regs 22 = (Z_to_bv 64 0) ->
    getr regs 23 = (Z_to_bv 64 0) ->
    getr regs 24 = (Z_to_bv 64 0) ->
    getr regs 25 = (Z_to_bv 64 0) ->
    getr regs 26 = (Z_to_bv 64 0) ->
    getr regs 27 = (Z_to_bv 64 0) ->
    (forall regs',
        getr regs' 1 = (Z_to_bv 64 422072) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 599632) ->
        getr regs' 8 = (Z_to_bv 64 500088) ->
        getr regs' 9 = (Z_to_bv 64 500032) ->
        getr regs' 10 = (Z_to_bv 64 176952) ->
        getr regs' 11 = (Z_to_bv 64 1) ->
        getr regs' 12 = (Z_to_bv 64 594724) ->
        getr regs' 13 = (Z_to_bv 64 526504) ->
        getr regs' 18 = (Z_to_bv 64 175208) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 9; 10; 11; 12; 13]%list) regs regs' ->
        G (mkst regs' (0x2b338 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 500088))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 527392) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 2])) (Z_to_bv 64 593056) (word_to_le_bytes 8 (Z_to_bv 64 526448))) (Z_to_bv 64 593064) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 2])) (Z_to_bv 64 593072) (word_to_le_bytes 8 (Z_to_bv 64 526504))) (Z_to_bv 64 593080) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x2b290 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 500088))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 527392) ([Z_to_bv 8 1]))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_2b290 D_2b290.  (* [comment removed for export] *)
      lb_step F_2b294 D_2b294 (Z_to_bv 8 0) ltac:(rd_img img_90ca8_1).  (* [comment removed for export] *)
      stepf F_2b298 D_2b298.  (* [comment removed for export] *)
      stepb_tk F_2b29c D_2b29c ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sv F_2b2a4 D_2b2a4 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2b2a8 D_2b2a8 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 422072) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_2b2ac D_2b2ac.  (* [comment removed for export] *)
      sn F_2b2b0 D_2b2b0.  (* [comment removed for export] *)
      sn F_2b2b4 D_2b2b4.  (* [comment removed for export] *)
      lb_step F_3c6a8 D_3c6a8 (Z_to_bv 8 0) ltac:(rd_img img_90ca8_1).  (* [comment removed for export] *)
      stepf F_3c6ac D_3c6ac.  (* [comment removed for export] *)
      stepb_tk F_3c6b0 D_3c6b0 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      lb_step F_3c6bc D_3c6bc (Z_to_bv 8 0) ltac:(rd_img img_90ca9_1).  (* [comment removed for export] *)
      sn F_3c6c0 D_3c6c0.  (* [comment removed for export] *)
      stepb_ft F_3c6c4 D_3c6c4 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_3c6c8 D_3c6c8.  (* [comment removed for export] *)
      stepb_ft F_3c6cc D_3c6cc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_3c6d0 D_3c6d0.  (* [comment removed for export] *)
      stw F_3c6d4 D_3c6d4 (Z_to_bv 64 593065) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3c6d8 D_3c6d8.  (* [comment removed for export] *)
      sn F_3c6dc D_3c6dc.  (* [comment removed for export] *)
      stepret F_3c6e0 D_3c6e0 (0x2b2b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b2b8 D_2b2b8.  (* [comment removed for export] *)
      ld_step F_2b2bc D_2b2bc (word_to_le_bytes 8 (Z_to_bv 64 422072)) (Z_to_bv 64 422072) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2b2c0 D_2b2c0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepb_ft F_2b2c4 D_2b2c4 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2b2c8 D_2b2c8.  (* [comment removed for export] *)
      sn F_2b2cc D_2b2cc.  (* [comment removed for export] *)
      sn F_2b2d0 D_2b2d0.  (* [comment removed for export] *)
      sn F_2b2d4 D_2b2d4.  (* [comment removed for export] *)
      sn F_2b2d8 D_2b2d8.  (* [comment removed for export] *)
      stw F_2b2dc D_2b2dc (Z_to_bv 64 593056) (Z_to_bv 64 526448) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2b2e0 D_2b2e0.  (* [comment removed for export] *)
      stepf F_3c6f8 D_3c6f8.  (* [comment removed for export] *)
      sn F_3c6fc D_3c6fc.  (* [comment removed for export] *)
      stw F_3c700 D_3c700 (Z_to_bv 64 593064) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3c704 D_3c704 (Z_to_bv 64 593065) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_3c708 D_3c708 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 176868)) (Z_to_bv 64 176868) ltac:(rd_img img_7a138_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2b2e4 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b2e4 D_2b2e4.  (* [comment removed for export] *)
      lb_step F_2b2e8 D_2b2e8 (Z_to_bv 8 0) ltac:(rd_img img_90cb8_1).  (* [comment removed for export] *)
      stepf F_2b2ec D_2b2ec.  (* [comment removed for export] *)
      stepb_tk F_2b2f0 D_2b2f0 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sv F_2b2f8 D_2b2f8 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2b2fc D_2b2fc (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 422072) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_2b300 D_2b300.  (* [comment removed for export] *)
      sn F_2b304 D_2b304.  (* [comment removed for export] *)
      sn F_2b308 D_2b308.  (* [comment removed for export] *)
      lb_step F_3c6a8 D_3c6a8 (Z_to_bv 8 0) ltac:(rd_img img_90cb8_1).  (* [comment removed for export] *)
      stepf F_3c6ac D_3c6ac.  (* [comment removed for export] *)
      stepb_tk F_3c6b0 D_3c6b0 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      lb_step F_3c6bc D_3c6bc (Z_to_bv 8 0) ltac:(rd_img img_90cb9_1).  (* [comment removed for export] *)
      sn F_3c6c0 D_3c6c0.  (* [comment removed for export] *)
      stepb_ft F_3c6c4 D_3c6c4 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_3c6c8 D_3c6c8.  (* [comment removed for export] *)
      stepb_ft F_3c6cc D_3c6cc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_3c6d0 D_3c6d0.  (* [comment removed for export] *)
      stw F_3c6d4 D_3c6d4 (Z_to_bv 64 593081) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3c6d8 D_3c6d8.  (* [comment removed for export] *)
      sn F_3c6dc D_3c6dc.  (* [comment removed for export] *)
      stepret F_3c6e0 D_3c6e0 (0x2b30c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b30c D_2b30c.  (* [comment removed for export] *)
      ld_step F_2b310 D_2b310 (word_to_le_bytes 8 (Z_to_bv 64 422072)) (Z_to_bv 64 422072) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2b314 D_2b314 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepb_ft F_2b318 D_2b318 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2b31c D_2b31c.  (* [comment removed for export] *)
      sn F_2b320 D_2b320.  (* [comment removed for export] *)
      sn F_2b324 D_2b324.  (* [comment removed for export] *)
      sn F_2b328 D_2b328.  (* [comment removed for export] *)
      sn F_2b32c D_2b32c.  (* [comment removed for export] *)
      stw F_2b330 D_2b330 (Z_to_bv 64 593072) (Z_to_bv 64 526504) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2b334 D_2b334.  (* [comment removed for export] *)
      stepf F_3c6f8 D_3c6f8.  (* [comment removed for export] *)
      sn F_3c6fc D_3c6fc.  (* [comment removed for export] *)
      stw F_3c700 D_3c700 (Z_to_bv 64 593080) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3c704 D_3c704 (Z_to_bv 64 593081) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_3c708 D_3c708 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 176952)) (Z_to_bv 64 176952) ltac:(rd_img img_7a140_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2b338 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P7.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
