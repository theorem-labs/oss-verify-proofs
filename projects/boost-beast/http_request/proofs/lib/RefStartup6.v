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

Section P8.
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

  Lemma fin_c9c : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = (Z_to_bv 64 422072) ->
    getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
    getr regs 3 = (Z_to_bv 64 67584) ->
    getr regs 4 = (Z_to_bv 64 599632) ->
    getr regs 8 = (Z_to_bv 64 500088) ->
    getr regs 9 = (Z_to_bv 64 500032) ->
    getr regs 10 = (Z_to_bv 64 176952) ->
    getr regs 11 = (Z_to_bv 64 1) ->
    getr regs 12 = (Z_to_bv 64 594724) ->
    getr regs 13 = (Z_to_bv 64 526504) ->
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
        getr regs' 9 = (Z_to_bv 64 500048) ->
        getr regs' 10 = (Z_to_bv 64 179752) ->
        getr regs' 11 = (Z_to_bv 64 1) ->
        getr regs' 12 = (Z_to_bv 64 594892) ->
        getr regs' 13 = (Z_to_bv 64 526616) ->
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
        G (mkst regs' (0x2be28 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 500088))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 527392) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 2])) (Z_to_bv 64 593056) (word_to_le_bytes 8 (Z_to_bv 64 526448))) (Z_to_bv 64 593064) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 2])) (Z_to_bv 64 593072) (word_to_le_bytes 8 (Z_to_bv 64 526504))) (Z_to_bv 64 593080) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 1])) (Z_to_bv 64 593097) ([Z_to_bv 8 2])) (Z_to_bv 64 593088) (word_to_le_bytes 8 (Z_to_bv 64 526560))) (Z_to_bv 64 593096) ([Z_to_bv 8 1])) (Z_to_bv 64 593097) ([Z_to_bv 8 1])) (Z_to_bv 64 593113) ([Z_to_bv 8 2])) (Z_to_bv 64 593104) (word_to_le_bytes 8 (Z_to_bv 64 526616))) (Z_to_bv 64 593112) ([Z_to_bv 8 1])) (Z_to_bv 64 593113) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x2b338 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 500088))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 527392) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 2])) (Z_to_bv 64 593056) (word_to_le_bytes 8 (Z_to_bv 64 526448))) (Z_to_bv 64 593064) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 2])) (Z_to_bv 64 593072) (word_to_le_bytes 8 (Z_to_bv 64 526504))) (Z_to_bv 64 593080) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 1]))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H13 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_2b338 D_2b338.  (* [comment removed for export] *)
      lb_step F_2b33c D_2b33c (Z_to_bv 8 0) ltac:(rd_img img_90cc8_1).  (* [comment removed for export] *)
      stepf F_2b340 D_2b340.  (* [comment removed for export] *)
      stepb_tk F_2b344 D_2b344 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sv F_2b34c D_2b34c (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2b350 D_2b350 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 422072) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_2b354 D_2b354.  (* [comment removed for export] *)
      sn F_2b358 D_2b358.  (* [comment removed for export] *)
      sn F_2b35c D_2b35c.  (* [comment removed for export] *)
      lb_step F_3c6a8 D_3c6a8 (Z_to_bv 8 0) ltac:(rd_img img_90cc8_1).  (* [comment removed for export] *)
      stepf F_3c6ac D_3c6ac.  (* [comment removed for export] *)
      stepb_tk F_3c6b0 D_3c6b0 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      lb_step F_3c6bc D_3c6bc (Z_to_bv 8 0) ltac:(rd_img img_90cc9_1).  (* [comment removed for export] *)
      sn F_3c6c0 D_3c6c0.  (* [comment removed for export] *)
      stepb_ft F_3c6c4 D_3c6c4 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_3c6c8 D_3c6c8.  (* [comment removed for export] *)
      stepb_ft F_3c6cc D_3c6cc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_3c6d0 D_3c6d0.  (* [comment removed for export] *)
      stw F_3c6d4 D_3c6d4 (Z_to_bv 64 593097) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3c6d8 D_3c6d8.  (* [comment removed for export] *)
      sn F_3c6dc D_3c6dc.  (* [comment removed for export] *)
      stepret F_3c6e0 D_3c6e0 (0x2b360 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b360 D_2b360.  (* [comment removed for export] *)
      ld_step F_2b364 D_2b364 (word_to_le_bytes 8 (Z_to_bv 64 422072)) (Z_to_bv 64 422072) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2b368 D_2b368 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepb_ft F_2b36c D_2b36c ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2b370 D_2b370.  (* [comment removed for export] *)
      sn F_2b374 D_2b374.  (* [comment removed for export] *)
      sn F_2b378 D_2b378.  (* [comment removed for export] *)
      sn F_2b37c D_2b37c.  (* [comment removed for export] *)
      sn F_2b380 D_2b380.  (* [comment removed for export] *)
      stw F_2b384 D_2b384 (Z_to_bv 64 593088) (Z_to_bv 64 526560) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2b388 D_2b388.  (* [comment removed for export] *)
      stepf F_3c6f8 D_3c6f8.  (* [comment removed for export] *)
      sn F_3c6fc D_3c6fc.  (* [comment removed for export] *)
      stw F_3c700 D_3c700 (Z_to_bv 64 593096) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3c704 D_3c704 (Z_to_bv 64 593097) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_3c708 D_3c708 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 177036)) (Z_to_bv 64 177036) ltac:(rd_img img_7a148_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2b38c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b38c D_2b38c.  (* [comment removed for export] *)
      lb_step F_2b390 D_2b390 (Z_to_bv 8 0) ltac:(rd_img img_90cd8_1).  (* [comment removed for export] *)
      stepf F_2b394 D_2b394.  (* [comment removed for export] *)
      stepb_tk F_2b398 D_2b398 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sv F_2b3a0 D_2b3a0 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2b3a4 D_2b3a4 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 422072) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_2b3a8 D_2b3a8.  (* [comment removed for export] *)
      sn F_2b3ac D_2b3ac.  (* [comment removed for export] *)
      sn F_2b3b0 D_2b3b0.  (* [comment removed for export] *)
      lb_step F_3c6a8 D_3c6a8 (Z_to_bv 8 0) ltac:(rd_img img_90cd8_1).  (* [comment removed for export] *)
      stepf F_3c6ac D_3c6ac.  (* [comment removed for export] *)
      stepb_tk F_3c6b0 D_3c6b0 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      lb_step F_3c6bc D_3c6bc (Z_to_bv 8 0) ltac:(rd_img img_90cd9_1).  (* [comment removed for export] *)
      sn F_3c6c0 D_3c6c0.  (* [comment removed for export] *)
      stepb_ft F_3c6c4 D_3c6c4 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_3c6c8 D_3c6c8.  (* [comment removed for export] *)
      stepb_ft F_3c6cc D_3c6cc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_3c6d0 D_3c6d0.  (* [comment removed for export] *)
      stw F_3c6d4 D_3c6d4 (Z_to_bv 64 593113) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3c6d8 D_3c6d8.  (* [comment removed for export] *)
      sn F_3c6dc D_3c6dc.  (* [comment removed for export] *)
      stepret F_3c6e0 D_3c6e0 (0x2b3b4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2b3b4 D_2b3b4.  (* [comment removed for export] *)
      ld_step F_2b3b8 D_2b3b8 (word_to_le_bytes 8 (Z_to_bv 64 422072)) (Z_to_bv 64 422072) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2b3bc D_2b3bc (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepb_ft F_2b3c0 D_2b3c0 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2b3c4 D_2b3c4.  (* [comment removed for export] *)
      sn F_2b3c8 D_2b3c8.  (* [comment removed for export] *)
      sn F_2b3cc D_2b3cc.  (* [comment removed for export] *)
      sn F_2b3d0 D_2b3d0.  (* [comment removed for export] *)
      sn F_2b3d4 D_2b3d4.  (* [comment removed for export] *)
      stw F_2b3d8 D_2b3d8 (Z_to_bv 64 593104) (Z_to_bv 64 526616) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2b3dc D_2b3dc.  (* [comment removed for export] *)
      stepf F_3c6f8 D_3c6f8.  (* [comment removed for export] *)
      sn F_3c6fc D_3c6fc.  (* [comment removed for export] *)
      stw F_3c700 D_3c700 (Z_to_bv 64 593112) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_3c704 D_3c704 (Z_to_bv 64 593113) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_3c708 D_3c708 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 179752)) (Z_to_bv 64 179752) ltac:(rd_img img_7a150_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2be28 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9d : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = (Z_to_bv 64 422072) ->
    getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
    getr regs 3 = (Z_to_bv 64 67584) ->
    getr regs 4 = (Z_to_bv 64 599632) ->
    getr regs 8 = (Z_to_bv 64 500088) ->
    getr regs 9 = (Z_to_bv 64 500048) ->
    getr regs 10 = (Z_to_bv 64 179752) ->
    getr regs 11 = (Z_to_bv 64 1) ->
    getr regs 12 = (Z_to_bv 64 594892) ->
    getr regs 13 = (Z_to_bv 64 526616) ->
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
        getr regs' 1 = (Z_to_bv 64 422264) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 599632) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 13 = (Z_to_bv 64 526616) ->
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
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
        G (mkst regs' (0x2ac68 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 500088))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 527392) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 2])) (Z_to_bv 64 593056) (word_to_le_bytes 8 (Z_to_bv 64 526448))) (Z_to_bv 64 593064) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 2])) (Z_to_bv 64 593072) (word_to_le_bytes 8 (Z_to_bv 64 526504))) (Z_to_bv 64 593080) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 1])) (Z_to_bv 64 593097) ([Z_to_bv 8 2])) (Z_to_bv 64 593088) (word_to_le_bytes 8 (Z_to_bv 64 526560))) (Z_to_bv 64 593096) ([Z_to_bv 8 1])) (Z_to_bv 64 593097) ([Z_to_bv 8 1])) (Z_to_bv 64 593113) ([Z_to_bv 8 2])) (Z_to_bv 64 593104) (word_to_le_bytes 8 (Z_to_bv 64 526616))) (Z_to_bv 64 593112) ([Z_to_bv 8 1])) (Z_to_bv 64 593113) ([Z_to_bv 8 1])) (Z_to_bv 64 593128) ([Z_to_bv 8 1])) (Z_to_bv 64 593144) ([Z_to_bv 8 1])) (Z_to_bv 64 593160) ([Z_to_bv 8 1])) (Z_to_bv 64 593176) ([Z_to_bv 8 1])) (Z_to_bv 64 593192) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x2be28 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421740))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 731360))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 421748))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 422248))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 500088))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 422072))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 730728) (word_to_le_bytes 8 (Z_to_bv 64 495912))) (Z_to_bv 64 730736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730752) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 731376) (word_to_le_bytes 8 (Z_to_bv 64 730720))) (Z_to_bv 64 731400) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 730744) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 730760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 731384) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 731392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 599656) (word_to_le_bytes 8 (Z_to_bv 64 601680))) (Z_to_bv 64 599648) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 599624) (word_to_le_bytes 8 (Z_to_bv 64 599648))) (Z_to_bv 64 599432) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 731360) ([Z_to_bv 8 1])) (Z_to_bv 64 599472) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 599464) (word_to_le_bytes 4 tid)) (Z_to_bv 64 599584) (word_to_le_bytes 8 (Z_to_bv 64 731416))) (Z_to_bv 64 599552) (word_to_le_bytes 8 (Z_to_bv 64 599552))) (Z_to_bv 64 599440) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599448) (word_to_le_bytes 8 (Z_to_bv 64 599432))) (Z_to_bv 64 599456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 730768) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 730772) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 730769) ([Z_to_bv 8 0])) (Z_to_bv 64 599616) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 527392) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 2])) (Z_to_bv 64 593056) (word_to_le_bytes 8 (Z_to_bv 64 526448))) (Z_to_bv 64 593064) ([Z_to_bv 8 1])) (Z_to_bv 64 593065) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 2])) (Z_to_bv 64 593072) (word_to_le_bytes 8 (Z_to_bv 64 526504))) (Z_to_bv 64 593080) ([Z_to_bv 8 1])) (Z_to_bv 64 593081) ([Z_to_bv 8 1])) (Z_to_bv 64 593097) ([Z_to_bv 8 2])) (Z_to_bv 64 593088) (word_to_le_bytes 8 (Z_to_bv 64 526560))) (Z_to_bv 64 593096) ([Z_to_bv 8 1])) (Z_to_bv 64 593097) ([Z_to_bv 8 1])) (Z_to_bv 64 593113) ([Z_to_bv 8 2])) (Z_to_bv 64 593104) (word_to_le_bytes 8 (Z_to_bv 64 526616))) (Z_to_bv 64 593112) ([Z_to_bv 8 1])) (Z_to_bv 64 593113) ([Z_to_bv 8 1]))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H13 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_2be28 D_2be28.  (* [comment removed for export] *)
      lb_step F_2be2c D_2be2c (Z_to_bv 8 0) ltac:(rd_img img_90ce8_1).  (* [comment removed for export] *)
      stepb_tk F_2be30 D_2be30 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2be38 D_2be38.  (* [comment removed for export] *)
      stw F_2be3c D_2be3c (Z_to_bv 64 593128) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2be40 D_2be40 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 179780)) (Z_to_bv 64 179780) ltac:(rd_img img_7a158_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2be44 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2be44 D_2be44.  (* [comment removed for export] *)
      lb_step F_2be48 D_2be48 (Z_to_bv 8 0) ltac:(rd_img img_90cf8_1).  (* [comment removed for export] *)
      stepb_tk F_2be4c D_2be4c ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2be54 D_2be54.  (* [comment removed for export] *)
      stw F_2be58 D_2be58 (Z_to_bv 64 593144) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2be5c D_2be5c (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 179808)) (Z_to_bv 64 179808) ltac:(rd_img img_7a160_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2be60 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2be60 D_2be60.  (* [comment removed for export] *)
      lb_step F_2be64 D_2be64 (Z_to_bv 8 0) ltac:(rd_img img_90d08_1).  (* [comment removed for export] *)
      stepb_tk F_2be68 D_2be68 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2be70 D_2be70.  (* [comment removed for export] *)
      stw F_2be74 D_2be74 (Z_to_bv 64 593160) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2be78 D_2be78 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 179836)) (Z_to_bv 64 179836) ltac:(rd_img img_7a168_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2be7c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2be7c D_2be7c.  (* [comment removed for export] *)
      lb_step F_2be80 D_2be80 (Z_to_bv 8 0) ltac:(rd_img img_90d18_1).  (* [comment removed for export] *)
      stepb_tk F_2be84 D_2be84 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2be8c D_2be8c.  (* [comment removed for export] *)
      stw F_2be90 D_2be90 (Z_to_bv 64 593176) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2be94 D_2be94 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_tk F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670b0 D_670b0 (word_to_le_bytes 8 (Z_to_bv 64 179864)) (Z_to_bv 64 179864) ltac:(rd_img img_7a170_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_670b4 D_670b4 (0x2be98 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2be98 D_2be98.  (* [comment removed for export] *)
      lb_step F_2be9c D_2be9c (Z_to_bv 8 0) ltac:(rd_img img_90d28_1).  (* [comment removed for export] *)
      stepb_tk F_2bea0 D_2bea0 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2bea8 D_2bea8.  (* [comment removed for export] *)
      stw F_2beac D_2beac (Z_to_bv 64 593192) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2beb0 D_2beb0 (0x670b8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_670b8 D_670b8.  (* [comment removed for export] *)
      stepb_ft F_670bc D_670bc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_670c0 D_670c0 (word_to_le_bytes 8 (Z_to_bv 64 422248)) (Z_to_bv 64 422248) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_670c4 D_670c4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_670c8 D_670c8 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_670cc D_670cc (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_670d0 D_670d0 (0x67168 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_67168 D_67168 (argc_w av).  (* [comment removed for export] *)
      sv F_6716c D_6716c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_67170 D_67170 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_67174 D_67174 (0x2ac68 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
