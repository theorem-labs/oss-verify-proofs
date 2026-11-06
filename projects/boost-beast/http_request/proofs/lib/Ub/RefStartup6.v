(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import StartupTac ArgvEnv RefLayout RefMemcpyLib StepFence Ub_code_2bf8c_2d06c Ub_code_40464_40a60 Ub_code_6b184_6b4a8.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefImg RefImgX RefStartupDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

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
    getr regs 1 = (Z_to_bv 64 439268) ->
    getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
    getr regs 3 = (Z_to_bv 64 67584) ->
    getr regs 4 = (Z_to_bv 64 616816) ->
    getr regs 8 = (Z_to_bv 64 517280) ->
    getr regs 9 = (Z_to_bv 64 517224) ->
    getr regs 10 = (Z_to_bv 64 180696) ->
    getr regs 11 = (Z_to_bv 64 1) ->
    getr regs 12 = (Z_to_bv 64 610756) ->
    getr regs 13 = (Z_to_bv 64 543696) ->
    getr regs 18 = (Z_to_bv 64 178924) ->
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
        getr regs' 1 = (Z_to_bv 64 439268) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 616816) ->
        getr regs' 8 = (Z_to_bv 64 517280) ->
        getr regs' 9 = (Z_to_bv 64 517240) ->
        getr regs' 10 = (Z_to_bv 64 183636) ->
        getr regs' 11 = (Z_to_bv 64 1) ->
        getr regs' 12 = (Z_to_bv 64 610924) ->
        getr regs' 13 = (Z_to_bv 64 543808) ->
        getr regs' 18 = (Z_to_bv 64 178924) ->
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
        G (mkst regs' (0x2cd54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 439444))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 517280))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 544576) ([Z_to_bv 8 1])) (Z_to_bv 64 610249) ([Z_to_bv 8 2])) (Z_to_bv 64 610240) (word_to_le_bytes 8 (Z_to_bv 64 543640))) (Z_to_bv 64 610248) ([Z_to_bv 8 1])) (Z_to_bv 64 610249) ([Z_to_bv 8 1])) (Z_to_bv 64 610265) ([Z_to_bv 8 2])) (Z_to_bv 64 610256) (word_to_le_bytes 8 (Z_to_bv 64 543696))) (Z_to_bv 64 610264) ([Z_to_bv 8 1])) (Z_to_bv 64 610265) ([Z_to_bv 8 1])) (Z_to_bv 64 610281) ([Z_to_bv 8 2])) (Z_to_bv 64 610272) (word_to_le_bytes 8 (Z_to_bv 64 543752))) (Z_to_bv 64 610280) ([Z_to_bv 8 1])) (Z_to_bv 64 610281) ([Z_to_bv 8 1])) (Z_to_bv 64 610297) ([Z_to_bv 8 2])) (Z_to_bv 64 610288) (word_to_le_bytes 8 (Z_to_bv 64 543808))) (Z_to_bv 64 610296) ([Z_to_bv 8 1])) (Z_to_bv 64 610297) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x2c1d8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 439444))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 517280))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 544576) ([Z_to_bv 8 1])) (Z_to_bv 64 610249) ([Z_to_bv 8 2])) (Z_to_bv 64 610240) (word_to_le_bytes 8 (Z_to_bv 64 543640))) (Z_to_bv 64 610248) ([Z_to_bv 8 1])) (Z_to_bv 64 610249) ([Z_to_bv 8 1])) (Z_to_bv 64 610265) ([Z_to_bv 8 2])) (Z_to_bv 64 610256) (word_to_le_bytes 8 (Z_to_bv 64 543696))) (Z_to_bv 64 610264) ([Z_to_bv 8 1])) (Z_to_bv 64 610265) ([Z_to_bv 8 1]))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H13 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_2c1d8 D_2c1d8.  (* [comment removed for export] *)
      lb_step F_2c1dc D_2c1dc (Z_to_bv 8 0) ltac:(rd_img img_94fe8_1).  (* [comment removed for export] *)
      stepf F_2c1e0 D_2c1e0.  (* [comment removed for export] *)
      stepb_tk F_2c1e4 D_2c1e4 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sv F_2c1ec D_2c1ec (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2c1f0 D_2c1f0 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 439268) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_2c1f4 D_2c1f4.  (* [comment removed for export] *)
      sn F_2c1f8 D_2c1f8.  (* [comment removed for export] *)
      sn F_2c1fc D_2c1fc.  (* [comment removed for export] *)
      lb_step F_409fc D_409fc (Z_to_bv 8 0) ltac:(rd_img img_94fe8_1).  (* [comment removed for export] *)
      stepf F_40a00 D_40a00.  (* [comment removed for export] *)
      stepb_tk F_40a04 D_40a04 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      lb_step F_40a10 D_40a10 (Z_to_bv 8 0) ltac:(rd_img img_94fe9_1).  (* [comment removed for export] *)
      sn F_40a14 D_40a14.  (* [comment removed for export] *)
      stepb_ft F_40a18 D_40a18 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_40a1c D_40a1c.  (* [comment removed for export] *)
      stepb_ft F_40a20 D_40a20 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_40a24 D_40a24.  (* [comment removed for export] *)
      stw F_40a28 D_40a28 (Z_to_bv 64 610281) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_40a2c D_40a2c.  (* [comment removed for export] *)
      sn F_40a30 D_40a30.  (* [comment removed for export] *)
      stepret F_40a34 D_40a34 (0x2c200 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2c200 D_2c200.  (* [comment removed for export] *)
      ld_step F_2c204 D_2c204 (word_to_le_bytes 8 (Z_to_bv 64 439268)) (Z_to_bv 64 439268) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2c208 D_2c208 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepb_ft F_2c20c D_2c20c ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2c210 D_2c210.  (* [comment removed for export] *)
      sn F_2c214 D_2c214.  (* [comment removed for export] *)
      sn F_2c218 D_2c218.  (* [comment removed for export] *)
      sn F_2c21c D_2c21c.  (* [comment removed for export] *)
      sn F_2c220 D_2c220.  (* [comment removed for export] *)
      stw F_2c224 D_2c224 (Z_to_bv 64 610272) (Z_to_bv 64 543752) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2c228 D_2c228.  (* [comment removed for export] *)
      stepf F_40a4c D_40a4c.  (* [comment removed for export] *)
      sn F_40a50 D_40a50.  (* [comment removed for export] *)
      stw F_40a54 D_40a54 (Z_to_bv 64 610280) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_40a58 D_40a58 (Z_to_bv 64 610281) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_40a5c D_40a5c (0x6b3e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b3e4 D_6b3e4.  (* [comment removed for export] *)
      stepb_tk F_6b3e8 D_6b3e8 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_6b3dc D_6b3dc (word_to_le_bytes 8 (Z_to_bv 64 180780)) (Z_to_bv 64 180780) ltac:(rd_img img_7e470_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_6b3e0 D_6b3e0 (0x2c22c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2c22c D_2c22c.  (* [comment removed for export] *)
      lb_step F_2c230 D_2c230 (Z_to_bv 8 0) ltac:(rd_img img_94ff8_1).  (* [comment removed for export] *)
      stepf F_2c234 D_2c234.  (* [comment removed for export] *)
      stepb_tk F_2c238 D_2c238 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sv F_2c240 D_2c240 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_2c244 D_2c244 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 439268) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_2c248 D_2c248.  (* [comment removed for export] *)
      sn F_2c24c D_2c24c.  (* [comment removed for export] *)
      sn F_2c250 D_2c250.  (* [comment removed for export] *)
      lb_step F_409fc D_409fc (Z_to_bv 8 0) ltac:(rd_img img_94ff8_1).  (* [comment removed for export] *)
      stepf F_40a00 D_40a00.  (* [comment removed for export] *)
      stepb_tk F_40a04 D_40a04 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      lb_step F_40a10 D_40a10 (Z_to_bv 8 0) ltac:(rd_img img_94ff9_1).  (* [comment removed for export] *)
      sn F_40a14 D_40a14.  (* [comment removed for export] *)
      stepb_ft F_40a18 D_40a18 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_40a1c D_40a1c.  (* [comment removed for export] *)
      stepb_ft F_40a20 D_40a20 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_40a24 D_40a24.  (* [comment removed for export] *)
      stw F_40a28 D_40a28 (Z_to_bv 64 610297) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_40a2c D_40a2c.  (* [comment removed for export] *)
      sn F_40a30 D_40a30.  (* [comment removed for export] *)
      stepret F_40a34 D_40a34 (0x2c254 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2c254 D_2c254.  (* [comment removed for export] *)
      ld_step F_2c258 D_2c258 (word_to_le_bytes 8 (Z_to_bv 64 439268)) (Z_to_bv 64 439268) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_2c25c D_2c25c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepb_ft F_2c260 D_2c260 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2c264 D_2c264.  (* [comment removed for export] *)
      sn F_2c268 D_2c268.  (* [comment removed for export] *)
      sn F_2c26c D_2c26c.  (* [comment removed for export] *)
      sn F_2c270 D_2c270.  (* [comment removed for export] *)
      sn F_2c274 D_2c274.  (* [comment removed for export] *)
      stw F_2c278 D_2c278 (Z_to_bv 64 610288) (Z_to_bv 64 543808) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_2c27c D_2c27c.  (* [comment removed for export] *)
      stepf F_40a4c D_40a4c.  (* [comment removed for export] *)
      sn F_40a50 D_40a50.  (* [comment removed for export] *)
      stw F_40a54 D_40a54 (Z_to_bv 64 610296) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_40a58 D_40a58 (Z_to_bv 64 610297) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_40a5c D_40a5c (0x6b3e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b3e4 D_6b3e4.  (* [comment removed for export] *)
      stepb_tk F_6b3e8 D_6b3e8 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_6b3dc D_6b3dc (word_to_le_bytes 8 (Z_to_bv 64 183636)) (Z_to_bv 64 183636) ltac:(rd_img img_7e478_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_6b3e0 D_6b3e0 (0x2cd54 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9d : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = (Z_to_bv 64 439268) ->
    getr regs 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
    getr regs 3 = (Z_to_bv 64 67584) ->
    getr regs 4 = (Z_to_bv 64 616816) ->
    getr regs 8 = (Z_to_bv 64 517280) ->
    getr regs 9 = (Z_to_bv 64 517240) ->
    getr regs 10 = (Z_to_bv 64 183636) ->
    getr regs 11 = (Z_to_bv 64 1) ->
    getr regs 12 = (Z_to_bv 64 610924) ->
    getr regs 13 = (Z_to_bv 64 543808) ->
    getr regs 18 = (Z_to_bv 64 178924) ->
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
        getr regs' 1 = (Z_to_bv 64 439460) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 616816) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 13 = (Z_to_bv 64 543808) ->
        getr regs' 18 = (Z_to_bv 64 178924) ->
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
        G (mkst regs' (0x2baec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 439444))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 517280))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 544576) ([Z_to_bv 8 1])) (Z_to_bv 64 610249) ([Z_to_bv 8 2])) (Z_to_bv 64 610240) (word_to_le_bytes 8 (Z_to_bv 64 543640))) (Z_to_bv 64 610248) ([Z_to_bv 8 1])) (Z_to_bv 64 610249) ([Z_to_bv 8 1])) (Z_to_bv 64 610265) ([Z_to_bv 8 2])) (Z_to_bv 64 610256) (word_to_le_bytes 8 (Z_to_bv 64 543696))) (Z_to_bv 64 610264) ([Z_to_bv 8 1])) (Z_to_bv 64 610265) ([Z_to_bv 8 1])) (Z_to_bv 64 610281) ([Z_to_bv 8 2])) (Z_to_bv 64 610272) (word_to_le_bytes 8 (Z_to_bv 64 543752))) (Z_to_bv 64 610280) ([Z_to_bv 8 1])) (Z_to_bv 64 610281) ([Z_to_bv 8 1])) (Z_to_bv 64 610297) ([Z_to_bv 8 2])) (Z_to_bv 64 610288) (word_to_le_bytes 8 (Z_to_bv 64 543808))) (Z_to_bv 64 610296) ([Z_to_bv 8 1])) (Z_to_bv 64 610297) ([Z_to_bv 8 1])) (Z_to_bv 64 610312) ([Z_to_bv 8 1])) (Z_to_bv 64 610328) ([Z_to_bv 8 1])) (Z_to_bv 64 610344) ([Z_to_bv 8 1])) (Z_to_bv 64 610360) ([Z_to_bv 8 1])) (Z_to_bv 64 610376) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x2cd54 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438936))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 748544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 438944))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 439444))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 517280))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 439268))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 747912) (word_to_le_bytes 8 (Z_to_bv 64 513104))) (Z_to_bv 64 747920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 748560) (word_to_le_bytes 8 (Z_to_bv 64 747904))) (Z_to_bv 64 748584) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 747928) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 747944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 748568) (word_to_le_bytes 8 (Z_to_bv 64 232))) (Z_to_bv 64 748576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 616840) (word_to_le_bytes 8 (Z_to_bv 64 618864))) (Z_to_bv 64 616832) (word_to_le_bytes 8 (Z_to_bv 64 1))) (Z_to_bv 64 616808) (word_to_le_bytes 8 (Z_to_bv 64 616832))) (Z_to_bv 64 616616) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 748544) ([Z_to_bv 8 1])) (Z_to_bv 64 616656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 616648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 616768) (word_to_le_bytes 8 (Z_to_bv 64 748600))) (Z_to_bv 64 616736) (word_to_le_bytes 8 (Z_to_bv 64 616736))) (Z_to_bv 64 616624) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616632) (word_to_le_bytes 8 (Z_to_bv 64 616616))) (Z_to_bv 64 616640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 747952) [rbn rnd 0; rbn rnd 1; rbn rnd 2; rbn rnd 3]) (Z_to_bv 64 747956) [rbn rnd 4; rbn rnd 5; rbn rnd 6; rbn rnd 7]) (Z_to_bv 64 747953) ([Z_to_bv 8 0])) (Z_to_bv 64 616800) (word_to_le_bytes 8 (canary_w rnd))) (Z_to_bv 64 544576) ([Z_to_bv 8 1])) (Z_to_bv 64 610249) ([Z_to_bv 8 2])) (Z_to_bv 64 610240) (word_to_le_bytes 8 (Z_to_bv 64 543640))) (Z_to_bv 64 610248) ([Z_to_bv 8 1])) (Z_to_bv 64 610249) ([Z_to_bv 8 1])) (Z_to_bv 64 610265) ([Z_to_bv 8 2])) (Z_to_bv 64 610256) (word_to_le_bytes 8 (Z_to_bv 64 543696))) (Z_to_bv 64 610264) ([Z_to_bv 8 1])) (Z_to_bv 64 610265) ([Z_to_bv 8 1])) (Z_to_bv 64 610281) ([Z_to_bv 8 2])) (Z_to_bv 64 610272) (word_to_le_bytes 8 (Z_to_bv 64 543752))) (Z_to_bv 64 610280) ([Z_to_bv 8 1])) (Z_to_bv 64 610281) ([Z_to_bv 8 1])) (Z_to_bv 64 610297) ([Z_to_bv 8 2])) (Z_to_bv 64 610288) (word_to_le_bytes 8 (Z_to_bv 64 543808))) (Z_to_bv 64 610296) ([Z_to_bv 8 1])) (Z_to_bv 64 610297) ([Z_to_bv 8 1]))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H13 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_2cd54 D_2cd54.  (* [comment removed for export] *)
      lb_step F_2cd58 D_2cd58 (Z_to_bv 8 0) ltac:(rd_img img_95008_1).  (* [comment removed for export] *)
      stepb_tk F_2cd5c D_2cd5c ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2cd64 D_2cd64.  (* [comment removed for export] *)
      stw F_2cd68 D_2cd68 (Z_to_bv 64 610312) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2cd6c D_2cd6c (0x6b3e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b3e4 D_6b3e4.  (* [comment removed for export] *)
      stepb_tk F_6b3e8 D_6b3e8 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_6b3dc D_6b3dc (word_to_le_bytes 8 (Z_to_bv 64 183664)) (Z_to_bv 64 183664) ltac:(rd_img img_7e480_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_6b3e0 D_6b3e0 (0x2cd70 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2cd70 D_2cd70.  (* [comment removed for export] *)
      lb_step F_2cd74 D_2cd74 (Z_to_bv 8 0) ltac:(rd_img img_95018_1).  (* [comment removed for export] *)
      stepb_tk F_2cd78 D_2cd78 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2cd80 D_2cd80.  (* [comment removed for export] *)
      stw F_2cd84 D_2cd84 (Z_to_bv 64 610328) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2cd88 D_2cd88 (0x6b3e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b3e4 D_6b3e4.  (* [comment removed for export] *)
      stepb_tk F_6b3e8 D_6b3e8 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_6b3dc D_6b3dc (word_to_le_bytes 8 (Z_to_bv 64 183692)) (Z_to_bv 64 183692) ltac:(rd_img img_7e488_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_6b3e0 D_6b3e0 (0x2cd8c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2cd8c D_2cd8c.  (* [comment removed for export] *)
      lb_step F_2cd90 D_2cd90 (Z_to_bv 8 0) ltac:(rd_img img_95028_1).  (* [comment removed for export] *)
      stepb_tk F_2cd94 D_2cd94 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2cd9c D_2cd9c.  (* [comment removed for export] *)
      stw F_2cda0 D_2cda0 (Z_to_bv 64 610344) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2cda4 D_2cda4 (0x6b3e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b3e4 D_6b3e4.  (* [comment removed for export] *)
      stepb_tk F_6b3e8 D_6b3e8 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_6b3dc D_6b3dc (word_to_le_bytes 8 (Z_to_bv 64 183720)) (Z_to_bv 64 183720) ltac:(rd_img img_7e490_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_6b3e0 D_6b3e0 (0x2cda8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2cda8 D_2cda8.  (* [comment removed for export] *)
      lb_step F_2cdac D_2cdac (Z_to_bv 8 0) ltac:(rd_img img_95038_1).  (* [comment removed for export] *)
      stepb_tk F_2cdb0 D_2cdb0 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2cdb8 D_2cdb8.  (* [comment removed for export] *)
      stw F_2cdbc D_2cdbc (Z_to_bv 64 610360) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2cdc0 D_2cdc0 (0x6b3e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b3e4 D_6b3e4.  (* [comment removed for export] *)
      stepb_tk F_6b3e8 D_6b3e8 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_6b3dc D_6b3dc (word_to_le_bytes 8 (Z_to_bv 64 183748)) (Z_to_bv 64 183748) ltac:(rd_img img_7e498_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_6b3e0 D_6b3e0 (0x2cdc4 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_2cdc4 D_2cdc4.  (* [comment removed for export] *)
      lb_step F_2cdc8 D_2cdc8 (Z_to_bv 8 0) ltac:(rd_img img_95048_1).  (* [comment removed for export] *)
      stepb_tk F_2cdcc D_2cdcc ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      sn F_2cdd4 D_2cdd4.  (* [comment removed for export] *)
      stw F_2cdd8 D_2cdd8 (Z_to_bv 64 610376) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      stepret F_2cddc D_2cddc (0x6b3e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_6b3e4 D_6b3e4.  (* [comment removed for export] *)
      stepb_ft F_6b3e8 D_6b3e8 ltac:(pin; cond_compute).  (* [comment removed for export] *) (* [comment removed for export] *)
      ld_step F_6b3ec D_6b3ec (word_to_le_bytes 8 (Z_to_bv 64 439444)) (Z_to_bv 64 439444) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b3f0 D_6b3f0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_6b3f4 D_6b3f4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_6b3f8 D_6b3f8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_6b3fc D_6b3fc (0x6b494 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_6b494 D_6b494 (argc_w av).  (* [comment removed for export] *)
      sv F_6b498 D_6b498 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_6b49c D_6b49c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_6b4a0 D_6b4a0 (0x2baec : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
