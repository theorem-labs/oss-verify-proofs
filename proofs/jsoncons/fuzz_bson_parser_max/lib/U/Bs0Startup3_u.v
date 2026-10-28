(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import StartupTac ArgvEnv RefLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Img_u Bs0StartupDefs_u
  Bs0_code_991c0_99470_u Bs0_code_r59000_59c90_u.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require PropExec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation RND := (ed_random rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j (at_random_bytes RND))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac RD_RND j :=
    eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    lazymatch goal with
    | |- rdn _ (wbytes (wbytes (wbytes ?DD (Z_to_bv 64 ?g) _) _ _) _ _) _ _ = _ =>
        let H := fresh in
        pose proof (rd_guard_at SEGS DD RND g ltac:(lia) ltac:(lia)) as H;
        cbn [Z.add Pos.add Pos.succ] in H; exact H
    end.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 632216 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 8 = (pn_w sp0 av ev) ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = Z_to_bv 64 959056 ->
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
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 5 = Z_to_bv 64 0 ->
        getr regs' 7 = Z_to_bv 64 7 ->
        getr regs' 9 = Z_to_bv 64 959056 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 958408 ->
        getr regs' 13 = Z_to_bv 64 10 ->
        getr regs' 15 = Z_to_bv 64 65600 ->
        getr regs' 16 = Z_to_bv 64 6 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        getr regs' 28 = Z_to_bv 64 1685382481 ->
        getr regs' 29 = Z_to_bv 64 65600 ->
        getr regs' 30 = Z_to_bv 64 131072 ->
        regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
        G (mkst regs' (0x9a830 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x9a7a8 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_991c0 D_991c0 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
      stw F_991c4 D_991c4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 632216) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_991c8 D_991c8 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_991cc D_991cc (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_991d0 D_991d0 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 959056) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_991d4 D_991d4 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_991d8 D_991d8 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_991dc D_991dc (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      ld_step F_991e0 D_991e0 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_991e4 D_991e4.  (* [comment removed for export] *)
      sn F_991e8 D_991e8.  (* [comment removed for export] *)
      sn F_991ec D_991ec.  (* [comment removed for export] *)
      sn F_991f0 D_991f0.  (* [comment removed for export] *)
      stepb_ft F_991f4 D_991f4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_991f8 D_991f8.  (* [comment removed for export] *)
      sn F_991fc D_991fc.  (* [comment removed for export] *)
      sn F_99200 D_99200.  (* [comment removed for export] *)
      ld_step F_99204 D_99204 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99208 D_99208 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_9920c D_9920c.  (* [comment removed for export] *)
      sn F_99210 D_99210.  (* [comment removed for export] *)
      ld_step F_99214 D_99214 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_b6ea8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      ld_step F_99218 D_99218 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b5a20_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_9921c D_9921c.  (* [comment removed for export] *)
      sn F_99220 D_99220.  (* [comment removed for export] *)
      sn F_99224 D_99224.  (* [comment removed for export] *)
      sn F_99228 D_99228.  (* [comment removed for export] *)
      sn F_9922c D_9922c.  (* [comment removed for export] *)
      sn F_99230 D_99230.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = Z_to_bv 64 959056 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 958408 ->
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
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 5 = Z_to_bv 64 0 ->
        getr regs' 7 = Z_to_bv 64 7 ->
        getr regs' 9 = Z_to_bv 64 959056 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 958408 ->
        getr regs' 13 = Z_to_bv 64 4 ->
        getr regs' 16 = Z_to_bv 64 6 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        getr regs' 28 = Z_to_bv 64 1685382481 ->
        getr regs' 29 = Z_to_bv 64 65936 ->
        getr regs' 30 = Z_to_bv 64 131072 ->
        regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0x9a830 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x9a830 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99234 D_99234 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_99238 D_99238.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_tk F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_tk F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_tk F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_tk F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_tk F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = Z_to_bv 64 959056 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 958408 ->
    getr regs 13 = Z_to_bv 64 4 ->
    getr regs 16 = Z_to_bv 64 6 ->
    getr regs 17 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    getr regs 28 = Z_to_bv 64 1685382481 ->
    getr regs 29 = Z_to_bv 64 65936 ->
    getr regs 30 = Z_to_bv 64 131072 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 9 = Z_to_bv 64 959056 ->
        getr regs' 11 = Z_to_bv 64 958408 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0x9a880 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x9a830 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_tk F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_ft F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99274 D_99274 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_99278 D_99278 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_tk F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_ft F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_99248 D_99248 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_9924c D_9924c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_99250 D_99250 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99264 D_99264.  (* [comment removed for export] *)
      stepb_ft F_99268 D_99268 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_9926c D_9926c.  (* [comment removed for export] *)
      stepb_tk F_99270 D_99270 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99290 D_99290.  (* [comment removed for export] *)
      sn F_99294 D_99294.  (* [comment removed for export] *)
      sn F_9923c D_9923c.  (* [comment removed for export] *)
      sn F_99240 D_99240.  (* [comment removed for export] *)
      stepb_tk F_99244 D_99244 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = Z_to_bv 64 959056 ->
    getr regs 11 = Z_to_bv 64 958408 ->
    getr regs 17 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 827328 ->
        getr regs' 10 = Z_to_bv 64 958408 ->
        getr regs' 11 = Z_to_bv 64 959112 ->
        getr regs' 12 = Z_to_bv 64 0 ->
        getr regs' 13 = Z_to_bv 64 827120 ->
        getr regs' 14 = Z_to_bv 64 0 ->
        getr regs' 15 = Z_to_bv 64 18446744073708724288 ->
        getr regs' 17 = Z_to_bv 64 96 ->
        getr regs' 18 = Z_to_bv 64 827128 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (0x9aa04 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (0x9a880 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { stepb_tk F_99298 D_99298 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_992d0 D_992d0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c88d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_992d4 D_992d4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c88e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_992d8 D_992d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c88f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_992dc D_992dc.  (* [comment removed for export] *)
      sn F_992e0 D_992e0.  (* [comment removed for export] *)
      sn F_992e4 D_992e4.  (* [comment removed for export] *)
      sn F_992e8 D_992e8.  (* [comment removed for export] *)
      sn F_992ec D_992ec.  (* [comment removed for export] *)
      sn F_992f0 D_992f0.  (* [comment removed for export] *)
      sn F_992f4 D_992f4.  (* [comment removed for export] *)
      stw F_992f8 D_992f8 (Z_to_bv 64 958440) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_992fc D_992fc (Z_to_bv 64 958456) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_ft F_99300 D_99300 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99304 D_99304.  (* [comment removed for export] *)
      stw F_99308 D_99308 (Z_to_bv 64 958448) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_9930c D_9930c.  (* [comment removed for export] *)
      sn F_99310 D_99310.  (* [comment removed for export] *)
      sn F_99314 D_99314.  (* [comment removed for export] *)
      sn F_99318 D_99318.  (* [comment removed for export] *)
      sn F_9931c D_9931c.  (* [comment removed for export] *)
      sn F_99320 D_99320.  (* [comment removed for export] *)
      stw F_99324 D_99324 (Z_to_bv 64 959080) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_99328 D_99328 (Z_to_bv 64 959088) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_tk F_9932c D_9932c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_99360 D_99360.  (* [comment removed for export] *)
      ld_step F_99364 D_99364 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c8cb0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99368 D_99368 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c8cc8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_9936c D_9936c.  (* [comment removed for export] *)
      sn F_99370 D_99370.  (* [comment removed for export] *)
      sn F_99374 D_99374.  (* [comment removed for export] *)
      sn F_99378 D_99378.  (* [comment removed for export] *)
      sn F_9937c D_9937c.  (* [comment removed for export] *)
      sn F_99380 D_99380.  (* [comment removed for export] *)
      sn F_99384 D_99384.  (* [comment removed for export] *)
      sn F_99388 D_99388.  (* [comment removed for export] *)
      sn F_9938c D_9938c.  (* [comment removed for export] *)
      sn F_99390 D_99390.  (* [comment removed for export] *)
      sn F_99394 D_99394.  (* [comment removed for export] *)
      stepb_tk F_99398 D_99398 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stw F_993e0 D_993e0 (Z_to_bv 64 827344) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_993e4 D_993e4 (Z_to_bv 64 827320) (Z_to_bv 64 827344) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_993e8 D_993e8 (Z_to_bv 64 827128) (Z_to_bv 64 827128) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_993ec D_993ec.  (* [comment removed for export] *)
      sn F_993f0 D_993f0.  (* [comment removed for export] *)
      sn F_ac50c D_ac50c.  (* [comment removed for export] *)
      sn F_ac510 D_ac510.  (* [comment removed for export] *)
      stepret F_ac514 D_ac514 (0x9a9dc : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      stepb_ft F_993f4 D_993f4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_ft F_993f8 D_993f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_993fc D_993fc.  (* [comment removed for export] *)
      stw F_99400 D_99400 (Z_to_bv 64 959056) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_99404 D_99404.  (* [comment removed for export] *)
      sn F_99408 D_99408.  (* [comment removed for export] *)
      stw F_9940c D_9940c (Z_to_bv 64 827168) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_99410 D_99410.  (* [comment removed for export] *)
      sn F_99414 D_99414.  (* [comment removed for export] *)
      sn F_99418 D_99418.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 827328 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 959112 ->
    getr regs 18 = Z_to_bv 64 827128 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 827328 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
        G (mkst regs' (0x9a598 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (0x9aa08 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_99420 D_99420.  (* [comment removed for export] *)
      stw F_99424 D_99424 (Z_to_bv 64 827160) tid ltac:(ok_data).  (* [comment removed for export] *)
      stw F_99428 D_99428 (Z_to_bv 64 827280) (Z_to_bv 64 959112) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_9942c D_9942c (Z_to_bv 64 827248) (Z_to_bv 64 827248) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_99430 D_99430.  (* [comment removed for export] *)
      ld_step F_99434 D_99434 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c8c88_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_99438 D_99438 (Z_to_bv 64 827136) (Z_to_bv 64 827128) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_9943c D_9943c (Z_to_bv 64 827144) (Z_to_bv 64 827128) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_99440 D_99440 (Z_to_bv 64 827152) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_99444 D_99444.  (* [comment removed for export] *)
      ld_step F_9944c D_9944c (word_to_le_bytes 8 (Z_to_bv 64 632216)) (Z_to_bv 64 632216) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99450 D_99450 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99454 D_99454 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99458 D_99458 (word_to_le_bytes 8 (Z_to_bv 64 959056)) (Z_to_bv 64 959056) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_9945c D_9945c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99460 D_99460 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99464 D_99464 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_99468 D_99468 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_9946c D_9946c (0x9a598 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
