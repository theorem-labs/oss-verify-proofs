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
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import StartupTac ArgvEnv RefLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Img_u5 Pm6StartupDefs_u5
  Pm6_code_a9980_a9c30_u5 Pm6_code_bc000_bd000_u5     .
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.

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
    getr regs 1 = Z_to_bv 64 708796 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 8 = (pn_w sp0 av ev) ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = Z_to_bv 64 1036960 ->
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
        getr regs' 9 = Z_to_bv 64 1036960 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 1036312 ->
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
        G (mkst regs' (0xad354 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xad2cc : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_a9980 D_a9980 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
      stw F_a9984 D_a9984 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 708796) ltac:(ok_win HJ).
      stw F_a9988 D_a9988 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
      stw F_a998c D_a998c (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
      stw F_a9990 D_a9990 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 1036960) ltac:(ok_win HJ).
      stw F_a9994 D_a9994 (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a9998 D_a9998 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a999c D_a999c (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      ld_step F_a99a0 D_a99a0 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_a99a4 D_a99a4.
      sn F_a99a8 D_a99a8.
      sn F_a99ac D_a99ac.
      sn F_a99b0 D_a99b0.
      stepb_ft F_a99b4 D_a99b4 ltac:(pin; cond_compute).
      sn F_a99b8 D_a99b8.
      sn F_a99bc D_a99bc.
      sn F_a99c0 D_a99c0.
      ld_step F_a99c4 D_a99c4 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a99c8 D_a99c8 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_a99cc D_a99cc.
      sn F_a99d0 D_a99d0.
      ld_step F_a99d4 D_a99d4 (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_c7af0_4) ltac:(vm_compute; reflexivity).
      ld_step F_a99d8 D_a99d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c6640_8) ltac:(apply bytes_le_to_Z_8).
      sn F_a99dc D_a99dc.
      sn F_a99e0 D_a99e0.
      sn F_a99e4 D_a99e4.
      sn F_a99e8 D_a99e8.
      sn F_a99ec D_a99ec.
      sn F_a99f0 D_a99f0.
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
    getr regs 9 = Z_to_bv 64 1036960 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 1036312 ->
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
        getr regs' 9 = Z_to_bv 64 1036960 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 1036312 ->
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
        G (mkst regs' (0xad354 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xad354 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
      stepb_tk F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      ld_step F_a99f4 D_a99f4 (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
      sn F_a99f8 D_a99f8.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_tk F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_tk F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_tk F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_tk F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_tk F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
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
    getr regs 9 = Z_to_bv 64 1036960 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 1036312 ->
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
        getr regs' 9 = Z_to_bv 64 1036960 ->
        getr regs' 11 = Z_to_bv 64 1036312 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0xad3a4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xad354 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_tk F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_ft F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      ld_step F_a9a34 D_a9a34 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_a9a38 D_a9a38 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_tk F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_ft F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      ld_step F_a9a08 D_a9a08 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
      stepb_ft F_a9a0c D_a9a0c ltac:(pin; cond_compute).
      stepb_tk F_a9a10 D_a9a10 ltac:(pin; cond_compute).
      sn F_a9a24 D_a9a24.
      stepb_ft F_a9a28 D_a9a28 ltac:(pin; cond_compute).
      sn F_a9a2c D_a9a2c.
      stepb_tk F_a9a30 D_a9a30 ltac:(pin; cond_compute).
      sn F_a9a50 D_a9a50.
      sn F_a9a54 D_a9a54.
      sn F_a99fc D_a99fc.
      sn F_a9a00 D_a9a00.
      stepb_tk F_a9a04 D_a9a04 ltac:(pin; cond_compute).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = Z_to_bv 64 1036960 ->
    getr regs 11 = Z_to_bv 64 1036312 ->
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
        getr regs' 4 = Z_to_bv 64 905232 ->
        getr regs' 10 = Z_to_bv 64 1036312 ->
        getr regs' 11 = Z_to_bv 64 1037016 ->
        getr regs' 12 = Z_to_bv 64 0 ->
        getr regs' 13 = Z_to_bv 64 905024 ->
        getr regs' 14 = Z_to_bv 64 0 ->
        getr regs' 15 = Z_to_bv 64 18446744073708646384 ->
        getr regs' 17 = Z_to_bv 64 96 ->
        getr regs' 18 = Z_to_bv 64 905032 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (0xad528 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (0xad3a4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { stepb_tk F_a9a58 D_a9a58 ltac:(pin; cond_compute).
      ld_step F_a9a90 D_a9a90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d9528_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9a94 D_a9a94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d9538_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9a98 D_a9a98 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d9540_8) ltac:(apply bytes_le_to_Z_8).
      sn F_a9a9c D_a9a9c.
      sn F_a9aa0 D_a9aa0.
      sn F_a9aa4 D_a9aa4.
      sn F_a9aa8 D_a9aa8.
      sn F_a9aac D_a9aac.
      sn F_a9ab0 D_a9ab0.
      sn F_a9ab4 D_a9ab4.
      stw F_a9ab8 D_a9ab8 (Z_to_bv 64 1036344) (Z_to_bv 64 0) ltac:(ok_data).
      stw F_a9abc D_a9abc (Z_to_bv 64 1036360) (Z_to_bv 64 0) ltac:(ok_data).
      stepb_ft F_a9ac0 D_a9ac0 ltac:(pin; cond_compute).
      sn F_a9ac4 D_a9ac4.
      stw F_a9ac8 D_a9ac8 (Z_to_bv 64 1036352) (Z_to_bv 64 8) ltac:(ok_data).
      sn F_a9acc D_a9acc.
      sn F_a9ad0 D_a9ad0.
      sn F_a9ad4 D_a9ad4.
      sn F_a9ad8 D_a9ad8.
      sn F_a9adc D_a9adc.
      sn F_a9ae0 D_a9ae0.
      stw F_a9ae4 D_a9ae4 (Z_to_bv 64 1036984) (Z_to_bv 64 224) ltac:(ok_data).
      stw F_a9ae8 D_a9ae8 (Z_to_bv 64 1036992) (Z_to_bv 64 8) ltac:(ok_data).
      stepb_tk F_a9aec D_a9aec ltac:(pin; cond_compute).
      sn F_a9b20 D_a9b20.
      ld_step F_a9b24 D_a9b24 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d9900_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9b28 D_a9b28 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d9918_8) ltac:(apply bytes_le_to_Z_8).
      sn F_a9b2c D_a9b2c.
      sn F_a9b30 D_a9b30.
      sn F_a9b34 D_a9b34.
      sn F_a9b38 D_a9b38.
      sn F_a9b3c D_a9b3c.
      sn F_a9b40 D_a9b40.
      sn F_a9b44 D_a9b44.
      sn F_a9b48 D_a9b48.
      sn F_a9b4c D_a9b4c.
      sn F_a9b50 D_a9b50.
      sn F_a9b54 D_a9b54.
      stepb_tk F_a9b58 D_a9b58 ltac:(pin; cond_compute).
      stw F_a9ba0 D_a9ba0 (Z_to_bv 64 905248) (Z_to_bv 64 0) ltac:(ok_data).
      stw F_a9ba4 D_a9ba4 (Z_to_bv 64 905224) (Z_to_bv 64 905248) ltac:(ok_data).
      stw F_a9ba8 D_a9ba8 (Z_to_bv 64 905032) (Z_to_bv 64 905032) ltac:(ok_data).
      sn F_a9bac D_a9bac.
      sn F_a9bb0 D_a9bb0.
      sn F_bcce0 D_bcce0.
      sn F_bcce4 D_bcce4.
      stepret F_bcce8 D_bcce8 (0xad500 : word) ltac:(pin; first [reflexivity | bveq]).
      stepb_ft F_a9bb4 D_a9bb4 ltac:(pin; cond_compute).
      stepb_ft F_a9bb8 D_a9bb8 ltac:(pin; cond_compute).
      sn F_a9bbc D_a9bbc.
      stw F_a9bc0 D_a9bc0 (Z_to_bv 64 1036960) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_a9bc4 D_a9bc4.
      sn F_a9bc8 D_a9bc8.
      stw F_a9bcc D_a9bcc (Z_to_bv 64 905072) (Z_to_bv 64 2) ltac:(ok_data).
      sn F_a9bd0 D_a9bd0.
      sn F_a9bd4 D_a9bd4.
      sn F_a9bd8 D_a9bd8.
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 905232 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 1037016 ->
    getr regs 18 = Z_to_bv 64 905032 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 905232 ->
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
        G (mkst regs' (0xad0bc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (0xad52c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_a9be0 D_a9be0.
      stw F_a9be4 D_a9be4 (Z_to_bv 64 905064) tid ltac:(ok_data).
      stw F_a9be8 D_a9be8 (Z_to_bv 64 905184) (Z_to_bv 64 1037016) ltac:(ok_data).
      stw F_a9bec D_a9bec (Z_to_bv 64 905152) (Z_to_bv 64 905152) ltac:(ok_data).
      sn F_a9bf0 D_a9bf0.
      ld_step F_a9bf4 D_a9bf4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d98d8_8) ltac:(apply bytes_le_to_Z_8).
      stw F_a9bf8 D_a9bf8 (Z_to_bv 64 905040) (Z_to_bv 64 905032) ltac:(ok_data).
      stw F_a9bfc D_a9bfc (Z_to_bv 64 905048) (Z_to_bv 64 905032) ltac:(ok_data).
      stw F_a9c00 D_a9c00 (Z_to_bv 64 905056) (Z_to_bv 64 0) ltac:(ok_data).
      sn F_a9c04 D_a9c04.
      ld_step F_a9c0c D_a9c0c (word_to_le_bytes 8 (Z_to_bv 64 708796)) (Z_to_bv 64 708796) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9c10 D_a9c10 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9c14 D_a9c14 (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9c18 D_a9c18 (word_to_le_bytes 8 (Z_to_bv 64 1036960)) (Z_to_bv 64 1036960) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9c1c D_a9c1c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9c20 D_a9c20 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9c24 D_a9c24 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_a9c28 D_a9c28 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_a9c2c D_a9c2c (0xad0bc : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
