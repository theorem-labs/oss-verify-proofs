(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  StartupTac ArgvEnv RefLayout Ub0Img Ub0StartupDefs
  Ub0_code_4b9d8_4bc88 Ub0_code_5a644_5a650.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
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
    getr regs 1 = Z_to_bv 64 309192 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 8 = (pn_w sp0 av ev) ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = Z_to_bv 64 594376 ->
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
        getr regs' 9 = Z_to_bv 64 594376 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 593728 ->
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
        G (mkst regs' (0x4ba60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x4b9d8 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_4b9d8 D_4b9d8 (Z_to_bv 64 (bv_unsigned sp0 - 480)).  (* [comment removed for export] *)
      stw F_4b9dc D_4b9dc (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 309192) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b9e0 D_4b9e0 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b9e4 D_4b9e4 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b9e8 D_4b9e8 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 594376) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b9ec D_4b9ec (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b9f0 D_4b9f0 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b9f4 D_4b9f4 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      ld_step F_4b9f8 D_4b9f8 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4b9fc D_4b9fc.  (* [comment removed for export] *)
      sn F_4ba00 D_4ba00.  (* [comment removed for export] *)
      sn F_4ba04 D_4ba04.  (* [comment removed for export] *)
      sn F_4ba08 D_4ba08.  (* [comment removed for export] *)
      stepb_ft F_4ba0c D_4ba0c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba10 D_4ba10.  (* [comment removed for export] *)
      sn F_4ba14 D_4ba14.  (* [comment removed for export] *)
      sn F_4ba18 D_4ba18.  (* [comment removed for export] *)
      ld_step F_4ba1c D_4ba1c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4ba20 D_4ba20 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4ba24 D_4ba24.  (* [comment removed for export] *)
      sn F_4ba28 D_4ba28.  (* [comment removed for export] *)
      ld_step F_4ba2c D_4ba2c (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_60358_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      ld_step F_4ba30 D_4ba30 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5ef98_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4ba34 D_4ba34.  (* [comment removed for export] *)
      sn F_4ba38 D_4ba38.  (* [comment removed for export] *)
      sn F_4ba3c D_4ba3c.  (* [comment removed for export] *)
      sn F_4ba40 D_4ba40.  (* [comment removed for export] *)
      sn F_4ba44 D_4ba44.  (* [comment removed for export] *)
      sn F_4ba48 D_4ba48.  (* [comment removed for export] *)
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
    getr regs 9 = Z_to_bv 64 594376 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 593728 ->
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
        getr regs' 9 = Z_to_bv 64 594376 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 593728 ->
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
        G (mkst regs' (0x4ba60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x4ba60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba4c D_4ba4c (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4ba50 D_4ba50.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_tk F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_tk F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_tk F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_tk F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_tk F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
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
    getr regs 9 = Z_to_bv 64 594376 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 593728 ->
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
        getr regs' 9 = Z_to_bv 64 594376 ->
        getr regs' 11 = Z_to_bv 64 593728 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0x4bab0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x4ba60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_tk F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_ft F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba8c D_4ba8c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_4ba90 D_4ba90 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_tk F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_ft F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ba60 D_4ba60 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ba64 D_4ba64 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_tk F_4ba68 D_4ba68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba7c D_4ba7c.  (* [comment removed for export] *)
      stepb_ft F_4ba80 D_4ba80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4ba84 D_4ba84.  (* [comment removed for export] *)
      stepb_tk F_4ba88 D_4ba88 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4baa8 D_4baa8.  (* [comment removed for export] *)
      sn F_4baac D_4baac.  (* [comment removed for export] *)
      sn F_4ba54 D_4ba54.  (* [comment removed for export] *)
      sn F_4ba58 D_4ba58.  (* [comment removed for export] *)
      stepb_tk F_4ba5c D_4ba5c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = Z_to_bv 64 594376 ->
    getr regs 11 = Z_to_bv 64 593728 ->
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
        getr regs' 4 = Z_to_bv 64 462648 ->
        getr regs' 10 = Z_to_bv 64 593728 ->
        getr regs' 11 = Z_to_bv 64 594432 ->
        getr regs' 12 = Z_to_bv 64 0 ->
        getr regs' 13 = Z_to_bv 64 462440 ->
        getr regs' 14 = Z_to_bv 64 0 ->
        getr regs' 15 = Z_to_bv 64 18446744073709088968 ->
        getr regs' 17 = Z_to_bv 64 96 ->
        getr regs' 18 = Z_to_bv 64 462448 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (0x4bc34 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (0x4bab0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { stepb_tk F_4bab0 D_4bab0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4bae8 D_4bae8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_90f50_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4baec D_4baec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_90f60_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4baf0 D_4baf0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_90f68_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4baf4 D_4baf4.  (* [comment removed for export] *)
      sn F_4baf8 D_4baf8.  (* [comment removed for export] *)
      sn F_4bafc D_4bafc.  (* [comment removed for export] *)
      sn F_4bb00 D_4bb00.  (* [comment removed for export] *)
      sn F_4bb04 D_4bb04.  (* [comment removed for export] *)
      sn F_4bb08 D_4bb08.  (* [comment removed for export] *)
      sn F_4bb0c D_4bb0c.  (* [comment removed for export] *)
      stw F_4bb10 D_4bb10 (Z_to_bv 64 593760) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4bb14 D_4bb14 (Z_to_bv 64 593776) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_ft F_4bb18 D_4bb18 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4bb1c D_4bb1c.  (* [comment removed for export] *)
      stw F_4bb20 D_4bb20 (Z_to_bv 64 593768) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4bb24 D_4bb24.  (* [comment removed for export] *)
      sn F_4bb28 D_4bb28.  (* [comment removed for export] *)
      sn F_4bb2c D_4bb2c.  (* [comment removed for export] *)
      sn F_4bb30 D_4bb30.  (* [comment removed for export] *)
      sn F_4bb34 D_4bb34.  (* [comment removed for export] *)
      sn F_4bb38 D_4bb38.  (* [comment removed for export] *)
      stw F_4bb3c D_4bb3c (Z_to_bv 64 594400) (Z_to_bv 64 224) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4bb40 D_4bb40 (Z_to_bv 64 594408) (Z_to_bv 64 8) ltac:(ok_data).  (* [comment removed for export] *)
      stepb_tk F_4bb44 D_4bb44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4bb78 D_4bb78.  (* [comment removed for export] *)
      ld_step F_4bb7c D_4bb7c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_911d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4bb80 D_4bb80 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_911f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4bb84 D_4bb84.  (* [comment removed for export] *)
      sn F_4bb88 D_4bb88.  (* [comment removed for export] *)
      sn F_4bb8c D_4bb8c.  (* [comment removed for export] *)
      sn F_4bb90 D_4bb90.  (* [comment removed for export] *)
      sn F_4bb94 D_4bb94.  (* [comment removed for export] *)
      sn F_4bb98 D_4bb98.  (* [comment removed for export] *)
      sn F_4bb9c D_4bb9c.  (* [comment removed for export] *)
      sn F_4bba0 D_4bba0.  (* [comment removed for export] *)
      sn F_4bba4 D_4bba4.  (* [comment removed for export] *)
      sn F_4bba8 D_4bba8.  (* [comment removed for export] *)
      sn F_4bbac D_4bbac.  (* [comment removed for export] *)
      stepb_tk F_4bbb0 D_4bbb0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stw F_4bbf8 D_4bbf8 (Z_to_bv 64 462664) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4bbfc D_4bbfc (Z_to_bv 64 462640) (Z_to_bv 64 462664) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4bc00 D_4bc00 (Z_to_bv 64 462448) (Z_to_bv 64 462448) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4bc04 D_4bc04.  (* [comment removed for export] *)
      sn F_4bc08 D_4bc08.  (* [comment removed for export] *)
      sn F_5a644 D_5a644.  (* [comment removed for export] *)
      sn F_5a648 D_5a648.  (* [comment removed for export] *)
      stepret F_5a64c D_5a64c (0x4bc0c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      stepb_ft F_4bc0c D_4bc0c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepb_ft F_4bc10 D_4bc10 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_4bc14 D_4bc14.  (* [comment removed for export] *)
      stw F_4bc18 D_4bc18 (Z_to_bv 64 594376) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4bc1c D_4bc1c.  (* [comment removed for export] *)
      sn F_4bc20 D_4bc20.  (* [comment removed for export] *)
      stw F_4bc24 D_4bc24 (Z_to_bv 64 462488) (Z_to_bv 64 2) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4bc28 D_4bc28.  (* [comment removed for export] *)
      sn F_4bc2c D_4bc2c.  (* [comment removed for export] *)
      sn F_4bc30 D_4bc30.  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 462648 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 594432 ->
    getr regs 18 = Z_to_bv 64 462448 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 462648 ->
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
        G (mkst regs' (0x4b7c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (0x4bc38 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sn F_4bc38 D_4bc38.  (* [comment removed for export] *)
      stw F_4bc3c D_4bc3c (Z_to_bv 64 462480) tid ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4bc40 D_4bc40 (Z_to_bv 64 462600) (Z_to_bv 64 594432) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4bc44 D_4bc44 (Z_to_bv 64 462568) (Z_to_bv 64 462568) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4bc48 D_4bc48.  (* [comment removed for export] *)
      ld_step F_4bc4c D_4bc4c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_911b0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_4bc50 D_4bc50 (Z_to_bv 64 462456) (Z_to_bv 64 462448) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4bc54 D_4bc54 (Z_to_bv 64 462464) (Z_to_bv 64 462448) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_4bc58 D_4bc58 (Z_to_bv 64 462472) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_4bc5c D_4bc5c.  (* [comment removed for export] *)
      ld_step F_4bc64 D_4bc64 (word_to_le_bytes 8 (Z_to_bv 64 309192)) (Z_to_bv 64 309192) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4bc68 D_4bc68 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4bc6c D_4bc6c (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4bc70 D_4bc70 (word_to_le_bytes 8 (Z_to_bv 64 594376)) (Z_to_bv 64 594376) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4bc74 D_4bc74 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4bc78 D_4bc78 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4bc7c D_4bc7c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4bc80 D_4bc80 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_4bc84 D_4bc84 (0x4b7c8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
