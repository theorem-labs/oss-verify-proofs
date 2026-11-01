(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  StartupTac ArgvEnv RefLayout Pm6Img Pm6StartupDefs
  Pm6_code_3975c_3a000 Pm6_code_a9000_aa000 Pm6_code_aa000_ab000 Pm6_code_ba000_bb000         .
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

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
  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 890400 ->
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
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 890400 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0xa9778 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694128))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1022128))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694136))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1021512) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021528) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021520) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1022152) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1022160) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 890416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 890392) (word_to_le_bytes 8 (Z_to_bv 64 890416))) (Z_to_bv 64 890200) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 1022128) ([Z_to_bv 8 1])) (Z_to_bv 64 890240) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 890232) (word_to_le_bytes 4 tid)) (Z_to_bv 64 890352) (word_to_le_bytes 8 (Z_to_bv 64 1022184))) (Z_to_bv 64 890320) (word_to_le_bytes 8 (Z_to_bv 64 890320))) (Z_to_bv 64 890208) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890216) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1022096) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1022100) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1022097) ([Z_to_bv 8 0])) (Z_to_bv 64 890384) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa9770 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694128))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1022128))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1021512) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021528) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021520) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1022152) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1022160) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 890416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 890392) (word_to_le_bytes 8 (Z_to_bv 64 890416))) (Z_to_bv 64 890200) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 1022128) ([Z_to_bv 8 1])) (Z_to_bv 64 890240) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 890232) (word_to_le_bytes 4 tid)) (Z_to_bv 64 890352) (word_to_le_bytes 8 (Z_to_bv 64 1022184))) (Z_to_bv 64 890320) (word_to_le_bytes 8 (Z_to_bv 64 890320))) (Z_to_bv 64 890208) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890216) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890224) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof using Hva Hve Hlo Hhi Hal.
    intros G Gback regs rom s1v tid Jwf Vsp Vgp Vtp Vs3 Vs4 Vs5 Vs6 Vs7 Vs8 Vs9 Vs10 Vs11 Kpost.
    destruct rnd_bounds as (Rabove & Rroom & Ralign8).
    assert (Ralign4 : (bv_unsigned (rnd_w sp0 av ev) mod 4 = 0)%Z).
    { apply (proj2 (Z.mod_divide _ 4 ltac:(lia))).
      apply (Z.divide_trans _ 8); [exists 2%Z; reflexivity |].
      exact (proj1 (Z.mod_divide _ 8 ltac:(lia)) Ralign8). }
    gsteps Gback.
    ld_step F_a9728 D_a9728 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev)
      ltac:(rewrite rdn_cmem_win by region_side; unfold J_aux; rd_hit8)
      ltac:(apply bytes_le_to_Z_8).
    sn F_a972c D_a972c.
    sv F_aa0e4 D_aa0e4 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
    stw F_aa0e8 D_aa0e8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 694136) ltac:(ok_win Jwf).
    stepb_ft F_aa0ec D_aa0ec ltac:(apply c_eq_0_false; lia).
    sn F_aa0f0 D_aa0f0.
    sn F_aa0f4 D_aa0f4.
    ld_step F_aa0f8 D_aa0f8 (word_to_le_bytes 8 (Z_to_bv 64 1022096)) (Z_to_bv 64 1022096)
      ltac:(rewrite rdn_cmem_data by region_side; unfold D_libc; peel; exact img_c67f8_8)
      ltac:(apply bytes_le_to_Z_8).
    sn F_aa0fc D_aa0fc.
    sn F_aa100 D_aa100.
    stepiv F_ba620 D_ba620 (Z_to_bv 64 0)
      ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; exact Ralign4).
    stepb F_ba624 D_ba624.
    sn F_ba734 D_ba734.
    sn F_ba738 D_ba738.
    stepb F_ba73c D_ba73c.
    sn F_ba740 D_ba740.
    stepb F_ba744 D_ba744.
    sn F_ba77c D_ba77c.
    stepb F_ba780 D_ba780.
    ld_step F_ba784 D_ba784 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
    ld_step F_ba788 D_ba788 (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
    stw F_ba78c D_ba78c (Z_to_bv 64 1022096) (rlw RND 0) ltac:(ok_data).
    stw F_ba790 D_ba790 (Z_to_bv 64 1022100) (rlw RND 4) ltac:(ok_data).
    sn F_ba794 D_ba794.
    sn F_ba798 D_ba798.
    sn F_ba79c D_ba79c.
    stepb F_ba7a0 D_ba7a0.
    sn F_ba9e0 D_ba9e0.
    stepb F_ba9e4 D_ba9e4.
    sn F_ba9e8 D_ba9e8.
    stepb F_ba9ec D_ba9ec.
    stepret F_ba9f0 D_ba9f0 (Z_to_bv 64 696640) ltac:(reflexivity).
    sn F_aa104 D_aa104.
    sn F_aa120 D_aa120.
    ld_step F_aa124 D_aa124 (word_to_le_bytes 8 (Z_to_bv 64 1022096)) (Z_to_bv 64 1022096)
      ltac:(rewrite rdn_cmem_data by region_side; unfold D_libc; peel; exact img_c67f8_8)
      ltac:(apply bytes_le_to_Z_8).
    stw F_aa128 D_aa128 (Z_to_bv 64 1022097) (Z_to_bv 64 0) ltac:(ok_data).
    ld_step F_aa12c D_aa12c (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
    sn F_aa130 D_aa130.
    stw F_aa134 D_aa134 (Z_to_bv 64 890384) (canary_w RND) ltac:(ok_data).
    ld_step F_aa138 D_aa138 (word_to_le_bytes 8 (Z_to_bv 64 694136)) (Z_to_bv 64 694136)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    sv F_aa13c D_aa13c (Z_to_bv 64 (bv_unsigned sp0 - 416)).
    stepret F_aa140 D_aa140 (Z_to_bv 64 694136) ltac:(reflexivity).
    apply mst_refl.
    apply Kpost; try solve_regs_agree; gres; first [ reflexivity | assumption ].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 890400 ->
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
        getr regs' 1 = Z_to_bv 64 0 ->
        getr regs' 2 = sp0 ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 890400 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 235760 ->
        getr regs' 11 = (argc_w av) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 18 = Z_to_bv 64 0 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
        G (mkst regs' (0xa9938 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694128))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1022128))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694136))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1021512) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021528) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021520) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1022152) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1022160) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 890416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 890392) (word_to_le_bytes 8 (Z_to_bv 64 890416))) (Z_to_bv 64 890200) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 1022128) ([Z_to_bv 8 1])) (Z_to_bv 64 890240) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 890232) (word_to_le_bytes 4 tid)) (Z_to_bv 64 890352) (word_to_le_bytes 8 (Z_to_bv 64 1022184))) (Z_to_bv 64 890320) (word_to_le_bytes 8 (Z_to_bv 64 890320))) (Z_to_bv 64 890208) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890216) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1022096) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1022100) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1022097) ([Z_to_bv 8 0])) (Z_to_bv 64 890384) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa9778 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694128))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1022128))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694136))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1021512) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021528) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021520) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1022152) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1022160) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 890416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 890392) (word_to_le_bytes 8 (Z_to_bv 64 890416))) (Z_to_bv 64 890200) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 1022128) ([Z_to_bv 8 1])) (Z_to_bv 64 890240) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 890232) (word_to_le_bytes 4 tid)) (Z_to_bv 64 890352) (word_to_le_bytes 8 (Z_to_bv 64 1022184))) (Z_to_bv 64 890320) (word_to_le_bytes 8 (Z_to_bv 64 890320))) (Z_to_bv 64 890208) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890216) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1022096) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1022100) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1022097) ([Z_to_bv 8 0])) (Z_to_bv 64 890384) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof using Hva Hve Hlo Hhi Hal.
    intros G Gback regs rom s1v tid Jwf Vsp Vgp Vtp Vs3 Vs4 Vs5 Vs6 Vs7 Vs8 Vs9 Vs10 Vs11 Kpost.
    lazymatch goal with
    | |- G (mkst _ _ (cmem _ _ ?Jm ?Dm) _) =>
      assert (Slots :
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 280)) 8 = Some (word_to_le_bytes 8 uid) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 272)) 8 = Some (word_to_le_bytes 8 uid) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 264)) 8 = Some (zeros 8) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 256)) 8 = Some (zeros 8) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 184)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 694540)) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 48)) 8 = Some (word_to_le_bytes 8 (argv_w sp0)) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (argc_w av)) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 235760)) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
        rdn SEGS (CM Jm Dm) (Z_to_bv 64 (bv_unsigned sp0 - 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)))
    end.
    { repeat match goal with |- _ /\ _ => split end;
        rewrite rdn_cmem_win by region_side; unfold J_aux, J_lsm, aux_base; peel;
        first [ apply rdn_wbytes_hit8 | apply rdn_wbytes_zeros_in ]; cbn [Z.of_nat]; unorm; lia. }
    destruct Slots as (S280 & S272 & S264 & S256 & S184 & S40 & S48 & S56 & S64 & S8 & S16 & S24 & S32).
    gsteps Gback.
    ld_step F_a9730 D_a9730 (word_to_le_bytes 8 uid) uid
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    ld_step F_a9734 D_a9734 (word_to_le_bytes 8 uid) uid
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_a9738 D_a9738 ltac:(apply c_eq_refl).
    ld_step F_a973c D_a973c (zeros 8) (Z_to_bv 64 0)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(rewrite bytes_le_to_Z_zeros; reflexivity).
    ld_step F_a9740 D_a9740 (zeros 8) (Z_to_bv 64 0)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(rewrite bytes_le_to_Z_zeros; reflexivity).
    stepb F_a9744 D_a9744.
    ld_step F_a9748 D_a9748 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    stepb F_a974c D_a974c.
    ld_step F_a982c D_a982c (word_to_le_bytes 8 (Z_to_bv 64 694540)) (Z_to_bv 64 694540)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    ld_step F_a9830 D_a9830 (word_to_le_bytes 8 (argv_w sp0)) (argv_w sp0)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    ld_step F_a9834 D_a9834 (word_to_le_bytes 8 (argc_w av)) (argc_w av)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    ld_step F_a9838 D_a9838 (word_to_le_bytes 8 (Z_to_bv 64 235760)) (Z_to_bv 64 235760)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    sv F_a983c D_a983c (Z_to_bv 64 (bv_unsigned sp0 - 32)).
    stepret F_a9840 D_a9840 (Z_to_bv 64 694540) ltac:(reflexivity).
    stepn F_a98c4 D_a98c4.
    stepn F_a98c8 D_a98c8.
    stepn F_a98cc D_a98cc.
    stepn F_a98d0 D_a98d0.
    stepn F_a98d4 D_a98d4.
    ld_step F_a98d8 D_a98d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    ld_step F_a98dc D_a98dc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    ld_step F_a98e0 D_a98e0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    ld_step F_a98e4 D_a98e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(idtac; match goal with Sl : rdn _ _ _ _ = _ |- _ => eapply rdn_addr; [exact Sl | f_equal; lia] end)
      ltac:(apply bytes_le_to_Z_8).
    sv F_a98e8 D_a98e8 sp0.
    stepret F_a98ec D_a98ec (Z_to_bv 64 694584) ltac:(reflexivity).
    apply mst_refl.
    apply Kpost; try solve_regs_agree; gres; first [ reflexivity | assumption ].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 890400 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 235760 ->
    getr regs 11 = (argc_w av) ->
    getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
    getr regs 18 = Z_to_bv 64 0 ->
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
        getr regs' 1 = Z_to_bv 64 694460 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 890400 ->
        getr regs' 8 = Z_to_bv 64 788168 ->
        getr regs' 9 = Z_to_bv 64 788160 ->
        getr regs' 18 = Z_to_bv 64 235760 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
        G (mkst regs' (0x397ec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694128))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1022128))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694136))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 694636))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1021512) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021528) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021520) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1022152) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1022160) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 890416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 890392) (word_to_le_bytes 8 (Z_to_bv 64 890416))) (Z_to_bv 64 890200) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 1022128) ([Z_to_bv 8 1])) (Z_to_bv 64 890240) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 890232) (word_to_le_bytes 4 tid)) (Z_to_bv 64 890352) (word_to_le_bytes 8 (Z_to_bv 64 1022184))) (Z_to_bv 64 890320) (word_to_le_bytes 8 (Z_to_bv 64 890320))) (Z_to_bv 64 890208) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890216) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1022096) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1022100) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1022097) ([Z_to_bv 8 0])) (Z_to_bv 64 890384) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa9938 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694128))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1022128))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694136))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1021512) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021528) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021520) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1022152) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1022160) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 890416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 890392) (word_to_le_bytes 8 (Z_to_bv 64 890416))) (Z_to_bv 64 890200) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 1022128) ([Z_to_bv 8 1])) (Z_to_bv 64 890240) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 890232) (word_to_le_bytes 4 tid)) (Z_to_bv 64 890352) (word_to_le_bytes 8 (Z_to_bv 64 1022184))) (Z_to_bv 64 890320) (word_to_le_bytes 8 (Z_to_bv 64 890320))) (Z_to_bv 64 890208) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890216) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1022096) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1022100) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1022097) ([Z_to_bv 8 0])) (Z_to_bv 64 890384) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof using Hva Hve Hlo Hhi Hal.
    intros G Gback regs rom s1v tid Jwf Vra Vsp Vgp Vtp Vs0 Vs1 Va0 Va1 Va2 Vs2
      Vs3 Vs4 Vs5 Vs6 Vs7 Vs8 Vs9 Vs10 Vs11 Kpost.
    pose proof len_av as Nargs.
    gsteps Gback.
    sv F_a98f0 D_a98f0 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
    stw F_a98f4 D_a98f4 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win Jwf).
    stw F_a98f8 D_a98f8 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win Jwf).
    stw F_a98fc D_a98fc (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win Jwf).
    stw F_a9900 D_a9900 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win Jwf).
    stw F_a9904 D_a9904 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win Jwf).
    sn F_a9908 D_a9908.
    sn F_a990c D_a990c.
    sn F_a9910 D_a9910.
    stepiv F_a9914 D_a9914 (Z_to_bv 64 (8 * Z.of_nat (length av)))
      ltac:(gres; pin; imm_norm; exact slli_argc).
    sv F_a9918 D_a9918 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
    sv F_a991c D_a991c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
    sn F_a9920 D_a9920.
    sv F_a9844 D_a9844 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
    stw F_a9848 D_a9848 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 694636) ltac:(ok_win Jwf).
    stw F_a984c D_a984c (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8))
      ltac:(ok_win Jwf).
    stw F_a9850 D_a9850 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win Jwf).
    sn F_a9854 D_a9854.
    stepret F_a9614 D_a9614 (Z_to_bv 64 694432) ltac:(reflexivity).
    sn F_a9858 D_a9858.
    sn F_a985c D_a985c.
    ld_step F_a9860 D_a9860 (word_to_le_bytes 8 (Z_to_bv 64 788168)) (Z_to_bv 64 788168)
      ltac:(rewrite rdn_cmem_data by region_side; unfold D_libc; peel; exact img_c67e8_8)
      ltac:(apply bytes_le_to_Z_8).
    ld_step F_a9864 D_a9864 (word_to_le_bytes 8 (Z_to_bv 64 788160)) (Z_to_bv 64 788160)
      ltac:(rewrite rdn_cmem_data by region_side; unfold D_libc; peel; exact img_c67f0_8)
      ltac:(apply bytes_le_to_Z_8).
    stepb F_a9868 D_a9868.
    ld_step F_a986c D_a986c (word_to_le_bytes 8 (Z_to_bv 64 235500)) (Z_to_bv 64 235500)
      ltac:(rewrite rdn_cmem_data by region_side; unfold D_libc; peel; exact img_c0688_8)
      ltac:(apply bytes_le_to_Z_8).
    stepjr F_a9870 D_a9870 (Z_to_bv 64 235500) ltac:(gres; reflexivity).
    apply mst_refl.
    apply Kpost; try solve_regs_agree; gres; first [ reflexivity | assumption ].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 694460 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 890400 ->
    getr regs 8 = Z_to_bv 64 788168 ->
    getr regs 9 = Z_to_bv 64 788160 ->
    getr regs 18 = Z_to_bv 64 235760 ->
    getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 694652 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 890400 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 235760 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
        G (mkst regs' (0x398f0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694128))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1022128))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694136))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 694636))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 694460))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 788168))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1021512) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021528) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021520) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1022152) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1022160) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 890416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 890392) (word_to_le_bytes 8 (Z_to_bv 64 890416))) (Z_to_bv 64 890200) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 1022128) ([Z_to_bv 8 1])) (Z_to_bv 64 890240) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 890232) (word_to_le_bytes 4 tid)) (Z_to_bv 64 890352) (word_to_le_bytes 8 (Z_to_bv 64 1022184))) (Z_to_bv 64 890320) (word_to_le_bytes 8 (Z_to_bv 64 890320))) (Z_to_bv 64 890208) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890216) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1022096) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1022100) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1022097) ([Z_to_bv 8 0])) (Z_to_bv 64 890384) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 818000) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x397ec : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694128))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1022128))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 694136))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 694636))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1021512) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021528) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1021520) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1022152) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1022160) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 890416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 890392) (word_to_le_bytes 8 (Z_to_bv 64 890416))) (Z_to_bv 64 890200) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 1022128) ([Z_to_bv 8 1])) (Z_to_bv 64 890240) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 890232) (word_to_le_bytes 4 tid)) (Z_to_bv 64 890352) (word_to_le_bytes 8 (Z_to_bv 64 1022184))) (Z_to_bv 64 890320) (word_to_le_bytes 8 (Z_to_bv 64 890320))) (Z_to_bv 64 890208) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890216) (word_to_le_bytes 8 (Z_to_bv 64 890200))) (Z_to_bv 64 890224) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1022096) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1022100) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1022097) ([Z_to_bv 8 0])) (Z_to_bv 64 890384) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof using Hva Hve Hlo Hhi Hal.
    intros G Gback regs rom s1v tid Jwf Vra Vsp Vgp Vtp Vs0 Vs1 Vs2 Vs3 Vs4 Vs5 Vs6 Vs7 Vs8 Vs9 Vs10 Vs11 Kpost.
    gsteps Gback.
    sv F_397a4 D_397a4 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
    stw F_397a8 D_397a8 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 694460) ltac:(ok_win Jwf).
    stw F_397ac D_397ac (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 788168) ltac:(ok_win Jwf).
    sn F_397b0 D_397b0.
    sn F_397b4 D_397b4.
    sn F_397b8 D_397b8.
    lb_step F_397bc D_397bc (Z_to_bv 8 0)
      ltac:(rewrite rdn_cmem_data by region_side; unfold D_libc; peel; exact img_c7b10_1).
    sn F_397c0 D_397c0.
    stepb F_397c4 D_397c4.
    sn F_397d0 D_397d0.
    sn F_397d4 D_397d4.
    sn F_397d8 D_397d8.
    stw F_397dc D_397dc (Z_to_bv 64 818000) (Z_to_bv 64 1) ltac:(ok_data).
    sn F_397e0 D_397e0.
    ld_step F_397e4 D_397e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_data by region_side; unfold D_libc; peel; exact img_c6660_8)
      ltac:(apply bytes_le_to_Z_8).
    stepb F_397e8 D_397e8.
    ld_step F_39808 D_39808 (word_to_le_bytes 8 (Z_to_bv 64 694460)) (Z_to_bv 64 694460)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step F_3980c D_3980c (word_to_le_bytes 8 (Z_to_bv 64 788168)) (Z_to_bv 64 788168)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    sv F_39810 D_39810 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
    stepret F_39814 D_39814 (Z_to_bv 64 694460) ltac:(reflexivity).
    sn F_a9874 D_a9874.
    stepb F_a9878 D_a9878.
    ld_step F_a987c D_a987c (word_to_le_bytes 8 (Z_to_bv 64 694636)) (Z_to_bv 64 694636)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step F_a9880 D_a9880 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))
      (Z_to_bv 64 (bv_unsigned sp0 + 8))
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step F_a9884 D_a9884 (word_to_le_bytes 8 (argc_w av)) (argc_w av)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    sv F_a9888 D_a9888 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
    stepret F_a988c D_a988c (Z_to_bv 64 694636) ltac:(reflexivity).
    sn F_a9924 D_a9924.
    sn F_a9928 D_a9928.
    sn F_a992c D_a992c.
    stepjr F_a9930 D_a9930 (Z_to_bv 64 235760) ltac:(gres; first [ reflexivity | assumption ]).
    apply mst_refl.
    apply Kpost; try solve_regs_agree; gres; first [ reflexivity | assumption ].
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
