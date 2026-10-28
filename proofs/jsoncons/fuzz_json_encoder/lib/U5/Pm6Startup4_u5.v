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
  Pm6_code_3975c_3a000_u5 Pm6_code_a9000_aa000_u5 Pm6_code_aa000_ab000_u5 Pm6_code_ba000_bb000_u5         .
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
  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 905232 ->
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
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0xad0c4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708804))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036928) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1036932) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1036929) ([Z_to_bv 8 0])) (Z_to_bv 64 905216) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xad0bc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_a9728 D_a9728 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_a972c D_a972c.
      sv F_aa0e4 D_aa0e4 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_aa0e8 D_aa0e8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 708804) ltac:(ok_win HJ).
      stepb_ft F_aa0ec D_aa0ec ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_aa0f0 D_aa0f0 (rnd_w sp0 av ev).
      sn F_aa0f4 D_aa0f4.
      ld_step F_aa0f8 D_aa0f8 (word_to_le_bytes 8 (Z_to_bv 64 1036928)) (Z_to_bv 64 1036928) ltac:(rd_img img_c67f8_8) ltac:(apply bytes_le_to_Z_8).
      sn F_aa0fc D_aa0fc.
      sn F_aa100 D_aa100.
      stepiv F_ba620 D_ba620 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_ba624 D_ba624 ltac:(pin; cond_compute).
      sn F_ba734 D_ba734.
      sn F_ba738 D_ba738.
      stepb_ft F_ba73c D_ba73c ltac:(pin; cond_compute).
      sn F_ba740 D_ba740.
      stepb_tk F_ba744 D_ba744 ltac:(pin; cond_compute).
      sn F_ba77c D_ba77c.
      stepb_ft F_ba780 D_ba780 ltac:(pin; cond_compute).
      ld_step F_ba784 D_ba784 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
      ld_step F_ba788 D_ba788 (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
      stw F_ba78c D_ba78c (Z_to_bv 64 1036928) (rlw RND 0) ltac:(ok_data).
      stw F_ba790 D_ba790 (Z_to_bv 64 1036932) (rlw RND 4) ltac:(ok_data).
      sn F_ba794 D_ba794.
      sv F_ba798 D_ba798 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).
      sn F_ba79c D_ba79c.
      stepb_tk F_ba7a0 D_ba7a0 ltac:(pin; cond_compute).
      sn F_ba9e0 D_ba9e0.
      stepb_ft F_ba9e4 D_ba9e4 ltac:(pin; cond_compute).
      sn F_ba9e8 D_ba9e8.
      stepb_ft F_ba9ec D_ba9ec ltac:(pin; cond_compute).
      stepret F_ba9f0 D_ba9f0 (0xada8c : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_aa104 D_aa104.
      sn F_aa120 D_aa120.
      ld_step F_aa124 D_aa124 (word_to_le_bytes 8 (Z_to_bv 64 1036928)) (Z_to_bv 64 1036928) ltac:(rd_img img_c67f8_8) ltac:(apply bytes_le_to_Z_8).
      stw F_aa128 D_aa128 (Z_to_bv 64 1036929) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_aa12c D_aa12c (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
      sn F_aa130 D_aa130.
      stw F_aa134 D_aa134 (Z_to_bv 64 905216) (canary_w RND) ltac:(ok_data).
      ld_step F_aa138 D_aa138 (word_to_le_bytes 8 (Z_to_bv 64 708804)) (Z_to_bv 64 708804) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_aa13c D_aa13c (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_aa140 D_aa140 (0xad0c4 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 905232 ->
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
        getr regs' 4 = Z_to_bv 64 905232 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 237936 ->
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
        G (mkst regs' (0xad284 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708804))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036928) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1036932) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1036929) ([Z_to_bv 8 0])) (Z_to_bv 64 905216) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xad0c4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708804))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036928) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1036932) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1036929) ([Z_to_bv 8 0])) (Z_to_bv 64 905216) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_a9730 D_a9730 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9734 D_a9734 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_a9738 D_a9738 ltac:(pin; first [apply c_eq_refl | cond_compute]).
      ld_step F_a973c D_a973c (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      ld_step F_a9740 D_a9740 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      stepb_ft F_a9744 D_a9744 ltac:(pin; cond_compute).
      ld_step F_a9748 D_a9748 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_a974c D_a974c ltac:(pin; cond_compute).
      ld_step F_a982c D_a982c (word_to_le_bytes 8 (Z_to_bv 64 709208)) (Z_to_bv 64 709208) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9830 D_a9830 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9834 D_a9834 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9838 D_a9838 (word_to_le_bytes 8 (Z_to_bv 64 237936)) (Z_to_bv 64 237936) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_a983c D_a983c (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_a9840 D_a9840 (0xad258 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_a98c4 D_a98c4.
      sn F_a98c8 D_a98c8.
      sn F_a98cc D_a98cc.
      sv F_a98d0 D_a98d0 (argc_w av).
      sv F_a98d4 D_a98d4 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_a98d8 D_a98d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a98dc D_a98dc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a98e0 D_a98e0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a98e4 D_a98e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_a98e8 D_a98e8 sp0.
      stepret F_a98ec D_a98ec (0xad284 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 905232 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 237936 ->
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
        getr regs' 1 = Z_to_bv 64 709128 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 905232 ->
        getr regs' 8 = Z_to_bv 64 803000 ->
        getr regs' 9 = Z_to_bv 64 802992 ->
        getr regs' 18 = Z_to_bv 64 237936 ->
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
        G (mkst regs' (0x3a06c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708804))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 709304))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036928) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1036932) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1036929) ([Z_to_bv 8 0])) (Z_to_bv 64 905216) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xad284 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708804))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036928) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1036932) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1036929) ([Z_to_bv 8 0])) (Z_to_bv 64 905216) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_a98f0 D_a98f0 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_a98f4 D_a98f4 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a98f8 D_a98f8 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a98fc D_a98fc (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a9900 D_a9900 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a9904 D_a9904 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_a9908 D_a9908 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_a990c D_a990c (argc_w av).
      sn F_a9910 D_a9910.
      stepiv F_a9914 D_a9914 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_a9918 D_a9918 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_a991c D_a991c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_a9920 D_a9920.
      sv F_a9844 D_a9844 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_a9848 D_a9848 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 709304) ltac:(ok_win HJ).
      stw F_a984c D_a984c (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_a9850 D_a9850 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).
      sn F_a9854 D_a9854.
      stepret F_a9614 D_a9614 (0xad1ec : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_a9858 D_a9858.
      sn F_a985c D_a985c.
      ld_step F_a9860 D_a9860 (word_to_le_bytes 8 (Z_to_bv 64 803000)) (Z_to_bv 64 803000) ltac:(rd_img img_c67e8_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9864 D_a9864 (word_to_le_bytes 8 (Z_to_bv 64 802992)) (Z_to_bv 64 802992) ltac:(rd_img img_c67f0_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_a9868 D_a9868 ltac:(pin; cond_compute).
      ld_step F_a986c D_a986c (word_to_le_bytes 8 (Z_to_bv 64 237676)) (Z_to_bv 64 237676) ltac:(rd_img img_c0688_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_a9870 D_a9870 (0x3a06c : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 709128 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 905232 ->
    getr regs 8 = Z_to_bv 64 803000 ->
    getr regs 9 = Z_to_bv 64 802992 ->
    getr regs 18 = Z_to_bv 64 237936 ->
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
        getr regs' 1 = Z_to_bv 64 709320 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 905232 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 237936 ->
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
        G (mkst regs' (0x3a170 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708804))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 709304))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 709128))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 803000))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036928) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1036932) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1036929) ([Z_to_bv 8 0])) (Z_to_bv 64 905216) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 832832) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x3a06c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708796))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1036960))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 708804))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 709304))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1036344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036360) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1036984) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1036992) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 905248) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 905224) (word_to_le_bytes 8 (Z_to_bv 64 905248))) (Z_to_bv 64 905032) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 1036960) ([Z_to_bv 8 1])) (Z_to_bv 64 905072) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 905064) (word_to_le_bytes 4 tid)) (Z_to_bv 64 905184) (word_to_le_bytes 8 (Z_to_bv 64 1037016))) (Z_to_bv 64 905152) (word_to_le_bytes 8 (Z_to_bv 64 905152))) (Z_to_bv 64 905040) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905048) (word_to_le_bytes 8 (Z_to_bv 64 905032))) (Z_to_bv 64 905056) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1036928) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1036932) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1036929) ([Z_to_bv 8 0])) (Z_to_bv 64 905216) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_397a4 D_397a4 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_397a8 D_397a8 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 709128) ltac:(ok_win HJ).
      stw F_397ac D_397ac (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 803000) ltac:(ok_win HJ).
      sv F_397b0 D_397b0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_397b4 D_397b4.
      sn F_397b8 D_397b8.
      lb_step F_397bc D_397bc (Z_to_bv 8 0) ltac:(rd_img img_c7b10_1).
      sn F_397c0 D_397c0.
      stepb_tk F_397c4 D_397c4 ltac:(pin; cond_compute).
      sn F_397d0 D_397d0.
      sn F_397d4 D_397d4.
      sn F_397d8 D_397d8.
      stw F_397dc D_397dc (Z_to_bv 64 832832) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_397e0 D_397e0.
      ld_step F_397e4 D_397e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c6660_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_397e8 D_397e8 ltac:(pin; cond_compute).
      ld_step F_39808 D_39808 (word_to_le_bytes 8 (Z_to_bv 64 709128)) (Z_to_bv 64 709128) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_3980c D_3980c (word_to_le_bytes 8 (Z_to_bv 64 803000)) (Z_to_bv 64 803000) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_39810 D_39810 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_39814 D_39814 (0xad208 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_a9874 D_a9874.
      stepb_ft F_a9878 D_a9878 ltac:(pin; cond_compute).
      ld_step F_a987c D_a987c (word_to_le_bytes 8 (Z_to_bv 64 709304)) (Z_to_bv 64 709304) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9880 D_a9880 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a9884 D_a9884 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_a9888 D_a9888 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_a988c D_a988c (0xad2b8 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_a9924 D_a9924 (argc_w av).
      sv F_a9928 D_a9928 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_a992c D_a992c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_a9930 D_a9930 (0x3a170 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
