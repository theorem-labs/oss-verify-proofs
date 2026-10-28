(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import StartupTac ArgvEnv RefLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10Img_u Pm10StartupDefs_u
  Pm10_code_38dc8_39000_u Pm10_code_a4000_a5000_u Pm10_code_a5000_a6000_u Pm10_code_b5000_b6000_u         .
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require PropExec.
Section FPX_1. Context {fx : PropExec.FPState}.

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
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

  Ltac RD_RND j :=
    eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

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

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 878592 ->
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
        getr regs' 4 = Z_to_bv 64 878592 ->
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
        G (mkst regs' (0xa6910 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682248))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1010320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682256))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1009704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1010344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1010352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 878608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 878584) (word_to_le_bytes 8 (Z_to_bv 64 878608))) (Z_to_bv 64 878392) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 1010320) ([Z_to_bv 8 1])) (Z_to_bv 64 878432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 878424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 878544) (word_to_le_bytes 8 (Z_to_bv 64 1010376))) (Z_to_bv 64 878512) (word_to_le_bytes 8 (Z_to_bv 64 878512))) (Z_to_bv 64 878400) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878408) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1010288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1010292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1010289) ([Z_to_bv 8 0])) (Z_to_bv 64 878576) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa6908 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682248))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1010320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1009704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1010344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1010352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 878608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 878584) (word_to_le_bytes 8 (Z_to_bv 64 878608))) (Z_to_bv 64 878392) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 1010320) ([Z_to_bv 8 1])) (Z_to_bv 64 878432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 878424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 878544) (word_to_le_bytes 8 (Z_to_bv 64 1010376))) (Z_to_bv 64 878512) (word_to_le_bytes 8 (Z_to_bv 64 878512))) (Z_to_bv 64 878400) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878408) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878416) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_a4b0c D_a4b0c (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_a4b10 D_a4b10.
      sv F_a54c8 D_a54c8 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_a54cc D_a54cc (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 682256) ltac:(ok_win HJ).
      stepb_ft F_a54d0 D_a54d0 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_a54d4 D_a54d4 (rnd_w sp0 av ev).
      sn F_a54d8 D_a54d8.
      ld_step F_a54dc D_a54dc (word_to_le_bytes 8 (Z_to_bv 64 1010288)) (Z_to_bv 64 1010288) ltac:(rd_img img_c1bb8_8) ltac:(apply bytes_le_to_Z_8).
      sn F_a54e0 D_a54e0.
      sn F_a54e4 D_a54e4.
      stepiv F_b5a04 D_b5a04 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_b5a08 D_b5a08 ltac:(pin; cond_compute).
      sn F_b5b18 D_b5b18.
      sn F_b5b1c D_b5b1c.
      stepb_ft F_b5b20 D_b5b20 ltac:(pin; cond_compute).
      sn F_b5b24 D_b5b24.
      stepb_tk F_b5b28 D_b5b28 ltac:(pin; cond_compute).
      sn F_b5b60 D_b5b60.
      stepb_ft F_b5b64 D_b5b64 ltac:(pin; cond_compute).
      ld_step F_b5b68 D_b5b68 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
      ld_step F_b5b6c D_b5b6c (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
      stw F_b5b70 D_b5b70 (Z_to_bv 64 1010288) (rlw RND 0) ltac:(ok_data).
      stw F_b5b74 D_b5b74 (Z_to_bv 64 1010292) (rlw RND 4) ltac:(ok_data).
      sn F_b5b78 D_b5b78.
      sv F_b5b7c D_b5b7c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).
      sn F_b5b80 D_b5b80.
      stepb_tk F_b5b84 D_b5b84 ltac:(pin; cond_compute).
      sn F_b5dc4 D_b5dc4.
      stepb_ft F_b5dc8 D_b5dc8 ltac:(pin; cond_compute).
      sn F_b5dcc D_b5dcc.
      stepb_ft F_b5dd0 D_b5dd0 ltac:(pin; cond_compute).
      stepret F_b5dd4 D_b5dd4 (0xa72d8 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_a54e8 D_a54e8.
      sn F_a5504 D_a5504.
      ld_step F_a5508 D_a5508 (word_to_le_bytes 8 (Z_to_bv 64 1010288)) (Z_to_bv 64 1010288) ltac:(rd_img img_c1bb8_8) ltac:(apply bytes_le_to_Z_8).
      stw F_a550c D_a550c (Z_to_bv 64 1010289) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_a5510 D_a5510 (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
      sn F_a5514 D_a5514.
      stw F_a5518 D_a5518 (Z_to_bv 64 878576) (canary_w RND) ltac:(ok_data).
      ld_step F_a551c D_a551c (word_to_le_bytes 8 (Z_to_bv 64 682256)) (Z_to_bv 64 682256) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_a5520 D_a5520 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_a5524 D_a5524 (0xa6910 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 878592 ->
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
        getr regs' 4 = Z_to_bv 64 878592 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 234060 ->
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
        G (mkst regs' (0xa6ad0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682248))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1010320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682256))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1009704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1010344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1010352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 878608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 878584) (word_to_le_bytes 8 (Z_to_bv 64 878608))) (Z_to_bv 64 878392) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 1010320) ([Z_to_bv 8 1])) (Z_to_bv 64 878432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 878424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 878544) (word_to_le_bytes 8 (Z_to_bv 64 1010376))) (Z_to_bv 64 878512) (word_to_le_bytes 8 (Z_to_bv 64 878512))) (Z_to_bv 64 878400) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878408) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1010288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1010292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1010289) ([Z_to_bv 8 0])) (Z_to_bv 64 878576) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa6910 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682248))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1010320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682256))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1009704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1010344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1010352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 878608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 878584) (word_to_le_bytes 8 (Z_to_bv 64 878608))) (Z_to_bv 64 878392) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 1010320) ([Z_to_bv 8 1])) (Z_to_bv 64 878432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 878424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 878544) (word_to_le_bytes 8 (Z_to_bv 64 1010376))) (Z_to_bv 64 878512) (word_to_le_bytes 8 (Z_to_bv 64 878512))) (Z_to_bv 64 878400) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878408) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1010288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1010292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1010289) ([Z_to_bv 8 0])) (Z_to_bv 64 878576) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_a4b14 D_a4b14 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4b18 D_a4b18 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_a4b1c D_a4b1c ltac:(pin; first [apply c_eq_refl | cond_compute]).
      ld_step F_a4b20 D_a4b20 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      ld_step F_a4b24 D_a4b24 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      stepb_ft F_a4b28 D_a4b28 ltac:(pin; cond_compute).
      ld_step F_a4b2c D_a4b2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_a4b30 D_a4b30 ltac:(pin; cond_compute).
      ld_step F_a4c10 D_a4c10 (word_to_le_bytes 8 (Z_to_bv 64 682660)) (Z_to_bv 64 682660) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4c14 D_a4c14 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4c18 D_a4c18 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4c1c D_a4c1c (word_to_le_bytes 8 (Z_to_bv 64 234060)) (Z_to_bv 64 234060) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_a4c20 D_a4c20 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_a4c24 D_a4c24 (0xa6aa4 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_a4ca8 D_a4ca8.
      sn F_a4cac D_a4cac.
      sn F_a4cb0 D_a4cb0.
      sv F_a4cb4 D_a4cb4 (argc_w av).
      sv F_a4cb8 D_a4cb8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_a4cbc D_a4cbc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4cc0 D_a4cc0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4cc4 D_a4cc4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4cc8 D_a4cc8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_a4ccc D_a4ccc sp0.
      stepret F_a4cd0 D_a4cd0 (0xa6ad0 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 878592 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 234060 ->
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
        getr regs' 1 = Z_to_bv 64 682580 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 878592 ->
        getr regs' 8 = Z_to_bv 64 776448 ->
        getr regs' 9 = Z_to_bv 64 776440 ->
        getr regs' 18 = Z_to_bv 64 234060 ->
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
        G (mkst regs' (0x39148 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682248))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1010320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682256))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 682756))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1009704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1010344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1010352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 878608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 878584) (word_to_le_bytes 8 (Z_to_bv 64 878608))) (Z_to_bv 64 878392) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 1010320) ([Z_to_bv 8 1])) (Z_to_bv 64 878432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 878424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 878544) (word_to_le_bytes 8 (Z_to_bv 64 1010376))) (Z_to_bv 64 878512) (word_to_le_bytes 8 (Z_to_bv 64 878512))) (Z_to_bv 64 878400) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878408) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1010288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1010292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1010289) ([Z_to_bv 8 0])) (Z_to_bv 64 878576) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa6ad0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682248))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1010320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682256))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1009704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1010344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1010352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 878608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 878584) (word_to_le_bytes 8 (Z_to_bv 64 878608))) (Z_to_bv 64 878392) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 1010320) ([Z_to_bv 8 1])) (Z_to_bv 64 878432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 878424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 878544) (word_to_le_bytes 8 (Z_to_bv 64 1010376))) (Z_to_bv 64 878512) (word_to_le_bytes 8 (Z_to_bv 64 878512))) (Z_to_bv 64 878400) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878408) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1010288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1010292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1010289) ([Z_to_bv 8 0])) (Z_to_bv 64 878576) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_a4cd4 D_a4cd4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_a4cd8 D_a4cd8 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a4cdc D_a4cdc (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a4ce0 D_a4ce0 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a4ce4 D_a4ce4 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_a4ce8 D_a4ce8 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_a4cec D_a4cec (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_a4cf0 D_a4cf0 (argc_w av).
      sn F_a4cf4 D_a4cf4.
      stepiv F_a4cf8 D_a4cf8 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_a4cfc D_a4cfc (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_a4d00 D_a4d00 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_a4d04 D_a4d04.
      sv F_a4c28 D_a4c28 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_a4c2c D_a4c2c (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 682756) ltac:(ok_win HJ).
      stw F_a4c30 D_a4c30 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_a4c34 D_a4c34 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).
      sn F_a4c38 D_a4c38.
      stepret F_a49f8 D_a49f8 (0xa6a38 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_a4c3c D_a4c3c.
      sn F_a4c40 D_a4c40.
      ld_step F_a4c44 D_a4c44 (word_to_le_bytes 8 (Z_to_bv 64 776448)) (Z_to_bv 64 776448) ltac:(rd_img img_c1ba8_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4c48 D_a4c48 (word_to_le_bytes 8 (Z_to_bv 64 776440)) (Z_to_bv 64 776440) ltac:(rd_img img_c1bb0_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_a4c4c D_a4c4c ltac:(pin; cond_compute).
      ld_step F_a4c50 D_a4c50 (word_to_le_bytes 8 (Z_to_bv 64 233800)) (Z_to_bv 64 233800) ltac:(rd_img img_bba68_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_a4c54 D_a4c54 (0x39148 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 682580 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 878592 ->
    getr regs 8 = Z_to_bv 64 776448 ->
    getr regs 9 = Z_to_bv 64 776440 ->
    getr regs 18 = Z_to_bv 64 234060 ->
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
        getr regs' 1 = Z_to_bv 64 682772 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 878592 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 234060 ->
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
        G (mkst regs' (0x3924c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682248))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1010320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682256))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 682756))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 682580))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 776448))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1009704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1010344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1010352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 878608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 878584) (word_to_le_bytes 8 (Z_to_bv 64 878608))) (Z_to_bv 64 878392) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 1010320) ([Z_to_bv 8 1])) (Z_to_bv 64 878432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 878424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 878544) (word_to_le_bytes 8 (Z_to_bv 64 1010376))) (Z_to_bv 64 878512) (word_to_le_bytes 8 (Z_to_bv 64 878512))) (Z_to_bv 64 878400) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878408) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1010288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1010292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1010289) ([Z_to_bv 8 0])) (Z_to_bv 64 878576) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 806256) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x39148 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682248))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1010320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 682256))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 682756))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1009704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1009712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1010344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1010352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 878608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 878584) (word_to_le_bytes 8 (Z_to_bv 64 878608))) (Z_to_bv 64 878392) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 1010320) ([Z_to_bv 8 1])) (Z_to_bv 64 878432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 878424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 878544) (word_to_le_bytes 8 (Z_to_bv 64 1010376))) (Z_to_bv 64 878512) (word_to_le_bytes 8 (Z_to_bv 64 878512))) (Z_to_bv 64 878400) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878408) (word_to_le_bytes 8 (Z_to_bv 64 878392))) (Z_to_bv 64 878416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1010288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1010292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1010289) ([Z_to_bv 8 0])) (Z_to_bv 64 878576) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_38e10 D_38e10 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_38e14 D_38e14 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 682580) ltac:(ok_win HJ).
      stw F_38e18 D_38e18 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 776448) ltac:(ok_win HJ).
      sv F_38e1c D_38e1c (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_38e20 D_38e20.
      sn F_38e24 D_38e24.
      lb_step F_38e28 D_38e28 (Z_to_bv 8 0) ltac:(rd_img img_c2ee0_1).
      sn F_38e2c D_38e2c.
      stepb_tk F_38e30 D_38e30 ltac:(pin; cond_compute).
      sn F_38e3c D_38e3c.
      sn F_38e40 D_38e40.
      sn F_38e44 D_38e44.
      stw F_38e48 D_38e48 (Z_to_bv 64 806256) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_38e4c D_38e4c.
      ld_step F_38e50 D_38e50 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c1a30_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_38e54 D_38e54 ltac:(pin; cond_compute).
      ld_step F_38e74 D_38e74 (word_to_le_bytes 8 (Z_to_bv 64 682580)) (Z_to_bv 64 682580) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_38e78 D_38e78 (word_to_le_bytes 8 (Z_to_bv 64 776448)) (Z_to_bv 64 776448) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_38e7c D_38e7c (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_38e80 D_38e80 (0xa6a54 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_a4c58 D_a4c58.
      stepb_ft F_a4c5c D_a4c5c ltac:(pin; cond_compute).
      ld_step F_a4c60 D_a4c60 (word_to_le_bytes 8 (Z_to_bv 64 682756)) (Z_to_bv 64 682756) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4c64 D_a4c64 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_a4c68 D_a4c68 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_a4c6c D_a4c6c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_a4c70 D_a4c70 (0xa6b04 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_a4d08 D_a4d08 (argc_w av).
      sv F_a4d0c D_a4d0c (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_a4d10 D_a4d10 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_a4d14 D_a4d14 (0x3924c : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
