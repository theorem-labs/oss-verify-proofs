(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  StartupTac ArgvEnv RefLayout Src0Img Src0StartupDefs
  Src0_code_1ffac_20088 Src0_code_4abb8_4b0b4 Src0_code_4b104_4b654 Src0_code_58828_59540.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

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
  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 459832 ->
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
        getr regs' 4 = Z_to_bv 64 459832 ->
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
        G (mkst regs' (0x4acd4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306388))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 591528) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 591532) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 591529) ([Z_to_bv 8 0])) (Z_to_bv 64 459816) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x4accc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_4accc D_4accc (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4acd0 D_4acd0.  (* [comment removed for export] *)
      sv F_4b5b4 D_4b5b4 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_4b5b8 D_4b5b8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 306388) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_4b5bc D_4b5bc ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_4b5c0 D_4b5c0 (rnd_w sp0 av ev).  (* [comment removed for export] *)
      sn F_4b5c4 D_4b5c4.  (* [comment removed for export] *)
      ld_step F_4b5c8 D_4b5c8 (word_to_le_bytes 8 (Z_to_bv 64 591528)) (Z_to_bv 64 591528) ltac:(rd_img img_5e5f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4b5cc D_4b5cc.  (* [comment removed for export] *)
      sn F_4b5d0 D_4b5d0.  (* [comment removed for export] *)
      stepiv F_58924 D_58924 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_58928 D_58928 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_58a38 D_58a38.  (* [comment removed for export] *)
      sn F_58a3c D_58a3c.  (* [comment removed for export] *)
      stepb_ft F_58a40 D_58a40 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_58a44 D_58a44.  (* [comment removed for export] *)
      stepb_tk F_58a48 D_58a48 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_58a80 D_58a80.  (* [comment removed for export] *)
      stepb_ft F_58a84 D_58a84 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_58a88 D_58a88 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).  (* [comment removed for export] *)
      ld_step F_58a8c D_58a8c (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).  (* [comment removed for export] *)
      stw F_58a90 D_58a90 (Z_to_bv 64 591528) (rlw RND 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_58a94 D_58a94 (Z_to_bv 64 591532) (rlw RND 4) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_58a98 D_58a98.  (* [comment removed for export] *)
      sv F_58a9c D_58a9c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_58aa0 D_58aa0.  (* [comment removed for export] *)
      stepb_tk F_58aa4 D_58aa4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_58ce4 D_58ce4.  (* [comment removed for export] *)
      stepb_ft F_58ce8 D_58ce8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_58cec D_58cec.  (* [comment removed for export] *)
      stepb_ft F_58cf0 D_58cf0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_58cf4 D_58cf4 (0x4b5d4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_4b5d4 D_4b5d4.  (* [comment removed for export] *)
      sn F_4b5f0 D_4b5f0.  (* [comment removed for export] *)
      ld_step F_4b5f4 D_4b5f4 (word_to_le_bytes 8 (Z_to_bv 64 591528)) (Z_to_bv 64 591528) ltac:(rd_img img_5e5f0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_4b5f8 D_4b5f8 (Z_to_bv 64 591529) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_4b5fc D_4b5fc (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_4b600 D_4b600.  (* [comment removed for export] *)
      stw F_4b604 D_4b604 (Z_to_bv 64 459816) (canary_w RND) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_4b608 D_4b608 (word_to_le_bytes 8 (Z_to_bv 64 306388)) (Z_to_bv 64 306388) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4b60c D_4b60c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_4b610 D_4b610 (0x4acd4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 459832 ->
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
        getr regs' 4 = Z_to_bv 64 459832 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 131320 ->
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
        G (mkst regs' (0x4ae94 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306388))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 591528) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 591532) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 591529) ([Z_to_bv 8 0])) (Z_to_bv 64 459816) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x4acd4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306388))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 591528) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 591532) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 591529) ([Z_to_bv 8 0])) (Z_to_bv 64 459816) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_4acd4 D_4acd4 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4acd8 D_4acd8 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_4acdc D_4acdc ltac:(pin; first [apply c_eq_refl | cond_compute]).  (* [comment removed for export] *)
      ld_step F_4ace0 D_4ace0 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_4ace4 D_4ace4 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4ace8 D_4ace8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4acec D_4acec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_4acf0 D_4acf0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4add0 D_4add0 (word_to_le_bytes 8 (Z_to_bv 64 306792)) (Z_to_bv 64 306792) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4add4 D_4add4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4add8 D_4add8 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4addc D_4addc (word_to_le_bytes 8 (Z_to_bv 64 131320)) (Z_to_bv 64 131320) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4ade0 D_4ade0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_4ade4 D_4ade4 (0x4ae68 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_4ae68 D_4ae68.  (* [comment removed for export] *)
      sn F_4ae6c D_4ae6c.  (* [comment removed for export] *)
      sn F_4ae70 D_4ae70.  (* [comment removed for export] *)
      sv F_4ae74 D_4ae74 (argc_w av).  (* [comment removed for export] *)
      sv F_4ae78 D_4ae78 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_4ae7c D_4ae7c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4ae80 D_4ae80 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4ae84 D_4ae84 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4ae88 D_4ae88 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4ae8c D_4ae8c sp0.  (* [comment removed for export] *)
      stepret F_4ae90 D_4ae90 (0x4ae94 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
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
    getr regs 4 = Z_to_bv 64 459832 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 131320 ->
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
        getr regs' 1 = Z_to_bv 64 306712 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 459832 ->
        getr regs' 8 = Z_to_bv 64 373224 ->
        getr regs' 9 = Z_to_bv 64 373216 ->
        getr regs' 18 = Z_to_bv 64 131320 ->
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
        G (mkst regs' (0x1fff4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306388))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 306888))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 591528) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 591532) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 591529) ([Z_to_bv 8 0])) (Z_to_bv 64 459816) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x4ae94 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306388))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 591528) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 591532) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 591529) ([Z_to_bv 8 0])) (Z_to_bv 64 459816) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_4ae94 D_4ae94 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_4ae98 D_4ae98 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4ae9c D_4ae9c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aea0 D_4aea0 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aea4 D_4aea4 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4aea8 D_4aea8 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_4aeac D_4aeac (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_4aeb0 D_4aeb0 (argc_w av).  (* [comment removed for export] *)
      sn F_4aeb4 D_4aeb4.  (* [comment removed for export] *)
      stepiv F_4aeb8 D_4aeb8 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_4aebc D_4aebc (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_4aec0 D_4aec0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_4aec4 D_4aec4.  (* [comment removed for export] *)
      sv F_4ade8 D_4ade8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_4adec D_4adec (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 306888) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4adf0 D_4adf0 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4adf4 D_4adf4 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_4adf8 D_4adf8.  (* [comment removed for export] *)
      stepret F_4abb8 D_4abb8 (0x4adfc : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_4adfc D_4adfc.  (* [comment removed for export] *)
      sn F_4ae00 D_4ae00.  (* [comment removed for export] *)
      ld_step F_4ae04 D_4ae04 (word_to_le_bytes 8 (Z_to_bv 64 373224)) (Z_to_bv 64 373224) ltac:(rd_img img_5e5e0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4ae08 D_4ae08 (word_to_le_bytes 8 (Z_to_bv 64 373216)) (Z_to_bv 64 373216) ltac:(rd_img img_5e5e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_4ae0c D_4ae0c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ae10 D_4ae10 (word_to_le_bytes 8 (Z_to_bv 64 131060)) (Z_to_bv 64 131060) ltac:(rd_img img_5b1e0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_4ae14 D_4ae14 (0x1fff4 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 306712 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 459832 ->
    getr regs 8 = Z_to_bv 64 373224 ->
    getr regs 9 = Z_to_bv 64 373216 ->
    getr regs 18 = Z_to_bv 64 131320 ->
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
        getr regs' 1 = Z_to_bv 64 306904 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 459832 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 131320 ->
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
        G (mkst regs' (0x200f8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306388))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 306888))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 306712))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 373224))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 591528) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 591532) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 591529) ([Z_to_bv 8 0])) (Z_to_bv 64 459816) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 391280) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x1fff4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306380))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 591560))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 306388))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 306888))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 590944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590960) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 590952) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 591584) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 591592) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 459848) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 459824) (word_to_le_bytes 8 (Z_to_bv 64 459848))) (Z_to_bv 64 459632) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 591560) ([Z_to_bv 8 1])) (Z_to_bv 64 459672) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 459664) (word_to_le_bytes 4 tid)) (Z_to_bv 64 459784) (word_to_le_bytes 8 (Z_to_bv 64 591616))) (Z_to_bv 64 459752) (word_to_le_bytes 8 (Z_to_bv 64 459752))) (Z_to_bv 64 459640) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459648) (word_to_le_bytes 8 (Z_to_bv 64 459632))) (Z_to_bv 64 459656) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 591528) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 591532) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 591529) ([Z_to_bv 8 0])) (Z_to_bv 64 459816) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_1fff4 D_1fff4 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_1fff8 D_1fff8 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 306712) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1fffc D_1fffc (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 373224) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_20000 D_20000 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_20004 D_20004.  (* [comment removed for export] *)
      sn F_20008 D_20008.  (* [comment removed for export] *)
      lb_step F_2000c D_2000c (Z_to_bv 8 0) ltac:(rd_img img_5f870_1).  (* [comment removed for export] *)
      sn F_20010 D_20010.  (* [comment removed for export] *)
      stepb_tk F_20014 D_20014 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20020 D_20020.  (* [comment removed for export] *)
      sn F_20024 D_20024.  (* [comment removed for export] *)
      sn F_20028 D_20028.  (* [comment removed for export] *)
      stw F_2002c D_2002c (Z_to_bv 64 391280) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_20030 D_20030.  (* [comment removed for export] *)
      ld_step F_20034 D_20034 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5e4c0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_20038 D_20038 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_20058 D_20058 (word_to_le_bytes 8 (Z_to_bv 64 306712)) (Z_to_bv 64 306712) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2005c D_2005c (word_to_le_bytes 8 (Z_to_bv 64 373224)) (Z_to_bv 64 373224) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_20060 D_20060 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_20064 D_20064 (0x4ae18 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_4ae18 D_4ae18.  (* [comment removed for export] *)
      stepb_ft F_4ae1c D_4ae1c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4ae20 D_4ae20 (word_to_le_bytes 8 (Z_to_bv 64 306888)) (Z_to_bv 64 306888) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4ae24 D_4ae24 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4ae28 D_4ae28 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4ae2c D_4ae2c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_4ae30 D_4ae30 (0x4aec8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_4aec8 D_4aec8 (argc_w av).  (* [comment removed for export] *)
      sv F_4aecc D_4aecc (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_4aed0 D_4aed0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_4aed4 D_4aed4 (0x200f8 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
