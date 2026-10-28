(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import
  StartupTac ArgvEnv RefLayout StartupRnd U.S0Img U.S0StartupDefs
  U.S0_code_1337c_1378c U.S0_code_1ed68_1f620 U.S0_code_1f620_20620 U.S0_code_256f4_26728 U.S0_code_26728_26f04.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHideSt.
Import WalkHideSt.OptIn.
Import ListNotations.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.                  (* [comment removed for export] *)
  Variable hw : word.                   (* [comment removed for export] *)
  Variable rnd : EntryDraw.             (* [comment removed for export] *)
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
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    cps_destruct (rnd_facts SEGS RPH sp0 av ev uid hw rnd Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (rnd_bytes rnd j n).
  Proof.
    intros J D j n Hjn.
    cps_destruct (rnd_facts SEGS RPH sp0 av ev uid hw rnd Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j n :=
    eapply rdn_addr; [apply (rd_rnd _ _ j n); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac ANDI_RND :=
    let RB := ident:(RB) in gres; pin; imm_norm;
    apply v_andi_3_aligned;
    cps_pose rnd_bounds as (_ & _ & RB); unorm;
    first [ rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity
          | exact RB | lia ].

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac RD_CANARY :=
    rewrite rdn_cmem_data by region_side;
    apply (rdn_canary SEGS _ 410704 rnd); lia.

  (* [comment removed for export] *)
  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 279008 ->
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
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 279008) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0x28a44 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166468))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410704) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 0 4)))))) (Z_to_bv 64 410708) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 4 4)))))) (Z_to_bv 64 410705) ([Z_to_bv 8 0])) (Z_to_bv 64 278992) (word_to_le_bytes 8 ((canary_w rnd))))) rom)) ->
    G (mkst regs (0x28a3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_1ee7c D_1ee7c (word_to_le_bytes 8 ((rnd_w sp0 av ev))) ((rnd_w sp0 av ev)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_1ee80 D_1ee80.  (* [comment removed for export] *)
      sv F_1f5d0 D_1f5d0 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1f5d4 D_1f5d4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 166468) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_1f5d8 D_1f5d8 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)  (* [comment removed for export] *)
      sv F_1f5dc D_1f5dc ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_1f5e0 D_1f5e0.  (* [comment removed for export] *)
      ld_step F_1f5e4 D_1f5e4 (word_to_le_bytes 8 (Z_to_bv 64 410704)) (Z_to_bv 64 410704) ltac:(rd_img img_27fa8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_1f5e8 D_1f5e8.  (* [comment removed for export] *)
      sn F_1f5ec D_1f5ec.  (* [comment removed for export] *)
      stepiv F_26534 D_26534 (Z_to_bv 64 0) ltac:(ANDI_RND).  (* [comment removed for export] *)
      stepb_tk F_26538 D_26538 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26648 D_26648.  (* [comment removed for export] *)
      sn F_2664c D_2664c.  (* [comment removed for export] *)
      stepb_ft F_26650 D_26650 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26654 D_26654.  (* [comment removed for export] *)
      stepb_tk F_26658 D_26658 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_26690 D_26690.  (* [comment removed for export] *)
      stepb_ft F_26694 D_26694 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_26698 D_26698 (rnd_bytes rnd 0 4) (lew (rnd_bytes rnd 0 4)) ltac:(RD_RND 0%nat 4%nat) ltac:(apply lew_ok; rewrite length_rnd_bytes; lia).  (* [comment removed for export] *)
      ld_step F_2669c D_2669c (rnd_bytes rnd 4 4) (lew (rnd_bytes rnd 4 4)) ltac:(RD_RND 4%nat 4%nat) ltac:(apply lew_ok; rewrite length_rnd_bytes; lia).  (* [comment removed for export] *)
      stw F_266a0 D_266a0 (Z_to_bv 64 410704) ((v_lw (lew (rnd_bytes rnd 0 4)))) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_266a4 D_266a4 (Z_to_bv 64 410708) ((v_lw (lew (rnd_bytes rnd 4 4)))) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_266a8 D_266a8.  (* [comment removed for export] *)
      sv F_266ac D_266ac (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_266b0 D_266b0.  (* [comment removed for export] *)
      stepb_tk F_266b4 D_266b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_268f4 D_268f4.  (* [comment removed for export] *)
      stepb_ft F_268f8 D_268f8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_268fc D_268fc.  (* [comment removed for export] *)
      stepb_ft F_26900 D_26900 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_26904 D_26904 (0x29338 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1f5f0 D_1f5f0.  (* [comment removed for export] *)
      sn F_1f60c D_1f60c.  (* [comment removed for export] *)
      ld_step F_1f610 D_1f610 (word_to_le_bytes 8 (Z_to_bv 64 410704)) (Z_to_bv 64 410704) ltac:(rd_img img_27fa8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_1f614 D_1f614 (Z_to_bv 64 410705) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1f618 D_1f618 (canary_bytes rnd) (canary_w rnd) ltac:(RD_CANARY) ltac:(apply canary_ok).  (* [comment removed for export] *)
      sn F_1f61c D_1f61c.  (* [comment removed for export] *)
      stw F_1f620 D_1f620 (Z_to_bv 64 278992) ((canary_w rnd)) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_1f624 D_1f624 (word_to_le_bytes 8 (Z_to_bv 64 166468)) (Z_to_bv 64 166468) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1f628 D_1f628 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_1f62c D_1f62c (0x28a44 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 279008 ->
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
        getr regs' 1 = (Z_to_bv 64 0) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 + 0)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 279008) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 79232) ->
        getr regs' 11 = ((argc_w av)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 18 = (Z_to_bv 64 0) ->
        getr regs' 19 = (Z_to_bv 64 0) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
        G (mkst regs' (0x28c04 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166468))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410704) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 0 4)))))) (Z_to_bv 64 410708) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 4 4)))))) (Z_to_bv 64 410705) ([Z_to_bv 8 0])) (Z_to_bv 64 278992) (word_to_le_bytes 8 ((canary_w rnd))))) rom)) ->
    G (mkst regs (0x28a44 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166468))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410704) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 0 4)))))) (Z_to_bv 64 410708) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 4 4)))))) (Z_to_bv 64 410705) ([Z_to_bv 8 0])) (Z_to_bv 64 278992) (word_to_le_bytes 8 ((canary_w rnd))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_1ee84 D_1ee84 (word_to_le_bytes 8 (uid)) (uid) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1ee88 D_1ee88 (word_to_le_bytes 8 (uid)) (uid) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_1ee8c D_1ee8c ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)  (* [comment removed for export] *)
      ld_step F_1ee90 D_1ee90 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_1ee94 D_1ee94 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_1ee98 D_1ee98 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_1ee9c D_1ee9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_1eea0 D_1eea0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_1ef80 D_1ef80 (word_to_le_bytes 8 (Z_to_bv 64 166872)) (Z_to_bv 64 166872) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1ef84 D_1ef84 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1ef88 D_1ef88 (word_to_le_bytes 8 ((argc_w av))) ((argc_w av)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1ef8c D_1ef8c (word_to_le_bytes 8 (Z_to_bv 64 79232)) (Z_to_bv 64 79232) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1ef90 D_1ef90 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_1ef94 D_1ef94 (0x28bd8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1f018 D_1f018.  (* [comment removed for export] *)
      sn F_1f01c D_1f01c.  (* [comment removed for export] *)
      sn F_1f020 D_1f020.  (* [comment removed for export] *)
      sv F_1f024 D_1f024 ((argc_w av)).  (* [comment removed for export] *)
      sv F_1f028 D_1f028 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_1f02c D_1f02c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1f030 D_1f030 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1f034 D_1f034 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1f038 D_1f038 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1f03c D_1f03c (Z_to_bv 64 (bv_unsigned sp0 + 0)).  (* [comment removed for export] *)
      stepret F_1f040 D_1f040 (0x28c04 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 + 0) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 279008 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 79232 ->
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
        getr regs' 1 = (Z_to_bv 64 166792) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 279008) ->
        getr regs' 8 = (Z_to_bv 64 204944) ->
        getr regs' 9 = (Z_to_bv 64 204936) ->
        getr regs' 18 = (Z_to_bv 64 79232) ->
        getr regs' 19 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 20 = (Z_to_bv 64 0) ->
        getr regs' 21 = (Z_to_bv 64 0) ->
        getr regs' 22 = (Z_to_bv 64 0) ->
        getr regs' 23 = (Z_to_bv 64 0) ->
        getr regs' 24 = (Z_to_bv 64 0) ->
        getr regs' 25 = (Z_to_bv 64 0) ->
        getr regs' 26 = (Z_to_bv 64 0) ->
        getr regs' 27 = (Z_to_bv 64 0) ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
        G (mkst regs' (0x1347c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166468))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 166968))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 ((argc_w av)))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410704) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 0 4)))))) (Z_to_bv 64 410708) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 4 4)))))) (Z_to_bv 64 410705) ([Z_to_bv 8 0])) (Z_to_bv 64 278992) (word_to_le_bytes 8 ((canary_w rnd))))) rom)) ->
    G (mkst regs (0x28c04 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166468))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410704) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 0 4)))))) (Z_to_bv 64 410708) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 4 4)))))) (Z_to_bv 64 410705) ([Z_to_bv 8 0])) (Z_to_bv 64 278992) (word_to_le_bytes 8 ((canary_w rnd))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_1f044 D_1f044 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_1f048 D_1f048 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1f04c D_1f04c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1f050 D_1f050 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1f054 D_1f054 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1f058 D_1f058 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_1f05c D_1f05c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_1f060 D_1f060 ((argc_w av)).  (* [comment removed for export] *)
      sn F_1f064 D_1f064.  (* [comment removed for export] *)
      stepiv F_1f068 D_1f068 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_1f06c D_1f06c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_1f070 D_1f070 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_1f074 D_1f074.  (* [comment removed for export] *)
      sv F_1ef98 D_1ef98 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_1ef9c D_1ef9c (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 166968) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1efa0 D_1efa0 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1efa4 D_1efa4 (Z_to_bv 64 (bv_unsigned sp0 - 72)) ((argc_w av)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_1efa8 D_1efa8.  (* [comment removed for export] *)
      stepret F_1ed68 D_1ed68 (0x28b6c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1efac D_1efac.  (* [comment removed for export] *)
      sn F_1efb0 D_1efb0.  (* [comment removed for export] *)
      ld_step F_1efb4 D_1efb4 (word_to_le_bytes 8 (Z_to_bv 64 204944)) (Z_to_bv 64 204944) ltac:(rd_img img_27f98_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1efb8 D_1efb8 (word_to_le_bytes 8 (Z_to_bv 64 204936)) (Z_to_bv 64 204936) ltac:(rd_img img_27fa0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_1efbc D_1efbc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_1efc0 D_1efc0 (word_to_le_bytes 8 (Z_to_bv 64 78972)) (Z_to_bv 64 78972) ltac:(rd_img img_27f08_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_1efc4 D_1efc4 (0x1347c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 166792 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 279008 ->
    getr regs 8 = Z_to_bv 64 204944 ->
    getr regs 9 = Z_to_bv 64 204936 ->
    getr regs 18 = Z_to_bv 64 79232 ->
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
        getr regs' 1 = (Z_to_bv 64 166984) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 279008) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = ((argc_w av)) ->
        getr regs' 10 = ((argc_w av)) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 79232) ->
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
        G (mkst regs' (0x13580 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166468))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 166968))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 ((argc_w av)))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 166792))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 204944))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410704) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 0 4)))))) (Z_to_bv 64 410708) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 4 4)))))) (Z_to_bv 64 410705) ([Z_to_bv 8 0])) (Z_to_bv 64 278992) (word_to_le_bytes 8 ((canary_w rnd)))) (Z_to_bv 64 213136) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x1347c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166460))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 ((pn_w sp0 av ev)))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 (s1v))) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 410736))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 166468))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 166968))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 ((argc_w av)))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 410120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410136) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410128) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 410760) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 410768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 279024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 279000) (word_to_le_bytes 8 (Z_to_bv 64 279024))) (Z_to_bv 64 278808) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 410736) ([Z_to_bv 8 1])) (Z_to_bv 64 278848) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 278840) (word_to_le_bytes 4 (tid))) (Z_to_bv 64 278960) (word_to_le_bytes 8 (Z_to_bv 64 410792))) (Z_to_bv 64 278928) (word_to_le_bytes 8 (Z_to_bv 64 278928))) (Z_to_bv 64 278816) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278824) (word_to_le_bytes 8 (Z_to_bv 64 278808))) (Z_to_bv 64 278832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 410704) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 0 4)))))) (Z_to_bv 64 410708) (word_to_le_bytes 4 ((v_lw (lew (rnd_bytes rnd 4 4)))))) (Z_to_bv 64 410705) ([Z_to_bv 8 0])) (Z_to_bv 64 278992) (word_to_le_bytes 8 ((canary_w rnd))))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. cps_pose rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    pose proof (u64_range uid) as Huid. pose proof (u64_range hw) as Hhw.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_133c4 D_133c4 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_133c8 D_133c8 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 166792) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_133cc D_133cc (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 204944) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_133d0 D_133d0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_133d4 D_133d4.  (* [comment removed for export] *)
      sn F_133d8 D_133d8.  (* [comment removed for export] *)
      lb_step F_133dc D_133dc (Z_to_bv 8 0) ltac:(rd_img img_29ec0_1).  (* [comment removed for export] *)
      sn F_133e0 D_133e0.  (* [comment removed for export] *)
      stepb_tk F_133e4 D_133e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_133f0 D_133f0.  (* [comment removed for export] *)
      sn F_133f4 D_133f4.  (* [comment removed for export] *)
      sn F_133f8 D_133f8.  (* [comment removed for export] *)
      stw F_133fc D_133fc (Z_to_bv 64 213136) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_13400 D_13400.  (* [comment removed for export] *)
      ld_step F_13404 D_13404 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_27f48_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_13408 D_13408 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_13428 D_13428 (word_to_le_bytes 8 (Z_to_bv 64 166792)) (Z_to_bv 64 166792) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1342c D_1342c (word_to_le_bytes 8 (Z_to_bv 64 204944)) (Z_to_bv 64 204944) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_13430 D_13430 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_13434 D_13434 (0x28b88 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1efc8 D_1efc8.  (* [comment removed for export] *)
      stepb_ft F_1efcc D_1efcc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_1efd0 D_1efd0 (word_to_le_bytes 8 (Z_to_bv 64 166968)) (Z_to_bv 64 166968) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1efd4 D_1efd4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1efd8 D_1efd8 (word_to_le_bytes 8 ((argc_w av))) ((argc_w av)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_1efdc D_1efdc (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_1efe0 D_1efe0 (0x28c38 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_1f078 D_1f078 ((argc_w av)).  (* [comment removed for export] *)
      sv F_1f07c D_1f07c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_1f080 D_1f080 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_1f084 D_1f084 (0x13580 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
