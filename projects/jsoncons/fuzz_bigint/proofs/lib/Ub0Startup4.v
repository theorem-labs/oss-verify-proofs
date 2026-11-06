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
  Ub0_code_201fc_21084 Ub0_code_4b6b4_4c150 Ub0_code_59324_59540 Ub0_code_59540_5a048.
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
  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 462648 ->
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
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0x4b7d0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309200))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 594344) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 594348) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 594345) ([Z_to_bv 8 0])) (Z_to_bv 64 462632) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x4b7c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_4b7c8 D_4b7c8 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4b7cc D_4b7cc.  (* [comment removed for export] *)
      sv F_4c0b0 D_4c0b0 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_4c0b4 D_4c0b4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 309200) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_4c0b8 D_4c0b8 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_4c0bc D_4c0bc (rnd_w sp0 av ev).  (* [comment removed for export] *)
      sn F_4c0c0 D_4c0c0.  (* [comment removed for export] *)
      ld_step F_4c0c4 D_4c0c4 (word_to_le_bytes 8 (Z_to_bv 64 594344)) (Z_to_bv 64 594344) ltac:(rd_img img_5f0e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_4c0c8 D_4c0c8.  (* [comment removed for export] *)
      sn F_4c0cc D_4c0cc.  (* [comment removed for export] *)
      stepiv F_59420 D_59420 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_59424 D_59424 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_59534 D_59534.  (* [comment removed for export] *)
      sn F_59538 D_59538.  (* [comment removed for export] *)
      stepb_ft F_5953c D_5953c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_59540 D_59540.  (* [comment removed for export] *)
      stepb_tk F_59544 D_59544 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_5957c D_5957c.  (* [comment removed for export] *)
      stepb_ft F_59580 D_59580 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_59584 D_59584 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).  (* [comment removed for export] *)
      ld_step F_59588 D_59588 (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).  (* [comment removed for export] *)
      stw F_5958c D_5958c (Z_to_bv 64 594344) (rlw RND 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_59590 D_59590 (Z_to_bv 64 594348) (rlw RND 4) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_59594 D_59594.  (* [comment removed for export] *)
      sv F_59598 D_59598 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_5959c D_5959c.  (* [comment removed for export] *)
      stepb_tk F_595a0 D_595a0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_597e0 D_597e0.  (* [comment removed for export] *)
      stepb_ft F_597e4 D_597e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_597e8 D_597e8.  (* [comment removed for export] *)
      stepb_ft F_597ec D_597ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_597f0 D_597f0 (0x4c0d0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_4c0d0 D_4c0d0.  (* [comment removed for export] *)
      sn F_4c0ec D_4c0ec.  (* [comment removed for export] *)
      ld_step F_4c0f0 D_4c0f0 (word_to_le_bytes 8 (Z_to_bv 64 594344)) (Z_to_bv 64 594344) ltac:(rd_img img_5f0e8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_4c0f4 D_4c0f4 (Z_to_bv 64 594345) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_4c0f8 D_4c0f8 (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_4c0fc D_4c0fc.  (* [comment removed for export] *)
      stw F_4c100 D_4c100 (Z_to_bv 64 462632) (canary_w RND) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_4c104 D_4c104 (word_to_le_bytes 8 (Z_to_bv 64 309200)) (Z_to_bv 64 309200) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4c108 D_4c108 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_4c10c D_4c10c (0x4b7d0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 462648 ->
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
        getr regs' 4 = Z_to_bv 64 462648 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 131912 ->
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
        G (mkst regs' (0x4b990 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309200))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 594344) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 594348) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 594345) ([Z_to_bv 8 0])) (Z_to_bv 64 462632) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x4b7d0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309200))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 594344) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 594348) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 594345) ([Z_to_bv 8 0])) (Z_to_bv 64 462632) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_4b7d0 D_4b7d0 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b7d4 D_4b7d4 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_4b7d8 D_4b7d8 ltac:(pin; first [apply c_eq_refl | cond_compute]).  (* [comment removed for export] *)
      ld_step F_4b7dc D_4b7dc (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_4b7e0 D_4b7e0 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_4b7e4 D_4b7e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4b7e8 D_4b7e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_4b7ec D_4b7ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4b8cc D_4b8cc (word_to_le_bytes 8 (Z_to_bv 64 309604)) (Z_to_bv 64 309604) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b8d0 D_4b8d0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b8d4 D_4b8d4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b8d8 D_4b8d8 (word_to_le_bytes 8 (Z_to_bv 64 131912)) (Z_to_bv 64 131912) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4b8dc D_4b8dc (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_4b8e0 D_4b8e0 (0x4b964 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_4b964 D_4b964.  (* [comment removed for export] *)
      sn F_4b968 D_4b968.  (* [comment removed for export] *)
      sn F_4b96c D_4b96c.  (* [comment removed for export] *)
      sv F_4b970 D_4b970 (argc_w av).  (* [comment removed for export] *)
      sv F_4b974 D_4b974 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_4b978 D_4b978 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b97c D_4b97c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b980 D_4b980 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b984 D_4b984 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4b988 D_4b988 sp0.  (* [comment removed for export] *)
      stepret F_4b98c D_4b98c (0x4b990 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
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
    getr regs 4 = Z_to_bv 64 462648 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 131912 ->
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
        getr regs' 1 = Z_to_bv 64 309524 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 462648 ->
        getr regs' 8 = Z_to_bv 64 376032 ->
        getr regs' 9 = Z_to_bv 64 376024 ->
        getr regs' 18 = Z_to_bv 64 131912 ->
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
        G (mkst regs' (0x20244 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309200))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 309700))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 594344) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 594348) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 594345) ([Z_to_bv 8 0])) (Z_to_bv 64 462632) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x4b990 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309200))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 594344) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 594348) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 594345) ([Z_to_bv 8 0])) (Z_to_bv 64 462632) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_4b990 D_4b990 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_4b994 D_4b994 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b998 D_4b998 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b99c D_4b99c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b9a0 D_4b9a0 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b9a4 D_4b9a4 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_4b9a8 D_4b9a8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_4b9ac D_4b9ac (argc_w av).  (* [comment removed for export] *)
      sn F_4b9b0 D_4b9b0.  (* [comment removed for export] *)
      stepiv F_4b9b4 D_4b9b4 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_4b9b8 D_4b9b8 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_4b9bc D_4b9bc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_4b9c0 D_4b9c0.  (* [comment removed for export] *)
      sv F_4b8e4 D_4b8e4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_4b8e8 D_4b8e8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 309700) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b8ec D_4b8ec (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_4b8f0 D_4b8f0 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_4b8f4 D_4b8f4.  (* [comment removed for export] *)
      stepret F_4b6b4 D_4b6b4 (0x4b8f8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_4b8f8 D_4b8f8.  (* [comment removed for export] *)
      sn F_4b8fc D_4b8fc.  (* [comment removed for export] *)
      ld_step F_4b900 D_4b900 (word_to_le_bytes 8 (Z_to_bv 64 376032)) (Z_to_bv 64 376032) ltac:(rd_img img_5f0d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b904 D_4b904 (word_to_le_bytes 8 (Z_to_bv 64 376024)) (Z_to_bv 64 376024) ltac:(rd_img img_5f0e0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_4b908 D_4b908 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4b90c D_4b90c (word_to_le_bytes 8 (Z_to_bv 64 131652)) (Z_to_bv 64 131652) ltac:(rd_img img_5bcd8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_4b910 D_4b910 (0x20244 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 309524 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 462648 ->
    getr regs 8 = Z_to_bv 64 376032 ->
    getr regs 9 = Z_to_bv 64 376024 ->
    getr regs 18 = Z_to_bv 64 131912 ->
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
        getr regs' 1 = Z_to_bv 64 309716 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 462648 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 131912 ->
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
        G (mkst regs' (0x20348 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309200))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 309700))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 309524))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 376032))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 594344) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 594348) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 594345) ([Z_to_bv 8 0])) (Z_to_bv 64 462632) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 394096) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x20244 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309192))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 594376))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 309200))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 309700))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 593760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593776) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 593768) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 594400) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 594408) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 462664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 462640) (word_to_le_bytes 8 (Z_to_bv 64 462664))) (Z_to_bv 64 462448) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 594376) ([Z_to_bv 8 1])) (Z_to_bv 64 462488) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 462480) (word_to_le_bytes 4 tid)) (Z_to_bv 64 462600) (word_to_le_bytes 8 (Z_to_bv 64 594432))) (Z_to_bv 64 462568) (word_to_le_bytes 8 (Z_to_bv 64 462568))) (Z_to_bv 64 462456) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462464) (word_to_le_bytes 8 (Z_to_bv 64 462448))) (Z_to_bv 64 462472) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 594344) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 594348) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 594345) ([Z_to_bv 8 0])) (Z_to_bv 64 462632) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_20244 D_20244 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_20248 D_20248 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 309524) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2024c D_2024c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 376032) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_20250 D_20250 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_20254 D_20254.  (* [comment removed for export] *)
      sn F_20258 D_20258.  (* [comment removed for export] *)
      lb_step F_2025c D_2025c (Z_to_bv 8 0) ltac:(rd_img img_60370_1).  (* [comment removed for export] *)
      sn F_20260 D_20260.  (* [comment removed for export] *)
      stepb_tk F_20264 D_20264 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_20270 D_20270.  (* [comment removed for export] *)
      sn F_20274 D_20274.  (* [comment removed for export] *)
      sn F_20278 D_20278.  (* [comment removed for export] *)
      stw F_2027c D_2027c (Z_to_bv 64 394096) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_20280 D_20280.  (* [comment removed for export] *)
      ld_step F_20284 D_20284 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_5efb8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_20288 D_20288 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_202a8 D_202a8 (word_to_le_bytes 8 (Z_to_bv 64 309524)) (Z_to_bv 64 309524) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_202ac D_202ac (word_to_le_bytes 8 (Z_to_bv 64 376032)) (Z_to_bv 64 376032) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_202b0 D_202b0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_202b4 D_202b4 (0x4b914 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_4b914 D_4b914.  (* [comment removed for export] *)
      stepb_ft F_4b918 D_4b918 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_4b91c D_4b91c (word_to_le_bytes 8 (Z_to_bv 64 309700)) (Z_to_bv 64 309700) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b920 D_4b920 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_4b924 D_4b924 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_4b928 D_4b928 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_4b92c D_4b92c (0x4b9c4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_4b9c4 D_4b9c4 (argc_w av).  (* [comment removed for export] *)
      sv F_4b9c8 D_4b9c8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_4b9cc D_4b9cc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_4b9d0 D_4b9d0 (0x20348 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
