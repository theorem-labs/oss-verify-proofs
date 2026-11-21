(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress3_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  StartupTac ArgvEnv RefLayout DrawDefs U8Img U8StartupDefs
 U8_code_14710_15000 U8_code_19000_1a000 U8_code_1a000_1b000 U8_code_21000_21d90                  .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.

Abbreviation SEGS := Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments.
Abbreviation RPH := Tgt_zlib_uncompress3_fuzzer_ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  (* the launch as Common/ArgvEnv's Scaffold has it; av / ev / uid / hw / gid / rseq are notations of inp. *)
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
  Variable rdraw : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Local Notation gid := (in_gid inp) (only parsing).
  Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress3_fuzzer_ubsan.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress3_fuzzer_ubsan.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N Tgt_zlib_uncompress3_fuzzer_ubsan.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). rewrite <- rnd_sub4 by exact Hjn. apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side; apply rdn_guard; [reflexivity | reflexivity | lia | lia].

  Lemma slli_argc : v_slli (argc_w inp) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. change (len_word av) with (argcN inp); rewrite (u_argcN inp Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475904 ->
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
        getr regs' 4 = (Z_to_bv 64 475904) ->
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
        G (mkst regs' (0x19d9c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105876))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607624))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105884))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 607016) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607024) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607648) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607656) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475896) (word_to_le_bytes 8 (Z_to_bv 64 475920))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 607624) ([Z_to_bv 8 1])) (Z_to_bv 64 475744) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475736) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475856) (word_to_le_bytes 8 (Z_to_bv 64 607680))) (Z_to_bv 64 475824) (word_to_le_bytes 8 (Z_to_bv 64 475824))) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607592) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607596) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607593) ([Z_to_bv 8 0])) (Z_to_bv 64 475888) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19d94 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105876))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607624))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 607016) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607024) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607648) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607656) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475896) (word_to_le_bytes 8 (Z_to_bv 64 475920))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 607624) ([Z_to_bv 8 1])) (Z_to_bv 64 475744) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475736) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475856) (word_to_le_bytes 8 (Z_to_bv 64 607680))) (Z_to_bv 64 475824) (word_to_le_bytes 8 (Z_to_bv 64 475824))) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_19c3c D_19c3c (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_19c40 D_19c40.
      sv F_1a460 D_1a460 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_1a464 D_1a464 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 105884) ltac:(ok_win HJ).
      stepb_ft F_1a468 D_1a468 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_1a46c D_1a46c ((rnd_w sp0 inp)).
      sn F_1a470 D_1a470.
      ld_step F_1a474 D_1a474 (word_to_le_bytes 8 (Z_to_bv 64 607592)) (Z_to_bv 64 607592) ltac:(rd_img img_22e40_8) ltac:(apply bytes_le_to_Z_8).
      sn F_1a478 D_1a478.
      sn F_1a47c D_1a47c.
      stepiv F_213b4 D_213b4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_213b8 D_213b8 ltac:(pin; cond_compute).
      sn F_214c8 D_214c8.
      sn F_214cc D_214cc.
      stepb_ft F_214d0 D_214d0 ltac:(pin; cond_compute).
      sn F_214d4 D_214d4.
      stepb_tk F_214d8 D_214d8 ltac:(pin; cond_compute).
      sn F_21510 D_21510.
      stepb_ft F_21514 D_21514 ltac:(pin; cond_compute).
      ld_step F_21518 D_21518 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      ld_step F_2151c D_2151c (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      stw F_21520 D_21520 (Z_to_bv 64 607592) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).
      stw F_21524 D_21524 (Z_to_bv 64 607596) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).
      sn F_21528 D_21528.
      sv F_2152c D_2152c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).
      sn F_21530 D_21530.
      stepb_tk F_21534 D_21534 ltac:(pin; cond_compute).
      sn F_21774 D_21774.
      stepb_ft F_21778 D_21778 ltac:(pin; cond_compute).
      sn F_2177c D_2177c.
      stepb_ft F_21780 D_21780 ltac:(pin; cond_compute).
      stepret F_21784 D_21784 (0x1a5cc : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_1a480 D_1a480.
      sn F_1a49c D_1a49c.
      ld_step F_1a4a0 D_1a4a0 (word_to_le_bytes 8 (Z_to_bv 64 607592)) (Z_to_bv 64 607592) ltac:(rd_img img_22e40_8) ltac:(apply bytes_le_to_Z_8).
      stw F_1a4a4 D_1a4a4 (Z_to_bv 64 607593) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_1a4a8 D_1a4a8 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).
      sn F_1a4ac D_1a4ac.
      stw F_1a4b0 D_1a4b0 (Z_to_bv 64 475888) (canary_w rdraw) ltac:(ok_data).
      ld_step F_1a4b4 D_1a4b4 (word_to_le_bytes 8 (Z_to_bv 64 105884)) (Z_to_bv 64 105884) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_1a4b8 D_1a4b8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_1a4bc D_1a4bc (0x19d9c : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_19c3c D_19c3c (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_19c40 D_19c40.
      sv F_1a460 D_1a460 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_1a464 D_1a464 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 105884) ltac:(ok_win HJ).
      stepb_ft F_1a468 D_1a468 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_1a46c D_1a46c ((rnd_w sp0 inp)).
      sn F_1a470 D_1a470.
      ld_step F_1a474 D_1a474 (word_to_le_bytes 8 (Z_to_bv 64 607592)) (Z_to_bv 64 607592) ltac:(rd_img img_22e40_8) ltac:(apply bytes_le_to_Z_8).
      sn F_1a478 D_1a478.
      sn F_1a47c D_1a47c.
      stepiv F_213b4 D_213b4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_213b8 D_213b8 ltac:(pin; cond_compute).
      sn F_214c8 D_214c8.
      sn F_214cc D_214cc.
      stepb_ft F_214d0 D_214d0 ltac:(pin; cond_compute).
      sn F_214d4 D_214d4.
      stepb_tk F_214d8 D_214d8 ltac:(pin; cond_compute).
      sn F_21510 D_21510.
      stepb_ft F_21514 D_21514 ltac:(pin; cond_compute).
      ld_step F_21518 D_21518 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      ld_step F_2151c D_2151c (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      stw F_21520 D_21520 (Z_to_bv 64 607592) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).
      stw F_21524 D_21524 (Z_to_bv 64 607596) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).
      sn F_21528 D_21528.
      sv F_2152c D_2152c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).
      sn F_21530 D_21530.
      stepb_tk F_21534 D_21534 ltac:(pin; cond_compute).
      sn F_21774 D_21774.
      stepb_ft F_21778 D_21778 ltac:(pin; cond_compute).
      sn F_2177c D_2177c.
      stepb_ft F_21780 D_21780 ltac:(pin; cond_compute).
      stepret F_21784 D_21784 (0x1a5cc : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_1a480 D_1a480.
      sn F_1a49c D_1a49c.
      ld_step F_1a4a0 D_1a4a0 (word_to_le_bytes 8 (Z_to_bv 64 607592)) (Z_to_bv 64 607592) ltac:(rd_img img_22e40_8) ltac:(apply bytes_le_to_Z_8).
      stw F_1a4a4 D_1a4a4 (Z_to_bv 64 607593) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_1a4a8 D_1a4a8 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).
      sn F_1a4ac D_1a4ac.
      stw F_1a4b0 D_1a4b0 (Z_to_bv 64 475888) (canary_w rdraw) ltac:(ok_data).
      ld_step F_1a4b4 D_1a4b4 (word_to_le_bytes 8 (Z_to_bv 64 105884)) (Z_to_bv 64 105884) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_1a4b8 D_1a4b8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_1a4bc D_1a4bc (0x19d9c : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475904 ->
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
        getr regs' 2 = sp0 ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 475904) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 84228) ->
        getr regs' 11 = (argc_w inp) ->
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
        G (mkst regs' (0x19f5c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105876))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607624))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105884))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 607016) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607024) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607648) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607656) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475896) (word_to_le_bytes 8 (Z_to_bv 64 475920))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 607624) ([Z_to_bv 8 1])) (Z_to_bv 64 475744) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475736) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475856) (word_to_le_bytes 8 (Z_to_bv 64 607680))) (Z_to_bv 64 475824) (word_to_le_bytes 8 (Z_to_bv 64 475824))) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607592) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607596) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607593) ([Z_to_bv 8 0])) (Z_to_bv 64 475888) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19d9c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105876))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607624))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105884))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 607016) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607024) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607648) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607656) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475896) (word_to_le_bytes 8 (Z_to_bv 64 475920))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 607624) ([Z_to_bv 8 1])) (Z_to_bv 64 475744) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475736) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475856) (word_to_le_bytes 8 (Z_to_bv 64 607680))) (Z_to_bv 64 475824) (word_to_le_bytes 8 (Z_to_bv 64 475824))) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607592) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607596) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607593) ([Z_to_bv 8 0])) (Z_to_bv 64 475888) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_19c44 D_19c44 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19c48 D_19c48 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_19c4c D_19c4c ltac:(pin; apply c_eq_refl).
      ld_step F_19c50 D_19c50 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19c54 D_19c54 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_19c58 D_19c58 ltac:(pin; apply c_eq_refl).
      ld_step F_19c5c D_19c5c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_19c60 D_19c60 ltac:(pin; cond_compute).
      ld_step F_19d40 D_19d40 (word_to_le_bytes 8 (Z_to_bv 64 106288)) (Z_to_bv 64 106288) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d44 D_19d44 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d48 D_19d48 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d4c D_19d4c (word_to_le_bytes 8 (Z_to_bv 64 84228)) (Z_to_bv 64 84228) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_19d50 D_19d50 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_19d54 D_19d54 (0x19f30 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_19dd8 D_19dd8.
      sn F_19ddc D_19ddc.
      sn F_19de0 D_19de0.
      sv F_19de4 D_19de4 (argc_w inp).
      sv F_19de8 D_19de8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_19dec D_19dec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19df0 D_19df0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19df4 D_19df4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19df8 D_19df8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_19dfc D_19dfc (sp0).
      stepret F_19e00 D_19e00 (0x19f5c : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_19c44 D_19c44 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19c48 D_19c48 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_19c4c D_19c4c ltac:(pin; apply c_eq_refl).
      ld_step F_19c50 D_19c50 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19c54 D_19c54 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_19c58 D_19c58 ltac:(pin; apply c_eq_refl).
      ld_step F_19c5c D_19c5c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_19c60 D_19c60 ltac:(pin; cond_compute).
      ld_step F_19d40 D_19d40 (word_to_le_bytes 8 (Z_to_bv 64 106288)) (Z_to_bv 64 106288) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d44 D_19d44 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d48 D_19d48 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d4c D_19d4c (word_to_le_bytes 8 (Z_to_bv 64 84228)) (Z_to_bv 64 84228) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_19d50 D_19d50 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_19d54 D_19d54 (0x19f30 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_19dd8 D_19dd8.
      sn F_19ddc D_19ddc.
      sn F_19de0 D_19de0.
      sv F_19de4 D_19de4 (argc_w inp).
      sv F_19de8 D_19de8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_19dec D_19dec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19df0 D_19df0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19df4 D_19df4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19df8 D_19df8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_19dfc D_19dfc (sp0).
      stepret F_19e00 D_19e00 (0x19f5c : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c8 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475904 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 84228 ->
    getr regs 11 = argc_w inp ->
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
        getr regs' 1 = (Z_to_bv 64 106208) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 475904) ->
        getr regs' 8 = (Z_to_bv 64 143080) ->
        getr regs' 9 = (Z_to_bv 64 143072) ->
        getr regs' 18 = (Z_to_bv 64 84228) ->
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
        G (mkst regs' (0x14800 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105876))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607624))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105884))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106384))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 607016) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607024) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607648) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607656) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475896) (word_to_le_bytes 8 (Z_to_bv 64 475920))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 607624) ([Z_to_bv 8 1])) (Z_to_bv 64 475744) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475736) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475856) (word_to_le_bytes 8 (Z_to_bv 64 607680))) (Z_to_bv 64 475824) (word_to_le_bytes 8 (Z_to_bv 64 475824))) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607592) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607596) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607593) ([Z_to_bv 8 0])) (Z_to_bv 64 475888) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x19f5c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105876))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607624))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105884))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 607016) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607024) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607648) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607656) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475896) (word_to_le_bytes 8 (Z_to_bv 64 475920))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 607624) ([Z_to_bv 8 1])) (Z_to_bv 64 475744) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475736) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475856) (word_to_le_bytes 8 (Z_to_bv 64 607680))) (Z_to_bv 64 475824) (word_to_le_bytes 8 (Z_to_bv 64 475824))) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607592) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607596) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607593) ([Z_to_bv 8 0])) (Z_to_bv 64 475888) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_19e04 D_19e04 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_19e08 D_19e08 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_19e0c D_19e0c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_19e10 D_19e10 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_19e14 D_19e14 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_19e18 D_19e18 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_19e1c D_19e1c (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_19e20 D_19e20 (argc_w inp).
      sn F_19e24 D_19e24.
      stepiv F_19e28 D_19e28 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_19e2c D_19e2c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_19e30 D_19e30 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_19e34 D_19e34.
      sv F_19d58 D_19d58 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_19d5c D_19d5c (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 106384) ltac:(ok_win HJ).
      stw F_19d60 D_19d60 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_19d64 D_19d64 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_19d68 D_19d68.
      stepret F_19b28 D_19b28 (0x19ec4 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_19d6c D_19d6c.
      sn F_19d70 D_19d70.
      ld_step F_19d74 D_19d74 (word_to_le_bytes 8 (Z_to_bv 64 143080)) (Z_to_bv 64 143080) ltac:(rd_img img_22e30_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d78 D_19d78 (word_to_le_bytes 8 (Z_to_bv 64 143072)) (Z_to_bv 64 143072) ltac:(rd_img img_22e38_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_19d7c D_19d7c ltac:(pin; cond_compute).
      ld_step F_19d80 D_19d80 (word_to_le_bytes 8 (Z_to_bv 64 83968)) (Z_to_bv 64 83968) ltac:(rd_img img_22d90_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_19d84 D_19d84 (0x14800 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_19e04 D_19e04 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_19e08 D_19e08 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_19e0c D_19e0c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_19e10 D_19e10 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_19e14 D_19e14 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_19e18 D_19e18 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_19e1c D_19e1c (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_19e20 D_19e20 (argc_w inp).
      sn F_19e24 D_19e24.
      stepiv F_19e28 D_19e28 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_19e2c D_19e2c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_19e30 D_19e30 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_19e34 D_19e34.
      sv F_19d58 D_19d58 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_19d5c D_19d5c (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 106384) ltac:(ok_win HJ).
      stw F_19d60 D_19d60 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_19d64 D_19d64 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_19d68 D_19d68.
      stepret F_19b28 D_19b28 (0x19ec4 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_19d6c D_19d6c.
      sn F_19d70 D_19d70.
      ld_step F_19d74 D_19d74 (word_to_le_bytes 8 (Z_to_bv 64 143080)) (Z_to_bv 64 143080) ltac:(rd_img img_22e30_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d78 D_19d78 (word_to_le_bytes 8 (Z_to_bv 64 143072)) (Z_to_bv 64 143072) ltac:(rd_img img_22e38_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_19d7c D_19d7c ltac:(pin; cond_compute).
      ld_step F_19d80 D_19d80 (word_to_le_bytes 8 (Z_to_bv 64 83968)) (Z_to_bv 64 83968) ltac:(rd_img img_22d90_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_19d84 D_19d84 (0x14800 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 106208 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 475904 ->
    getr regs 8 = Z_to_bv 64 143080 ->
    getr regs 9 = Z_to_bv 64 143072 ->
    getr regs 18 = Z_to_bv 64 84228 ->
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
        getr regs' 1 = (Z_to_bv 64 106400) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 475904) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 84228) ->
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
        G (mkst regs' (0x14904 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105876))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607624))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105884))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106384))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 106208))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 143080))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 607016) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607024) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607648) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607656) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475896) (word_to_le_bytes 8 (Z_to_bv 64 475920))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 607624) ([Z_to_bv 8 1])) (Z_to_bv 64 475744) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475736) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475856) (word_to_le_bytes 8 (Z_to_bv 64 607680))) (Z_to_bv 64 475824) (word_to_le_bytes 8 (Z_to_bv 64 475824))) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607592) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607596) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607593) ([Z_to_bv 8 0])) (Z_to_bv 64 475888) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 147888) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x14800 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105876))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 607624))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 105884))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 106384))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 607016) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607032) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607024) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 607648) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 607656) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 475920) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 475896) (word_to_le_bytes 8 (Z_to_bv 64 475920))) (Z_to_bv 64 475704) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 607624) ([Z_to_bv 8 1])) (Z_to_bv 64 475744) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 475736) (word_to_le_bytes 4 tid)) (Z_to_bv 64 475856) (word_to_le_bytes 8 (Z_to_bv 64 607680))) (Z_to_bv 64 475824) (word_to_le_bytes 8 (Z_to_bv 64 475824))) (Z_to_bv 64 475712) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475720) (word_to_le_bytes 8 (Z_to_bv 64 475704))) (Z_to_bv 64 475728) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 607592) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 607596) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 607593) ([Z_to_bv 8 0])) (Z_to_bv 64 475888) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_14758 D_14758 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_1475c D_1475c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 106208) ltac:(ok_win HJ).
      stw F_14760 D_14760 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 143080) ltac:(ok_win HJ).
      sv F_14764 D_14764 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_14768 D_14768.
      sn F_1476c D_1476c.
      lb_step F_14770 D_14770 (Z_to_bv 8 0) ltac:(rd_img img_24070_1).
      sn F_14774 D_14774.
      stepb_tk F_14778 D_14778 ltac:(pin; cond_compute).
      sn F_14784 D_14784.
      sn F_14788 D_14788.
      sn F_1478c D_1478c.
      stw F_14790 D_14790 (Z_to_bv 64 147888) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_14794 D_14794.
      ld_step F_14798 D_14798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_22dd8_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_1479c D_1479c ltac:(pin; cond_compute).
      ld_step F_147bc D_147bc (word_to_le_bytes 8 (Z_to_bv 64 106208)) (Z_to_bv 64 106208) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_147c0 D_147c0 (word_to_le_bytes 8 (Z_to_bv 64 143080)) (Z_to_bv 64 143080) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_147c4 D_147c4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_147c8 D_147c8 (0x19ee0 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_19d88 D_19d88.
      stepb_ft F_19d8c D_19d8c ltac:(pin; cond_compute).
      ld_step F_19d90 D_19d90 (word_to_le_bytes 8 (Z_to_bv 64 106384)) (Z_to_bv 64 106384) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d94 D_19d94 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d98 D_19d98 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_19d9c D_19d9c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_19da0 D_19da0 (0x19f90 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_19e38 D_19e38 (argc_w inp).
      sv F_19e3c D_19e3c (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_19e40 D_19e40 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_19e44 D_19e44 (0x14904 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_14758 D_14758 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_1475c D_1475c (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 106208) ltac:(ok_win HJ).
      stw F_14760 D_14760 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 143080) ltac:(ok_win HJ).
      sv F_14764 D_14764 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_14768 D_14768.
      sn F_1476c D_1476c.
      lb_step F_14770 D_14770 (Z_to_bv 8 0) ltac:(rd_img img_24070_1).
      sn F_14774 D_14774.
      stepb_tk F_14778 D_14778 ltac:(pin; cond_compute).
      sn F_14784 D_14784.
      sn F_14788 D_14788.
      sn F_1478c D_1478c.
      stw F_14790 D_14790 (Z_to_bv 64 147888) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_14794 D_14794.
      ld_step F_14798 D_14798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_22dd8_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_1479c D_1479c ltac:(pin; cond_compute).
      ld_step F_147bc D_147bc (word_to_le_bytes 8 (Z_to_bv 64 106208)) (Z_to_bv 64 106208) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_147c0 D_147c0 (word_to_le_bytes 8 (Z_to_bv 64 143080)) (Z_to_bv 64 143080) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_147c4 D_147c4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_147c8 D_147c8 (0x19ee0 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_19d88 D_19d88.
      stepb_ft F_19d8c D_19d8c ltac:(pin; cond_compute).
      ld_step F_19d90 D_19d90 (word_to_le_bytes 8 (Z_to_bv 64 106384)) (Z_to_bv 64 106384) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d94 D_19d94 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_19d98 D_19d98 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_19d9c D_19d9c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_19da0 D_19da0 (0x19f90 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_19e38 D_19e38 (argc_w inp).
      sv F_19e3c D_19e3c (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_19e40 D_19e40 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_19e44 D_19e44 (0x14904 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step_kit.
