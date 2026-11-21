(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import
  StartupTac ArgvEnv RefLayout DrawDefs U0Img U0StartupDefs
 U0_code_13bc4_14000 U0_code_15000_16000 U0_code_1c000_1d000 U0_code_1d000_1d8c4              .
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require L10Walk.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_chain_step.

Abbreviation SEGS := Tgt_checksum_fuzzer_ubsan.M.loaded_segments.
Abbreviation RPH := Tgt_checksum_fuzzer_ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  (* port727 (): the launch as Common/ArgvEnv's Scaffold has it; av / ev / uid / hw / gid / rseq are notations of inp. *)
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

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
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
    getr regs 4 = Z_to_bv 64 195968 ->
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
        getr regs' 4 = (Z_to_bv 64 195968) ->
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
        G (mkst regs' (0x1568c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87692))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327665) ([Z_to_bv 8 0])) (Z_to_bv 64 195952) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x15684 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_155d8 D_155d8 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_155dc D_155dc.
      sv F_15ec0 D_15ec0 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_15ec4 D_15ec4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 87692) ltac:(ok_win HJ).
      stepb_ft F_15ec8 D_15ec8 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_15ecc D_15ecc ((rnd_w sp0 inp)).
      sn F_15ed0 D_15ed0.
      ld_step F_15ed4 D_15ed4 (word_to_le_bytes 8 (Z_to_bv 64 327664)) (Z_to_bv 64 327664) ltac:(rd_img img_1e968_8) ltac:(apply bytes_le_to_Z_8).
      sn F_15ed8 D_15ed8.
      sn F_15edc D_15edc.
      stepiv F_1cee8 D_1cee8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_1ceec D_1ceec ltac:(pin; cond_compute).
      sn F_1cffc D_1cffc.
      sn F_1d000 D_1d000.
      stepb_ft F_1d004 D_1d004 ltac:(pin; cond_compute).
      sn F_1d008 D_1d008.
      stepb_tk F_1d00c D_1d00c ltac:(pin; cond_compute).
      sn F_1d044 D_1d044.
      stepb_ft F_1d048 D_1d048 ltac:(pin; cond_compute).
      ld_step F_1d04c D_1d04c (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      ld_step F_1d050 D_1d050 (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      stw F_1d054 D_1d054 (Z_to_bv 64 327664) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).
      stw F_1d058 D_1d058 (Z_to_bv 64 327668) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).
      sn F_1d05c D_1d05c.
      sv F_1d060 D_1d060 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).
      sn F_1d064 D_1d064.
      stepb_tk F_1d068 D_1d068 ltac:(pin; cond_compute).
      sn F_1d2a8 D_1d2a8.
      stepb_ft F_1d2ac D_1d2ac ltac:(pin; cond_compute).
      sn F_1d2b0 D_1d2b0.
      stepb_ft F_1d2b4 D_1d2b4 ltac:(pin; cond_compute).
      stepret F_1d2b8 D_1d2b8 (0x15f80 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15ee0 D_15ee0.
      sn F_15efc D_15efc.
      ld_step F_15f00 D_15f00 (word_to_le_bytes 8 (Z_to_bv 64 327664)) (Z_to_bv 64 327664) ltac:(rd_img img_1e968_8) ltac:(apply bytes_le_to_Z_8).
      stw F_15f04 D_15f04 (Z_to_bv 64 327665) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_15f08 D_15f08 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).
      sn F_15f0c D_15f0c.
      stw F_15f10 D_15f10 (Z_to_bv 64 195952) (canary_w rdraw) ltac:(ok_data).
      ld_step F_15f14 D_15f14 (word_to_le_bytes 8 (Z_to_bv 64 87692)) (Z_to_bv 64 87692) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15f18 D_15f18 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_15f1c D_15f1c (0x1568c : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_155d8 D_155d8 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_155dc D_155dc.
      sv F_15ec0 D_15ec0 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_15ec4 D_15ec4 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 87692) ltac:(ok_win HJ).
      stepb_ft F_15ec8 D_15ec8 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_15ecc D_15ecc ((rnd_w sp0 inp)).
      sn F_15ed0 D_15ed0.
      ld_step F_15ed4 D_15ed4 (word_to_le_bytes 8 (Z_to_bv 64 327664)) (Z_to_bv 64 327664) ltac:(rd_img img_1e968_8) ltac:(apply bytes_le_to_Z_8).
      sn F_15ed8 D_15ed8.
      sn F_15edc D_15edc.
      stepiv F_1cee8 D_1cee8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_1ceec D_1ceec ltac:(pin; cond_compute).
      sn F_1cffc D_1cffc.
      sn F_1d000 D_1d000.
      stepb_ft F_1d004 D_1d004 ltac:(pin; cond_compute).
      sn F_1d008 D_1d008.
      stepb_tk F_1d00c D_1d00c ltac:(pin; cond_compute).
      sn F_1d044 D_1d044.
      stepb_ft F_1d048 D_1d048 ltac:(pin; cond_compute).
      ld_step F_1d04c D_1d04c (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      ld_step F_1d050 D_1d050 (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      stw F_1d054 D_1d054 (Z_to_bv 64 327664) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).
      stw F_1d058 D_1d058 (Z_to_bv 64 327668) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).
      sn F_1d05c D_1d05c.
      sv F_1d060 D_1d060 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).
      sn F_1d064 D_1d064.
      stepb_tk F_1d068 D_1d068 ltac:(pin; cond_compute).
      sn F_1d2a8 D_1d2a8.
      stepb_ft F_1d2ac D_1d2ac ltac:(pin; cond_compute).
      sn F_1d2b0 D_1d2b0.
      stepb_ft F_1d2b4 D_1d2b4 ltac:(pin; cond_compute).
      stepret F_1d2b8 D_1d2b8 (0x15f80 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15ee0 D_15ee0.
      sn F_15efc D_15efc.
      ld_step F_15f00 D_15f00 (word_to_le_bytes 8 (Z_to_bv 64 327664)) (Z_to_bv 64 327664) ltac:(rd_img img_1e968_8) ltac:(apply bytes_le_to_Z_8).
      stw F_15f04 D_15f04 (Z_to_bv 64 327665) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_15f08 D_15f08 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).
      sn F_15f0c D_15f0c.
      stw F_15f10 D_15f10 (Z_to_bv 64 195952) (canary_w rdraw) ltac:(ok_data).
      ld_step F_15f14 D_15f14 (word_to_le_bytes 8 (Z_to_bv 64 87692)) (Z_to_bv 64 87692) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15f18 D_15f18 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_15f1c D_15f1c (0x1568c : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 195968 ->
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
        getr regs' 4 = (Z_to_bv 64 195968) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 81264) ->
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
        G (mkst regs' (0x1584c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87692))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327665) ([Z_to_bv 8 0])) (Z_to_bv 64 195952) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x1568c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87692))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327665) ([Z_to_bv 8 0])) (Z_to_bv 64 195952) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_155e0 D_155e0 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_155e4 D_155e4 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_155e8 D_155e8 ltac:(pin; apply c_eq_refl).
      ld_step F_155ec D_155ec (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_155f0 D_155f0 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_155f4 D_155f4 ltac:(pin; apply c_eq_refl).
      ld_step F_155f8 D_155f8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_155fc D_155fc ltac:(pin; cond_compute).
      ld_step F_156dc D_156dc (word_to_le_bytes 8 (Z_to_bv 64 88096)) (Z_to_bv 64 88096) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_156e0 D_156e0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_156e4 D_156e4 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_156e8 D_156e8 (word_to_le_bytes 8 (Z_to_bv 64 81264)) (Z_to_bv 64 81264) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_156ec D_156ec (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_156f0 D_156f0 (0x15820 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15774 D_15774.
      sn F_15778 D_15778.
      sn F_1577c D_1577c.
      sv F_15780 D_15780 (argc_w inp).
      sv F_15784 D_15784 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_15788 D_15788 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1578c D_1578c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15790 D_15790 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15794 D_15794 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15798 D_15798 (sp0).
      stepret F_1579c D_1579c (0x1584c : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_155e0 D_155e0 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_155e4 D_155e4 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_155e8 D_155e8 ltac:(pin; apply c_eq_refl).
      ld_step F_155ec D_155ec (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_155f0 D_155f0 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_155f4 D_155f4 ltac:(pin; apply c_eq_refl).
      ld_step F_155f8 D_155f8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_155fc D_155fc ltac:(pin; cond_compute).
      ld_step F_156dc D_156dc (word_to_le_bytes 8 (Z_to_bv 64 88096)) (Z_to_bv 64 88096) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_156e0 D_156e0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_156e4 D_156e4 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_156e8 D_156e8 (word_to_le_bytes 8 (Z_to_bv 64 81264)) (Z_to_bv 64 81264) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_156ec D_156ec (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_156f0 D_156f0 (0x15820 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15774 D_15774.
      sn F_15778 D_15778.
      sn F_1577c D_1577c.
      sv F_15780 D_15780 (argc_w inp).
      sv F_15784 D_15784 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_15788 D_15788 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1578c D_1578c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15790 D_15790 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15794 D_15794 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15798 D_15798 (sp0).
      stepret F_1579c D_1579c (0x1584c : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c8 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 195968 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 81264 ->
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
        getr regs' 1 = (Z_to_bv 64 88016) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 195968) ->
        getr regs' 8 = (Z_to_bv 64 125296) ->
        getr regs' 9 = (Z_to_bv 64 125288) ->
        getr regs' 18 = (Z_to_bv 64 81264) ->
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
        G (mkst regs' (0x13c6c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87692))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 88192))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327665) ([Z_to_bv 8 0])) (Z_to_bv 64 195952) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x1584c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87692))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327665) ([Z_to_bv 8 0])) (Z_to_bv 64 195952) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_157a0 D_157a0 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_157a4 D_157a4 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_157a8 D_157a8 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_157ac D_157ac (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_157b0 D_157b0 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_157b4 D_157b4 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_157b8 D_157b8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_157bc D_157bc (argc_w inp).
      sn F_157c0 D_157c0.
      stepiv F_157c4 D_157c4 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_157c8 D_157c8 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_157cc D_157cc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_157d0 D_157d0.
      sv F_156f4 D_156f4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_156f8 D_156f8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 88192) ltac:(ok_win HJ).
      stw F_156fc D_156fc (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_15700 D_15700 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_15704 D_15704.
      stepret F_154c4 D_154c4 (0x157b4 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15708 D_15708.
      sn F_1570c D_1570c.
      ld_step F_15710 D_15710 (word_to_le_bytes 8 (Z_to_bv 64 125296)) (Z_to_bv 64 125296) ltac:(rd_img img_1e958_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15714 D_15714 (word_to_le_bytes 8 (Z_to_bv 64 125288)) (Z_to_bv 64 125288) ltac:(rd_img img_1e960_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15718 D_15718 ltac:(pin; cond_compute).
      ld_step F_1571c D_1571c (word_to_le_bytes 8 (Z_to_bv 64 81004)) (Z_to_bv 64 81004) ltac:(rd_img img_1e8c8_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_15720 D_15720 (0x13c6c : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_157a0 D_157a0 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_157a4 D_157a4 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_157a8 D_157a8 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_157ac D_157ac (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_157b0 D_157b0 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_157b4 D_157b4 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_157b8 D_157b8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_157bc D_157bc (argc_w inp).
      sn F_157c0 D_157c0.
      stepiv F_157c4 D_157c4 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_157c8 D_157c8 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_157cc D_157cc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_157d0 D_157d0.
      sv F_156f4 D_156f4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_156f8 D_156f8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 88192) ltac:(ok_win HJ).
      stw F_156fc D_156fc (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_15700 D_15700 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_15704 D_15704.
      stepret F_154c4 D_154c4 (0x157b4 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15708 D_15708.
      sn F_1570c D_1570c.
      ld_step F_15710 D_15710 (word_to_le_bytes 8 (Z_to_bv 64 125296)) (Z_to_bv 64 125296) ltac:(rd_img img_1e958_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15714 D_15714 (word_to_le_bytes 8 (Z_to_bv 64 125288)) (Z_to_bv 64 125288) ltac:(rd_img img_1e960_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15718 D_15718 ltac:(pin; cond_compute).
      ld_step F_1571c D_1571c (word_to_le_bytes 8 (Z_to_bv 64 81004)) (Z_to_bv 64 81004) ltac:(rd_img img_1e8c8_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_15720 D_15720 (0x13c6c : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 88016 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 195968 ->
    getr regs 8 = Z_to_bv 64 125296 ->
    getr regs 9 = Z_to_bv 64 125288 ->
    getr regs 18 = Z_to_bv 64 81264 ->
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
        getr regs' 1 = (Z_to_bv 64 88208) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 195968) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 81264) ->
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
        G (mkst regs' (0x13d70 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87692))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 88192))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 88016))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 125296))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327665) ([Z_to_bv 8 0])) (Z_to_bv 64 195952) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 130096) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x13c6c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87684))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327696))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87692))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 88192))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327720) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327728) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195984) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195960) (word_to_le_bytes 8 (Z_to_bv 64 195984))) (Z_to_bv 64 195768) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 327696) ([Z_to_bv 8 1])) (Z_to_bv 64 195808) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195800) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195920) (word_to_le_bytes 8 (Z_to_bv 64 327752))) (Z_to_bv 64 195888) (word_to_le_bytes 8 (Z_to_bv 64 195888))) (Z_to_bv 64 195776) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195784) (word_to_le_bytes 8 (Z_to_bv 64 195768))) (Z_to_bv 64 195792) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327664) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327668) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327665) ([Z_to_bv 8 0])) (Z_to_bv 64 195952) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_13c0c D_13c0c (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_13c10 D_13c10 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 88016) ltac:(ok_win HJ).
      stw F_13c14 D_13c14 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 125296) ltac:(ok_win HJ).
      sv F_13c18 D_13c18 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_13c1c D_13c1c.
      sn F_13c20 D_13c20.
      lb_step F_13c24 D_13c24 (Z_to_bv 8 0) ltac:(rd_img img_1fb90_1).
      sn F_13c28 D_13c28.
      stepb_tk F_13c2c D_13c2c ltac:(pin; cond_compute).
      sn F_13c38 D_13c38.
      sn F_13c3c D_13c3c.
      sn F_13c40 D_13c40.
      stw F_13c44 D_13c44 (Z_to_bv 64 130096) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_13c48 D_13c48.
      ld_step F_13c4c D_13c4c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_1e910_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_13c50 D_13c50 ltac:(pin; cond_compute).
      ld_step F_13c70 D_13c70 (word_to_le_bytes 8 (Z_to_bv 64 88016)) (Z_to_bv 64 88016) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_13c74 D_13c74 (word_to_le_bytes 8 (Z_to_bv 64 125296)) (Z_to_bv 64 125296) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_13c78 D_13c78 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_13c7c D_13c7c (0x157d0 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15724 D_15724.
      stepb_ft F_15728 D_15728 ltac:(pin; cond_compute).
      ld_step F_1572c D_1572c (word_to_le_bytes 8 (Z_to_bv 64 88192)) (Z_to_bv 64 88192) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15730 D_15730 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15734 D_15734 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15738 D_15738 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_1573c D_1573c (0x15880 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_157d4 D_157d4 (argc_w inp).
      sv F_157d8 D_157d8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_157dc D_157dc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_157e0 D_157e0 (0x13d70 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_13c0c D_13c0c (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_13c10 D_13c10 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 88016) ltac:(ok_win HJ).
      stw F_13c14 D_13c14 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 125296) ltac:(ok_win HJ).
      sv F_13c18 D_13c18 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_13c1c D_13c1c.
      sn F_13c20 D_13c20.
      lb_step F_13c24 D_13c24 (Z_to_bv 8 0) ltac:(rd_img img_1fb90_1).
      sn F_13c28 D_13c28.
      stepb_tk F_13c2c D_13c2c ltac:(pin; cond_compute).
      sn F_13c38 D_13c38.
      sn F_13c3c D_13c3c.
      sn F_13c40 D_13c40.
      stw F_13c44 D_13c44 (Z_to_bv 64 130096) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_13c48 D_13c48.
      ld_step F_13c4c D_13c4c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_1e910_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_13c50 D_13c50 ltac:(pin; cond_compute).
      ld_step F_13c70 D_13c70 (word_to_le_bytes 8 (Z_to_bv 64 88016)) (Z_to_bv 64 88016) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_13c74 D_13c74 (word_to_le_bytes 8 (Z_to_bv 64 125296)) (Z_to_bv 64 125296) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_13c78 D_13c78 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_13c7c D_13c7c (0x157d0 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15724 D_15724.
      stepb_ft F_15728 D_15728 ltac:(pin; cond_compute).
      ld_step F_1572c D_1572c (word_to_le_bytes 8 (Z_to_bv 64 88192)) (Z_to_bv 64 88192) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15730 D_15730 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15734 D_15734 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15738 D_15738 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_1573c D_1573c (0x15880 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_157d4 D_157d4 (argc_w inp).
      sv F_157d8 D_157d8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_157dc D_157dc (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_157e0 D_157e0 (0x13d70 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.L10Walk.l10_chain_step_kit.
