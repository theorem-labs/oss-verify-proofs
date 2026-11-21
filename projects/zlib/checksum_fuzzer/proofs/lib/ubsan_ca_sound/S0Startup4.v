(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import
  StartupTac ArgvEnv RefLayout DrawDefs S0Img S0StartupDefs
 S0_code_13ba4_14000 S0_code_15000_16000 S0_code_1c000_1d000 S0_code_1d000_1d640            .
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require L10Walk.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_chain_step.

Abbreviation SEGS := Src_zlib_checksum_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := Src_zlib_checksum_fuzzer_repro.M.phdrs.

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

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_checksum_fuzzer_repro.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_checksum_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_checksum_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
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
    getr regs 4 = Z_to_bv 64 195328 ->
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
        getr regs' 4 = (Z_to_bv 64 195328) ->
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
        G (mkst regs' (0x15408 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87048))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327024) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327028) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327025) ([Z_to_bv 8 0])) (Z_to_bv 64 195312) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x15400 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_15354 D_15354 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_15358 D_15358.
      sv F_15c3c D_15c3c (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_15c40 D_15c40 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 87048) ltac:(ok_win HJ).
      stepb_ft F_15c44 D_15c44 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_15c48 D_15c48 ((rnd_w sp0 inp)).
      sn F_15c4c D_15c4c.
      ld_step F_15c50 D_15c50 (word_to_le_bytes 8 (Z_to_bv 64 327024)) (Z_to_bv 64 327024) ltac:(rd_img img_1e6e0_8) ltac:(apply bytes_le_to_Z_8).
      sn F_15c54 D_15c54.
      sn F_15c58 D_15c58.
      stepiv F_1cc64 D_1cc64 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_1cc68 D_1cc68 ltac:(pin; cond_compute).
      sn F_1cd78 D_1cd78.
      sn F_1cd7c D_1cd7c.
      stepb_ft F_1cd80 D_1cd80 ltac:(pin; cond_compute).
      sn F_1cd84 D_1cd84.
      stepb_tk F_1cd88 D_1cd88 ltac:(pin; cond_compute).
      sn F_1cdc0 D_1cdc0.
      stepb_ft F_1cdc4 D_1cdc4 ltac:(pin; cond_compute).
      ld_step F_1cdc8 D_1cdc8 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      ld_step F_1cdcc D_1cdcc (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      stw F_1cdd0 D_1cdd0 (Z_to_bv 64 327024) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).
      stw F_1cdd4 D_1cdd4 (Z_to_bv 64 327028) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).
      sn F_1cdd8 D_1cdd8.
      sv F_1cddc D_1cddc (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).
      sn F_1cde0 D_1cde0.
      stepb_tk F_1cde4 D_1cde4 ltac:(pin; cond_compute).
      sn F_1d024 D_1d024.
      stepb_ft F_1d028 D_1d028 ltac:(pin; cond_compute).
      sn F_1d02c D_1d02c.
      stepb_ft F_1d030 D_1d030 ltac:(pin; cond_compute).
      stepret F_1d034 D_1d034 (0x15cfc : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15c5c D_15c5c.
      sn F_15c78 D_15c78.
      ld_step F_15c7c D_15c7c (word_to_le_bytes 8 (Z_to_bv 64 327024)) (Z_to_bv 64 327024) ltac:(rd_img img_1e6e0_8) ltac:(apply bytes_le_to_Z_8).
      stw F_15c80 D_15c80 (Z_to_bv 64 327025) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_15c84 D_15c84 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).
      sn F_15c88 D_15c88.
      stw F_15c8c D_15c8c (Z_to_bv 64 195312) (canary_w rdraw) ltac:(ok_data).
      ld_step F_15c90 D_15c90 (word_to_le_bytes 8 (Z_to_bv 64 87048)) (Z_to_bv 64 87048) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15c94 D_15c94 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_15c98 D_15c98 (0x15408 : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_15354 D_15354 (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_15358 D_15358.
      sv F_15c3c D_15c3c (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_15c40 D_15c40 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 87048) ltac:(ok_win HJ).
      stepb_ft F_15c44 D_15c44 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_15c48 D_15c48 ((rnd_w sp0 inp)).
      sn F_15c4c D_15c4c.
      ld_step F_15c50 D_15c50 (word_to_le_bytes 8 (Z_to_bv 64 327024)) (Z_to_bv 64 327024) ltac:(rd_img img_1e6e0_8) ltac:(apply bytes_le_to_Z_8).
      sn F_15c54 D_15c54.
      sn F_15c58 D_15c58.
      stepiv F_1cc64 D_1cc64 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_1cc68 D_1cc68 ltac:(pin; cond_compute).
      sn F_1cd78 D_1cd78.
      sn F_1cd7c D_1cd7c.
      stepb_ft F_1cd80 D_1cd80 ltac:(pin; cond_compute).
      sn F_1cd84 D_1cd84.
      stepb_tk F_1cd88 D_1cd88 ltac:(pin; cond_compute).
      sn F_1cdc0 D_1cdc0.
      stepb_ft F_1cdc4 D_1cdc4 ltac:(pin; cond_compute).
      ld_step F_1cdc8 D_1cdc8 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      ld_step F_1cdcc D_1cdcc (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      stw F_1cdd0 D_1cdd0 (Z_to_bv 64 327024) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).
      stw F_1cdd4 D_1cdd4 (Z_to_bv 64 327028) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).
      sn F_1cdd8 D_1cdd8.
      sv F_1cddc D_1cddc (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).
      sn F_1cde0 D_1cde0.
      stepb_tk F_1cde4 D_1cde4 ltac:(pin; cond_compute).
      sn F_1d024 D_1d024.
      stepb_ft F_1d028 D_1d028 ltac:(pin; cond_compute).
      sn F_1d02c D_1d02c.
      stepb_ft F_1d030 D_1d030 ltac:(pin; cond_compute).
      stepret F_1d034 D_1d034 (0x15cfc : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15c5c D_15c5c.
      sn F_15c78 D_15c78.
      ld_step F_15c7c D_15c7c (word_to_le_bytes 8 (Z_to_bv 64 327024)) (Z_to_bv 64 327024) ltac:(rd_img img_1e6e0_8) ltac:(apply bytes_le_to_Z_8).
      stw F_15c80 D_15c80 (Z_to_bv 64 327025) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_15c84 D_15c84 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).
      sn F_15c88 D_15c88.
      stw F_15c8c D_15c8c (Z_to_bv 64 195312) (canary_w rdraw) ltac:(ok_data).
      ld_step F_15c90 D_15c90 (word_to_le_bytes 8 (Z_to_bv 64 87048)) (Z_to_bv 64 87048) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15c94 D_15c94 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_15c98 D_15c98 (0x15408 : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 195328 ->
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
        getr regs' 4 = (Z_to_bv 64 195328) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 81232) ->
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
        G (mkst regs' (0x155c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87048))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327024) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327028) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327025) ([Z_to_bv 8 0])) (Z_to_bv 64 195312) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x15408 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87048))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327024) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327028) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327025) ([Z_to_bv 8 0])) (Z_to_bv 64 195312) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_1535c D_1535c (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15360 D_15360 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15364 D_15364 ltac:(pin; apply c_eq_refl).
      ld_step F_15368 D_15368 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1536c D_1536c (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15370 D_15370 ltac:(pin; apply c_eq_refl).
      ld_step F_15374 D_15374 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_15378 D_15378 ltac:(pin; cond_compute).
      ld_step F_15458 D_15458 (word_to_le_bytes 8 (Z_to_bv 64 87452)) (Z_to_bv 64 87452) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1545c D_1545c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15460 D_15460 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15464 D_15464 (word_to_le_bytes 8 (Z_to_bv 64 81232)) (Z_to_bv 64 81232) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15468 D_15468 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_1546c D_1546c (0x1559c : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_154f0 D_154f0.
      sn F_154f4 D_154f4.
      sn F_154f8 D_154f8.
      sv F_154fc D_154fc (argc_w inp).
      sv F_15500 D_15500 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_15504 D_15504 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15508 D_15508 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1550c D_1550c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15510 D_15510 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15514 D_15514 (sp0).
      stepret F_15518 D_15518 (0x155c8 : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_1535c D_1535c (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15360 D_15360 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15364 D_15364 ltac:(pin; apply c_eq_refl).
      ld_step F_15368 D_15368 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1536c D_1536c (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15370 D_15370 ltac:(pin; apply c_eq_refl).
      ld_step F_15374 D_15374 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_15378 D_15378 ltac:(pin; cond_compute).
      ld_step F_15458 D_15458 (word_to_le_bytes 8 (Z_to_bv 64 87452)) (Z_to_bv 64 87452) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1545c D_1545c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15460 D_15460 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15464 D_15464 (word_to_le_bytes 8 (Z_to_bv 64 81232)) (Z_to_bv 64 81232) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15468 D_15468 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_1546c D_1546c (0x1559c : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_154f0 D_154f0.
      sn F_154f4 D_154f4.
      sn F_154f8 D_154f8.
      sv F_154fc D_154fc (argc_w inp).
      sv F_15500 D_15500 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_15504 D_15504 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15508 D_15508 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_1550c D_1550c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15510 D_15510 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_15514 D_15514 (sp0).
      stepret F_15518 D_15518 (0x155c8 : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c8 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 195328 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 81232 ->
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
        getr regs' 1 = (Z_to_bv 64 87372) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 195328) ->
        getr regs' 8 = (Z_to_bv 64 124648) ->
        getr regs' 9 = (Z_to_bv 64 124640) ->
        getr regs' 18 = (Z_to_bv 64 81232) ->
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
        G (mkst regs' (0x13c4c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87048))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 87548))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327024) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327028) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327025) ([Z_to_bv 8 0])) (Z_to_bv 64 195312) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x155c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87048))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327024) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327028) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327025) ([Z_to_bv 8 0])) (Z_to_bv 64 195312) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_1551c D_1551c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_15520 D_15520 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_15524 D_15524 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_15528 D_15528 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_1552c D_1552c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_15530 D_15530 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_15538 D_15538 (argc_w inp).
      sn F_1553c D_1553c.
      stepiv F_15540 D_15540 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_15544 D_15544 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_1554c D_1554c.
      sv F_15470 D_15470 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_15474 D_15474 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 87548) ltac:(ok_win HJ).
      stw F_15478 D_15478 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_1547c D_1547c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_15480 D_15480.
      stepret F_15240 D_15240 (0x15530 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15484 D_15484.
      sn F_15488 D_15488.
      ld_step F_1548c D_1548c (word_to_le_bytes 8 (Z_to_bv 64 124648)) (Z_to_bv 64 124648) ltac:(rd_img img_1e6d0_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15490 D_15490 (word_to_le_bytes 8 (Z_to_bv 64 124640)) (Z_to_bv 64 124640) ltac:(rd_img img_1e6d8_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15494 D_15494 ltac:(pin; cond_compute).
      ld_step F_15498 D_15498 (word_to_le_bytes 8 (Z_to_bv 64 80972)) (Z_to_bv 64 80972) ltac:(rd_img img_1e640_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_1549c D_1549c (0x13c4c : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_1551c D_1551c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_15520 D_15520 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_15524 D_15524 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_15528 D_15528 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_1552c D_1552c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_15530 D_15530 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_15538 D_15538 (argc_w inp).
      sn F_1553c D_1553c.
      stepiv F_15540 D_15540 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_15544 D_15544 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_1554c D_1554c.
      sv F_15470 D_15470 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_15474 D_15474 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 87548) ltac:(ok_win HJ).
      stw F_15478 D_15478 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_1547c D_1547c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_15480 D_15480.
      stepret F_15240 D_15240 (0x15530 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_15484 D_15484.
      sn F_15488 D_15488.
      ld_step F_1548c D_1548c (word_to_le_bytes 8 (Z_to_bv 64 124648)) (Z_to_bv 64 124648) ltac:(rd_img img_1e6d0_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_15490 D_15490 (word_to_le_bytes 8 (Z_to_bv 64 124640)) (Z_to_bv 64 124640) ltac:(rd_img img_1e6d8_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_15494 D_15494 ltac:(pin; cond_compute).
      ld_step F_15498 D_15498 (word_to_le_bytes 8 (Z_to_bv 64 80972)) (Z_to_bv 64 80972) ltac:(rd_img img_1e640_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_1549c D_1549c (0x13c4c : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 87372 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 195328 ->
    getr regs 8 = Z_to_bv 64 124648 ->
    getr regs 9 = Z_to_bv 64 124640 ->
    getr regs 18 = Z_to_bv 64 81232 ->
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
        getr regs' 1 = (Z_to_bv 64 87564) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 195328) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 81232) ->
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
        G (mkst regs' (0x13d50 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87048))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 87548))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 87372))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 124648))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327024) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327028) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327025) ([Z_to_bv 8 0])) (Z_to_bv 64 195312) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 129456) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x13c4c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87040))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 327056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 87048))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 87548))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 326440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 326448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 327080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 327088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 195344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 195320) (word_to_le_bytes 8 (Z_to_bv 64 195344))) (Z_to_bv 64 195128) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 327056) ([Z_to_bv 8 1])) (Z_to_bv 64 195168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 195160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 195280) (word_to_le_bytes 8 (Z_to_bv 64 327112))) (Z_to_bv 64 195248) (word_to_le_bytes 8 (Z_to_bv 64 195248))) (Z_to_bv 64 195136) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195144) (word_to_le_bytes 8 (Z_to_bv 64 195128))) (Z_to_bv 64 195152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 327024) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 327028) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 327025) ([Z_to_bv 8 0])) (Z_to_bv 64 195312) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* port727: J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_13bec D_13bec (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_13bf0 D_13bf0 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 87372) ltac:(ok_win HJ).
      stw F_13bf4 D_13bf4 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 124648) ltac:(ok_win HJ).
      sv F_13bf8 D_13bf8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_13bfc D_13bfc.
      sn F_13c00 D_13c00.
      lb_step F_13c04 D_13c04 (Z_to_bv 8 0) ltac:(rd_img img_1f910_1).
      sn F_13c08 D_13c08.
      stepb_tk F_13c0c D_13c0c ltac:(pin; cond_compute).
      sn F_13c18 D_13c18.
      sn F_13c1c D_13c1c.
      sn F_13c20 D_13c20.
      stw F_13c24 D_13c24 (Z_to_bv 64 129456) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_13c28 D_13c28.
      ld_step F_13c2c D_13c2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_1e688_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_13c30 D_13c30 ltac:(pin; cond_compute).
      ld_step F_13c50 D_13c50 (word_to_le_bytes 8 (Z_to_bv 64 87372)) (Z_to_bv 64 87372) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_13c54 D_13c54 (word_to_le_bytes 8 (Z_to_bv 64 124648)) (Z_to_bv 64 124648) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_13c58 D_13c58 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_13c5c D_13c5c (0x1554c : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_154a0 D_154a0.
      stepb_ft F_154a4 D_154a4 ltac:(pin; cond_compute).
      ld_step F_154a8 D_154a8 (word_to_le_bytes 8 (Z_to_bv 64 87548)) (Z_to_bv 64 87548) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_154ac D_154ac (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_154b0 D_154b0 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_154b4 D_154b4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_154b8 D_154b8 (0x155fc : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_15550 D_15550 (argc_w inp).
      sv F_15554 D_15554 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_15558 D_15558 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_1555c D_1555c (0x13d50 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_13bec D_13bec (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_13bf0 D_13bf0 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 87372) ltac:(ok_win HJ).
      stw F_13bf4 D_13bf4 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 124648) ltac:(ok_win HJ).
      sv F_13bf8 D_13bf8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_13bfc D_13bfc.
      sn F_13c00 D_13c00.
      lb_step F_13c04 D_13c04 (Z_to_bv 8 0) ltac:(rd_img img_1f910_1).
      sn F_13c08 D_13c08.
      stepb_tk F_13c0c D_13c0c ltac:(pin; cond_compute).
      sn F_13c18 D_13c18.
      sn F_13c1c D_13c1c.
      sn F_13c20 D_13c20.
      stw F_13c24 D_13c24 (Z_to_bv 64 129456) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_13c28 D_13c28.
      ld_step F_13c2c D_13c2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_1e688_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_13c30 D_13c30 ltac:(pin; cond_compute).
      ld_step F_13c50 D_13c50 (word_to_le_bytes 8 (Z_to_bv 64 87372)) (Z_to_bv 64 87372) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_13c54 D_13c54 (word_to_le_bytes 8 (Z_to_bv 64 124648)) (Z_to_bv 64 124648) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_13c58 D_13c58 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_13c5c D_13c5c (0x1554c : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_154a0 D_154a0.
      stepb_ft F_154a4 D_154a4 ltac:(pin; cond_compute).
      ld_step F_154a8 D_154a8 (word_to_le_bytes 8 (Z_to_bv 64 87548)) (Z_to_bv 64 87548) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_154ac D_154ac (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_154b0 D_154b0 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_154b4 D_154b4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_154b8 D_154b8 (0x155fc : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_15550 D_15550 (argc_w inp).
      sv F_15554 D_15554 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_15558 D_15558 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_1555c D_1555c (0x13d50 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_chain_step_kit.
