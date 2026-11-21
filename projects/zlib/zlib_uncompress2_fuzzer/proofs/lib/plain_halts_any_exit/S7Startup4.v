(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import
  StartupTac ArgvEnv RefLayout DrawDefs S7Img S7StartupDefs
 S7_code_146e4_15000 S7_code_18000_19000 S7_code_19000_1a000 S7_code_20000_20a30              .
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_chain_step.

Abbreviation SEGS := Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments.
Abbreviation RPH := Src_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs.

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

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc)) sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 inp))%Z
    /\ (bv_unsigned (rnd_w sp0 inp) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 inp) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j, (j + 4 <= 16)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + Z.of_nat j)) 4 = Some (rnd4 rdraw j).
  Proof.
    intros J D j Hjn.
    destruct (rnd_facts (run_segments SEGS rc_inp rc_sp rc_mb) Sv48 inp mbase RPH (Z_to_bv 64 (Z.of_N Src_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc)) sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
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
    getr regs 4 = Z_to_bv 64 470912 ->
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
        getr regs' 4 = (Z_to_bv 64 470912) ->
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
        G (mkst regs' (0x18a20 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100896))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602600) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602604) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602601) ([Z_to_bv 8 0])) (Z_to_bv 64 470896) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18a18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_188dc D_188dc (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_188e0 D_188e0.
      sv F_19100 D_19100 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_19104 D_19104 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100896) ltac:(ok_win HJ).
      stepb_ft F_19108 D_19108 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_1910c D_1910c ((rnd_w sp0 inp)).
      sn F_19110 D_19110.
      ld_step F_19114 D_19114 (word_to_le_bytes 8 (Z_to_bv 64 602600)) (Z_to_bv 64 602600) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).
      sn F_19118 D_19118.
      sn F_1911c D_1911c.
      stepiv F_20054 D_20054 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_20058 D_20058 ltac:(pin; cond_compute).
      sn F_20168 D_20168.
      sn F_2016c D_2016c.
      stepb_ft F_20170 D_20170 ltac:(pin; cond_compute).
      sn F_20174 D_20174.
      stepb_tk F_20178 D_20178 ltac:(pin; cond_compute).
      sn F_201b0 D_201b0.
      stepb_ft F_201b4 D_201b4 ltac:(pin; cond_compute).
      ld_step F_201b8 D_201b8 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      ld_step F_201bc D_201bc (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      stw F_201c0 D_201c0 (Z_to_bv 64 602600) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).
      stw F_201c4 D_201c4 (Z_to_bv 64 602604) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).
      sn F_201c8 D_201c8.
      sv F_201cc D_201cc (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).
      sn F_201d0 D_201d0.
      stepb_tk F_201d4 D_201d4 ltac:(pin; cond_compute).
      sn F_20414 D_20414.
      stepb_ft F_20418 D_20418 ltac:(pin; cond_compute).
      sn F_2041c D_2041c.
      stepb_ft F_20420 D_20420 ltac:(pin; cond_compute).
      stepret F_20424 D_20424 (0x19250 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_19120 D_19120.
      sn F_1913c D_1913c.
      ld_step F_19140 D_19140 (word_to_le_bytes 8 (Z_to_bv 64 602600)) (Z_to_bv 64 602600) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).
      stw F_19144 D_19144 (Z_to_bv 64 602601) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_19148 D_19148 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).
      sn F_1914c D_1914c.
      stw F_19150 D_19150 (Z_to_bv 64 470896) (canary_w rdraw) ltac:(ok_data).
      ld_step F_19154 D_19154 (word_to_le_bytes 8 (Z_to_bv 64 100896)) (Z_to_bv 64 100896) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_19158 D_19158 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_1915c D_1915c (0x18a20 : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_188dc D_188dc (word_to_le_bytes 8 (rnd_w sp0 inp)) (rnd_w sp0 inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_188e0 D_188e0.
      sv F_19100 D_19100 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_19104 D_19104 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 100896) ltac:(ok_win HJ).
      stepb_ft F_19108 D_19108 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_1910c D_1910c ((rnd_w sp0 inp)).
      sn F_19110 D_19110.
      ld_step F_19114 D_19114 (word_to_le_bytes 8 (Z_to_bv 64 602600)) (Z_to_bv 64 602600) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).
      sn F_19118 D_19118.
      sn F_1911c D_1911c.
      stepiv F_20054 D_20054 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_20058 D_20058 ltac:(pin; cond_compute).
      sn F_20168 D_20168.
      sn F_2016c D_2016c.
      stepb_ft F_20170 D_20170 ltac:(pin; cond_compute).
      sn F_20174 D_20174.
      stepb_tk F_20178 D_20178 ltac:(pin; cond_compute).
      sn F_201b0 D_201b0.
      stepb_ft F_201b4 D_201b4 ltac:(pin; cond_compute).
      ld_step F_201b8 D_201b8 (rnd4 rdraw 0) (le_bytes_to_word (rnd4 rdraw 0)) ltac:(RD_RND 0%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      ld_step F_201bc D_201bc (rnd4 rdraw 4) (le_bytes_to_word (rnd4 rdraw 4)) ltac:(RD_RND 4%nat) ltac:(apply lw_bridge; rewrite length_rnd4; lia).
      stw F_201c0 D_201c0 (Z_to_bv 64 602600) (lw_val (rnd4 rdraw 0)) ltac:(ok_data).
      stw F_201c4 D_201c4 (Z_to_bv 64 602604) (lw_val (rnd4 rdraw 4)) ltac:(ok_data).
      sn F_201c8 D_201c8.
      sv F_201cc D_201cc (Z_to_bv 64 (bv_unsigned (rnd_w sp0 inp) + 8)).
      sn F_201d0 D_201d0.
      stepb_tk F_201d4 D_201d4 ltac:(pin; cond_compute).
      sn F_20414 D_20414.
      stepb_ft F_20418 D_20418 ltac:(pin; cond_compute).
      sn F_2041c D_2041c.
      stepb_ft F_20420 D_20420 ltac:(pin; cond_compute).
      stepret F_20424 D_20424 (0x19250 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_19120 D_19120.
      sn F_1913c D_1913c.
      ld_step F_19140 D_19140 (word_to_le_bytes 8 (Z_to_bv 64 602600)) (Z_to_bv 64 602600) ltac:(rd_img img_21ae0_8) ltac:(apply bytes_le_to_Z_8).
      stw F_19144 D_19144 (Z_to_bv 64 602601) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_19148 D_19148 (canary_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply ld_canary).
      sn F_1914c D_1914c.
      stw F_19150 D_19150 (Z_to_bv 64 470896) (canary_w rdraw) ltac:(ok_data).
      ld_step F_19154 D_19154 (word_to_le_bytes 8 (Z_to_bv 64 100896)) (Z_to_bv 64 100896) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_19158 D_19158 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_1915c D_1915c (0x18a20 : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c7 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 470912 ->
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
        getr regs' 4 = (Z_to_bv 64 470912) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 84172) ->
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
        G (mkst regs' (0x18be0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100896))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602600) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602604) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602601) ([Z_to_bv 8 0])) (Z_to_bv 64 470896) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18a20 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100896))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602600) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602604) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602601) ([Z_to_bv 8 0])) (Z_to_bv 64 470896) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { ld_step F_188e4 D_188e4 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_188e8 D_188e8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_188ec D_188ec ltac:(pin; apply c_eq_refl).
      ld_step F_188f0 D_188f0 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_188f4 D_188f4 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_188f8 D_188f8 ltac:(pin; apply c_eq_refl).
      ld_step F_188fc D_188fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_18900 D_18900 ltac:(pin; cond_compute).
      ld_step F_189e0 D_189e0 (word_to_le_bytes 8 (Z_to_bv 64 101300)) (Z_to_bv 64 101300) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_189e4 D_189e4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_189e8 D_189e8 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_189ec D_189ec (word_to_le_bytes 8 (Z_to_bv 64 84172)) (Z_to_bv 64 84172) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_189f0 D_189f0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_189f4 D_189f4 (0x18bb4 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_18a78 D_18a78.
      sn F_18a7c D_18a7c.
      sn F_18a80 D_18a80.
      sv F_18a84 D_18a84 (argc_w inp).
      sv F_18a88 D_18a88 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_18a8c D_18a8c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a90 D_18a90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a94 D_18a94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a98 D_18a98 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_18a9c D_18a9c (sp0).
      stepret F_18aa0 D_18aa0 (0x18be0 : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { ld_step F_188e4 D_188e4 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_188e8 D_188e8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_188ec D_188ec ltac:(pin; apply c_eq_refl).
      ld_step F_188f0 D_188f0 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_188f4 D_188f4 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_188f8 D_188f8 ltac:(pin; apply c_eq_refl).
      ld_step F_188fc D_188fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_18900 D_18900 ltac:(pin; cond_compute).
      ld_step F_189e0 D_189e0 (word_to_le_bytes 8 (Z_to_bv 64 101300)) (Z_to_bv 64 101300) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_189e4 D_189e4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_189e8 D_189e8 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_189ec D_189ec (word_to_le_bytes 8 (Z_to_bv 64 84172)) (Z_to_bv 64 84172) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_189f0 D_189f0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_189f4 D_189f4 (0x18bb4 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_18a78 D_18a78.
      sn F_18a7c D_18a7c.
      sn F_18a80 D_18a80.
      sv F_18a84 D_18a84 (argc_w inp).
      sv F_18a88 D_18a88 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_18a8c D_18a8c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a90 D_18a90 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a94 D_18a94 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a98 D_18a98 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_18a9c D_18a9c (sp0).
      stepret F_18aa0 D_18aa0 (0x18be0 : word) ltac:(pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c8 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 470912 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 84172 ->
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
        getr regs' 1 = (Z_to_bv 64 101220) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 470912) ->
        getr regs' 8 = (Z_to_bv 64 138088) ->
        getr regs' 9 = (Z_to_bv 64 138080) ->
        getr regs' 18 = (Z_to_bv 64 84172) ->
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
        G (mkst regs' (0x147c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100896))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101396))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602600) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602604) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602601) ([Z_to_bv 8 0])) (Z_to_bv 64 470896) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x18be0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100896))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602600) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602604) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602601) ([Z_to_bv 8 0])) (Z_to_bv 64 470896) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_18aa4 D_18aa4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_18aa8 D_18aa8 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18aac D_18aac (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18ab0 D_18ab0 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18ab4 D_18ab4 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18ab8 D_18ab8 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_18abc D_18abc (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_18ac0 D_18ac0 (argc_w inp).
      sn F_18ac4 D_18ac4.
      stepiv F_18ac8 D_18ac8 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_18acc D_18acc (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_18ad0 D_18ad0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_18ad4 D_18ad4.
      sv F_189f8 D_189f8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_189fc D_189fc (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 101396) ltac:(ok_win HJ).
      stw F_18a00 D_18a00 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_18a04 D_18a04 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_18a08 D_18a08.
      stepret F_187c8 D_187c8 (0x18b48 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_18a0c D_18a0c.
      sn F_18a10 D_18a10.
      ld_step F_18a14 D_18a14 (word_to_le_bytes 8 (Z_to_bv 64 138088)) (Z_to_bv 64 138088) ltac:(rd_img img_21ad0_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a18 D_18a18 (word_to_le_bytes 8 (Z_to_bv 64 138080)) (Z_to_bv 64 138080) ltac:(rd_img img_21ad8_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_18a1c D_18a1c ltac:(pin; cond_compute).
      ld_step F_18a20 D_18a20 (word_to_le_bytes 8 (Z_to_bv 64 83912)) (Z_to_bv 64 83912) ltac:(rd_img img_21a30_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_18a24 D_18a24 (0x147c8 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_18aa4 D_18aa4 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_18aa8 D_18aa8 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18aac D_18aac (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18ab0 D_18ab0 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18ab4 D_18ab4 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_18ab8 D_18ab8 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_18abc D_18abc (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_18ac0 D_18ac0 (argc_w inp).
      sn F_18ac4 D_18ac4.
      stepiv F_18ac8 D_18ac8 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_18acc D_18acc (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_18ad0 D_18ad0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_18ad4 D_18ad4.
      sv F_189f8 D_189f8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_189fc D_189fc (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 101396) ltac:(ok_win HJ).
      stw F_18a00 D_18a00 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_18a04 D_18a04 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_18a08 D_18a08.
      stepret F_187c8 D_187c8 (0x18b48 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_18a0c D_18a0c.
      sn F_18a10 D_18a10.
      ld_step F_18a14 D_18a14 (word_to_le_bytes 8 (Z_to_bv 64 138088)) (Z_to_bv 64 138088) ltac:(rd_img img_21ad0_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a18 D_18a18 (word_to_le_bytes 8 (Z_to_bv 64 138080)) (Z_to_bv 64 138080) ltac:(rd_img img_21ad8_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_18a1c D_18a1c ltac:(pin; cond_compute).
      ld_step F_18a20 D_18a20 (word_to_le_bytes 8 (Z_to_bv 64 83912)) (Z_to_bv 64 83912) ltac:(rd_img img_21a30_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_18a24 D_18a24 (0x147c8 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.

  Lemma fin_c9 : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 101220 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 470912 ->
    getr regs 8 = Z_to_bv 64 138088 ->
    getr regs 9 = Z_to_bv 64 138080 ->
    getr regs 18 = Z_to_bv 64 84172 ->
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
        getr regs' 1 = (Z_to_bv 64 101412) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 470912) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 84172) ->
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
        G (mkst regs' (0x148cc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100896))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101396))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 101220))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 138088))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602600) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602604) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602601) ([Z_to_bv 8 0])) (Z_to_bv 64 470896) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 142896) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x147c8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 inp mbase rdraw (J_lsm sp0 inp Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100888))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 602632))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 100896))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 101396))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 inp rdraw) (Z_to_bv 64 602024) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602040) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 602656) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 602664) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 470928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 470904) (word_to_le_bytes 8 (Z_to_bv 64 470928))) (Z_to_bv 64 470712) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 602632) ([Z_to_bv 8 1])) (Z_to_bv 64 470752) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 470744) (word_to_le_bytes 4 tid)) (Z_to_bv 64 470864) (word_to_le_bytes 8 (Z_to_bv 64 602688))) (Z_to_bv 64 470832) (word_to_le_bytes 8 (Z_to_bv 64 470832))) (Z_to_bv 64 470720) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470728) (word_to_le_bytes 8 (Z_to_bv 64 470712))) (Z_to_bv 64 470736) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 602600) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 0)))) (Z_to_bv 64 602604) (word_to_le_bytes 4 (lw_val (rnd4 rdraw 4)))) (Z_to_bv 64 602601) ([Z_to_bv 8 0])) (Z_to_bv 64 470896) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_aux0, J_lsm, D_libc, aux_base, argv_w in *.
    (* J_aux's two AT_RSEQ_* stores follow the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RSQ; rewrite ?RSQ in *; cbn iota in *.
    {
    eapply HG.
    { sv F_1472c D_1472c (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_14730 D_14730 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 101220) ltac:(ok_win HJ).
      stw F_14734 D_14734 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 138088) ltac:(ok_win HJ).
      sv F_14738 D_14738 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_1473c D_1473c.
      sn F_14740 D_14740.
      lb_step F_14744 D_14744 (Z_to_bv 8 0) ltac:(rd_img img_22d10_1).
      sn F_14748 D_14748.
      stepb_tk F_1474c D_1474c ltac:(pin; cond_compute).
      sn F_14758 D_14758.
      sn F_1475c D_1475c.
      sn F_14760 D_14760.
      stw F_14764 D_14764 (Z_to_bv 64 142896) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_14768 D_14768.
      ld_step F_1476c D_1476c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_21a78_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_14770 D_14770 ltac:(pin; cond_compute).
      ld_step F_14790 D_14790 (word_to_le_bytes 8 (Z_to_bv 64 101220)) (Z_to_bv 64 101220) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_14794 D_14794 (word_to_le_bytes 8 (Z_to_bv 64 138088)) (Z_to_bv 64 138088) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_14798 D_14798 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_1479c D_1479c (0x18b64 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_18a28 D_18a28.
      stepb_ft F_18a2c D_18a2c ltac:(pin; cond_compute).
      ld_step F_18a30 D_18a30 (word_to_le_bytes 8 (Z_to_bv 64 101396)) (Z_to_bv 64 101396) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a34 D_18a34 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a38 D_18a38 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_18a3c D_18a3c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_18a40 D_18a40 (0x18c14 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_18ad8 D_18ad8 (argc_w inp).
      sv F_18adc D_18adc (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_18ae0 D_18ae0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_18ae4 D_18ae4 (0x148cc : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
    {
    eapply HG.
    { sv F_1472c D_1472c (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_14730 D_14730 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 101220) ltac:(ok_win HJ).
      stw F_14734 D_14734 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 138088) ltac:(ok_win HJ).
      sv F_14738 D_14738 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_1473c D_1473c.
      sn F_14740 D_14740.
      lb_step F_14744 D_14744 (Z_to_bv 8 0) ltac:(rd_img img_22d10_1).
      sn F_14748 D_14748.
      stepb_tk F_1474c D_1474c ltac:(pin; cond_compute).
      sn F_14758 D_14758.
      sn F_1475c D_1475c.
      sn F_14760 D_14760.
      stw F_14764 D_14764 (Z_to_bv 64 142896) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_14768 D_14768.
      ld_step F_1476c D_1476c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_21a78_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_14770 D_14770 ltac:(pin; cond_compute).
      ld_step F_14790 D_14790 (word_to_le_bytes 8 (Z_to_bv 64 101220)) (Z_to_bv 64 101220) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_14794 D_14794 (word_to_le_bytes 8 (Z_to_bv 64 138088)) (Z_to_bv 64 138088) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_14798 D_14798 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_1479c D_1479c (0x18b64 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_18a28 D_18a28.
      stepb_ft F_18a2c D_18a2c ltac:(pin; cond_compute).
      ld_step F_18a30 D_18a30 (word_to_le_bytes 8 (Z_to_bv 64 101396)) (Z_to_bv 64 101396) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a34 D_18a34 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_18a38 D_18a38 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_18a3c D_18a3c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_18a40 D_18a40 (0x18c14 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_18ad8 D_18ad8 (argc_w inp).
      sv F_18adc D_18adc (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_18ae0 D_18ae0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_18ae4 D_18ae4 (0x148cc : word) ltac:(gres; pin; first [reflexivity | bveq]).
      OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
    }
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.L10Walk.l10_chain_step_kit.
