(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ArgvEnv RefLayout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1BootCode U1BootDefs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RefMemcpyLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Img.
  Variable SEGS : list Segment.
  Hypothesis HX : u1b_ok SEGS = true.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

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
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
    = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_GUARD := rewrite rdn_cmem_data by region_side; apply rd_guard.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Ltac rd_J9 R :=
    lazymatch goal with |- rdn _ _ ?a _ = _ =>
      lazymatch type of R with rdn _ _ ?a' _ = _ =>
        first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end end;
    exact R.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 1057816 ->
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
        getr regs' 4 = (Z_to_bv 64 1057816) ->
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
        G (mkst regs' (0xd1604 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857604))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1057648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1057768) (word_to_le_bytes 8 (Z_to_bv 64 1189600))) (Z_to_bv 64 1057736) (word_to_le_bytes 8 (Z_to_bv 64 1057736))) (Z_to_bv 64 1057624) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057632) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1189512) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189516) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189513) [Z_to_bv 8 0]) (Z_to_bv 64 1057800) (word_to_le_bytes 8 (canary rdraw)))) rom)) ->
    G (mkst regs (0xd15fc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1057648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1057768) (word_to_le_bytes 8 (Z_to_bv 64 1189600))) (Z_to_bv 64 1057736) (word_to_le_bytes 8 (Z_to_bv 64 1057736))) (Z_to_bv 64 1057624) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057632) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057640) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step (F_d15bc _ HX) D_d15bc (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn (F_d15c0 _ HX) D_d15c0.
      sv (F_d1f78 _ HX) D_d1f78 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw (F_d1f7c _ HX) D_d1f7c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 857604) ltac:(ok_win HJ).
      stepb_ft (F_d1f80 _ HX) D_d1f80 ltac:(pin; apply c_eq_0_false; lia).
      sv (F_d1f84 _ HX) D_d1f84 (rnd_w sp0 av ev).
      sn (F_d1f88 _ HX) D_d1f88.
      ld_step (F_d1f8c _ HX) D_d1f8c (word_to_le_bytes 8 (Z_to_bv 64 1189512)) (Z_to_bv 64 1189512) ltac:(rd_img (img_eede0_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      sn (F_d1f90 _ HX) D_d1f90.
      sn (F_d1f94 _ HX) D_d1f94.
      stepiv (F_e2b68 _ HX) D_e2b68 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite Hr3; reflexivity).
      stepb_tk (F_e2b6c _ HX) D_e2b6c ltac:(pin; cond_compute).
      sn (F_e2c7c _ HX) D_e2c7c.
      sn (F_e2c80 _ HX) D_e2c80.
      stepb_ft (F_e2c84 _ HX) D_e2c84 ltac:(pin; cond_compute).
      sn (F_e2c88 _ HX) D_e2c88.
      stepb_tk (F_e2c8c _ HX) D_e2c8c ltac:(pin; cond_compute).
      sn (F_e2cc4 _ HX) D_e2cc4.
      stepb_ft (F_e2cc8 _ HX) D_e2cc8 ltac:(pin; cond_compute).
      ld_step (F_e2ccc _ HX) D_e2ccc (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) (Z_to_bv 64 (lez (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))))) ltac:(RD_RND 0%nat) ltac:(symmetry; apply u_lez4; reflexivity).
      ld_step (F_e2cd0 _ HX) D_e2cd0 (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) (Z_to_bv 64 (lez (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))))) ltac:(RD_RND 4%nat) ltac:(symmetry; apply u_lez4; reflexivity).
      stw (F_e2cd4 _ HX) D_e2cd4 (Z_to_bv 64 1189512) (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))) ltac:(ok_dat HX).
      stw (F_e2cd8 _ HX) D_e2cd8 (Z_to_bv 64 1189516) (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))) ltac:(ok_dat HX).
      sn (F_e2cdc _ HX) D_e2cdc.
      sv (F_e2ce0 _ HX) D_e2ce0 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).
      sn (F_e2ce4 _ HX) D_e2ce4.
      stepb_tk (F_e2ce8 _ HX) D_e2ce8 ltac:(pin; cond_compute).
      sn (F_e2f28 _ HX) D_e2f28.
      stepb_ft (F_e2f2c _ HX) D_e2f2c ltac:(pin; cond_compute).
      sn (F_e2f30 _ HX) D_e2f30.
      stepb_ft (F_e2f34 _ HX) D_e2f34 ltac:(pin; cond_compute).
      stepret (F_e2f38 _ HX) D_e2f38 (0xd1fcc : word) ltac:(pin; first [reflexivity | bveq]).
      sn (F_d1f98 _ HX) D_d1f98.
      sn (F_d1fb4 _ HX) D_d1fb4.
      ld_step (F_d1fb8 _ HX) D_d1fb8 (word_to_le_bytes 8 (Z_to_bv 64 1189512)) (Z_to_bv 64 1189512) ltac:(rd_img (img_eede0_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stw (F_d1fbc _ HX) D_d1fbc (Z_to_bv 64 1189513) (Z_to_bv 64 0) ltac:(ok_dat HX).
      ld_step (F_d1fc0 _ HX) D_d1fc0 (word_to_le_bytes 8 (canary rdraw)) (canary rdraw) ltac:(RD_GUARD) ltac:(apply bytes_le_to_Z_8).
      sn (F_d1fc4 _ HX) D_d1fc4.
      stw (F_d1fc8 _ HX) D_d1fc8 (Z_to_bv 64 1057800) (canary rdraw) ltac:(ok_dat HX).
      ld_step (F_d1fcc _ HX) D_d1fcc (word_to_le_bytes 8 (Z_to_bv 64 857604)) (Z_to_bv 64 857604) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv (F_d1fd0 _ HX) D_d1fd0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret (F_d1fd4 _ HX) D_d1fd4 (0xd1604 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 1057816 ->
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
        getr regs' 4 = (Z_to_bv 64 1057816) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 415804) ->
        getr regs' 11 = (argc_w av) ->
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
        G (mkst regs' (0xd17c4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857604))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1057648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1057768) (word_to_le_bytes 8 (Z_to_bv 64 1189600))) (Z_to_bv 64 1057736) (word_to_le_bytes 8 (Z_to_bv 64 1057736))) (Z_to_bv 64 1057624) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057632) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1189512) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189516) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189513) [Z_to_bv 8 0]) (Z_to_bv 64 1057800) (word_to_le_bytes 8 (canary rdraw)))) rom)) ->
    G (mkst regs (0xd1604 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857604))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1057648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1057768) (word_to_le_bytes 8 (Z_to_bv 64 1189600))) (Z_to_bv 64 1057736) (word_to_le_bytes 8 (Z_to_bv 64 1057736))) (Z_to_bv 64 1057624) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057632) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1189512) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189516) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189513) [Z_to_bv 8 0]) (Z_to_bv 64 1057800) (word_to_le_bytes 8 (canary rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step (F_d15c4 _ HX) D_d15c4 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d15c8 _ HX) D_d15c8 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft (F_d15cc _ HX) D_d15cc ltac:(pin; apply c_eq_refl).
      ld_step (F_d15d0 _ HX) D_d15d0 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      ld_step (F_d15d4 _ HX) D_d15d4 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      stepb_ft (F_d15d8 _ HX) D_d15d8 ltac:(pin; cond_compute).
      ld_step (F_d15dc _ HX) D_d15dc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk (F_d15e0 _ HX) D_d15e0 ltac:(pin; cond_compute).
      ld_step (F_d16c0 _ HX) D_d16c0 (word_to_le_bytes 8 (Z_to_bv 64 858008)) (Z_to_bv 64 858008) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d16c4 _ HX) D_d16c4 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d16c8 _ HX) D_d16c8 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d16cc _ HX) D_d16cc (word_to_le_bytes 8 (Z_to_bv 64 415804)) (Z_to_bv 64 415804) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv (F_d16d0 _ HX) D_d16d0 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret (F_d16d4 _ HX) D_d16d4 (0xd1798 : word) ltac:(pin; first [reflexivity | bveq]).
      sn (F_d1758 _ HX) D_d1758.
      sn (F_d175c _ HX) D_d175c.
      sn (F_d1760 _ HX) D_d1760.
      sv (F_d1764 _ HX) D_d1764 (argc_w av).
      sv (F_d1768 _ HX) D_d1768 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step (F_d176c _ HX) D_d176c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1770 _ HX) D_d1770 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1774 _ HX) D_d1774 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d1778 _ HX) D_d1778 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv (F_d177c _ HX) D_d177c (sp0).
      stepret (F_d1780 _ HX) D_d1780 (0xd17c4 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 1057816 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 415804 ->
    getr regs 11 = argc_w av ->
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
        getr regs' 1 = (Z_to_bv 64 857928) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 1057816) ->
        getr regs' 8 = (Z_to_bv 64 953456) ->
        getr regs' 9 = (Z_to_bv 64 953440) ->
        getr regs' 18 = (Z_to_bv 64 415804) ->
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
        G (mkst regs' (0x94e14 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857604))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 858104))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1057648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1057768) (word_to_le_bytes 8 (Z_to_bv 64 1189600))) (Z_to_bv 64 1057736) (word_to_le_bytes 8 (Z_to_bv 64 1057736))) (Z_to_bv 64 1057624) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057632) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1189512) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189516) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189513) [Z_to_bv 8 0]) (Z_to_bv 64 1057800) (word_to_le_bytes 8 (canary rdraw)))) rom)) ->
    G (mkst regs (0xd17c4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857596))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1189544))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 857604))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1188928) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188944) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1188936) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1189568) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1189576) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1057832) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1057808) (word_to_le_bytes 8 (Z_to_bv 64 1057832))) (Z_to_bv 64 1057616) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1189544) ([Z_to_bv 8 1])) (Z_to_bv 64 1057656) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1057648) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1057768) (word_to_le_bytes 8 (Z_to_bv 64 1189600))) (Z_to_bv 64 1057736) (word_to_le_bytes 8 (Z_to_bv 64 1057736))) (Z_to_bv 64 1057624) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057632) (word_to_le_bytes 8 (Z_to_bv 64 1057616))) (Z_to_bv 64 1057640) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1189512) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189516) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1189513) [Z_to_bv 8 0]) (Z_to_bv 64 1057800) (word_to_le_bytes 8 (canary rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv (F_d1784 _ HX) D_d1784 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw (F_d1788 _ HX) D_d1788 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_d178c _ HX) D_d178c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_d1790 _ HX) D_d1790 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_d1794 _ HX) D_d1794 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_d1798 _ HX) D_d1798 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv (F_d179c _ HX) D_d179c (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv (F_d17a0 _ HX) D_d17a0 (argc_w av).
      sn (F_d17a4 _ HX) D_d17a4.
      stepiv (F_d17a8 _ HX) D_d17a8 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv (F_d17ac _ HX) D_d17ac (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv (F_d17b0 _ HX) D_d17b0 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn (F_d17b4 _ HX) D_d17b4.
      sv (F_d16d8 _ HX) D_d16d8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw (F_d16dc _ HX) D_d16dc (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 858104) ltac:(ok_win HJ).
      stw (F_d16e0 _ HX) D_d16e0 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw (F_d16e4 _ HX) D_d16e4 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).
      sn (F_d16e8 _ HX) D_d16e8.
      stepret (F_d14a8 _ HX) D_d14a8 (0xd172c : word) ltac:(pin; first [reflexivity | bveq]).
      sn (F_d16ec _ HX) D_d16ec.
      sn (F_d16f0 _ HX) D_d16f0.
      ld_step (F_d16f4 _ HX) D_d16f4 (word_to_le_bytes 8 (Z_to_bv 64 953456)) (Z_to_bv 64 953456) ltac:(rd_img (img_eedd0_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_d16f8 _ HX) D_d16f8 (word_to_le_bytes 8 (Z_to_bv 64 953440)) (Z_to_bv 64 953440) ltac:(rd_img (img_eedd8_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stepb_ft (F_d16fc _ HX) D_d16fc ltac:(pin; cond_compute).
      ld_step (F_d1700 _ HX) D_d1700 (word_to_le_bytes 8 (Z_to_bv 64 609812)) (Z_to_bv 64 609812) ltac:(rd_img (img_e8c30_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stepjr (F_d1704 _ HX) D_d1704 (0x94e14 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P6.

End Img.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
