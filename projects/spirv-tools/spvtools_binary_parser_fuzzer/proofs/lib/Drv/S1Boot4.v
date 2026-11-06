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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1BootCode S1BootDefs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RefMemcpyLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Img.
  Variable SEGS : list Segment.
  Hypothesis HX : s1b_ok SEGS = true.

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
    getr regs 4 = Z_to_bv 64 1050296 ->
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
        getr regs' 4 = (Z_to_bv 64 1050296) ->
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
        G (mkst regs' (0xcf8ac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850092))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1050128) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1050248) (word_to_le_bytes 8 (Z_to_bv 64 1182080))) (Z_to_bv 64 1050216) (word_to_le_bytes 8 (Z_to_bv 64 1050216))) (Z_to_bv 64 1050104) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050112) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181992) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181996) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181993) [Z_to_bv 8 0]) (Z_to_bv 64 1050280) (word_to_le_bytes 8 (canary rdraw)))) rom)) ->
    G (mkst regs (0xcf8a4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1050128) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1050248) (word_to_le_bytes 8 (Z_to_bv 64 1182080))) (Z_to_bv 64 1050216) (word_to_le_bytes 8 (Z_to_bv 64 1050216))) (Z_to_bv 64 1050104) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050112) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050120) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step (F_cf864 _ HX) D_cf864 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn (F_cf868 _ HX) D_cf868.
      sv (F_d0220 _ HX) D_d0220 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw (F_d0224 _ HX) D_d0224 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 850092) ltac:(ok_win HJ).
      stepb_ft (F_d0228 _ HX) D_d0228 ltac:(pin; apply c_eq_0_false; lia).
      sv (F_d022c _ HX) D_d022c (rnd_w sp0 av ev).
      sn (F_d0230 _ HX) D_d0230.
      ld_step (F_d0234 _ HX) D_d0234 (word_to_le_bytes 8 (Z_to_bv 64 1181992)) (Z_to_bv 64 1181992) ltac:(rd_img (img_ed088_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      sn (F_d0238 _ HX) D_d0238.
      sn (F_d023c _ HX) D_d023c.
      stepiv (F_e0e10 _ HX) D_e0e10 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite Hr3; reflexivity).
      stepb_tk (F_e0e14 _ HX) D_e0e14 ltac:(pin; cond_compute).
      sn (F_e0f24 _ HX) D_e0f24.
      sn (F_e0f28 _ HX) D_e0f28.
      stepb_ft (F_e0f2c _ HX) D_e0f2c ltac:(pin; cond_compute).
      sn (F_e0f30 _ HX) D_e0f30.
      stepb_tk (F_e0f34 _ HX) D_e0f34 ltac:(pin; cond_compute).
      sn (F_e0f6c _ HX) D_e0f6c.
      stepb_ft (F_e0f70 _ HX) D_e0f70 ltac:(pin; cond_compute).
      ld_step (F_e0f74 _ HX) D_e0f74 (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) (Z_to_bv 64 (lez (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))))) ltac:(RD_RND 0%nat) ltac:(symmetry; apply u_lez4; reflexivity).
      ld_step (F_e0f78 _ HX) D_e0f78 (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) (Z_to_bv 64 (lez (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))))) ltac:(RD_RND 4%nat) ltac:(symmetry; apply u_lez4; reflexivity).
      stw (F_e0f7c _ HX) D_e0f7c (Z_to_bv 64 1181992) (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))) ltac:(ok_dat HX).
      stw (F_e0f80 _ HX) D_e0f80 (Z_to_bv 64 1181996) (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))) ltac:(ok_dat HX).
      sn (F_e0f84 _ HX) D_e0f84.
      sv (F_e0f88 _ HX) D_e0f88 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).
      sn (F_e0f8c _ HX) D_e0f8c.
      stepb_tk (F_e0f90 _ HX) D_e0f90 ltac:(pin; cond_compute).
      sn (F_e11d0 _ HX) D_e11d0.
      stepb_ft (F_e11d4 _ HX) D_e11d4 ltac:(pin; cond_compute).
      sn (F_e11d8 _ HX) D_e11d8.
      stepb_ft (F_e11dc _ HX) D_e11dc ltac:(pin; cond_compute).
      stepret (F_e11e0 _ HX) D_e11e0 (0xd0274 : word) ltac:(pin; first [reflexivity | bveq]).
      sn (F_d0240 _ HX) D_d0240.
      sn (F_d025c _ HX) D_d025c.
      ld_step (F_d0260 _ HX) D_d0260 (word_to_le_bytes 8 (Z_to_bv 64 1181992)) (Z_to_bv 64 1181992) ltac:(rd_img (img_ed088_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stw (F_d0264 _ HX) D_d0264 (Z_to_bv 64 1181993) (Z_to_bv 64 0) ltac:(ok_dat HX).
      ld_step (F_d0268 _ HX) D_d0268 (word_to_le_bytes 8 (canary rdraw)) (canary rdraw) ltac:(RD_GUARD) ltac:(apply bytes_le_to_Z_8).
      sn (F_d026c _ HX) D_d026c.
      stw (F_d0270 _ HX) D_d0270 (Z_to_bv 64 1050280) (canary rdraw) ltac:(ok_dat HX).
      ld_step (F_d0274 _ HX) D_d0274 (word_to_le_bytes 8 (Z_to_bv 64 850092)) (Z_to_bv 64 850092) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv (F_d0278 _ HX) D_d0278 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret (F_d027c _ HX) D_d027c (0xcf8ac : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 1050296 ->
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
        getr regs' 4 = (Z_to_bv 64 1050296) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 415208) ->
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
        G (mkst regs' (0xcfa6c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850092))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1050128) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1050248) (word_to_le_bytes 8 (Z_to_bv 64 1182080))) (Z_to_bv 64 1050216) (word_to_le_bytes 8 (Z_to_bv 64 1050216))) (Z_to_bv 64 1050104) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050112) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181992) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181996) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181993) [Z_to_bv 8 0]) (Z_to_bv 64 1050280) (word_to_le_bytes 8 (canary rdraw)))) rom)) ->
    G (mkst regs (0xcf8ac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850092))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1050128) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1050248) (word_to_le_bytes 8 (Z_to_bv 64 1182080))) (Z_to_bv 64 1050216) (word_to_le_bytes 8 (Z_to_bv 64 1050216))) (Z_to_bv 64 1050104) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050112) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181992) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181996) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181993) [Z_to_bv 8 0]) (Z_to_bv 64 1050280) (word_to_le_bytes 8 (canary rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step (F_cf86c _ HX) D_cf86c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cf870 _ HX) D_cf870 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft (F_cf874 _ HX) D_cf874 ltac:(pin; apply c_eq_refl).
      ld_step (F_cf878 _ HX) D_cf878 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      ld_step (F_cf87c _ HX) D_cf87c (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      stepb_ft (F_cf880 _ HX) D_cf880 ltac:(pin; cond_compute).
      ld_step (F_cf884 _ HX) D_cf884 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk (F_cf888 _ HX) D_cf888 ltac:(pin; cond_compute).
      ld_step (F_cf968 _ HX) D_cf968 (word_to_le_bytes 8 (Z_to_bv 64 850496)) (Z_to_bv 64 850496) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cf96c _ HX) D_cf96c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cf970 _ HX) D_cf970 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cf974 _ HX) D_cf974 (word_to_le_bytes 8 (Z_to_bv 64 415208)) (Z_to_bv 64 415208) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv (F_cf978 _ HX) D_cf978 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret (F_cf97c _ HX) D_cf97c (0xcfa40 : word) ltac:(pin; first [reflexivity | bveq]).
      sn (F_cfa00 _ HX) D_cfa00.
      sn (F_cfa04 _ HX) D_cfa04.
      sn (F_cfa08 _ HX) D_cfa08.
      sv (F_cfa0c _ HX) D_cfa0c (argc_w av).
      sv (F_cfa10 _ HX) D_cfa10 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step (F_cfa14 _ HX) D_cfa14 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfa18 _ HX) D_cfa18 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfa1c _ HX) D_cfa1c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cfa20 _ HX) D_cfa20 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv (F_cfa24 _ HX) D_cfa24 (sp0).
      stepret (F_cfa28 _ HX) D_cfa28 (0xcfa6c : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 1050296 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 415208 ->
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
        getr regs' 1 = (Z_to_bv 64 850416) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 1050296) ->
        getr regs' 8 = (Z_to_bv 64 945944) ->
        getr regs' 9 = (Z_to_bv 64 945928) ->
        getr regs' 18 = (Z_to_bv 64 415208) ->
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
        G (mkst regs' (0x930bc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850092))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 850592))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1050128) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1050248) (word_to_le_bytes 8 (Z_to_bv 64 1182080))) (Z_to_bv 64 1050216) (word_to_le_bytes 8 (Z_to_bv 64 1050216))) (Z_to_bv 64 1050104) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050112) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181992) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181996) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181993) [Z_to_bv 8 0]) (Z_to_bv 64 1050280) (word_to_le_bytes 8 (canary rdraw)))) rom)) ->
    G (mkst regs (0xcfa6c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850084))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1182024))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 850092))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1181408) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181424) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181416) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1182048) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1182056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1050312) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1050288) (word_to_le_bytes 8 (Z_to_bv 64 1050312))) (Z_to_bv 64 1050096) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1182024) ([Z_to_bv 8 1])) (Z_to_bv 64 1050136) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 1050128) (word_to_le_bytes 4 tid)) (Z_to_bv 64 1050248) (word_to_le_bytes 8 (Z_to_bv 64 1182080))) (Z_to_bv 64 1050216) (word_to_le_bytes 8 (Z_to_bv 64 1050216))) (Z_to_bv 64 1050104) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050112) (word_to_le_bytes 8 (Z_to_bv 64 1050096))) (Z_to_bv 64 1050120) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1181992) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181996) (word_to_le_bytes 4 (LWv (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw))))))) (Z_to_bv 64 1181993) [Z_to_bv 8 0]) (Z_to_bv 64 1050280) (word_to_le_bytes 8 (canary rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv (F_cfa2c _ HX) D_cfa2c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw (F_cfa30 _ HX) D_cfa30 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_cfa34 _ HX) D_cfa34 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_cfa38 _ HX) D_cfa38 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_cfa3c _ HX) D_cfa3c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw (F_cfa40 _ HX) D_cfa40 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv (F_cfa44 _ HX) D_cfa44 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv (F_cfa48 _ HX) D_cfa48 (argc_w av).
      sn (F_cfa4c _ HX) D_cfa4c.
      stepiv (F_cfa50 _ HX) D_cfa50 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv (F_cfa54 _ HX) D_cfa54 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv (F_cfa58 _ HX) D_cfa58 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn (F_cfa5c _ HX) D_cfa5c.
      sv (F_cf980 _ HX) D_cf980 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw (F_cf984 _ HX) D_cf984 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 850592) ltac:(ok_win HJ).
      stw (F_cf988 _ HX) D_cf988 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw (F_cf98c _ HX) D_cf98c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).
      sn (F_cf990 _ HX) D_cf990.
      stepret (F_cf750 _ HX) D_cf750 (0xcf9d4 : word) ltac:(pin; first [reflexivity | bveq]).
      sn (F_cf994 _ HX) D_cf994.
      sn (F_cf998 _ HX) D_cf998.
      ld_step (F_cf99c _ HX) D_cf99c (word_to_le_bytes 8 (Z_to_bv 64 945944)) (Z_to_bv 64 945944) ltac:(rd_img (img_ed078_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      ld_step (F_cf9a0 _ HX) D_cf9a0 (word_to_le_bytes 8 (Z_to_bv 64 945928)) (Z_to_bv 64 945928) ltac:(rd_img (img_ed080_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stepb_ft (F_cf9a4 _ HX) D_cf9a4 ltac:(pin; cond_compute).
      ld_step (F_cf9a8 _ HX) D_cf9a8 (word_to_le_bytes 8 (Z_to_bv 64 602300)) (Z_to_bv 64 602300) ltac:(rd_img (img_e6ed8_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
      stepjr (F_cf9ac _ HX) D_cf9ac (0x930bc : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P6.

End Img.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
