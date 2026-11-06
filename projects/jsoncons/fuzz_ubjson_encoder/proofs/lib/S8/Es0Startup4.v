(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import StartupTac ArgvEnv RefLayout Es0Img Es0StartupDefs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Es0_code_r1ff24_20000 Es0_code_r4a000_4b000 Es0_code_r4b000_4c000 Es0_code_r58000_59000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.

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
    getr regs 4 = Z_to_bv 64 831552 ->
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
        getr regs' 4 = Z_to_bv 64 831552 ->
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
        G (mkst regs' (0x9b5a8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636328))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 963248) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 963252) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 963249) ([Z_to_bv 8 0])) (Z_to_bv 64 831536) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9b5a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_9b548 D_9b548 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_9b54c D_9b54c.
      sv F_9bf04 D_9bf04 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_9bf08 D_9bf08 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 636328) ltac:(ok_win HJ).
      stepb_ft F_9bf0c D_9bf0c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_9bf10 D_9bf10 (rnd_w sp0 av ev).
      sn F_9bf14 D_9bf14.
      ld_step F_9bf18 D_9bf18 (word_to_le_bytes 8 (Z_to_bv 64 963248)) (Z_to_bv 64 963248) ltac:(rd_img img_b8258_8) ltac:(apply bytes_le_to_Z_8).
      sn F_9bf1c D_9bf1c.
      sn F_9bf20 D_9bf20.
      stepiv F_ac440 D_ac440 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_ac444 D_ac444 ltac:(pin; cond_compute).
      sn F_ac554 D_ac554.
      sn F_ac558 D_ac558.
      stepb_ft F_ac55c D_ac55c ltac:(pin; cond_compute).
      sn F_ac560 D_ac560.
      stepb_tk F_ac564 D_ac564 ltac:(pin; cond_compute).
      sn F_ac59c D_ac59c.
      stepb_ft F_ac5a0 D_ac5a0 ltac:(pin; cond_compute).
      ld_step F_ac5a4 D_ac5a4 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
      ld_step F_ac5a8 D_ac5a8 (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
      stw F_ac5ac D_ac5ac (Z_to_bv 64 963248) (rlw RND 0) ltac:(ok_data).
      stw F_ac5b0 D_ac5b0 (Z_to_bv 64 963252) (rlw RND 4) ltac:(ok_data).
      sn F_ac5b4 D_ac5b4.
      sv F_ac5b8 D_ac5b8 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).
      sn F_ac5bc D_ac5bc.
      stepb_tk F_ac5c0 D_ac5c0 ltac:(pin; cond_compute).
      sn F_ac800 D_ac800.
      stepb_ft F_ac804 D_ac804 ltac:(pin; cond_compute).
      sn F_ac808 D_ac808.
      stepb_ft F_ac80c D_ac80c ltac:(pin; cond_compute).
      stepret F_ac810 D_ac810 (0x9bf70 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_9bf24 D_9bf24.
      sn F_9bf40 D_9bf40.
      ld_step F_9bf44 D_9bf44 (word_to_le_bytes 8 (Z_to_bv 64 963248)) (Z_to_bv 64 963248) ltac:(rd_img img_b8258_8) ltac:(apply bytes_le_to_Z_8).
      stw F_9bf48 D_9bf48 (Z_to_bv 64 963249) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_9bf4c D_9bf4c (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
      sn F_9bf50 D_9bf50.
      stw F_9bf54 D_9bf54 (Z_to_bv 64 831536) (canary_w RND) ltac:(ok_data).
      ld_step F_9bf58 D_9bf58 (word_to_le_bytes 8 (Z_to_bv 64 636328)) (Z_to_bv 64 636328) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_9bf5c D_9bf5c (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_9bf60 D_9bf60 (0x9b5a8 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 831552 ->
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
        getr regs' 4 = Z_to_bv 64 831552 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 214340 ->
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
        G (mkst regs' (0x9b768 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636328))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 963248) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 963252) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 963249) ([Z_to_bv 8 0])) (Z_to_bv 64 831536) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9b5a8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636328))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 963248) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 963252) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 963249) ([Z_to_bv 8 0])) (Z_to_bv 64 831536) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_9b550 D_9b550 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b554 D_9b554 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9b558 D_9b558 ltac:(pin; first [apply c_eq_refl | cond_compute]).
      ld_step F_9b55c D_9b55c (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      ld_step F_9b560 D_9b560 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
      stepb_ft F_9b564 D_9b564 ltac:(pin; cond_compute).
      ld_step F_9b568 D_9b568 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_9b56c D_9b56c ltac:(pin; cond_compute).
      ld_step F_9b64c D_9b64c (word_to_le_bytes 8 (Z_to_bv 64 636732)) (Z_to_bv 64 636732) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b650 D_9b650 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b654 D_9b654 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b658 D_9b658 (word_to_le_bytes 8 (Z_to_bv 64 214340)) (Z_to_bv 64 214340) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_9b65c D_9b65c (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_9b660 D_9b660 (0x9b73c : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_9b6e4 D_9b6e4.
      sn F_9b6e8 D_9b6e8.
      sn F_9b6ec D_9b6ec.
      sv F_9b6f0 D_9b6f0 (argc_w av).
      sv F_9b6f4 D_9b6f4 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_9b6f8 D_9b6f8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b6fc D_9b6fc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b700 D_9b700 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b704 D_9b704 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_9b708 D_9b708 sp0.
      stepret F_9b70c D_9b70c (0x9b768 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 831552 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 214340 ->
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
        getr regs' 1 = Z_to_bv 64 636652 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 831552 ->
        getr regs' 8 = Z_to_bv 64 730360 ->
        getr regs' 9 = Z_to_bv 64 730352 ->
        getr regs' 18 = Z_to_bv 64 214340 ->
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
        G (mkst regs' (0x34440 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636328))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 636828))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 963248) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 963252) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 963249) ([Z_to_bv 8 0])) (Z_to_bv 64 831536) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9b768 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636328))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 963248) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 963252) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 963249) ([Z_to_bv 8 0])) (Z_to_bv 64 831536) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_9b710 D_9b710 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_9b714 D_9b714 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_9b718 D_9b718 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_9b71c D_9b71c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_9b720 D_9b720 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_9b724 D_9b724 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_9b728 D_9b728 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_9b72c D_9b72c (argc_w av).
      sn F_9b730 D_9b730.
      stepiv F_9b734 D_9b734 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_9b738 D_9b738 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_9b73c D_9b73c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_9b740 D_9b740.
      sv F_9b664 D_9b664 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_9b668 D_9b668 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 636828) ltac:(ok_win HJ).
      stw F_9b66c D_9b66c (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_9b670 D_9b670 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).
      sn F_9b674 D_9b674.
      stepret F_9b434 D_9b434 (0x9b6d0 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_9b678 D_9b678.
      sn F_9b67c D_9b67c.
      ld_step F_9b680 D_9b680 (word_to_le_bytes 8 (Z_to_bv 64 730360)) (Z_to_bv 64 730360) ltac:(rd_img img_b8248_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b684 D_9b684 (word_to_le_bytes 8 (Z_to_bv 64 730352)) (Z_to_bv 64 730352) ltac:(rd_img img_b8250_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9b688 D_9b688 ltac:(pin; cond_compute).
      ld_step F_9b68c D_9b68c (word_to_le_bytes 8 (Z_to_bv 64 214080)) (Z_to_bv 64 214080) ltac:(rd_img img_b24a8_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_9b690 D_9b690 (0x34440 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 636652 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 831552 ->
    getr regs 8 = Z_to_bv 64 730360 ->
    getr regs 9 = Z_to_bv 64 730352 ->
    getr regs 18 = Z_to_bv 64 214340 ->
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
        getr regs' 1 = Z_to_bv 64 636844 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 831552 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 214340 ->
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
        G (mkst regs' (0x34544 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636328))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 636828))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 636652))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 730360))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 963248) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 963252) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 963249) ([Z_to_bv 8 0])) (Z_to_bv 64 831536) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 759232) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x34440 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636320))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 963280))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 636328))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 636828))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 962664) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962680) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 962672) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 963304) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 963312) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 831568) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 831544) (word_to_le_bytes 8 (Z_to_bv 64 831568))) (Z_to_bv 64 831352) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 963280) ([Z_to_bv 8 1])) (Z_to_bv 64 831392) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 831384) (word_to_le_bytes 4 tid)) (Z_to_bv 64 831504) (word_to_le_bytes 8 (Z_to_bv 64 963336))) (Z_to_bv 64 831472) (word_to_le_bytes 8 (Z_to_bv 64 831472))) (Z_to_bv 64 831360) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831368) (word_to_le_bytes 8 (Z_to_bv 64 831352))) (Z_to_bv 64 831376) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 963248) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 963252) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 963249) ([Z_to_bv 8 0])) (Z_to_bv 64 831536) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_343e8 D_343e8 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_343ec D_343ec (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 636652) ltac:(ok_win HJ).
      stw F_343f0 D_343f0 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 730360) ltac:(ok_win HJ).
      sv F_343f4 D_343f4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_343f8 D_343f8.
      sn F_343fc D_343fc.
      lb_step F_34400 D_34400 (Z_to_bv 8 0) ltac:(rd_img img_b9570_1).
      sn F_34404 D_34404.
      stepb_tk F_34408 D_34408 ltac:(pin; cond_compute).
      sn F_34414 D_34414.
      sn F_34418 D_34418.
      sn F_3441c D_3441c.
      stw F_34420 D_34420 (Z_to_bv 64 759232) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_34424 D_34424.
      ld_step F_34428 D_34428 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b80e8_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_3442c D_3442c ltac:(pin; cond_compute).
      ld_step F_3444c D_3444c (word_to_le_bytes 8 (Z_to_bv 64 636652)) (Z_to_bv 64 636652) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_34450 D_34450 (word_to_le_bytes 8 (Z_to_bv 64 730360)) (Z_to_bv 64 730360) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_34454 D_34454 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_34458 D_34458 (0x9b6ec : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_9b694 D_9b694.
      stepb_ft F_9b698 D_9b698 ltac:(pin; cond_compute).
      ld_step F_9b69c D_9b69c (word_to_le_bytes 8 (Z_to_bv 64 636828)) (Z_to_bv 64 636828) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b6a0 D_9b6a0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9b6a4 D_9b6a4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_9b6a8 D_9b6a8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_9b6ac D_9b6ac (0x9b79c : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_9b744 D_9b744 (argc_w av).
      sv F_9b748 D_9b748 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_9b74c D_9b74c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_9b750 D_9b750 (0x34544 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
