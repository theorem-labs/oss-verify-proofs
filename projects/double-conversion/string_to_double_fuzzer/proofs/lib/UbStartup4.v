(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  StartupTac ArgvEnv RefLayout UbImg UbStartupDefs
 Ub_code_32468_33000 Ub_code_95000_96000 Ub_code_96000_97000 Ub_code_a6000_a7000 Ub_code_a7000_a8000              .
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := ImgU.M.loaded_segments.
Abbreviation RPH := ImgU.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPW_1. Context {fx : PropExec.FPState}.


Section P6.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  #[using="Hlo"] Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  #[using="Hhi"] Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  #[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  #[using="uid hw rdraw Hva Hve Hlo Hhi Hal"] Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j (rnd_bytes rdraw))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w, rnd_bytes. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  #[using="Type"] Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side; apply (rd_guard_raw rdraw).

  #[using="sp0 Hva"] Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 806936 ->
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
        getr regs' 4 = (Z_to_bv 64 806936) ->
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
        G (mkst regs' (0x95f3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614196))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 938664))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614204))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 938048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 938688) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 938696) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 806952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 806928) (word_to_le_bytes 8 (Z_to_bv 64 806952))) (Z_to_bv 64 806736) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 938664) ([Z_to_bv 8 1])) (Z_to_bv 64 806776) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 806768) (word_to_le_bytes 4 tid)) (Z_to_bv 64 806888) (word_to_le_bytes 8 (Z_to_bv 64 938720))) (Z_to_bv 64 806856) (word_to_le_bytes 8 (Z_to_bv 64 806856))) (Z_to_bv 64 806744) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806752) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938632) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 938636) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 938633) ([Z_to_bv 8 0])) (Z_to_bv 64 806920) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x95f34 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614196))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 938664))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 938048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 938688) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 938696) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 806952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 806928) (word_to_le_bytes 8 (Z_to_bv 64 806952))) (Z_to_bv 64 806736) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 938664) ([Z_to_bv 8 1])) (Z_to_bv 64 806776) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 806768) (word_to_le_bytes 4 tid)) (Z_to_bv 64 806888) (word_to_le_bytes 8 (Z_to_bv 64 938720))) (Z_to_bv 64 806856) (word_to_le_bytes 8 (Z_to_bv 64 806856))) (Z_to_bv 64 806744) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806752) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806760) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_95f34 D_95f34 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_95f38 D_95f38.  (* [comment removed for export] *)
      sv F_968e4 D_968e4 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_968e8 D_968e8 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 614204) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_968ec D_968ec ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_968f0 D_968f0 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_968f4 D_968f4.  (* [comment removed for export] *)
      ld_step F_968f8 D_968f8 (word_to_le_bytes 8 (Z_to_bv 64 938632)) (Z_to_bv 64 938632) ltac:(rd_img img_b20d0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_968fc D_968fc.  (* [comment removed for export] *)
      sn F_96900 D_96900.  (* [comment removed for export] *)
      stepiv F_a6e20 D_a6e20 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_a6e24 D_a6e24 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a6f34 D_a6f34.  (* [comment removed for export] *)
      sn F_a6f38 D_a6f38.  (* [comment removed for export] *)
      stepb_ft F_a6f3c D_a6f3c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a6f40 D_a6f40.  (* [comment removed for export] *)
      stepb_tk F_a6f44 D_a6f44 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a6f7c D_a6f7c.  (* [comment removed for export] *)
      stepb_ft F_a6f80 D_a6f80 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_a6f84 D_a6f84 (rnd_lo4 rdraw) (ssp_lo rdraw) ltac:(RD_RND 0%nat) ltac:(apply ssp_lo_val).  (* [comment removed for export] *)
      ld_step F_a6f88 D_a6f88 (rnd_hi4 rdraw) (ssp_hi rdraw) ltac:(RD_RND 4%nat) ltac:(apply ssp_hi_val).  (* [comment removed for export] *)
      stw F_a6f8c D_a6f8c (Z_to_bv 64 938632) (v_lw (ssp_lo rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_a6f90 D_a6f90 (Z_to_bv 64 938636) (v_lw (ssp_hi rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_a6f94 D_a6f94.  (* [comment removed for export] *)
      sv F_a6f98 D_a6f98 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_a6f9c D_a6f9c.  (* [comment removed for export] *)
      stepb_tk F_a6fa0 D_a6fa0 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a71e0 D_a71e0.  (* [comment removed for export] *)
      stepb_ft F_a71e4 D_a71e4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a71e8 D_a71e8.  (* [comment removed for export] *)
      stepb_ft F_a71ec D_a71ec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_a71f0 D_a71f0 (0x96904 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_96904 D_96904.  (* [comment removed for export] *)
      sn F_96920 D_96920.  (* [comment removed for export] *)
      ld_step F_96924 D_96924 (word_to_le_bytes 8 (Z_to_bv 64 938632)) (Z_to_bv 64 938632) ltac:(rd_img img_b20d0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_96928 D_96928 (Z_to_bv 64 938633) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_9692c D_9692c (guard_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_96930 D_96930.  (* [comment removed for export] *)
      stw F_96934 D_96934 (Z_to_bv 64 806920) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_96938 D_96938 (word_to_le_bytes 8 (Z_to_bv 64 614204)) (Z_to_bv 64 614204) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_9693c D_9693c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_96940 D_96940 (0x95f3c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 806936 ->
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
        getr regs' 4 = (Z_to_bv 64 806936) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 206388) ->
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
        G (mkst regs' (0x960fc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614196))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 938664))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614204))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 938048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 938688) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 938696) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 806952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 806928) (word_to_le_bytes 8 (Z_to_bv 64 806952))) (Z_to_bv 64 806736) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 938664) ([Z_to_bv 8 1])) (Z_to_bv 64 806776) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 806768) (word_to_le_bytes 4 tid)) (Z_to_bv 64 806888) (word_to_le_bytes 8 (Z_to_bv 64 938720))) (Z_to_bv 64 806856) (word_to_le_bytes 8 (Z_to_bv 64 806856))) (Z_to_bv 64 806744) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806752) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938632) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 938636) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 938633) ([Z_to_bv 8 0])) (Z_to_bv 64 806920) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x95f3c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614196))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 938664))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614204))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 938048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 938688) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 938696) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 806952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 806928) (word_to_le_bytes 8 (Z_to_bv 64 806952))) (Z_to_bv 64 806736) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 938664) ([Z_to_bv 8 1])) (Z_to_bv 64 806776) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 806768) (word_to_le_bytes 4 tid)) (Z_to_bv 64 806888) (word_to_le_bytes 8 (Z_to_bv 64 938720))) (Z_to_bv 64 806856) (word_to_le_bytes 8 (Z_to_bv 64 806856))) (Z_to_bv 64 806744) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806752) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938632) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 938636) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 938633) ([Z_to_bv 8 0])) (Z_to_bv 64 806920) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_95f3c D_95f3c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_95f40 D_95f40 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_95f44 D_95f44 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_95f48 D_95f48 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_95f4c D_95f4c (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_95f50 D_95f50 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_95f54 D_95f54 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_95f58 D_95f58 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_96038 D_96038 (word_to_le_bytes 8 (Z_to_bv 64 614608)) (Z_to_bv 64 614608) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_9603c D_9603c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_96040 D_96040 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_96044 D_96044 (word_to_le_bytes 8 (Z_to_bv 64 206388)) (Z_to_bv 64 206388) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_96048 D_96048 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_9604c D_9604c (0x960d0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_960d0 D_960d0.  (* [comment removed for export] *)
      sn F_960d4 D_960d4.  (* [comment removed for export] *)
      sn F_960d8 D_960d8.  (* [comment removed for export] *)
      sv F_960dc D_960dc (argc_w av).  (* [comment removed for export] *)
      sv F_960e0 D_960e0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_960e4 D_960e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_960e8 D_960e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_960ec D_960ec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_960f0 D_960f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_960f4 D_960f4 (sp0).  (* [comment removed for export] *)
      stepret F_960f8 D_960f8 (0x960fc : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 806936 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 206388 ->
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
        getr regs' 1 = (Z_to_bv 64 614528) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 806936) ->
        getr regs' 8 = (Z_to_bv 64 708088) ->
        getr regs' 9 = (Z_to_bv 64 708080) ->
        getr regs' 18 = (Z_to_bv 64 206388) ->
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
        G (mkst regs' (0x32530 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614196))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 938664))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614204))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 614704))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 938048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 938688) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 938696) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 806952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 806928) (word_to_le_bytes 8 (Z_to_bv 64 806952))) (Z_to_bv 64 806736) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 938664) ([Z_to_bv 8 1])) (Z_to_bv 64 806776) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 806768) (word_to_le_bytes 4 tid)) (Z_to_bv 64 806888) (word_to_le_bytes 8 (Z_to_bv 64 938720))) (Z_to_bv 64 806856) (word_to_le_bytes 8 (Z_to_bv 64 806856))) (Z_to_bv 64 806744) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806752) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938632) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 938636) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 938633) ([Z_to_bv 8 0])) (Z_to_bv 64 806920) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x960fc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614196))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 938664))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614204))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 938048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 938688) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 938696) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 806952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 806928) (word_to_le_bytes 8 (Z_to_bv 64 806952))) (Z_to_bv 64 806736) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 938664) ([Z_to_bv 8 1])) (Z_to_bv 64 806776) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 806768) (word_to_le_bytes 4 tid)) (Z_to_bv 64 806888) (word_to_le_bytes 8 (Z_to_bv 64 938720))) (Z_to_bv 64 806856) (word_to_le_bytes 8 (Z_to_bv 64 806856))) (Z_to_bv 64 806744) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806752) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938632) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 938636) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 938633) ([Z_to_bv 8 0])) (Z_to_bv 64 806920) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_960fc D_960fc (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_96100 D_96100 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_96104 D_96104 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_96108 D_96108 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_9610c D_9610c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_96110 D_96110 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_96114 D_96114 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_96118 D_96118 (argc_w av).  (* [comment removed for export] *)
      sn F_9611c D_9611c.  (* [comment removed for export] *)
      stepiv F_96120 D_96120 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_96124 D_96124 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_96128 D_96128 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_9612c D_9612c.  (* [comment removed for export] *)
      sv F_96050 D_96050 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_96054 D_96054 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 614704) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_96058 D_96058 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_9605c D_9605c (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_96060 D_96060.  (* [comment removed for export] *)
      stepret F_95e20 D_95e20 (0x96064 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_96064 D_96064.  (* [comment removed for export] *)
      sn F_96068 D_96068.  (* [comment removed for export] *)
      ld_step F_9606c D_9606c (word_to_le_bytes 8 (Z_to_bv 64 708088)) (Z_to_bv 64 708088) ltac:(rd_img img_b20c0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_96070 D_96070 (word_to_le_bytes 8 (Z_to_bv 64 708080)) (Z_to_bv 64 708080) ltac:(rd_img img_b20c8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_96074 D_96074 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_96078 D_96078 (word_to_le_bytes 8 (Z_to_bv 64 206128)) (Z_to_bv 64 206128) ltac:(rd_img img_acc28_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_9607c D_9607c (0x32530 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 614528 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 806936 ->
    getr regs 8 = Z_to_bv 64 708088 ->
    getr regs 9 = Z_to_bv 64 708080 ->
    getr regs 18 = Z_to_bv 64 206388 ->
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
        getr regs' 1 = (Z_to_bv 64 614720) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 806936) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 206388) ->
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
        G (mkst regs' (0x32634 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614196))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 938664))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614204))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 614704))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 614528))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 708088))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 938048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 938688) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 938696) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 806952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 806928) (word_to_le_bytes 8 (Z_to_bv 64 806952))) (Z_to_bv 64 806736) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 938664) ([Z_to_bv 8 1])) (Z_to_bv 64 806776) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 806768) (word_to_le_bytes 4 tid)) (Z_to_bv 64 806888) (word_to_le_bytes 8 (Z_to_bv 64 938720))) (Z_to_bv 64 806856) (word_to_le_bytes 8 (Z_to_bv 64 806856))) (Z_to_bv 64 806744) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806752) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938632) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 938636) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 938633) ([Z_to_bv 8 0])) (Z_to_bv 64 806920) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 734624) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x32530 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614196))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 938664))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 614204))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 614704))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 938048) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938064) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938056) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 938688) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 938696) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 806952) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 806928) (word_to_le_bytes 8 (Z_to_bv 64 806952))) (Z_to_bv 64 806736) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 938664) ([Z_to_bv 8 1])) (Z_to_bv 64 806776) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 806768) (word_to_le_bytes 4 tid)) (Z_to_bv 64 806888) (word_to_le_bytes 8 (Z_to_bv 64 938720))) (Z_to_bv 64 806856) (word_to_le_bytes 8 (Z_to_bv 64 806856))) (Z_to_bv 64 806744) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806752) (word_to_le_bytes 8 (Z_to_bv 64 806736))) (Z_to_bv 64 806760) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 938632) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 938636) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 938633) ([Z_to_bv 8 0])) (Z_to_bv 64 806920) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_32530 D_32530 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_32534 D_32534 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 614528) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_32538 D_32538 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 708088) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_3253c D_3253c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_32540 D_32540.  (* [comment removed for export] *)
      sn F_32544 D_32544.  (* [comment removed for export] *)
      lb_step F_32548 D_32548 (Z_to_bv 8 0) ltac:(rd_img img_b33c0_1).  (* [comment removed for export] *)
      sn F_3254c D_3254c.  (* [comment removed for export] *)
      stepb_tk F_32550 D_32550 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3255c D_3255c.  (* [comment removed for export] *)
      sn F_32560 D_32560.  (* [comment removed for export] *)
      sn F_32564 D_32564.  (* [comment removed for export] *)
      stw F_32568 D_32568 (Z_to_bv 64 734624) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_3256c D_3256c.  (* [comment removed for export] *)
      ld_step F_32570 D_32570 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b1f90_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_32574 D_32574 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_32594 D_32594 (word_to_le_bytes 8 (Z_to_bv 64 614528)) (Z_to_bv 64 614528) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_32598 D_32598 (word_to_le_bytes 8 (Z_to_bv 64 708088)) (Z_to_bv 64 708088) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_3259c D_3259c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_325a0 D_325a0 (0x96080 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_96080 D_96080.  (* [comment removed for export] *)
      stepb_ft F_96084 D_96084 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_96088 D_96088 (word_to_le_bytes 8 (Z_to_bv 64 614704)) (Z_to_bv 64 614704) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_9608c D_9608c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_96090 D_96090 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_96094 D_96094 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_96098 D_96098 (0x96130 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_96130 D_96130 (argc_w av).  (* [comment removed for export] *)
      sv F_96134 D_96134 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_96138 D_96138 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_9613c D_9613c (0x32634 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
