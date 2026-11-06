(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_13084_14000 RCode_15000_16000 RCode_1c000_1d000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import StartupBase StartupDefs.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := rl_segs.
Abbreviation RPH := RPH0.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
  Variable sp0 : word.
  Variable Jb : word -> option byte.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variables (hw : word) (drw : EntryDraw).   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw drw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof.
    destruct (rnd_facts SEGS RPH sp0 drw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j (RB drw))).
  Proof.
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 drw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). unfold RB. apply E. exact Hjn.
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD := rewrite rdn_cmem_data by region_side; apply rdn_guard.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
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
        getr regs' 4 = (rl dA_2f6b0 0x2f7b8) ->
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
        G (mkst regs' (rl dF_15170 0x15288) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15288))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8s 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw)))) (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw)))) (rl dA_2f848 0x2f849) ([Z_to_bv 8 0])) (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw)))) rom)) ->
    G (mkst regs (rl dF_15170 0x15280) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8s 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_15280 D_15280 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_15284 D_15284.  (* [comment removed for export] *)
      sv F_15958 D_15958 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_1595c D_1595c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (rl dF_15170 0x15288) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_15960 D_15960 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_15964 D_15964 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_15968 D_15968.  (* [comment removed for export] *)
      ld_step F_1596c D_1596c (word_to_le_bytes 8 (rl dA_2f848 0x2f848)) (rl dA_2f848 0x2f848) ltac:(rd_img img_1e3e0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_15970 D_15970.  (* [comment removed for export] *)
      sn F_15974 D_15974.  (* [comment removed for export] *)
      stepiv F_1c9b4 D_1c9b4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_1c9b8 D_1c9b8 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      sn F_1cac8 D_1cac8.  (* [comment removed for export] *)
      sn F_1cacc D_1cacc.  (* [comment removed for export] *)
      rl_andi3.   (* [comment removed for export] *)
      stepb_ft F_1cad0 D_1cad0 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      sn F_1cad4 D_1cad4.  (* [comment removed for export] *)
      stepb_tk F_1cad8 D_1cad8 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      sn F_1cb10 D_1cb10.  (* [comment removed for export] *)
      stepb_ft F_1cb14 D_1cb14 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      ld_step F_1cb18 D_1cb18 (rba drw) (rwa drw) ltac:(RD_RND 0%nat) ltac:(apply rwa_val).  (* [comment removed for export] *)
      ld_step F_1cb1c D_1cb1c (rbb drw) (rwb drw) ltac:(RD_RND 4%nat) ltac:(apply rwb_val).  (* [comment removed for export] *)
      stw F_1cb20 D_1cb20 (rl dA_2f848 0x2f848) (v_lw (rwa drw)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_1cb24 D_1cb24 (rl dA_2f848 0x2f84c) (v_lw (rwb drw)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_1cb28 D_1cb28.  (* [comment removed for export] *)
      sv F_1cb2c D_1cb2c (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_1cb30 D_1cb30.  (* [comment removed for export] *)
      stepb_tk F_1cb34 D_1cb34 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      sn F_1cd74 D_1cd74.  (* [comment removed for export] *)
      stepb_ft F_1cd78 D_1cd78 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      sn F_1cd7c D_1cd7c.  (* [comment removed for export] *)
      stepb_ft F_1cd80 D_1cd80 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      stepretK F_1cd84 D_1cd84 F_15978 ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_15978 D_15978.  (* [comment removed for export] *)
      sn F_15994 D_15994.  (* [comment removed for export] *)
      ld_step F_15998 D_15998 (word_to_le_bytes 8 (rl dA_2f848 0x2f848)) (rl dA_2f848 0x2f848) ltac:(rd_img img_1e3e0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_1599c D_1599c (rl dA_2f848 0x2f849) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_159a0 D_159a0 (guard_bytes drw) (canary_w drw) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_159a4 D_159a4.  (* [comment removed for export] *)
      stw F_159a8 D_159a8 (rl dA_2f6b0 0x2f7a8) (canary_w drw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_159ac D_159ac (word_to_le_bytes 8 (rl dF_15170 0x15288)) (rl dF_15170 0x15288) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_159b0 D_159b0 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepretK F_159b4 D_159b4 F_15288 ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
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
        getr regs' 4 = (rl dA_2f6b0 0x2f7b8) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (rl dF_131d0 0x131d0) ->
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
        G (mkst regs' (rl dF_15448 0x15448) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15288))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8s 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw)))) (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw)))) (rl dA_2f848 0x2f849) ([Z_to_bv 8 0])) (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw)))) rom)) ->
    G (mkst regs (rl dF_15170 0x15288) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15288))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8s 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw)))) (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw)))) (rl dA_2f848 0x2f849) ([Z_to_bv 8 0])) (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_15288 D_15288 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1528c D_1528c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_15290 D_15290 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_15294 D_15294 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_15298 D_15298 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_1529c D_1529c ltac:(pin; rl_cond).  (* [comment removed for export] *)
      ld_step F_152a0 D_152a0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_152a4 D_152a4 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      ld_step F_15384 D_15384 (word_to_le_bytes 8 (rl dF_153e8 0x1541c)) (rl dF_153e8 0x1541c) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15388 D_15388 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1538c D_1538c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15390 D_15390 (word_to_le_bytes 8 (rl dF_131d0 0x131d0)) (rl dF_131d0 0x131d0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_15394 D_15394 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepretK F_15398 D_15398 F_1541c ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_1541c D_1541c.  (* [comment removed for export] *)
      sn F_15420 D_15420.  (* [comment removed for export] *)
      sn F_15424 D_15424.  (* [comment removed for export] *)
      sv F_15428 D_15428 (argc_w av).  (* [comment removed for export] *)
      sv F_1542c D_1542c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_15430 D_15430 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15434 D_15434 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_15438 D_15438 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_1543c D_1543c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_15440 D_15440 (sp0).  (* [comment removed for export] *)
      stepretK F_15444 D_15444 F_15448 ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = rl dF_131d0 0x131d0 ->
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
        getr regs' 1 = (rl dF_1539c 0x153cc) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (rl dA_2f6b0 0x2f7b8) ->
        getr regs' 8 = (rl dA_1e348 0x1e350) ->
        getr regs' 9 = (rl dA_1e348 0x1e348) ->
        getr regs' 18 = (rl dF_131d0 0x131d0) ->
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
        G (mkst regs' (rl dF_130cc 0x130cc) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15288))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (rl dF_15448 0x1547c))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8s 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw)))) (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw)))) (rl dA_2f848 0x2f849) ([Z_to_bv 8 0])) (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw)))) rom)) ->
    G (mkst regs (rl dF_15448 0x15448) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15288))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8s 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw)))) (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw)))) (rl dA_2f848 0x2f849) ([Z_to_bv 8 0])) (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_15448 D_15448 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_1544c D_1544c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15450 D_15450 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15454 D_15454 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_15458 D_15458 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_1545c D_1545c (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_15460 D_15460 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_15464 D_15464 (argc_w av).  (* [comment removed for export] *)
      sn F_15468 D_15468.  (* [comment removed for export] *)
      stepiv F_1546c D_1546c (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_15470 D_15470 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_15474 D_15474 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_15478 D_15478.  (* [comment removed for export] *)
      sv F_1539c D_1539c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_153a0 D_153a0 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (rl dF_15448 0x1547c) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_153a4 D_153a4 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_153a8 D_153a8 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_153ac D_153ac.  (* [comment removed for export] *)
      stepretK F_1516c D_1516c F_153b0 ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_153b0 D_153b0.  (* [comment removed for export] *)
      sn F_153b4 D_153b4.  (* [comment removed for export] *)
      ld_step F_153b8 D_153b8 (word_to_le_bytes 8 (rl dA_1e348 0x1e350)) (rl dA_1e348 0x1e350) ltac:(rd_img img_1e3d0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_153bc D_153bc (word_to_le_bytes 8 (rl dA_1e348 0x1e348)) (rl dA_1e348 0x1e348) ltac:(rd_img img_1e3d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_153c0 D_153c0 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      ld_step F_153c4 D_153c4 (word_to_le_bytes 8 (rl dF_130cc 0x130cc)) (rl dF_130cc 0x130cc) ltac:(rd_img img_1e348_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjrK F_153c8 D_153c8 F_130cc ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = rl dF_1539c 0x153cc ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
    getr regs 8 = rl dA_1e348 0x1e350 ->
    getr regs 9 = rl dA_1e348 0x1e348 ->
    getr regs 18 = rl dF_131d0 0x131d0 ->
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
        getr regs' 1 = (rl dF_15448 0x1548c) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (rl dA_2f6b0 0x2f7b8) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (rl dF_131d0 0x131d0) ->
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
        G (mkst regs' (rl dF_131d0 0x131d0) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15288))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (rl dF_15448 0x1547c))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (rl dF_1539c 0x153cc))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (rl dA_1e348 0x1e350))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8s 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw)))) (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw)))) (rl dA_2f848 0x2f849) ([Z_to_bv 8 0])) (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw))) (rl dA_1f630 0x1f630) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (rl dF_130cc 0x130cc) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15280))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (rl dA_2f848 0x2f868))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15288))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (rl dF_15448 0x1547c))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (rl dA_2f6b8s 0x2f6d8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b8s 0x2f6e0) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f848 0x2f880) (word_to_le_bytes 8 (Z_to_bv 64 224))) (rl dA_2f848 0x2f888) (word_to_le_bytes 8 (Z_to_bv 64 8))) (rl dA_2f6b0 0x2f7c8) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f6b0 0x2f7b0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f7c8))) (rl dA_2f6b0 0x2f6f0) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f848 0x2f868) ([Z_to_bv 8 1])) (rl dA_2f6b0 0x2f718) (word_to_le_bytes 4 (Z_to_bv 64 2))) (rl dA_2f6b0 0x2f710) (word_to_le_bytes 4 tid)) (rl dA_2f6b0 0x2f788) (word_to_le_bytes 8 (rl dA_2f848 0x2f8a0))) (rl dA_2f6b0 0x2f768) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f768))) (rl dA_2f6b0 0x2f6f8) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f700) (word_to_le_bytes 8 (rl dA_2f6b0 0x2f6f0))) (rl dA_2f6b0 0x2f708) (word_to_le_bytes 8 (Z_to_bv 64 0))) (rl dA_2f848 0x2f848) (word_to_le_bytes 4 (v_lw (rwa drw)))) (rl dA_2f848 0x2f84c) (word_to_le_bytes 4 (v_lw (rwb drw)))) (rl dA_2f848 0x2f849) ([Z_to_bv 8 0])) (rl dA_2f6b0 0x2f7a8) (word_to_le_bytes 8 (canary_w drw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_130cc D_130cc (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_130d0 D_130d0 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (rl dF_1539c 0x153cc) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_130d4 D_130d4 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (rl dA_1e348 0x1e350) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_130d8 D_130d8 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_130dc D_130dc.  (* [comment removed for export] *)
      sn F_130e0 D_130e0.  (* [comment removed for export] *)
      lb_step F_130e4 D_130e4 (Z_to_bv 8 0) ltac:(rd_img img_1f630_1).  (* [comment removed for export] *)
      sn F_130e8 D_130e8.  (* [comment removed for export] *)
      stepb_tk F_130ec D_130ec ltac:(pin; rl_cond).  (* [comment removed for export] *)
      sn F_130f8 D_130f8.  (* [comment removed for export] *)
      sn F_130fc D_130fc.  (* [comment removed for export] *)
      sn F_13100 D_13100.  (* [comment removed for export] *)
      stw F_13104 D_13104 (rl dA_1f630 0x1f630) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_13108 D_13108.  (* [comment removed for export] *)
      ld_step F_1310c D_1310c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_1e388_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_13110 D_13110 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      ld_step F_13130 D_13130 (word_to_le_bytes 8 (rl dF_1539c 0x153cc)) (rl dF_1539c 0x153cc) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_13134 D_13134 (word_to_le_bytes 8 (rl dA_1e348 0x1e350)) (rl dA_1e348 0x1e350) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_13138 D_13138 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepretK F_1313c D_1313c F_153cc ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_153cc D_153cc.  (* [comment removed for export] *)
      stepb_ft F_153d0 D_153d0 ltac:(pin; rl_cond).  (* [comment removed for export] *)
      ld_step F_153d4 D_153d4 (word_to_le_bytes 8 (rl dF_15448 0x1547c)) (rl dF_15448 0x1547c) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_153d8 D_153d8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_153dc D_153dc (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_153e0 D_153e0 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepretK F_153e4 D_153e4 F_1547c ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_1547c D_1547c (argc_w av).  (* [comment removed for export] *)
      sv F_15480 D_15480 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_15484 D_15484 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      assert (RKmain : ret_ok (rl dF_131d0 0x131d0)) by rl_ret_ok.   (* [comment removed for export] *)
      stepjr F_15488 D_15488 (rl dF_131d0 0x131d0) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      imm_norm; rewrite (RKmain : v_jalr (rl dF_131d0 0x131d0) 0 = rl dF_131d0 0x131d0).
      apply mst_refl. }
    apply Hk; try (gres; pin; rl_norm_s; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
