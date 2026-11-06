(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StartupTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.StartupTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefImg RefStartupDefs Ref_code_224ec_22638 Ref_code_50584_51020 Ref_code_5e870_5e968 Ref_code_5f47c_5f488 Ref_code_memcpy.
Import ListNotations.
Open Scope bv_scope.
Local Instance clf_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P6.
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

  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  #[using="Hlo"] Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. LiaFast.lf_pins (fun (Hlo : LiaFast.U) => LiaFast.u0). exact Hlo. Qed.
  #[using="Hhi"] Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. LiaFast.lf_pins (fun (Hhi : LiaFast.U) => LiaFast.u0). exact Hhi. Qed.
  #[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. LiaFast.lf_pins (fun (sp0 Hva : LiaFast.U) => LiaFast.u0). destruct Hva as [[H1 H2] _]. lia. Qed.

  #[using="uid hw rdraw Hva Hve Hlo Hhi Hal"] Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
  Proof. LiaFast.lf_pins (fun (uid hw rdraw Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n
    = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros J D j n Hjn.
    destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
    unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
  Qed.

  #[using="Type"] Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. LiaFast.lf_pins LiaFast.u0. intros; subst; reflexivity. Qed.

  Ltac RD_RND j :=
    eapply rdn_addr; [apply (rd_rnd _ _ j); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  #[using="sp0 Hva"] Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof. LiaFast.lf_pins (fun (sp0 Hva : LiaFast.U) => LiaFast.u0).
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.


  (* [comment removed for export] *)
  Ltac rd_J9 R :=
    lazymatch goal with |- rdn _ _ ?a _ = _ =>
      lazymatch type of R with rdn _ _ ?a' _ = _ =>
        first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end end;
    exact R.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 482256 ->
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
        getr regs' 4 = (Z_to_bv 64 482256) ->
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
        G (mkst regs' (0x506a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329376))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom)) ->
    G (mkst regs (0x50698 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_50698 D_50698 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_5069c D_5069c.  (* [comment removed for export] *)
      sv F_50f80 D_50f80 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_50f84 D_50f84 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 329376) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_50f88 D_50f88 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_50f8c D_50f8c ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_50f90 D_50f90.  (* [comment removed for export] *)
      ld_step F_50f94 D_50f94 (word_to_le_bytes 8 (Z_to_bv 64 613952)) (Z_to_bv 64 613952) ltac:(rd_img img_63da0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_50f98 D_50f98.  (* [comment removed for export] *)
      sn F_50f9c D_50f9c.  (* [comment removed for export] *)
      stepiv F_5e2f0 D_5e2f0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_5e2f4 D_5e2f4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_5e404 D_5e404.  (* [comment removed for export] *)
      sn F_5e408 D_5e408.  (* [comment removed for export] *)
      stepb_ft F_5e40c D_5e40c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_5e410 D_5e410.  (* [comment removed for export] *)
      stepb_tk F_5e414 D_5e414 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_5e44c D_5e44c.  (* [comment removed for export] *)
      stepb_ft F_5e450 D_5e450 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_5e454 D_5e454 (firstn 4 (skipn 0 (at_random_bytes (ed_random rdraw)))) (rnd_lo rdraw) ltac:(RD_RND 0%nat) ltac:(apply rnd_lo_val).  (* [comment removed for export] *)
      ld_step F_5e458 D_5e458 (firstn 4 (skipn 4 (at_random_bytes (ed_random rdraw)))) (rnd_hi rdraw) ltac:(RD_RND 4%nat) ltac:(apply rnd_hi_val).  (* [comment removed for export] *)
      stw F_5e45c D_5e45c (Z_to_bv 64 613952) (v_lw (rnd_lo rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_5e460 D_5e460 (Z_to_bv 64 613956) (v_lw (rnd_hi rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_5e464 D_5e464.  (* [comment removed for export] *)
      sv F_5e468 D_5e468 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_5e46c D_5e46c.  (* [comment removed for export] *)
      stepb_tk F_5e470 D_5e470 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_5e6b0 D_5e6b0.  (* [comment removed for export] *)
      stepb_ft F_5e6b4 D_5e6b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_5e6b8 D_5e6b8.  (* [comment removed for export] *)
      stepb_ft F_5e6bc D_5e6bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_5e6c0 D_5e6c0 (0x50fa0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_50fa0 D_50fa0.  (* [comment removed for export] *)
      sn F_50fbc D_50fbc.  (* [comment removed for export] *)
      ld_step F_50fc0 D_50fc0 (word_to_le_bytes 8 (Z_to_bv 64 613952)) (Z_to_bv 64 613952) ltac:(rd_img img_63da0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_50fc4 D_50fc4 (Z_to_bv 64 613953) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_50fc8 D_50fc8 (canary_bytes rdraw) (canary rdraw) ltac:(rewrite rdn_cmem_data by region_side; apply rd_guard) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_50fcc D_50fcc.  (* [comment removed for export] *)
      stw F_50fd0 D_50fd0 (Z_to_bv 64 482240) (canary rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_50fd4 D_50fd4 (word_to_le_bytes 8 (Z_to_bv 64 329376)) (Z_to_bv 64 329376) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_50fd8 D_50fd8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_50fdc D_50fdc (0x506a0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 482256 ->
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
        getr regs' 4 = (Z_to_bv 64 482256) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 140856) ->
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
        G (mkst regs' (0x50860 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329376))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom)) ->
    G (mkst regs (0x506a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329376))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, D_ssp, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_506a0 D_506a0 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_506a4 D_506a4 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_506a8 D_506a8 ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_506ac D_506ac (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_506b0 D_506b0 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_506b4 D_506b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_506b8 D_506b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_506bc D_506bc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_5079c D_5079c (word_to_le_bytes 8 (Z_to_bv 64 329780)) (Z_to_bv 64 329780) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_507a0 D_507a0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_507a4 D_507a4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_507a8 D_507a8 (word_to_le_bytes 8 (Z_to_bv 64 140856)) (Z_to_bv 64 140856) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_507ac D_507ac (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_507b0 D_507b0 (0x50834 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_50834 D_50834.  (* [comment removed for export] *)
      sn F_50838 D_50838.  (* [comment removed for export] *)
      sn F_5083c D_5083c.  (* [comment removed for export] *)
      sv F_50840 D_50840 (argc_w av).  (* [comment removed for export] *)
      sv F_50844 D_50844 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_50848 D_50848 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_5084c D_5084c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_50850 D_50850 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_50854 D_50854 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_50858 D_50858 (sp0).  (* [comment removed for export] *)
      stepret F_5085c D_5085c (0x50860 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 482256 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 140856 ->
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
        getr regs' 1 = (Z_to_bv 64 329700) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 482256) ->
        getr regs' 8 = (Z_to_bv 64 396056) ->
        getr regs' 9 = (Z_to_bv 64 396048) ->
        getr regs' 18 = (Z_to_bv 64 140856) ->
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
        G (mkst regs' (0x22534 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329376))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 329876))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom)) ->
    G (mkst regs (0x50860 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329368))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 613984))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 329376))) (D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0))))) rom).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, D_ssp, aux_base, argv_w in *.
    eapply HG.
    { sv F_50860 D_50860 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_50864 D_50864 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_50868 D_50868 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_5086c D_5086c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_50870 D_50870 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_50874 D_50874 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_50878 D_50878 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_5087c D_5087c (argc_w av).  (* [comment removed for export] *)
      sn F_50880 D_50880.  (* [comment removed for export] *)
      stepiv F_50884 D_50884 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_50888 D_50888 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_5088c D_5088c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_50890 D_50890.  (* [comment removed for export] *)
      sv F_507b4 D_507b4 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_507b8 D_507b8 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 329876) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_507bc D_507bc (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_507c0 D_507c0 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_507c4 D_507c4.  (* [comment removed for export] *)
      stepret F_50584 D_50584 (0x507c8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_507c8 D_507c8.  (* [comment removed for export] *)
      sn F_507cc D_507cc.  (* [comment removed for export] *)
      ld_step F_507d0 D_507d0 (word_to_le_bytes 8 (Z_to_bv 64 396056)) (Z_to_bv 64 396056) ltac:(rd_img img_63d90_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_507d4 D_507d4 (word_to_le_bytes 8 (Z_to_bv 64 396048)) (Z_to_bv 64 396048) ltac:(rd_img img_63d98_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_507d8 D_507d8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_507dc D_507dc (word_to_le_bytes 8 (Z_to_bv 64 140596)) (Z_to_bv 64 140596) ltac:(rd_img img_60b10_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_507e0 D_507e0 (0x22534 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word) (J9 : word -> option byte),
    wfJ sp0 J9 ->
    rdn SEGS J9 (Z_to_bv 64 (bv_unsigned sp0 - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 329876)) ->
    rdn SEGS J9 (Z_to_bv 64 (bv_unsigned sp0 - 64)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) ->
    rdn SEGS J9 (Z_to_bv 64 (bv_unsigned sp0 - 72)) 8 = Some (word_to_le_bytes 8 (argc_w av)) ->
    getr regs 1 = Z_to_bv 64 329700 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 482256 ->
    getr regs 8 = Z_to_bv 64 396056 ->
    getr regs 9 = Z_to_bv 64 396048 ->
    getr regs 18 = Z_to_bv 64 140856 ->
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
        getr regs' 1 = (Z_to_bv 64 329892) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 482256) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 140856) ->
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
        G (mkst regs' (0x22638 : word) (CM (wbytes (wbytes J9 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 329700))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 396056))) (wbytes ((D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0))))) (Z_to_bv 64 413712) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x22534 : word) (CM J9 ((D_ssp rdraw (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 613368) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 613376) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 614008) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 614016) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 482272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 482248) (word_to_le_bytes 8 (Z_to_bv 64 482272))) (Z_to_bv 64 482056) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 613984) ([Z_to_bv 8 1])) (Z_to_bv 64 482096) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 482088) (word_to_le_bytes 4 tid)) (Z_to_bv 64 482208) (word_to_le_bytes 8 (Z_to_bv 64 614040))) (Z_to_bv 64 482176) (word_to_le_bytes 8 (Z_to_bv 64 482176))) (Z_to_bv 64 482064) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482072) (word_to_le_bytes 8 (Z_to_bv 64 482056))) (Z_to_bv 64 482080) (word_to_le_bytes 8 (Z_to_bv 64 0)))))) rom).
  Proof. LiaFast.lf_pins (fun (Hva Hve Hlo Hhi Hal : LiaFast.U) => LiaFast.u0).
    intros G HG regs rom s1v tid J9 HJ R56 R64 R72 H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, D_ssp, aux_base, argv_w in *.
    eapply HG.
    { sv F_22534 D_22534 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_22538 D_22538 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 329700) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_2253c D_2253c (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 396056) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_22540 D_22540 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_22544 D_22544.  (* [comment removed for export] *)
      sn F_22548 D_22548.  (* [comment removed for export] *)
      lb_step F_2254c D_2254c (Z_to_bv 8 0) ltac:(rd_img img_65010_1).  (* [comment removed for export] *)
      sn F_22550 D_22550.  (* [comment removed for export] *)
      stepb_tk F_22554 D_22554 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_22560 D_22560.  (* [comment removed for export] *)
      sn F_22564 D_22564.  (* [comment removed for export] *)
      sn F_22568 D_22568.  (* [comment removed for export] *)
      stw F_2256c D_2256c (Z_to_bv 64 413712) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_22570 D_22570.  (* [comment removed for export] *)
      ld_step F_22574 D_22574 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_63c88_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_22578 D_22578 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_22598 D_22598 (word_to_le_bytes 8 (Z_to_bv 64 329700)) (Z_to_bv 64 329700) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_2259c D_2259c (word_to_le_bytes 8 (Z_to_bv 64 396056)) (Z_to_bv 64 396056) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_225a0 D_225a0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_225a4 D_225a4 (0x507e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_507e4 D_507e4.  (* [comment removed for export] *)
      stepb_ft F_507e8 D_507e8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_507ec D_507ec (word_to_le_bytes 8 (Z_to_bv 64 329876)) (Z_to_bv 64 329876) ltac:(rewrite rdn_cmem_win by region_side; peel; rd_J9 R56) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_507f0 D_507f0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; peel; rd_J9 R64) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_507f4 D_507f4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; peel; rd_J9 R72) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_507f8 D_507f8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_507fc D_507fc (0x50894 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_50894 D_50894 (argc_w av).  (* [comment removed for export] *)
      sv F_50898 D_50898 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_5089c D_5089c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_508a0 D_508a0 (0x22638 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
