(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import StartupTac ArgvEnv RefLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Img_u Bs0StartupDefs_u
  Bs0_code_r1ff24_20000_u Bs0_code_r4a000_4b000_u Bs0_code_r4b000_4c000_u Bs0_code_r58000_59000_u.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require PropExec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Ltac RD_RND j :=
    eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 827328 ->
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
        getr regs' 4 = Z_to_bv 64 827328 ->
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
        G (mkst regs' (0x9a5a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632224))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 959024) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 959028) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 959025) ([Z_to_bv 8 0])) (Z_to_bv 64 827312) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9a598 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_98f58 D_98f58 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_98f5c D_98f5c.  (* [comment removed for export] *)
      sv F_99914 D_99914 (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_99918 D_99918 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 632224) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_9991c D_9991c ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_99920 D_99920 (rnd_w sp0 av ev).  (* [comment removed for export] *)
      sn F_99924 D_99924.  (* [comment removed for export] *)
      ld_step F_99928 D_99928 (word_to_le_bytes 8 (Z_to_bv 64 959024)) (Z_to_bv 64 959024) ltac:(rd_img img_b5bb0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_9992c D_9992c.  (* [comment removed for export] *)
      sn F_99930 D_99930.  (* [comment removed for export] *)
      stepiv F_a9e4c D_a9e4c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_a9e50 D_a9e50 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a9f60 D_a9f60.  (* [comment removed for export] *)
      sn F_a9f64 D_a9f64.  (* [comment removed for export] *)
      stepb_ft F_a9f68 D_a9f68 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a9f6c D_a9f6c.  (* [comment removed for export] *)
      stepb_tk F_a9f70 D_a9f70 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a9fa8 D_a9fa8.  (* [comment removed for export] *)
      stepb_ft F_a9fac D_a9fac ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_a9fb0 D_a9fb0 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).  (* [comment removed for export] *)
      ld_step F_a9fb4 D_a9fb4 (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).  (* [comment removed for export] *)
      stw F_a9fb8 D_a9fb8 (Z_to_bv 64 959024) (rlw RND 0) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_a9fbc D_a9fbc (Z_to_bv 64 959028) (rlw RND 4) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_a9fc0 D_a9fc0.  (* [comment removed for export] *)
      sv F_a9fc4 D_a9fc4 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_a9fc8 D_a9fc8.  (* [comment removed for export] *)
      stepb_tk F_a9fcc D_a9fcc ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_aa20c D_aa20c.  (* [comment removed for export] *)
      stepb_ft F_aa210 D_aa210 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_aa214 D_aa214.  (* [comment removed for export] *)
      stepb_ft F_aa218 D_aa218 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_aa21c D_aa21c (0x9af68 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_99934 D_99934.  (* [comment removed for export] *)
      sn F_99950 D_99950.  (* [comment removed for export] *)
      ld_step F_99954 D_99954 (word_to_le_bytes 8 (Z_to_bv 64 959024)) (Z_to_bv 64 959024) ltac:(rd_img img_b5bb0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_99958 D_99958 (Z_to_bv 64 959025) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_9995c D_9995c (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_99960 D_99960.  (* [comment removed for export] *)
      stw F_99964 D_99964 (Z_to_bv 64 827312) (canary_w RND) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_99968 D_99968 (word_to_le_bytes 8 (Z_to_bv 64 632224)) (Z_to_bv 64 632224) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_9996c D_9996c (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_99970 D_99970 (0x9a5a0 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 827328 ->
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
        getr regs' 4 = Z_to_bv 64 827328 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 213628 ->
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
        G (mkst regs' (0x9a760 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632224))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 959024) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 959028) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 959025) ([Z_to_bv 8 0])) (Z_to_bv 64 827312) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9a5a0 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632224))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 959024) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 959028) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 959025) ([Z_to_bv 8 0])) (Z_to_bv 64 827312) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_98f60 D_98f60 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_98f64 D_98f64 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_98f68 D_98f68 ltac:(pin; first [apply c_eq_refl | cond_compute]).  (* [comment removed for export] *)
      ld_step F_98f6c D_98f6c (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_98f70 D_98f70 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_98f74 D_98f74 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_98f78 D_98f78 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_98f7c D_98f7c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_9905c D_9905c (word_to_le_bytes 8 (Z_to_bv 64 632628)) (Z_to_bv 64 632628) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99060 D_99060 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99064 D_99064 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99068 D_99068 (word_to_le_bytes 8 (Z_to_bv 64 213628)) (Z_to_bv 64 213628) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_9906c D_9906c (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_99070 D_99070 (0x9a734 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_990f4 D_990f4.  (* [comment removed for export] *)
      sn F_990f8 D_990f8.  (* [comment removed for export] *)
      sn F_990fc D_990fc.  (* [comment removed for export] *)
      sv F_99100 D_99100 (argc_w av).  (* [comment removed for export] *)
      sv F_99104 D_99104 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_99108 D_99108 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_9910c D_9910c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99110 D_99110 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99114 D_99114 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_99118 D_99118 sp0.  (* [comment removed for export] *)
      stepret F_9911c D_9911c (0x9a760 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 827328 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 213628 ->
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
        getr regs' 1 = Z_to_bv 64 632548 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 827328 ->
        getr regs' 8 = Z_to_bv 64 726256 ->
        getr regs' 9 = Z_to_bv 64 726248 ->
        getr regs' 18 = Z_to_bv 64 213628 ->
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
        G (mkst regs' (0x34178 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632224))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 632724))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 959024) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 959028) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 959025) ([Z_to_bv 8 0])) (Z_to_bv 64 827312) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9a760 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632224))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 959024) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 959028) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 959025) ([Z_to_bv 8 0])) (Z_to_bv 64 827312) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_99120 D_99120 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_99124 D_99124 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_99128 D_99128 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_9912c D_9912c (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_99130 D_99130 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_99134 D_99134 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_99138 D_99138 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_9913c D_9913c (argc_w av).  (* [comment removed for export] *)
      sn F_99140 D_99140.  (* [comment removed for export] *)
      stepiv F_99144 D_99144 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_99148 D_99148 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_9914c D_9914c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_99150 D_99150.  (* [comment removed for export] *)
      sv F_99074 D_99074 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_99078 D_99078 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 632724) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_9907c D_9907c (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_99080 D_99080 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_99084 D_99084.  (* [comment removed for export] *)
      stepret F_98e44 D_98e44 (0x9a6c8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_99088 D_99088.  (* [comment removed for export] *)
      sn F_9908c D_9908c.  (* [comment removed for export] *)
      ld_step F_99090 D_99090 (word_to_le_bytes 8 (Z_to_bv 64 726256)) (Z_to_bv 64 726256) ltac:(rd_img img_b5ba0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_99094 D_99094 (word_to_le_bytes 8 (Z_to_bv 64 726248)) (Z_to_bv 64 726248) ltac:(rd_img img_b5ba8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_99098 D_99098 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_9909c D_9909c (word_to_le_bytes 8 (Z_to_bv 64 213368)) (Z_to_bv 64 213368) ltac:(rd_img img_afeb0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_990a0 D_990a0 (0x34178 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 632548 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 827328 ->
    getr regs 8 = Z_to_bv 64 726256 ->
    getr regs 9 = Z_to_bv 64 726248 ->
    getr regs 18 = Z_to_bv 64 213628 ->
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
        getr regs' 1 = Z_to_bv 64 632740 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 827328 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 213628 ->
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
        G (mkst regs' (0x3427c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632224))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 632724))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 632548))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 726256))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 959024) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 959028) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 959025) ([Z_to_bv 8 0])) (Z_to_bv 64 827312) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 754944) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x34178 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632216))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 959056))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 632224))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 632724))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 958440) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958456) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 958448) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 959080) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 959088) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 827344) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 827320) (word_to_le_bytes 8 (Z_to_bv 64 827344))) (Z_to_bv 64 827128) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 959056) ([Z_to_bv 8 1])) (Z_to_bv 64 827168) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 827160) (word_to_le_bytes 4 tid)) (Z_to_bv 64 827280) (word_to_le_bytes 8 (Z_to_bv 64 959112))) (Z_to_bv 64 827248) (word_to_le_bytes 8 (Z_to_bv 64 827248))) (Z_to_bv 64 827136) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827144) (word_to_le_bytes 8 (Z_to_bv 64 827128))) (Z_to_bv 64 827152) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 959024) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 959028) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 959025) ([Z_to_bv 8 0])) (Z_to_bv 64 827312) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_33df8 D_33df8 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_33dfc D_33dfc (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 632548) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_33e00 D_33e00 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 726256) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_33e04 D_33e04 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_33e08 D_33e08.  (* [comment removed for export] *)
      sn F_33e0c D_33e0c.  (* [comment removed for export] *)
      lb_step F_33e10 D_33e10 (Z_to_bv 8 0) ltac:(rd_img img_b6ed0_1).  (* [comment removed for export] *)
      sn F_33e14 D_33e14.  (* [comment removed for export] *)
      stepb_tk F_33e18 D_33e18 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_33e24 D_33e24.  (* [comment removed for export] *)
      sn F_33e28 D_33e28.  (* [comment removed for export] *)
      sn F_33e2c D_33e2c.  (* [comment removed for export] *)
      stw F_33e30 D_33e30 (Z_to_bv 64 754944) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_33e34 D_33e34.  (* [comment removed for export] *)
      ld_step F_33e38 D_33e38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b5a40_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_33e3c D_33e3c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_33e5c D_33e5c (word_to_le_bytes 8 (Z_to_bv 64 632548)) (Z_to_bv 64 632548) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_33e60 D_33e60 (word_to_le_bytes 8 (Z_to_bv 64 726256)) (Z_to_bv 64 726256) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_33e64 D_33e64 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_33e68 D_33e68 (0x9a6e4 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_990a4 D_990a4.  (* [comment removed for export] *)
      stepb_ft F_990a8 D_990a8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_990ac D_990ac (word_to_le_bytes 8 (Z_to_bv 64 632724)) (Z_to_bv 64 632724) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_990b0 D_990b0 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_990b4 D_990b4 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_990b8 D_990b8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_990bc D_990bc (0x9a794 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_99154 D_99154 (argc_w av).  (* [comment removed for export] *)
      sv F_99158 D_99158 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_9915c D_9915c (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_99160 D_99160 (0x3427c : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
