(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  StartupTac ArgvEnv RefLayout RefImg RefStartupDefs
 Ref_code_323a8_33000 Ref_code_95000_96000 Ref_code_96000_97000 Ref_code_a6000_a7000           .
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := ImgP.M.loaded_segments.
Abbreviation RPH := ImgP.M.phdrs.

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
    getr regs 4 = Z_to_bv 64 805144 ->
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
        getr regs' 4 = (Z_to_bv 64 805144) ->
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
        G (mkst regs' (0x95844 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612420))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936840) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 936844) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 936841) ([Z_to_bv 8 0])) (Z_to_bv 64 805128) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x9583c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_9583c D_9583c (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_95840 D_95840.  (* [comment removed for export] *)
      sv F_961ec D_961ec (Z_to_bv 64 (bv_unsigned sp0 - 432)).  (* [comment removed for export] *)
      stw F_961f0 D_961f0 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 612420) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stepb_ft F_961f4 D_961f4 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).  (* [comment removed for export] *)
      sv F_961f8 D_961f8 ((rnd_w sp0 av ev)).  (* [comment removed for export] *)
      sn F_961fc D_961fc.  (* [comment removed for export] *)
      ld_step F_96200 D_96200 (word_to_le_bytes 8 (Z_to_bv 64 936840)) (Z_to_bv 64 936840) ltac:(rd_img img_b19d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sn F_96204 D_96204.  (* [comment removed for export] *)
      sn F_96208 D_96208.  (* [comment removed for export] *)
      stepiv F_a6728 D_a6728 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).  (* [comment removed for export] *)
      stepb_tk F_a672c D_a672c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a683c D_a683c.  (* [comment removed for export] *)
      sn F_a6840 D_a6840.  (* [comment removed for export] *)
      stepb_ft F_a6844 D_a6844 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a6848 D_a6848.  (* [comment removed for export] *)
      stepb_tk F_a684c D_a684c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a6884 D_a6884.  (* [comment removed for export] *)
      stepb_ft F_a6888 D_a6888 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_a688c D_a688c (rnd_lo4 rdraw) (ssp_lo rdraw) ltac:(RD_RND 0%nat) ltac:(apply ssp_lo_val).  (* [comment removed for export] *)
      ld_step F_a6890 D_a6890 (rnd_hi4 rdraw) (ssp_hi rdraw) ltac:(RD_RND 4%nat) ltac:(apply ssp_hi_val).  (* [comment removed for export] *)
      stw F_a6894 D_a6894 (Z_to_bv 64 936840) (v_lw (ssp_lo rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      stw F_a6898 D_a6898 (Z_to_bv 64 936844) (v_lw (ssp_hi rdraw)) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_a689c D_a689c.  (* [comment removed for export] *)
      sv F_a68a0 D_a68a0 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).  (* [comment removed for export] *)
      sn F_a68a4 D_a68a4.  (* [comment removed for export] *)
      stepb_tk F_a68a8 D_a68a8 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a6ae8 D_a6ae8.  (* [comment removed for export] *)
      stepb_ft F_a6aec D_a6aec ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_a6af0 D_a6af0.  (* [comment removed for export] *)
      stepb_ft F_a6af4 D_a6af4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      stepret F_a6af8 D_a6af8 (0x9620c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_9620c D_9620c.  (* [comment removed for export] *)
      sn F_96228 D_96228.  (* [comment removed for export] *)
      ld_step F_9622c D_9622c (word_to_le_bytes 8 (Z_to_bv 64 936840)) (Z_to_bv 64 936840) ltac:(rd_img img_b19d8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stw F_96230 D_96230 (Z_to_bv 64 936841) (Z_to_bv 64 0) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_96234 D_96234 (guard_bytes rdraw) (canary_w rdraw) ltac:(RD_GUARD) ltac:(apply canary_val).  (* [comment removed for export] *)
      sn F_96238 D_96238.  (* [comment removed for export] *)
      stw F_9623c D_9623c (Z_to_bv 64 805128) (canary_w rdraw) ltac:(ok_data).  (* [comment removed for export] *)
      ld_step F_96240 D_96240 (word_to_le_bytes 8 (Z_to_bv 64 612420)) (Z_to_bv 64 612420) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_96244 D_96244 (Z_to_bv 64 (bv_unsigned sp0 - 416)).  (* [comment removed for export] *)
      stepret F_96248 D_96248 (0x95844 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 805144 ->
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
        getr regs' 4 = (Z_to_bv 64 805144) ->
        getr regs' 8 = (Z_to_bv 64 0) ->
        getr regs' 9 = (Z_to_bv 64 0) ->
        getr regs' 10 = (Z_to_bv 64 206196) ->
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
        G (mkst regs' (0x95a04 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612420))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936840) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 936844) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 936841) ([Z_to_bv 8 0])) (Z_to_bv 64 805128) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x95844 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612420))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936840) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 936844) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 936841) ([Z_to_bv 8 0])) (Z_to_bv 64 805128) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_95844 D_95844 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_95848 D_95848 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_9584c D_9584c ltac:(pin; apply c_eq_refl).  (* [comment removed for export] *)
      ld_step F_95850 D_95850 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      ld_step F_95854 D_95854 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).  (* [comment removed for export] *)
      stepb_ft F_95858 D_95858 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_9585c D_9585c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_95860 D_95860 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_95940 D_95940 (word_to_le_bytes 8 (Z_to_bv 64 612824)) (Z_to_bv 64 612824) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_95944 D_95944 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_95948 D_95948 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_9594c D_9594c (word_to_le_bytes 8 (Z_to_bv 64 206196)) (Z_to_bv 64 206196) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_95950 D_95950 (Z_to_bv 64 (bv_unsigned sp0 - 32)).  (* [comment removed for export] *)
      stepret F_95954 D_95954 (0x959d8 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_959d8 D_959d8.  (* [comment removed for export] *)
      sn F_959dc D_959dc.  (* [comment removed for export] *)
      sn F_959e0 D_959e0.  (* [comment removed for export] *)
      sv F_959e4 D_959e4 (argc_w av).  (* [comment removed for export] *)
      sv F_959e8 D_959e8 (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      ld_step F_959ec D_959ec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_959f0 D_959f0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_959f4 D_959f4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_959f8 D_959f8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_959fc D_959fc (sp0).  (* [comment removed for export] *)
      stepret F_95a00 D_95a00 (0x95a04 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 805144 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 206196 ->
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
        getr regs' 1 = (Z_to_bv 64 612744) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 80)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 805144) ->
        getr regs' 8 = (Z_to_bv 64 706304) ->
        getr regs' 9 = (Z_to_bv 64 706296) ->
        getr regs' 18 = (Z_to_bv 64 206196) ->
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
        G (mkst regs' (0x32470 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612420))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 612920))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936840) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 936844) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 936841) ([Z_to_bv 8 0])) (Z_to_bv 64 805128) (word_to_le_bytes 8 (canary_w rdraw)))) rom)) ->
    G (mkst regs (0x95a04 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612420))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936840) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 936844) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 936841) ([Z_to_bv 8 0])) (Z_to_bv 64 805128) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_95a04 D_95a04 (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stw F_95a08 D_95a08 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_95a0c D_95a0c (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_95a10 D_95a10 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_95a14 D_95a14 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_95a18 D_95a18 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_95a1c D_95a1c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_95a20 D_95a20 (argc_w av).  (* [comment removed for export] *)
      sn F_95a24 D_95a24.  (* [comment removed for export] *)
      stepiv F_95a28 D_95a28 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).  (* [comment removed for export] *)
      sv F_95a2c D_95a2c (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sv F_95a30 D_95a30 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      sn F_95a34 D_95a34.  (* [comment removed for export] *)
      sv F_95958 D_95958 (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stw F_9595c D_9595c (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 612920) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_95960 D_95960 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_95964 D_95964 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sn F_95968 D_95968.  (* [comment removed for export] *)
      stepret F_95728 D_95728 (0x9596c : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_9596c D_9596c.  (* [comment removed for export] *)
      sn F_95970 D_95970.  (* [comment removed for export] *)
      ld_step F_95974 D_95974 (word_to_le_bytes 8 (Z_to_bv 64 706304)) (Z_to_bv 64 706304) ltac:(rd_img img_b19c8_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_95978 D_95978 (word_to_le_bytes 8 (Z_to_bv 64 706296)) (Z_to_bv 64 706296) ltac:(rd_img img_b19d0_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_ft F_9597c D_9597c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_95980 D_95980 (word_to_le_bytes 8 (Z_to_bv 64 205936)) (Z_to_bv 64 205936) ltac:(rd_img img_ac530_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepjr F_95984 D_95984 (0x32470 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  #[using="Hva Hve Hlo Hhi Hal"] Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 612744 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 805144 ->
    getr regs 8 = Z_to_bv 64 706304 ->
    getr regs 9 = Z_to_bv 64 706296 ->
    getr regs 18 = Z_to_bv 64 206196 ->
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
        getr regs' 1 = (Z_to_bv 64 612936) ->
        getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 48)) ->
        getr regs' 3 = (Z_to_bv 64 67584) ->
        getr regs' 4 = (Z_to_bv 64 805144) ->
        getr regs' 8 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = (Z_to_bv 64 (bv_unsigned sp0 + 8)) ->
        getr regs' 12 = (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ->
        getr regs' 18 = (Z_to_bv 64 206196) ->
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
        G (mkst regs' (0x32574 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612420))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 612920))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 612744))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 706304))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936840) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 936844) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 936841) ([Z_to_bv 8 0])) (Z_to_bv 64 805128) (word_to_le_bytes 8 (canary_w rdraw))) (Z_to_bv 64 732832) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x32470 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612412))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 936872))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 612420))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 612920))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 936256) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936264) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 936896) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 936904) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 805160) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 805136) (word_to_le_bytes 8 (Z_to_bv 64 805160))) (Z_to_bv 64 804944) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 936872) ([Z_to_bv 8 1])) (Z_to_bv 64 804984) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 804976) (word_to_le_bytes 4 tid)) (Z_to_bv 64 805096) (word_to_le_bytes 8 (Z_to_bv 64 936928))) (Z_to_bv 64 805064) (word_to_le_bytes 8 (Z_to_bv 64 805064))) (Z_to_bv 64 804952) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804960) (word_to_le_bytes 8 (Z_to_bv 64 804944))) (Z_to_bv 64 804968) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 936840) (word_to_le_bytes 4 (v_lw (ssp_lo rdraw)))) (Z_to_bv 64 936844) (word_to_le_bytes 4 (v_lw (ssp_hi rdraw)))) (Z_to_bv 64 936841) ([Z_to_bv 8 0])) (Z_to_bv 64 805128) (word_to_le_bytes 8 (canary_w rdraw)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_32470 D_32470 (Z_to_bv 64 (bv_unsigned sp0 - 96)).  (* [comment removed for export] *)
      stw F_32474 D_32474 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 612744) ltac:(ok_win HJ).  (* [comment removed for export] *)
      stw F_32478 D_32478 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 706304) ltac:(ok_win HJ).  (* [comment removed for export] *)
      sv F_3247c D_3247c (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      sn F_32480 D_32480.  (* [comment removed for export] *)
      sn F_32484 D_32484.  (* [comment removed for export] *)
      lb_step F_32488 D_32488 (Z_to_bv 8 0) ltac:(rd_img img_b2cd0_1).  (* [comment removed for export] *)
      sn F_3248c D_3248c.  (* [comment removed for export] *)
      stepb_tk F_32490 D_32490 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      sn F_3249c D_3249c.  (* [comment removed for export] *)
      sn F_324a0 D_324a0.  (* [comment removed for export] *)
      sn F_324a4 D_324a4.  (* [comment removed for export] *)
      stw F_324a8 D_324a8 (Z_to_bv 64 732832) (Z_to_bv 64 1) ltac:(ok_data).  (* [comment removed for export] *)
      sn F_324ac D_324ac.  (* [comment removed for export] *)
      ld_step F_324b0 D_324b0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b1898_8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      stepb_tk F_324b4 D_324b4 ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_324d4 D_324d4 (word_to_le_bytes 8 (Z_to_bv 64 612744)) (Z_to_bv 64 612744) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_324d8 D_324d8 (word_to_le_bytes 8 (Z_to_bv 64 706304)) (Z_to_bv 64 706304) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_324dc D_324dc (Z_to_bv 64 (bv_unsigned sp0 - 80)).  (* [comment removed for export] *)
      stepret F_324e0 D_324e0 (0x95988 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sn F_95988 D_95988.  (* [comment removed for export] *)
      stepb_ft F_9598c D_9598c ltac:(pin; cond_compute).  (* [comment removed for export] *)
      ld_step F_95990 D_95990 (word_to_le_bytes 8 (Z_to_bv 64 612920)) (Z_to_bv 64 612920) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_95994 D_95994 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      ld_step F_95998 D_95998 (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).  (* [comment removed for export] *)
      sv F_9599c D_9599c (Z_to_bv 64 (bv_unsigned sp0 - 48)).  (* [comment removed for export] *)
      stepret F_959a0 D_959a0 (0x95a38 : word) ltac:(pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      sv F_95a38 D_95a38 (argc_w av).  (* [comment removed for export] *)
      sv F_95a3c D_95a3c (Z_to_bv 64 (bv_unsigned sp0 + 8)).  (* [comment removed for export] *)
      sv F_95a40 D_95a40 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).  (* [comment removed for export] *)
      stepjr F_95a44 D_95a44 (0x32574 : word) ltac:(gres; pin; first [reflexivity | bveq]).  (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.
End P6.
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
