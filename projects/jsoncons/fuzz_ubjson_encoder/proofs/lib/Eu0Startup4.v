(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the CONFIG_RSEQ flag; the BMode context; addresses and numbers; new lemmas; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Ub0Startup4.v, 180 lines within its lines 15-422. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  StartupTac ArgvEnv RefLayout Eu0Img Eu0StartupDefs
  Eu0_code_r20174_21000 Eu0_code_r4b000_4c000 Eu0_code_r58000_59000 Eu0_code_r59000_5a000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
Local Set Default Proof Using "All".
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.

Section P.
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variable rdraw : EntryDraw.
  Variable Jb : word -> option byte.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation RND := (ed_random rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_facts_here :
    (bv_unsigned sp0
     <= bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev))%Z
    /\ (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) + 16
        <= bv_unsigned sp0 + Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)))%Z
    /\ (bv_unsigned sp0 + Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) < 2^64)%Z
    /\ (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn SEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
            (Z_to_bv 64 (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev)
                         + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
  Proof.
    eapply rnd_facts;
      first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal].
  Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w inp sp0))%Z
    /\ (bv_unsigned (rnd_w inp sp0) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w inp sp0) mod 8 = 0)%Z.
  Proof.
    destruct rnd_facts_here as (A & B & C & D & _).
    unfold rnd_w. repeat split; lia.
  Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + Z.of_nat j)) n
    = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
  Proof.
    intros J D j n Hjn.
    destruct rnd_facts_here as (A & B & C & D' & E).
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

  Lemma slli_argc : v_slli (argc_w inp) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
  Proof.
    pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN inp Hva).
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
  Qed.

  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 838592 ->
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
        getr regs' 4 = Z_to_bv 64 838592 ->
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
        G (mkst regs' (0x9d124 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643364))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 970288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 970292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 970289) ([Z_to_bv 8 0])) (Z_to_bv 64 838576) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9d11c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_9d0c4 D_9d0c4 (word_to_le_bytes 8 (rnd_w inp sp0)) (rnd_w inp sp0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sn F_9d0c8 D_9d0c8.
      sv F_9da80 D_9da80 (Z_to_bv 64 (bv_unsigned sp0 - 432)).
      stw F_9da84 D_9da84 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 643364) ltac:(ok_win HJ).
      stepb_ft F_9da88 D_9da88 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
      sv F_9da8c D_9da8c (rnd_w inp sp0).
      sn F_9da90 D_9da90.
      ld_step F_9da94 D_9da94 (word_to_le_bytes 8 (Z_to_bv 64 970288)) (Z_to_bv 64 970288) ltac:(rd_img img_b9dd0_8) ltac:(apply bytes_le_to_Z_8).
      sn F_9da98 D_9da98.
      sn F_9da9c D_9da9c.
      stepiv F_adfbc D_adfbc (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
      stepb_tk F_adfc0 D_adfc0 ltac:(pin; cond_compute).
      sn F_ae0d0 D_ae0d0.
      sn F_ae0d4 D_ae0d4.
      stepb_ft F_ae0d8 D_ae0d8 ltac:(pin; cond_compute).
      sn F_ae0dc D_ae0dc.
      stepb_tk F_ae0e0 D_ae0e0 ltac:(pin; cond_compute).
      sn F_ae118 D_ae118.
      stepb_ft F_ae11c D_ae11c ltac:(pin; cond_compute).
      ld_step F_ae120 D_ae120 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
      ld_step F_ae124 D_ae124 (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
      stw F_ae128 D_ae128 (Z_to_bv 64 970288) (rlw RND 0) ltac:(ok_data).
      stw F_ae12c D_ae12c (Z_to_bv 64 970292) (rlw RND 4) ltac:(ok_data).
      sn F_ae130 D_ae130.
      sv F_ae134 D_ae134 (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + 8)).
      sn F_ae138 D_ae138.
      stepb_tk F_ae13c D_ae13c ltac:(pin; cond_compute).
      sn F_ae37c D_ae37c.
      stepb_ft F_ae380 D_ae380 ltac:(pin; cond_compute).
      sn F_ae384 D_ae384.
      stepb_ft F_ae388 D_ae388 ltac:(pin; cond_compute).
      stepret F_ae38c D_ae38c (0x9daec : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_9daa0 D_9daa0.
      sn F_9dabc D_9dabc.
      ld_step F_9dac0 D_9dac0 (word_to_le_bytes 8 (Z_to_bv 64 970288)) (Z_to_bv 64 970288) ltac:(rd_img img_b9dd0_8) ltac:(apply bytes_le_to_Z_8).
      stw F_9dac4 D_9dac4 (Z_to_bv 64 970289) (Z_to_bv 64 0) ltac:(ok_data).
      ld_step F_9dac8 D_9dac8 (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
      sn F_9dacc D_9dacc.
      stw F_9dad0 D_9dad0 (Z_to_bv 64 838576) (canary_w RND) ltac:(ok_data).
      ld_step F_9dad4 D_9dad4 (word_to_le_bytes 8 (Z_to_bv 64 643364)) (Z_to_bv 64 643364) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_9dad8 D_9dad8 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
      stepret F_9dadc D_9dadc (0x9d124 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 838592 ->
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
        getr regs' 4 = Z_to_bv 64 838592 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 215628 ->
        getr regs' 11 = (argc_w inp) ->
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
        G (mkst regs' (0x9d2e4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643364))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 970288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 970292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 970289) ([Z_to_bv 8 0])) (Z_to_bv 64 838576) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9d124 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643364))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 970288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 970292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 970289) ([Z_to_bv 8 0])) (Z_to_bv 64 838576) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { ld_step F_9d0cc D_9d0cc (word_to_le_bytes 8 uid) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d0d0 D_9d0d0 (word_to_le_bytes 8 uid) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9d0d4 D_9d0d4 ltac:(pin; first [apply c_eq_refl | cond_compute]).
      (* 08b1429: AT_GID / AT_EGID hold [in_gid inp] (StackLayout.auxv_entries), not 0 *)
      ld_step F_9d0d8 D_9d0d8 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d0dc D_9d0dc (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9d0e0 D_9d0e0 ltac:(pin; first [apply c_eq_refl | cond_compute]).
      ld_step F_9d0e4 D_9d0e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_9d0e8 D_9d0e8 ltac:(pin; cond_compute).
      ld_step F_9d1c8 D_9d1c8 (word_to_le_bytes 8 (Z_to_bv 64 643768)) (Z_to_bv 64 643768) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d1cc D_9d1cc (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d1d0 D_9d1d0 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d1d4 D_9d1d4 (word_to_le_bytes 8 (Z_to_bv 64 215628)) (Z_to_bv 64 215628) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_9d1d8 D_9d1d8 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
      stepret F_9d1dc D_9d1dc (0x9d2b8 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_9d260 D_9d260.
      sn F_9d264 D_9d264.
      sn F_9d268 D_9d268.
      sv F_9d26c D_9d26c (argc_w inp).
      sv F_9d270 D_9d270 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      ld_step F_9d274 D_9d274 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d278 D_9d278 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d27c D_9d27c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d280 D_9d280 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_9d284 D_9d284 sp0.
      stepret F_9d288 D_9d288 (0x9d2e4 : word) ltac:(pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 838592 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 215628 ->
    getr regs 11 = (argc_w inp) ->
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
        getr regs' 1 = Z_to_bv 64 643688 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 838592 ->
        getr regs' 8 = Z_to_bv 64 737400 ->
        getr regs' 9 = Z_to_bv 64 737392 ->
        getr regs' 18 = Z_to_bv 64 215628 ->
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
        G (mkst regs' (0x34948 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643364))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 643864))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 970288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 970292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 970289) ([Z_to_bv 8 0])) (Z_to_bv 64 838576) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0x9d2e4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643364))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 970288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 970292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 970289) ([Z_to_bv 8 0])) (Z_to_bv 64 838576) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_9d28c D_9d28c (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stw F_9d290 D_9d290 (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_9d294 D_9d294 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_9d298 D_9d298 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_9d29c D_9d29c (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      stw F_9d2a0 D_9d2a0 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
      sv F_9d2a4 D_9d2a4 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_9d2a8 D_9d2a8 (argc_w inp).
      sn F_9d2ac D_9d2ac.
      stepiv F_9d2b0 D_9d2b0 (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
      sv F_9d2b4 D_9d2b4 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
      sv F_9d2b8 D_9d2b8 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      sn F_9d2bc D_9d2bc.
      sv F_9d1e0 D_9d1e0 (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stw F_9d1e4 D_9d1e4 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 643864) ltac:(ok_win HJ).
      stw F_9d1e8 D_9d1e8 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
      stw F_9d1ec D_9d1ec (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
      sn F_9d1f0 D_9d1f0.
      stepret F_9cfb0 D_9cfb0 (0x9d24c : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_9d1f4 D_9d1f4.
      sn F_9d1f8 D_9d1f8.
      ld_step F_9d1fc D_9d1fc (word_to_le_bytes 8 (Z_to_bv 64 737400)) (Z_to_bv 64 737400) ltac:(rd_img img_b9dc0_8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d200 D_9d200 (word_to_le_bytes 8 (Z_to_bv 64 737392)) (Z_to_bv 64 737392) ltac:(rd_img img_b9dc8_8) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9d204 D_9d204 ltac:(pin; cond_compute).
      ld_step F_9d208 D_9d208 (word_to_le_bytes 8 (Z_to_bv 64 215368)) (Z_to_bv 64 215368) ltac:(rd_img img_b4020_8) ltac:(apply bytes_le_to_Z_8).
      stepjr F_9d20c D_9d20c (0x34948 : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 643688 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 838592 ->
    getr regs 8 = Z_to_bv 64 737400 ->
    getr regs 9 = Z_to_bv 64 737392 ->
    getr regs 18 = Z_to_bv 64 215628 ->
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
        getr regs' 1 = Z_to_bv 64 643880 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 838592 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w inp) ->
        getr regs' 10 = (argc_w inp) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 215628 ->
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
        G (mkst regs' (0x34a4c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643364))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 643864))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 643688))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 737400))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 970288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 970292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 970289) ([Z_to_bv 8 0])) (Z_to_bv 64 838576) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 766272) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x34948 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643356))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 970320))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 643364))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 643864))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 969704) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969720) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 969712) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 970344) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 970352) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 838608) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 838584) (word_to_le_bytes 8 (Z_to_bv 64 838608))) (Z_to_bv 64 838392) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 970320) ([Z_to_bv 8 1])) (Z_to_bv 64 838432) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 838424) (word_to_le_bytes 4 tid)) (Z_to_bv 64 838544) (word_to_le_bytes 8 (Z_to_bv 64 970376))) (Z_to_bv 64 838512) (word_to_le_bytes 8 (Z_to_bv 64 838512))) (Z_to_bv 64 838400) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838408) (word_to_le_bytes 8 (Z_to_bv 64 838392))) (Z_to_bv 64 838416) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 970288) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 970292) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 970289) ([Z_to_bv 8 0])) (Z_to_bv 64 838576) (word_to_le_bytes 8 (canary_w RND)))) rom).
  Proof.
    intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
    pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
    unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
    eapply HG.
    { sv F_348f0 D_348f0 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
      stw F_348f4 D_348f4 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 643688) ltac:(ok_win HJ).
      stw F_348f8 D_348f8 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 737400) ltac:(ok_win HJ).
      sv F_348fc D_348fc (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      sn F_34900 D_34900.
      sn F_34904 D_34904.
      lb_step F_34908 D_34908 (Z_to_bv 8 0) ltac:(rd_img img_bb0f0_1).
      sn F_3490c D_3490c.
      stepb_tk F_34910 D_34910 ltac:(pin; cond_compute).
      sn F_3491c D_3491c.
      sn F_34920 D_34920.
      sn F_34924 D_34924.
      stw F_34928 D_34928 (Z_to_bv 64 766272) (Z_to_bv 64 1) ltac:(ok_data).
      sn F_3492c D_3492c.
      ld_step F_34930 D_34930 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b9c60_8) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_34934 D_34934 ltac:(pin; cond_compute).
      ld_step F_34954 D_34954 (word_to_le_bytes 8 (Z_to_bv 64 643688)) (Z_to_bv 64 643688) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_34958 D_34958 (word_to_le_bytes 8 (Z_to_bv 64 737400)) (Z_to_bv 64 737400) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_3495c D_3495c (Z_to_bv 64 (bv_unsigned sp0 - 80)).
      stepret F_34960 D_34960 (0x9d268 : word) ltac:(pin; first [reflexivity | bveq]).
      sn F_9d210 D_9d210.
      stepb_ft F_9d214 D_9d214 ltac:(pin; cond_compute).
      ld_step F_9d218 D_9d218 (word_to_le_bytes 8 (Z_to_bv 64 643864)) (Z_to_bv 64 643864) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d21c D_9d21c (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_9d220 D_9d220 (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
      sv F_9d224 D_9d224 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
      stepret F_9d228 D_9d228 (0x9d318 : word) ltac:(pin; first [reflexivity | bveq]).
      sv F_9d2c0 D_9d2c0 (argc_w inp).
      sv F_9d2c4 D_9d2c4 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
      sv F_9d2c8 D_9d2c8 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
      stepjr F_9d2cc D_9d2cc (0x34a4c : word) ltac:(gres; pin; first [reflexivity | bveq]).
      apply mst_refl. }
    apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
    ra_chain.
  Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
