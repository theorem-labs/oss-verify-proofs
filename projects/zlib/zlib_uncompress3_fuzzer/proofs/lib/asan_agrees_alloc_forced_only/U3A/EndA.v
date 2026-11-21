(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps Harness.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import U2AObj U2AIface U2AGlue EndA_pre.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma strm_sh_pres : forall (AI : AMallocIface) LB SP m m' Fu Zs,
  aheap_pres (aci AI) LB SP m m' -> In (mkABlock (ABFake 2) Fu 256) LB ->
  Zs = Fu + 32 -> Fu mod 256 = 0 -> ablk Fu (Fu + 256) ->
  shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0) ->
  shadow_bytes m' (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0).
Proof.
  intros AI LB SP m m' Fu Zs PRES HIN ZSE FU256 FUB SHZ.
  pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1. atop_facts.
  assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
  eapply (fake_sh_pres AI LB _ m m' 2 Fu 256 Zs 14); [exact PRES| exact HIN| exact Z8| lia| lia| lia| lia| exact SHZ].
Qed.

Theorem inflateEnd_proofA : forall (AI : AMallocIface) (withwin : bool), inflateEnd_stmtA AI withwin.
Proof.
  intros AI withwin. unfold inflateEnd_stmtA. intros until next.
  intros AH (HIN & ZSE & FU256 & FUB) (SHZ & RZ & WSF & RSF) HS HW STRM SSC MODE ST LOC LOS SP16 MI TP A0 TOPS INUW INUS RSTK RI APS.
  subst a0.
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as ART. unfold artcells in ART.
  destruct ART as (_ & GOT & _ & _ & SHB & _).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64) with (2^64) in RSP.
  atop_facts. pose proof (ablk_lin _ _ FUB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (SPT : bv_unsigned sp + 16 < KEND) by (unfold KEND; lia).
  assert (RSTK' : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
  assert (Z8 : Zs mod 8 = 0) by (subst Zs; Z.div_mod_to_equations; lia).
  assert (RSZ : rng RNG (Z.shiftr Zs 3 + 2147450880) 14).
  { eapply rng_sub'; [exact RSF|]. rewrite shad_div. unfold ASHOFF. subst Zs. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (AI_block AI _ _ _ _ _ ps S 7176 AH HS) as (_ & ABR & RS & RSS0 & BSH & _).
  destruct ABR as (SB & _ & _ & S16).
  pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
  assert (RSS : rng RNG (Z.shiftr S 3 + 2147450880) 897).
  { eapply rng_sub'; [exact RSS0|]. rewrite shadE. change (shlen (7176 + 7)) with 897. lia. }
  assert (SHS : shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)).
  { change 897 with (7176 / 8). apply ablock_sh0; [exact BSH| reflexivity| lia| lia| lia]. }
  unfold END_STACK in LOS.
  destruct withwin.
  -
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HW) as (WB1 & _ & WB3). cbn [ab_addr ab_size] in WB1, WB3. unfold AIMG_HI in WB1.
    assert (NEQ : ps <> pw).
    { intros E. subst pw. pose proof (hb_same_id _ _ _ _ _ _ (AI_hb_ids AI _ _ _ _ _ AH) HS HW) as X. inversion X. }
    cbn [free_all]. 
    eapply implMA_evtF.
    { eapply (end_preW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S Wd lo RNG); try eassumption; lia. }
    cbv beta. intros ms1 (m1 & x5 & x6 & x7 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & MU & WM & MI1 & ST1 & FR0 & STRM1).
    assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
    { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU WM). unfold end_W.
      constructor; [cbn [fst snd]; apply acr_stack; lia|].
      constructor; [cbn [fst snd]; eapply acr_fake; [exact HIN| lia| lia]| constructor]. }
    eapply implMA_bind.
    { eapply (implMA_afree_call AI L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc m1 s LB pw Wd 32768 lo []);
        rewrite ?unsigned_lit by lia; try reflexivity; try eassumption; try (unfold AFREE_STACK, AFREE_PC; lia).
      all: lazymatch goal with
           | |- aunw5 _ _ _ _ _ _ _ => apply aunw_data; rewrite ?unsigned_lit by lia; [lia| lia| exact INUW]
           | |- _ => first [ lia | Z.div_mod_to_equations; lia ]
           end. }
    cbv beta. intros [] s1' RNG1 ms' (REST1 & FPLE1 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MI2 & ST2 & PRES1 & AH2).
    rewrite ?unsigned_lit in * by lia.
    assert (HIN2 : In (mkABlock (ABFake 2) Fu 256) (lb_remove pw LB)) by (apply in_lb_remove; [exact HIN| discriminate]).
    assert (HS2 : In (HB ps S 7176) (lb_remove pw LB)) by (apply in_lb_remove; [exact HS| cbn; congruence]).
    assert (SHZ2 : shadow_bytes m2 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
    { eapply (strm_sh_pres AI _ _ m1 m2 Fu Zs PRES1 HIN2 ZSE FU256 FUB).
      eapply sh0_mu; [exact SHZ| exact MU|]. unfold end_W. cbn [disjoint_from].
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB. Z.div_mod_to_equations. lia. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) (end_FR ra s0 s1 s2 s3 s4 s5 s6)).
    { eapply aheap_pres_rw_cells; [exact PRES1| exact FR0|]. left. left. unfold end_FR. cbn [cells_size csize Nat.add]. lia. }
    assert (STRM2 : rw_cells asegs m2 Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                      (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3)).
    { eapply aheap_pres_rw_cells; [exact PRES1| exact STRM1|]. left. right. right. exists 2, Fu, 256. split; [exact HIN2|]. rewrite strm_cells_size. lia. }
    replace (ret_pc (Z_to_bv 64 0x93fa0)) with (Z_to_bv 64 0x93fa0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply implMA_evtF.
    { eapply (end_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S Wd lo RNG1); try eassumption;
        try lia; try (eapply rng_fp_le; [exact FPLE1| eassumption]). }
    cbv beta. intros ms2 (y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & ->).
    eapply implMA_bind.
    { eapply (implMA_afree_call AI L RNG1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc m2 s1' (lb_remove pw LB) ps S 7176 lo []);
        rewrite ?unsigned_lit by lia; try reflexivity; try eassumption; try (unfold AFREE_STACK, AFREE_PC; lia).
      all: lazymatch goal with
           | |- aunw5 _ _ _ _ _ _ _ => apply aunw_data; rewrite ?unsigned_lit by lia; [lia| lia| exact INUS]
           | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE1| exact RSTK]
           | |- aps_ok _ _ => exact (aps_ok_rest _ _ _ REST1 APS)
           | |- _ => first [ lia | Z.div_mod_to_equations; lia ]
           end. }
    cbv beta. intros [] s2' RNG2 ms' (REST2 & FPLE2 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & -> & MI3 & ST3 & PRES2 & AH3).
    rewrite ?unsigned_lit in * by lia.
    assert (HIN3 : In (mkABlock (ABFake 2) Fu 256) (lb_remove ps (lb_remove pw LB))) by (apply in_lb_remove; [exact HIN2| discriminate]).
    assert (SHZ3 : shadow_bytes m3 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
    { exact (strm_sh_pres AI _ _ m2 m3 Fu Zs PRES2 HIN3 ZSE FU256 FUB SHZ2). }
    assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -64) (end_FR ra s0 s1 s2 s3 s4 s5 s6)).
    { eapply aheap_pres_rw_cells; [exact PRES2| exact FR2|]. left. left. unfold end_FR. cbn [cells_size csize Nat.add]. lia. }
    assert (STRM3 : rw_cells asegs m3 Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                      (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3)).
    { eapply aheap_pres_rw_cells; [exact PRES2| exact STRM2|]. left. right. right. exists 2, Fu, 256. split; [exact HIN3|]. rewrite strm_cells_size. lia. }
    replace (ret_pc (Z_to_bv 64 0x93fd4)) with (Z_to_bv 64 0x93fd4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [free_all]. apply implMA_ret.
    assert (FPLE : fp_le RNG RNG2) by (eapply fp_le_trans; [exact FPLE1| exact FPLE2]).
    eapply evtF_mono.
    { eapply (end_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S Wd lo RNG2); try eassumption;
        try lia; try (eapply rng_fp_le; [exact FPLE| eassumption]). }
    cbv beta. intros ms4 (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & STRM4).
    split; [exact FPLE|].
    exists z5, z6, z7, z11, z12, z13, z14, z15, z16, z17, z28, z29, z30, z31, m4.
    split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [rewrite REST2; exact REST1|].
    split.
    { eapply client_agree_trans; [| eapply client_agree_trans; [| eapply client_agree_trans]].
      - eapply (client_agree_munch AI _ _ _ (end_W sp Zs) m m1 MU WM). intros a Ha HC HN.
        destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH3 HC) as [C|[C|[(b & Hb & C)|C]]]; unfold end_W; cbn [outside]; unfold AIMG_HI, KLS in *.
        + split; [lia|]. split; [| exact I]. lia.
        + split; [lia|]. split; [| exact I]. lia.
        + pose proof (AI_block_bounds AI _ _ _ _ _ b AH3 Hb) as (B1 & B2 & B3).
          split; [lia|]. split; [| exact I]. intros X. apply HN. exists (Zs, Zs + 112). split; [left; reflexivity| exact X].
        + split; [lia|]. split; [| exact I]. unfold ablk, AIMG_HI, KLS in FUB. lia.
      - eapply (client_agree_pres AI _ (lb_remove pw LB) _ (bv_unsigned sp + -64)); [exact PRES1| lia|]. intros b Hb. eapply lb_remove_sub; exact Hb.
      - eapply (client_agree_pres AI _ (lb_remove ps (lb_remove pw LB)) _ (bv_unsigned sp + -64)); [exact PRES2| lia| auto].
      - eapply (client_agree_munch AI _ _ _ (end_W sp Zs) m3 m4 MU4 WM4). intros a Ha HC HN.
        destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH3 HC) as [C|[C|[(b & Hb & C)|C]]]; unfold end_W; cbn [outside]; unfold AIMG_HI, KLS in *.
        + split; [lia|]. split; [| exact I]. lia.
        + split; [lia|]. split; [| exact I]. lia.
        + pose proof (AI_block_bounds AI _ _ _ _ _ b AH3 Hb) as (B1 & B2 & B3).
          split; [lia|]. split; [| exact I]. intros X. apply HN. exists (Zs, Zs + 112). split; [left; reflexivity| exact X].
        + split; [lia|]. split; [| exact I]. unfold ablk, AIMG_HI, KLS in FUB. lia. }
    split; [| exact STRM4].
    eapply (AI_frame AI _ _ _ _ m3 m4 _ AH3 MU4 WM4). unfold end_W.
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply acr_fake; [exact HIN3| lia| lia]| constructor].
  -
    cbn [free_all].
    eapply implMA_evtF.
    { eapply (end_preNW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S Wd lo RNG); try eassumption; lia. }
    cbv beta. intros ms1 (m1 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & MU & WM & MI1 & ST1 & FR0 & STRM1).
    assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
    { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU WM). unfold end_W.
      constructor; [cbn [fst snd]; apply acr_stack; lia|].
      constructor; [cbn [fst snd]; eapply acr_fake; [exact HIN| lia| lia]| constructor]. }
    eapply implMA_bind.
    { eapply (implMA_afree_call AI L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc m1 s LB ps S 7176 lo []);
        rewrite ?unsigned_lit by lia; try reflexivity; try eassumption; try (unfold AFREE_STACK, AFREE_PC; lia).
      all: lazymatch goal with
           | |- aunw5 _ _ _ _ _ _ _ => apply aunw_data; rewrite ?unsigned_lit by lia; [lia| lia| exact INUS]
           | |- _ => first [ lia | Z.div_mod_to_equations; lia ]
           end. }
    cbv beta. intros [] s1' RNG1 ms' (REST1 & FPLE1 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MI2 & ST2 & PRES1 & AH2).
    rewrite ?unsigned_lit in * by lia.
    assert (HIN2 : In (mkABlock (ABFake 2) Fu 256) (lb_remove ps LB)) by (apply in_lb_remove; [exact HIN| discriminate]).
    assert (SHZ2 : shadow_bytes m2 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
    { eapply (strm_sh_pres AI _ _ m1 m2 Fu Zs PRES1 HIN2 ZSE FU256 FUB).
      eapply sh0_mu; [exact SHZ| exact MU|]. unfold end_W. cbn [disjoint_from].
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB. Z.div_mod_to_equations. lia. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) (end_FR ra s0 s1 s2 s3 s4 s5 s6)).
    { eapply aheap_pres_rw_cells; [exact PRES1| exact FR0|]. left. left. unfold end_FR. cbn [cells_size csize Nat.add]. lia. }
    assert (STRM2 : rw_cells asegs m2 Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                      (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3)).
    { eapply aheap_pres_rw_cells; [exact PRES1| exact STRM1|]. left. right. right. exists 2, Fu, 256. split; [exact HIN2|]. rewrite strm_cells_size. lia. }
    replace (ret_pc (Z_to_bv 64 0x93fd4)) with (Z_to_bv 64 0x93fd4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply implMA_ret.
    eapply evtF_mono.
    { eapply (end_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S Wd lo RNG1); try eassumption;
        try lia; try (eapply rng_fp_le; [exact FPLE1| eassumption]). }
    cbv beta. intros ms4 (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m4 & -> & MU4 & WM4 & MI4 & ST4 & STRM4).
    split; [exact FPLE1|].
    exists z5, z6, z7, z11, z12, z13, z14, z15, z16, z17, z28, z29, z30, z31, m4.
    split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact REST1|].
    split.
    { eapply client_agree_trans; [| eapply client_agree_trans].
      - eapply (client_agree_munch AI _ _ _ (end_W sp Zs) m m1 MU WM). intros a Ha HC HN.
        destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH2 HC) as [C|[C|[(b & Hb & C)|C]]]; unfold end_W; cbn [outside]; unfold AIMG_HI, KLS in *.
        + split; [lia|]. split; [| exact I]. lia.
        + split; [lia|]. split; [| exact I]. lia.
        + pose proof (AI_block_bounds AI _ _ _ _ _ b AH2 Hb) as (B1 & B2 & B3).
          split; [lia|]. split; [| exact I]. intros X. apply HN. exists (Zs, Zs + 112). split; [left; reflexivity| exact X].
        + split; [lia|]. split; [| exact I]. unfold ablk, AIMG_HI, KLS in FUB. lia.
      - eapply (client_agree_pres AI _ (lb_remove ps LB) _ (bv_unsigned sp + -64)); [exact PRES1| lia| auto].
      - eapply (client_agree_munch AI _ _ _ (end_W sp Zs) m2 m4 MU4 WM4). intros a Ha HC HN.
        destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH2 HC) as [C|[C|[(b & Hb & C)|C]]]; unfold end_W; cbn [outside]; unfold AIMG_HI, KLS in *.
        + split; [lia|]. split; [| exact I]. lia.
        + split; [lia|]. split; [| exact I]. lia.
        + pose proof (AI_block_bounds AI _ _ _ _ _ b AH2 Hb) as (B1 & B2 & B3).
          split; [lia|]. split; [| exact I]. intros X. apply HN. exists (Zs, Zs + 112). split; [left; reflexivity| exact X].
        + split; [lia|]. split; [| exact I]. unfold ablk, AIMG_HI, KLS in FUB. lia. }
    split; [| exact STRM4].
    eapply (AI_frame AI _ _ _ _ m2 m4 _ AH2 MU4 WM4). unfold end_W.
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply acr_fake; [exact HIN2| lia| lia]| constructor].
Qed.

End CANSEC1.
