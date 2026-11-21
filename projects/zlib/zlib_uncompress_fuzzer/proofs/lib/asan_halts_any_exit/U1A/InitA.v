(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AIface U2AGlue InitA_pre InitA_fin.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Theorem inflateInit_proofA : forall (AI : AMallocIface), inflateInit_stmtA AI.
Proof.
  intros AI. unfold inflateInit_stmtA. intros until p3.
  intros AH (HIN & ZSE & FU256 & FUB) (SHZ & RZ & WSF & RSF) STRM UIMG SHV ST LOC LOS SP16 MI TP A0 A1 A2 RA4 TOPS UIN RSTK RI RISH APS.
  subst a0 a1 a2.
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
  unfold INIT_STACK in LOS.
  eapply implMA_evtF.
  { eapply (init_pre ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs lo RNG); try eassumption; unfold INIT_STACK; lia. }
  cbv beta. intros ms1 (m1 & q4 & q5 & q6 & q7 & j8 & -> & MU & WM & MI1 & ST1 & FR0 & STRM1).
  assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
  { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU WM). unfold init_W.
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply acr_fake; [exact HIN| lia| lia]| constructor]. }
  eapply implMA_post_evtF.
  { eapply (implMA_amalloc_call AI L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc m1 s LB 7176 lo []);
      rewrite ?unsigned_lit by lia; try reflexivity; try eassumption; try (unfold AMALLOC_STACK, AREQMAX, AMALLOC_PC; lia).
    (* s0 = strm + 80 is a fake-frame address below sp, so the depot chain stops at once (aunw_data) *)
    all: lazymatch goal with
         | |- aunw5 _ _ _ _ _ _ _ => apply aunw_data; rewrite ?unsigned_lit by lia; [lia| lia| exact UIN]
         | |- _ => first [ lia | Z.div_mod_to_equations; lia ]
         end. }
  cbv beta. intros r s' RNG' ms' (REST & FPLE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6'' & a7'' & t3' & t4' & t5' & t6' & m2 & -> & MI2 & ST2 & PRES & CASE).
  cbn [snd fst] in CASE. destruct r as [p|]; [| contradiction].
  destruct CASE as (S & junk & -> & ABR & AH2 & SBLK & RS & RSS & _).
  rewrite ?unsigned_lit in * by lia.
  destruct ABR as (SB & _ & _ & S16).
  pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
  pose proof (AI_rtcells AI _ _ _ _ _ AH2) as ART. unfold artcells in ART.
  destruct ART as (_ & GOT2 & RIC2 & REAL2 & SHB2 & _ & INI2 & LAY2 & _).
  assert (HIN2 : In (mkABlock (ABFake 2) Fu 256) (HB p S 7176 :: LB)) by (right; exact HIN).
  assert (SEP : S + 7176 <= Fu \/ Fu + 256 <= S).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p S 7176) (mkABlock (ABFake 2) Fu 256) AH2 ltac:(left; reflexivity) HIN2 ltac:(discriminate)) as D.
    cbn [ab_addr ab_size] in D. lia. }
  pose proof (AI_block AI _ _ _ _ _ p S 7176 AH2 ltac:(left; reflexivity))
    as (_ & _ & _ & _ & BSH & _ & _ & BLO & BHI & BLO4 & BHI4 & BLOS & BHIS & BRNG & BWR).
  (* __asan_memset(S + 8, 0, 7168) runs over a 64-aligned window inside the block's 4096-aligned one *)
  set (WLO := 64 * ((S - 64) / 64)). set (WHI := 64 * ((S + 7176 + 64 + 63) / 64)).
  assert (WLO64 : WLO mod 64 = 0) by (unfold WLO; rewrite Z.mul_comm; apply Z.mod_mul; lia).
  assert (WHI64 : WHI mod 64 = 0) by (unfold WHI; rewrite Z.mul_comm; apply Z.mod_mul; lia).
  assert (WLO0 : 0 <= WLO) by (unfold WLO; Z.div_mod_to_equations; lia).
  assert (WLOS : WLO + 64 <= S) by (unfold WLO; Z.div_mod_to_equations; lia).
  assert (WHIS : S + 7176 + 64 <= WHI) by (unfold WHI; Z.div_mod_to_equations; lia).
  assert (WHIK : WHI <= KEND) by (unfold WHI, KEND; Z.div_mod_to_equations; lia).
  assert (WLOB : BLO <= WLO) by (unfold WLO; Z.div_mod_to_equations; lia).
  assert (WHIB : WHI <= BHI) by (unfold WHI; Z.div_mod_to_equations; lia).
  clearbody WLO WHI.
  assert (WSUB : shad BLO <= shad WLO /\ shad WLO + shlen (WHI - WLO) <= shad BLO + shlen (BHI - BLO) /\ 0 <= shlen (WHI - WLO)).
  { rewrite !shad_div. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  destruct WSUB as (WS1 & WS2 & WS3).
  assert (WRNG : rng RNG' (shad WLO) (shlen (WHI - WLO))) by (eapply rng_sub'; [exact BRNG| lia]).
  assert (WWR : wr_at asegs m2 (shad WLO) (shlen (WHI - WLO))) by (eapply wr_at_sub; [exact BWR| lia ..]).
  assert (SHS2 : shadow_bytes m2 (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)).
  { change 897 with (7176 / 8). apply ablock_sh0; [exact BSH| reflexivity| lia| lia| lia]. }
  assert (SHZ2 : shadow_bytes m2 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
  { eapply (fake_sh_pres AI LB _ m1 m2 2 Fu 256 Zs 14); [exact PRES| exact HIN| exact Z8| lia| lia| lia| lia|].
    eapply sh0_mu; [exact SHZ| exact MU|]. unfold init_W. cbn [disjoint_from].
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB. Z.div_mod_to_equations. lia. }
  assert (WSF2 : wr_at asegs m2 (shad Fu) 32).
  { change 32 with (256 / 8). eapply (fake_shwr_pres AI LB _ m1 m2 2 Fu 256); [exact PRES| exact HIN| | lia| reflexivity| lia|].
    - Z.div_mod_to_equations. lia.
    - eapply wr_at_transport; [exact WSF| exact WM]. }
  assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply aheap_pres_rw_cells; [exact PRES| exact FR0|]. left. left. cbn [cells_size csize Nat.add]. lia. }
  assert (STRM2 : rw_cells asegs m2 Zs (strm_cells next_in avail_in total_in next_out avail_out total_out (Z_to_bv 64 0) state
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0) data_type adler reserved p1 p2 p3)).
  { eapply aheap_pres_rw_cells; [exact PRES| exact STRM1|]. left. right. right. exists 2, Fu, 256. split; [exact HIN|]. rewrite strm_cells_size. lia. }
  replace (ret_pc (Z_to_bv 64 0x8d850)) with (Z_to_bv 64 0x8d850) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply evtF_mono.
  { eapply (init_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S lo RNG') with (j8 := j8) (RLO := WLO) (RHI := WHI); try eassumption;
      try (unfold INIT_STACK; lia); try (eapply rng_fp_le; [exact FPLE| eassumption]).
    eapply rng_sub'; [exact RSS|]. rewrite shadE. change (shlen (7176 + 7)) with 897. lia. }
  cbv beta. intros ms3 (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & check & len & off & ext & lb & db & ncode & nlen & ndist & have & was & pad & jarr
                        & -> & MU3 & WM3 & MI3 & ST3 & STRM3 & SSC3 & SARR3 & STAIL3).
  split; [exact FPLE|].
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m3.
  split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact REST|].
  split.
  {
    eapply client_agree_trans; [| eapply client_agree_trans].
    - eapply (client_agree_munch AI LB _ _ (init_W sp Zs) m m1 MU WM). intros a Ha HC HN.
      destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH HC) as [C|[C|[(b & Hb & C)|C]]]; unfold init_W; cbn [outside]; unfold AIMG_HI, KLS in *.
      + split; [lia|]. split; [| exact I]. lia.
      + split; [lia|]. split; [| exact I]. lia.
      + pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (B1 & B2 & B3).
        split; [lia|]. split; [| exact I]. intros X. apply HN. exists (Zs, Zs + 112). split; [left; reflexivity| exact X].
      + split; [lia|]. split; [| exact I]. unfold ablk, AIMG_HI, KLS in FUB. lia.
    - eapply (client_agree_pres AI LB LB _ (bv_unsigned sp + -112)); [exact PRES| lia| auto].
    - eapply (client_agree_munch AI LB _ _ (init_finW sp Zs S lo) m2 m3 MU3 WM3). intros a Ha HC HN.
      destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH HC) as [C|[C|[(b & Hb & C)|C]]]; unfold init_finW; cbn [outside]; unfold AIMG_HI, KLS in *.
      + split; [lia|]. split; [lia|]. split; [lia| exact I].
      + split; [lia|]. split; [lia|]. split; [lia| exact I].
      + pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (B1 & B2 & B3).
        assert (NE : HB p S 7176 <> b).
        { intros <-. pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as ND. inversion ND as [|? ? NI _]. exact (NI Hb). }
        pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p S 7176) b AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D.
        cbn [ab_addr ab_size] in D.
        split; [lia|]. split; [| split; [lia| exact I]]. intros X. apply HN. exists (Zs, Zs + 112). split; [left; reflexivity| exact X].
      + split; [lia|]. unfold ablk, AIMG_HI, KLS in FUB, SB. split; [lia|]. split; [lia| exact I]. }
  exists S, check, len, off, ext, lb, db, ncode, nlen, ndist, have, (Z_to_bv 64 0), jarr, was, pad.
  split.
  {
    eapply (AI_frame AI _ _ _ _ m2 m3 _ AH2 MU3 WM3). unfold init_finW.
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply acr_fake; [exact HIN2| lia| lia]|].
    constructor; [cbn [fst snd]; eapply (acr_block AI _ (HB p S 7176)); [left; reflexivity| cbn; lia| cbn; lia]| constructor]. }
  split; [exact S16|]. split; [exact SB|]. split; [exact STRM3|]. split; [exact SSC3|]. split; [exact SARR3| exact STAIL3].
Qed.

End CANSEC1.
