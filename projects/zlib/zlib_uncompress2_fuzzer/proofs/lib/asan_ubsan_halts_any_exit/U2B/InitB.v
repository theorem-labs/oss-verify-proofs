(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj U2BIface U2BGlue InitB_pre InitB_fin.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [U14B] A2 2026-11-12: the 64-aligned hull of the state block inside AI_block's 4096-aligned shadow window, in the
   shape U2BCall.asan_memset_callz asks for (UwB.win_hull's twin for the 7176-byte block): for zlib 1.4's
   memset(state, 0, sizeof(struct inflate_state)) in inflateInit2_ (InitB_fin). *)
Lemma init_hull : forall (m : amem) RNG S RLO RHI,
  ablk S (S + 7176) ->
  RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= S -> S + 7176 + 64 <= RHI ->
  rng RNG (shad RLO) (shlen (RHI - RLO)) -> wr_at bsegs m (shad RLO) (shlen (RHI - RLO)) ->
  let WLO := S / 64 * 64 in let WHI := (S + 7176 + 63) / 64 * 64 in
  (WLO <= S /\ S + 7176 <= WHI /\ WLO mod 64 = 0 /\ WHI mod 64 = 0 /\ 0 <= WLO /\ WHI <= KEND)
  /\ rng RNG (shad WLO) (shad WHI - shad WLO) /\ wr_at bsegs m (shad WLO) (shad WHI - shad WLO).
Proof.
  intros m RNG S RLO RHI WB R1 R2 R3 R4 RR RW WLO WHI.
  pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1. atop_facts.
  assert (A1 : WLO <= S /\ S - 64 < WLO /\ WLO mod 64 = 0) by (subst WLO; Z.div_mod_to_equations; lia).
  assert (A2 : S + 7176 <= WHI /\ WHI < S + 7176 + 64 /\ WHI mod 64 = 0) by (subst WHI; Z.div_mod_to_equations; lia).
  split; [unfold KEND; lia|].
  unfold shlen in *. rewrite !shad_div. rewrite shad_div in RR, RW. rewrite Z.shiftr_div_pow2 in RR, RW by lia. change (2^3) with 8 in RR, RW.
  split.
  - eapply rng_sub'; [exact RR|]. Z.div_mod_to_equations. lia.
  - eapply wr_at_sub; [exact RW|..]; Z.div_mod_to_equations; lia.
Qed.

Theorem inflateInit_proofA : forall (AI : AMallocIface), inflateInit_stmtA AI.
Proof.
  intros AI. unfold inflateInit_stmtA. intros until p3.
  intros AH (HIN & ZSE & FU256 & FUB) (SHZ & RZ & WSF & RSF) STRM UIMG SHV ST LOC LOS SP16 MI TP A0 A1 A2 RA4 TOPS INU RSTK RI RISH APS.
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
  cbv beta. intros ms1 (m1 & -> & MU & WM & MI1 & ST1 & FR0 & STRM1).
  assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
  { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU WM). unfold init_W.
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply acr_fake; [exact HIN| lia| lia]| constructor]. }
  eapply implMA_post_evtF.
  { eapply (implMA_amalloc_call AI L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc m1 s LB 7176 lo []);
      rewrite ?unsigned_lit by lia; try reflexivity; try eassumption; try (unfold AMALLOC_STACK, AREQMAX, AMALLOC_PC; lia).
    all: lazymatch goal with
         | |- aunw5 _ _ _ _ _ _ _ =>
             left; rewrite ?unsigned_lit by lia; split; [lia|]; split;
             [ apply uc_stop; lia
             | split; [cbn [length]; lia| exact INU] ]
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
    as (_ & _ & _ & _ & BSH & _ & _ & (RLO & RHI & RL1 & RL2 & RL3 & RL4 & RRNG & RWR)).
  (* [U14B] A2 2026-11-12: the shadow window of the new block, for InitB_fin's memset over it *)
  destruct (init_hull m2 RNG' S RLO RHI SB RL1 RL2 RL3 RL4 RRNG RWR) as (WHULL & RWH & WRW).
  assert (SHS2 : shadow_bytes m2 (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)).
  { change 897 with (7176 / 8). apply ablock_sh0; [exact BSH| reflexivity| lia| lia| lia]. }
  assert (SHZ2 : shadow_bytes m2 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
  { eapply (fake_sh_pres AI LB _ m1 m2 2 Fu 256 Zs 14); [exact PRES| exact HIN| exact Z8| lia| lia| lia| lia|].
    eapply sh0_mu; [exact SHZ| exact MU|]. unfold init_W. cbn [disjoint_from].
    rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ablk, AIMG_HI, KLS in FUB. Z.div_mod_to_equations. lia. }
  assert (WSF2 : wr_at bsegs m2 (shad Fu) 32).
  { change 32 with (256 / 8). eapply (fake_shwr_pres AI LB _ m1 m2 2 Fu 256); [exact PRES| exact HIN| | lia| reflexivity| lia|].
    - Z.div_mod_to_equations. lia.
    - eapply wr_at_transport; [exact WSF| exact WM]. }
  assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply aheap_pres_rw_cells; [exact PRES| exact FR0|]. left. left. cbn [cells_size csize Nat.add]. lia. }
  assert (STRM2 : rw_cells bsegs m2 Zs (strm_cells next_in avail_in total_in next_out avail_out total_out (Z_to_bv 64 0) state
                                    (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0) data_type adler reserved p1 p2 p3)).
  { eapply aheap_pres_rw_cells; [exact PRES| exact STRM1|]. left. right. right. exists 2, Fu, 256. split; [exact HIN|]. rewrite strm_cells_size. lia. }
  replace (ret_pc (Z_to_bv 64 581304)) with (Z_to_bv 64 581304) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply evtF_mono.
  { eapply (init_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S lo RNG')
      with (WLO := S / 64 * 64) (WHI := (S + 7176 + 63) / 64 * 64); try eassumption;
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
    - eapply (client_agree_pres AI LB LB _ (bv_unsigned sp + -80)); [exact PRES| lia| auto].
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
