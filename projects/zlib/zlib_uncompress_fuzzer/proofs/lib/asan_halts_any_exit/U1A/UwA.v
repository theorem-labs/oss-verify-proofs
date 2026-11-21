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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AIface U2AIfaceS U2AGlue UwA_copy UwA_pre.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac dj_side :=
  first [ solve [ repeat match goal with
                         | H : ?T |- _ => lazymatch T with
                                          | (_ <= _)%Z => fail | (_ < _)%Z => fail | (_ <= _ <= _)%Z => fail | (_ <= _ < _)%Z => fail
                                          | (_ < _ <= _)%Z => fail | (_ < _ < _)%Z => fail | _ => clear H end
                         end; Z.div_mod_to_equations; lia ]
        | (Z.div_mod_to_equations; lia) ].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma win_hull : forall (m : amem) RNG Wd RLO RHI,
  ablk Wd (Wd + 32768) ->
  RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= Wd -> Wd + 32768 + 64 <= RHI ->
  rng RNG (shad RLO) (shlen (RHI - RLO)) -> wr_at asegs m (shad RLO) (shlen (RHI - RLO)) ->
  let WLO := Wd / 64 * 64 in let WHI := (Wd + 32768 + 63) / 64 * 64 in
  (WLO <= Wd /\ Wd + 32768 <= WHI /\ WLO mod 64 = 0 /\ WHI mod 64 = 0 /\ 0 <= WLO /\ WHI <= KEND)
  /\ rng RNG (shad WLO) (shad WHI - shad WLO) /\ wr_at asegs m (shad WLO) (shad WHI - shad WLO).
Proof.
  intros m RNG Wd RLO RHI WB R1 R2 R3 R4 RR RW WLO WHI.
  pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1. atop_facts.
  assert (A1 : WLO <= Wd /\ Wd - 64 < WLO /\ WLO mod 64 = 0) by (subst WLO; Z.div_mod_to_equations; lia).
  assert (A2 : Wd + 32768 <= WHI /\ WHI < Wd + 32768 + 64 /\ WHI mod 64 = 0) by (subst WHI; Z.div_mod_to_equations; lia).
  split; [unfold KEND; lia|].
  unfold shlen in *. rewrite !shad_div. rewrite shad_div in RR, RW. rewrite Z.shiftr_div_pow2 in RR, RW by lia. change (2^3) with 8 in RR, RW.
  split.
  - eapply rng_sub'; [exact RR|]. Z.div_mod_to_equations. lia.
  - eapply wr_at_sub; [exact RW|..]; Z.div_mod_to_equations; lia.
Qed.

Theorem updatewindow_old_proofA : forall (AI : AMallocIface), updatewindow_old_stmtA AI.
Proof.
  intros AI. unfold updatewindow_old_stmtA. intros until wbytes.
  intros AH (HIN & ZSE & FU256 & FUB) (SHZ & RZ & WSF & RSF) HS HW STRM SSC WBLK ((obs & OBLK) & SHO & WRO) CPY COUT WN WH ST LOC LOS SP16 TOPS MI TP A0 A1 A2 RSTK RI RISH.
  subst a0 a1 a2. unfold A_OUTBUF in *. change (Z.shiftr 6335680 3) with 791960 in SHO.
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
  pose proof (AI_block AI _ _ _ _ _ pw Wd 32768 AH HW) as (_ & ABRW & RW & _ & BSHW & _ & _ & (RLO & RHI & RL1 & RL2 & RL3 & RL4 & RRNG & RWR)).
  destruct ABRW as (WB & _ & _ & W16).
  pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1.
  assert (SHW : shadow_bytes m (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0)).
  { change 4096 with (32768 / 8). apply ablock_sh0; [exact BSHW| reflexivity| lia| lia| lia]. }
  destruct (win_hull m RNG Wd RLO RHI WB RL1 RL2 RL3 RL4 RRNG RWR) as (WHULL & RWH & WRW).
  set (WLO := Wd / 64 * 64) in *. set (WHI := (Wd + 32768 + 63) / 64 * 64) in *.
  assert (SEPW : S + 7176 <= Wd \/ Wd + 32768 <= S).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB ps S 7176) (HB pw Wd 32768) AH HS HW ltac:(intros E; inversion E)) as D.
    cbn [ab_addr ab_size] in D. lia. }
  unfold UW_STACK in LOS.
  eapply evtF_cut.
  { eapply (uw_preO ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S lo RNG); try (first [key_assumption | eassumption]); try lia. }
  cbv beta. intros ms1 (m1 & j8 & -> & MU & WM & MI1 & ST1 & FR0).
  assert (AH1 : AHEAP AI L RNG st LB m1).
  { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU WM).
    constructor; [cbn [fst snd]; apply acr_stack; lia| constructor]. }
  pose proof (AI_rtcells AI _ _ _ _ _ AH1) as ART1. unfold artcells in ART1.
  destruct ART1 as (_ & GOT1 & RIC1 & REAL1 & SHB1 & _ & INI1 & LAY1 & _).
  assert (TRS : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 112 -> rw_cells asegs m1 A cs).
  { intros Ax csx HCx HAx. eapply rw_cells_transport; [exact HCx| exact MU| exact WM|]. cbn [disjoint_from]. split; [lia| exact I]. }
  assert (SSC1 := TRS _ _ SSC ltac:(rewrite istate_cells_size; lia)).
  assert (WBLK1 := TRS _ _ WBLK ltac:(cbn [cells_size csize]; lia)).
  assert (OBLK1 := TRS _ _ OBLK ltac:(cbn [cells_size csize]; lia)).
  assert (DJ1 : forall a n, a + n <= 0x10007fff8000 -> KLS <= a -> 0 <= n -> disjoint_from [(bv_unsigned sp - 112, bv_unsigned sp)] a n).
  { intros a n H1 H2 H3. cbn [disjoint_from]. unfold KLS in *. split; [lia| exact I]. }
  assert (SHS1 : shadow_bytes m1 (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)).
  { eapply sh0_mu; [exact SHS| exact MU|]. apply DJ1; unfold KLS; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; dj_side. }
  assert (SHW1 : shadow_bytes m1 (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0)).
  { eapply sh0_mu; [exact SHW| exact MU|]. apply DJ1; unfold KLS; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; dj_side. }
  assert (SHO1 : shadow_bytes m1 (791960 + 2147450880) (791960 + 2147450880 + 32768) (fun _ => 0)).
  { eapply sh0_mu; [exact SHO| exact MU|]. apply DJ1; unfold KLS; lia. }
  assert (WRW1 : wr_at asegs m1 (shad WLO) (shad WHI - shad WLO)) by (eapply wr_at_transport; [exact WRW| exact WM]).
  assert (WRO1 : wr_at asegs m1 (shad 6335680) 32768) by (eapply wr_at_transport; [exact WRO| exact WM]).
  eapply evtF_mono.
  { eapply (uw_copy ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S lo RNG); try (first [key_assumption | eassumption]); try lia. }
  cbv beta. intros ms2 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & wbytes' & -> & MU2 & WM2 & MI2 & ST2 & SSC2 & WBLK2).
  unfold uw_post_core.
  exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m2, wbytes'.
  split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|].
  split.
  { eapply client_agree_trans.
    - eapply (client_agree_munch AI LB _ _ [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 MU WM). intros a Ha HC HN.
      destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH HC) as [C|[C|[(b & Hb & C)|C]]]; cbn [outside]; unfold AIMG_HI, KLS in *.
      + split; [lia| exact I].
      + split; [lia| exact I].
      + pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (B1 & B2 & B3). split; [lia| exact I].
      + split; [lia| exact I].
    - eapply (client_agree_munch AI LB _ _ (uw_cW sp S lo Wd) m1 m2 MU2 WM2). intros a Ha HC HN.
      assert (NS : ~ (S + 68 <= a < S + 96)) by (intros X; apply HN; exists (S + 68, S + 96); split; [left; reflexivity| exact X]).
      assert (NW : ~ (Wd <= a < Wd + 32768)) by (intros X; apply HN; exists (Wd, Wd + 32768); split; [right; left; reflexivity| exact X]).
      destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH HC) as [C|[C|[(b & Hb & C)|C]]]; unfold uw_cW; cbn [outside]; unfold AIMG_HI, KLS in *.
      + split; [lia|]. split; [exact NS|]. split; [exact NW| exact I].
      + split; [lia|]. split; [exact NS|]. split; [exact NW| exact I].
      + pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (B1 & B2 & B3).
        split; [lia|]. split; [exact NS|]. split; [exact NW| exact I].
      + split; [lia|]. split; [exact NS|]. split; [exact NW| exact I]. }
  split.
  { eapply (AI_frame AI _ _ _ _ m1 m2 _ AH1 MU2 WM2). unfold uw_cW.
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply (acr_block AI _ (HB ps S 7176)); [exact HS| cbn; lia| cbn; lia]|].
    constructor; [cbn [fst snd]; eapply (acr_block AI _ (HB pw Wd 32768)); [exact HW| cbn; lia| cbn; lia]| constructor]. }
  split; [exact SSC2| exact WBLK2].
Qed.


Lemma sh_pres_range : forall (AI : AMallocIface) LB SP m m' s1 s2 f,
  aheap_pres (aci AI) LB SP m m' -> aclient_range (aci AI) LB SP s1 (s2 - s1) ->
  shadow_bytes m s1 s2 f -> shadow_bytes m' s1 s2 f.
Proof.
  intros AI LB SP m m' s1 s2 f HP HR SBm. pose proof SBm as (A & B & _).
  eapply shadow_bytes_agree; [exact SBm|]. intros s Hs.
  destruct (HP s ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR| lia])) as [E _]. exact E.
Qed.

Theorem updatewindow_new_proofA : forall (AI : AMallocIface), updatewindow_new_stmtA AI.
Proof.
  intros AI. unfold updatewindow_new_stmtA. intros until next.
  intros AH (HIN & ZSE & FU256 & FUB) (SHZ & RZ & WSF & RSF) HS (civ & CIV & CIV1 & CIV2) STRM SSC ((obs & OBLK) & SHO & WRO) CPY COUT ST LOC LOS SP16 MI TP A0 A1 A2 TOPS UCH LTR INU S0GE RSTK RI RISH APS.
  subst a0 a1 a2. unfold A_OUTBUF in *. change (Z.shiftr 6335680 3) with 791960 in SHO.
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
  unfold UW_STACK in LOS.
  eapply implMA_evtF.
  { eapply (uw_preN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S lo RNG); try (first [key_assumption | eassumption]); try lia. }
  cbv beta. intros ms1 (m1 & j8 & a4' & -> & MU & WM & MI1 & ST1 & FR0).
  assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
  { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU WM).
    constructor; [cbn [fst snd]; apply acr_stack; lia| constructor]. }
  assert (TRS : forall Ax csx, rw_cells asegs m Ax csx -> Ax + Z.of_nat (cells_size csx) <= bv_unsigned sp - 112 -> rw_cells asegs m1 Ax csx).
  { intros Ax csx HCx HAx. eapply rw_cells_transport; [exact HCx| exact MU| exact WM|]. cbn [disjoint_from]. split; [lia| exact I]. }
  assert (SSC1 := TRS _ _ SSC ltac:(rewrite istate_cells_size; lia)).
  assert (OBLK1 := TRS _ _ OBLK ltac:(cbn [cells_size csize]; lia)).
  assert (DJ1 : forall a n, a + n <= 0x10007fff8000 -> KLS <= a -> 0 <= n -> disjoint_from [(bv_unsigned sp - 112, bv_unsigned sp)] a n).
  { intros a n H1 H2 H3. cbn [disjoint_from]. unfold KLS in *. split; [lia| exact I]. }
  assert (SHO1 : shadow_bytes m1 (791960 + 2147450880) (791960 + 2147450880 + 32768) (fun _ => 0)).
  { eapply sh0_mu; [exact SHO| exact MU|]. apply DJ1; unfold KLS; lia. }
  assert (WRO1 : wr_at asegs m1 (shad 6335680) 32768) by (eapply wr_at_transport; [exact WRO| exact WM]).
  eapply implMA_post_evtF.
  { eapply (implMA_amalloc_call AI L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR fc m1 s LB 32768 lo tr);
      rewrite ?unsigned_lit by lia; try reflexivity; try eassumption; try (unfold AMALLOC_STACK, AREQMAX, AMALLOC_PC; lia).
    all: lazymatch goal with
         | |- aunw5 _ _ _ _ _ _ _ =>
             left; rewrite ?unsigned_lit by lia; split; [lia|]; split;
             [ replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia;
               eapply uchain_munch; [exact UCH| exact MU| | lia| lia];
               intros a Ha; cbn [outside]; lia
             | split; [exact LTR| exact INU] ]
         | |- _ => first [ lia | Z.div_mod_to_equations; lia ]
         end. }
  cbv beta. intros r s' RNG' ms' (REST & FPLE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4'' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MI2 & ST2 & PRES & CASE).
  cbn [snd fst] in CASE. destruct r as [pw|]; [| contradiction].
  destruct CASE as (Wd & junk & -> & ABRW & AH2 & WBLK & RW & RWS & _).
  rewrite ?unsigned_lit in * by lia.
  destruct ABRW as (WB & _ & _ & W16).
  pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1.
  assert (HS2 : In (HB ps S 7176) (HB pw Wd 32768 :: LB)) by (right; exact HS).
  assert (HW2 : In (HB pw Wd 32768) (HB pw Wd 32768 :: LB)) by (left; reflexivity).
  pose proof (AI_rtcells AI _ _ _ _ _ AH2) as ART2. unfold artcells in ART2.
  destruct ART2 as (_ & GOT2 & RIC2 & REAL2 & SHB2 & _ & INI2 & LAY2 & _).
  pose proof (AI_block AI _ _ _ _ _ ps S 7176 AH2 HS2) as (_ & _ & _ & _ & BSH2 & _).
  assert (SHS2 : shadow_bytes m2 (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)).
  { change 897 with (7176 / 8). apply ablock_sh0; [exact BSH2| reflexivity| lia| lia| lia]. }
  pose proof (AI_block AI _ _ _ _ _ pw Wd 32768 AH2 HW2) as (_ & _ & _ & _ & BSHW & _ & _ & (RLO & RHI & RL1 & RL2 & RL3 & RL4 & RRNG & RWR)).
  assert (SHW2 : shadow_bytes m2 (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0)).
  { change 4096 with (32768 / 8). apply ablock_sh0; [exact BSHW| reflexivity| lia| lia| lia]. }
  destruct (win_hull m2 RNG' Wd RLO RHI WB RL1 RL2 RL3 RL4 RRNG RWR) as (WHULL & RWH & WRW).
  set (WLO := Wd / 64 * 64) in *. set (WHI := (Wd + 32768 + 63) / 64 * 64) in *.
  assert (SEPW : S + 7176 <= Wd \/ Wd + 32768 <= S).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB ps S 7176) (HB pw Wd 32768) AH2 HS2 HW2 ltac:(intros E; inversion E)) as D.
    cbn [ab_addr ab_size] in D. lia. }
  assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -112) (CB 8 j8 :: uw_FR ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply aheap_pres_rw_cells; [exact PRES| exact FR0|]. left. left. unfold uw_FR. cbn [cells_size csize Nat.add]. lia. }
  assert (SSC2 := aheap_pres_rw_cells _ _ _ _ _ _ _ PRES SSC1 ltac:(right; left; exists (HB ps S 7176); split; [exact HS| rewrite istate_cells_size; cbn [ab_addr ab_size]; lia])).
  assert (CRO : aclient_range (aci AI) LB (bv_unsigned sp + -112) 6335680 262144).
  { left. right. left. exists civ. split; [exact CIV|]. unfold A_OUTBUF in *. lia. }
  assert (OBLK2 : rw_cells asegs m2 6335680 [CB (Z.to_nat 262144) obs]).
  { eapply aheap_pres_rw_cells; [exact PRES| exact OBLK1|]. cbn [cells_size csize]. replace (Z.of_nat (Z.to_nat 262144 + 0)) with 262144 by lia. exact CRO. }
  assert (CROS : aclient_range (aci AI) LB (bv_unsigned sp + -112) (791960 + 2147450880) 32768).
  { right. right. right. left. exists civ. split; [exact CIV|]. unfold ASHOFF, A_OUTBUF in *. lia. }
  assert (SHO2 : shadow_bytes m2 (791960 + 2147450880) (791960 + 2147450880 + 32768) (fun _ => 0)).
  { eapply sh_pres_range; [exact PRES| | exact SHO1]. replace (791960 + 2147450880 + 32768 - (791960 + 2147450880)) with 32768 by lia. exact CROS. }
  assert (WRO2 : wr_at asegs m2 (shad 6335680) 32768).
  { eapply aheap_pres_wr_at; [exact PRES| exact WRO1|]. change (shad 6335680) with (791960 + 2147450880). exact CROS. }
  replace (ret_pc (Z_to_bv 64 0x93750)) with (Z_to_bv 64 0x93750) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FPRNG : forall lo0 n0, rng RNG lo0 n0 -> rng RNG' lo0 n0) by (intros; eapply rng_fp_le; [exact FPLE| assumption]).
  eapply evtF_cut.
  { eapply (uw_midN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S lo RNG'); try (first [key_assumption | eassumption]); try lia; try (apply FPRNG; assumption). }
  cbv beta. intros ms3 (m3 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & MU3 & WM3 & MI3 & ST3 & SSC3).
  assert (AH3 : AHEAP AI L RNG' (aps_m s') (HB pw Wd 32768 :: LB) m3).
  { eapply (AI_frame AI _ _ _ _ m2 m3 _ AH2 MU3 WM3).
    constructor; [cbn [fst snd]; eapply (acr_block AI _ (HB ps S 7176)); [exact HS2| cbn; lia| cbn; lia]| constructor]. }
  pose proof (AI_rtcells AI _ _ _ _ _ AH3) as ART3. unfold artcells in ART3.
  destruct ART3 as (_ & GOT3 & RIC3 & REAL3 & SHB3 & _ & INI3 & LAY3 & _).
  assert (TR3 : forall Ax csx, rw_cells asegs m2 Ax csx -> (Ax + Z.of_nat (cells_size csx) <= S + 68 \/ S + 96 <= Ax) -> rw_cells asegs m3 Ax csx).
  { intros Ax csx HCx HAx. eapply rw_cells_transport; [exact HCx| exact MU3| exact WM3|]. cbn [disjoint_from]. split; [lia| exact I]. }
  assert (FR3 := TR3 _ _ FR2 ltac:(unfold uw_FR; cbn [cells_size csize Nat.add]; lia)).
  assert (WBLK3 := TR3 _ _ WBLK ltac:(cbn [cells_size csize]; lia)).
  assert (OBLK3 := TR3 _ _ OBLK2 ltac:(cbn [cells_size csize]; lia)).
  assert (DJ3 : forall a n, a + n <= 0x10007fff8000 -> KLS <= a -> 0 <= n -> disjoint_from [(S + 68, S + 96)] a n).
  { intros a n H1 H2 H3. cbn [disjoint_from]. pose proof SB as SB'. unfold ablk, AIMG_HI, KLS in SB'. unfold KLS in *. split; [lia| exact I]. }
  assert (SHS3 : shadow_bytes m3 (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)).
  { eapply sh0_mu; [exact SHS2| exact MU3|]. apply DJ3; unfold KLS; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; dj_side. }
  assert (SHW3 : shadow_bytes m3 (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0)).
  { eapply sh0_mu; [exact SHW2| exact MU3|]. apply DJ3; unfold KLS; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; dj_side. }
  assert (SHO3 : shadow_bytes m3 (791960 + 2147450880) (791960 + 2147450880 + 32768) (fun _ => 0)).
  { eapply sh0_mu; [exact SHO2| exact MU3|]. apply DJ3; unfold KLS; lia. }
  assert (WRW3 : wr_at asegs m3 (shad WLO) (shad WHI - shad WLO)) by (eapply wr_at_transport; [exact WRW| exact WM3]).
  assert (WRO3 : wr_at asegs m3 (shad 6335680) 32768) by (eapply wr_at_transport; [exact WRO2| exact WM3]).
  eapply evtF_mono.
  { eapply (uw_copy ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc Fu Zs S lo RNG' LOS LOC SP16 SPT ZSE FU256 FUB SB S16
                    ltac:(apply FPRNG; exact RSTK') ltac:(apply FPRNG; exact RI) ltac:(apply FPRNG; exact RZ) ltac:(apply FPRNG; exact RSZ)
                    ltac:(apply FPRNG; exact RS) ltac:(apply FPRNG; exact RSS) Wd WLO WHI WB W16 RW SEPW WHULL RWH ltac:(apply FPRNG; exact RISH)
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 cout copy mode 0 0); try (first [key_assumption | eassumption]); try lia. }
  cbv beta. intros ms4 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4 & wbytes' & -> & MU4 & WM4 & MI4 & ST4 & SSC4 & WBLK4).
  unfold uw_new_post. split; [exact FPLE|]. split; [exact REST|].
  exists Wd. split; [exact W16|]. split; [exact WB|].
  unfold uw_post_core.
  exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m4, wbytes'.
  split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|].
  split.
  { eapply client_agree_trans; [| eapply client_agree_trans; [| eapply client_agree_trans]].
    - eapply (client_agree_munch AI LB _ _ [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 MU WM). intros a Ha HC HN.
      destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH HC) as [C|[C|[(b & Hb & C)|C]]]; cbn [outside]; unfold AIMG_HI, KLS in *.
      + split; [lia| exact I].
      + split; [lia| exact I].
      + pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (B1 & B2 & B3). split; [lia| exact I].
      + split; [lia| exact I].
    - eapply (client_agree_pres AI LB LB _ (bv_unsigned sp + -112)); [exact PRES| lia| auto].
    - eapply (client_agree_munch AI LB _ _ [(S + 68, S + 96)] m2 m3 MU3 WM3). intros a Ha HC HN.
      cbn [outside]. split; [| exact I]. intros X. apply HN. exists (S + 68, S + 96). split; [left; reflexivity| exact X].
    - eapply (client_agree_munch AI LB _ _ (uw_cW sp S lo Wd) m3 m4 MU4 WM4). intros a Ha HC HN.
      assert (NS : ~ (S + 68 <= a < S + 96)) by (intros X; apply HN; exists (S + 68, S + 96); split; [left; reflexivity| exact X]).
      assert (NW : ~ (Wd <= a < Wd + 32768)) by (intros X; apply HN; exists (Wd, Wd + 32768); split; [right; left; reflexivity| exact X]).
      destruct (aclient_addr_cases AI _ _ _ _ _ _ a AH HC) as [C|[C|[(b & Hb & C)|C]]]; unfold uw_cW; cbn [outside]; unfold AIMG_HI, KLS in *.
      + split; [lia|]. split; [exact NS|]. split; [exact NW| exact I].
      + split; [lia|]. split; [exact NS|]. split; [exact NW| exact I].
      + pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (B1 & B2 & B3).
        split; [lia|]. split; [exact NS|]. split; [exact NW| exact I].
      + split; [lia|]. split; [exact NS|]. split; [exact NW| exact I]. }
  split.
  { eapply (AI_frame AI _ _ _ _ m3 m4 _ AH3 MU4 WM4). unfold uw_cW.
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply (acr_block AI _ (HB ps S 7176)); [exact HS2| cbn; lia| cbn; lia]|].
    constructor; [cbn [fst snd]; eapply (acr_block AI _ (HB pw Wd 32768)); [exact HW2| cbn; lia| cbn; lia]| constructor]. }
  split; [exact SSC4| exact WBLK4].
Qed.

End CANSEC1.
