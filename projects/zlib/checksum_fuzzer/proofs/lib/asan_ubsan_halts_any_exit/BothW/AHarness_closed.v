(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed ProgA AsanProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit Stdio_kit AHarness_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.CkB Require CkBImg CkBTables CkBShadow CkBIface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1. Context {rc : runConstT}.

Lemma page_round_up_ge : forall z, z <= page_round_up_Z z.
Proof. intros z. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Theorem fuzz_oneA_of_ck : CkBIface.ck_fuzz_stmtA -> forall (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop), fuzz_oneA_stmt AI rng_fs.
Proof.
  intros CK AI rng_fs. unfold fuzz_oneA_stmt. intros until rstk.
  intros AH HLB PAY BY FA D16 SZB HI ST BOT LOS SPG SP16 RC RLO RHI RRLO S0 MI FRM TP A0 A1 RA HU RSTK RI RISH RFS RR ROK.
  pose proof atop_range as ATR. unfold AHARNESS_STACK in LOS.
  destruct (AI_layout AI L RNG (aps_m s) LB m AH) as (LT1 & LT2 & LT3 & LT4 & _).
  assert (SPT : bv_unsigned sp + 32 <= al_top L) by (unfold al_top; pose proof (page_round_up_ge (al_sp0 L - 0xa0)); lia).
  destruct (AI_rtcells AI L RNG (aps_m s) LB m AH) as (_ & GOT & _ & _ & SHB & _).
  change (fuzz_oneA AAllocAsan payload) with (mret (St:=APS) 0). apply implMA_ret.
  assert (LEN0 : 0 <= zlength payload) by (unfold zlength; lia).
  eapply evtF_mono.
  - eapply (CK RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo D (zlength payload));
      try eassumption.
    + unfold CkBIface.CK_FUZZ_STACK. lia.
    + unfold KHIGH. lia.
    + lia.
    + destruct PAY as [(p & HIN & _)|[_ ->]];
        [ destruct (AI_block_bounds AI L RNG (aps_m s) LB m _ AH HIN) as (B1 & _ & B3); cbn [ab_addr ab_size] in B1, B3; unfold AIMG_HI in B1; lia
        | unfold AEMPTY; lia ].
    + intros NR. destruct PAY as [(p & HIN & _)|[-> _]]; [|unfold zlength in NR; cbn in NR; lia].
      destruct (AI_block AI L RNG (aps_m s) LB m p D (zlength payload) AH HIN) as (_ & _ & RB & RSB & SHD & _).
      destruct (AI_block_bounds AI L RNG (aps_m s) LB m _ AH HIN) as (B1 & _ & B3). cbn [ab_addr ab_size] in B1, B3. unfold AIMG_HI in B1.
      exists payload. split; [reflexivity|]. split; [|lia].
      split; [exact BY|]. split; [exact FA|]. fold (zlength payload).
      split. { apply ablock_unpoisoned; [exact SHD| Z.div_mod_to_equations; lia| lia | lia | lia]. }
      split. { exact RB. }
      apply CkBShadow.shrng_of_block.
      { exact RSB. }
      { Z.div_mod_to_equations; lia. }
      { lia. }
    + eapply rng_sub'; [exact RSTK| lia].
  - cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST').
    unfold CkBIface.CK_FUZZ_STACK in MU.
    split; [apply fp_le_refl|].
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, fc, m'.
    split; [reflexivity|]. split; [lia|]. split; [exact MI'|]. split; [exact FRM|]. split; [exact ST'|].
    split.
    { eapply (aheap_pres_stack_writes AI (aci AI) L RNG (aps_m s) LB m [(bv_unsigned sp - 288, bv_unsigned sp)] m m' (bv_unsigned sp) lo AH);
        [ intros b Hb; exact (AI_block_bounds AI L RNG (aps_m s) LB m b AH Hb) | apply (AI_aci_img AI) | exact MU | exact WM | | lia ].
      constructor; [cbn [fst snd]; lia | constructor]. }
    split.
    { intros a Ha. apply MU. cbn [outside]. split; [|exact I]. rewrite !shad_div in Ha. unfold ASHOFF in Ha.
      rewrite wa_unsigned by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
    split.
    { eapply (AI_frame AI L RNG (aps_m s) LB m m' [(bv_unsigned sp - 288, bv_unsigned sp)] AH MU WM).
      constructor; [|constructor]. cbn [fst snd]. left. left. lia. }
    split; [|reflexivity].
    eapply (CkBShadow.ck_sh_mu [(bv_unsigned sp - 288, bv_unsigned sp)] (bv_unsigned sp - 288) m m' HI MU); [cbn; split; [lia| exact I]| unfold KHIGH; lia].
Qed.
End CANSEC1.
