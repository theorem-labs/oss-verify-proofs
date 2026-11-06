From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes tx_put_c TxCalls TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PjWriteHyp round_trip_text_c RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import
RttGlue RttModel RttBase RttA_Lib RttA_Call.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require RttRunsA.
Import ListNotations.
Local Open Scope Z_scope.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis TXP : forall fx' : YK11.FPState, @tx_put_contract fx' rc B API F.
Hypothesis NEXT : stg_txv_st B API F.

(* 0x15364: pj_write returned the text q in a0; s2 := q, the 32-byte struct text at S - 112 zeroed (RttRunsA.rtt_seg1),
   tx_put(&t, "", 0) (RttA_Call.ra_put), on to stg_txv at 0x1538c *)
Theorem stg_tx1_holds : stg_tx1_st B API F.
Proof.
  unfold stg_tx1_st.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx' L A regs mem md Lam peak q.
  cbv zeta. intros ENT FL INV RR G10 RT.
  pose proof ENT as (REN & _ & _ & _ & _ & R10 & R11 & R12 & PR & _ & _ & _ & DOCS & _ & DEP & WL & _ & ROOM).
  pose proof REN as (_ & _ & ERRB & _ & _ & PRE0 & _).
  pose proof PRE0 as (_ & _ & _ & _ & SP16 & SPC & SP63 & _).
  pose proof INV as (RS & _).
  pose proof RS as (MRc & _ & _ & _ & _ & _ & _ & _ & _ & WRc).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  pose proof RR as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  pose proof alloc_ceiling_val as HCV.
  assert (HRK : 112 <= RTT_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (STK : Frame.stk rsegs mem (spZ regs0 - 112) (spZ regs0 - 112 + 32)).
  { rewrite <- HSEG. apply (@ra_stk fx rc B API F HSEG FA); [lia | lia | lia |].
    intros a Ha. apply WRc. unfold rwin. left. lia. }
  eapply (@ra_run fx rc B API F HSEG FA fx' regs _ mem md _ _ Hh Hz).
  { unfold rmk. rewrite G2.
    exact (RttRunsA.rtt_seg1 (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx') (@fp_csr fx') mem (spZ regs0 - 112)
      ltac:(lia) ltac:(lia) STK). }
  { intros ms' (m' & _ & _ & _ & _ & _ & _ & _ & E). eexists _, _, _. exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  destruct HQ as (m1 & MU & WM & Z0 & Z8 & Z16 & Z24 & WR & E).
  ra_inj E R pc' mem1.
  assert (S1 : getr regs1 1 = Z_to_bv 64 0x1538c) by (rewrite HGr; reflexivity).
  assert (S2 : getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; reflexivity).
  assert (S4 : getr regs1 4 = getr regs0 4) by (rewrite HGr; exact G4).
  assert (S10 : getr regs1 10 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; reflexivity).
  assert (S11 : getr regs1 11 = Z_to_bv 64 0x102e8) by (rewrite HGr; reflexivity).
  assert (S12 : getr regs1 12 = Z_to_bv 64 0) by (rewrite HGr; reflexivity).
  assert (RR1 : rtt_regs regs0 regs1 copy (Z_to_bv 64 q) (Z_to_bv 64 pretty) (getr regs0 20) (getr regs0 21)).
  { split; [exact S2|].
    split; [rewrite HGr; exact G8|].
    split; [rewrite HGr; exact G9|].
    split; [rewrite HGr; exact G10|].
    split; [rewrite HGr; exact G19|].
    split; [rewrite HGr; exact G20|].
    split; [rewrite HGr; exact G21|].
    split; [rewrite HGr; exact G3|].
    split; [exact S4|].
    intros r Hr. rewrite HGr, <- (G22 r Hr).
    assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity. }
  destruct (@ra_write fx rc B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx' L A mem md
    [(q, wcap t (negb (pretty =? 0)))] Lam peak (cnt0 + wcalls t (negb (pretty =? 0))) (rtt_bw F b0 cnt0 t (negb (pretty =? 0)))
    q m1 (spZ regs0 - 112) (spZ regs0 - 112 + 32) ENT INV RT MU) as (INV1 & RT1).
  { rewrite HSEG. exact WM. }
  { lia. }
  { lia. }
  { lia. }
  { intros a Ha. rewrite HSEG. destruct WR as (_ & _ & W).
    replace a with (spZ regs0 - 112 + (a - (spZ regs0 - 112))) by lia. exact (W (a - (spZ regs0 - 112)) ltac:(lia)). }
  assert (HARN1 : rt_harn B L0 A0 L A m1 Lam (spZ regs0 - 112) 0 0 0 []).
  { apply (@ra_harn0 fx rc B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A m1 md _ Lam peak _ _
      INV1); rewrite HSEG; [exact Z0 | exact Z8 | exact Z16 | exact Z24 |].
    intros i Hi. destruct WR as (_ & _ & W). exact (W i ltac:(lia)). }
  assert (ROOM1 : 0 < 0 + 0 + 1 -> rf_room F (rtt_bw F b0 cnt0 t (negb (pretty =? 0))) (2 * (0 + 0 + 1))).
  { destruct ROOM as (_ & RTX & _). unfold rtt_ns in RTX. cbn [app tx_rooms] in RTX. exact (proj1 RTX). }
  eapply (@ra_put fx rc B API F HSEG FA TXP L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx' L A m1 md
    [(q, wcap t (negb (pretty =? 0)))] Lam peak (cnt0 + wcalls t (negb (pretty =? 0))) (rtt_bw F b0 cnt0 t (negb (pretty =? 0)))
    q 0 0 0 [] regs1 0x102e8 0 [] _ ENT INV1 RT1 HARN1 S2 S4).
  - rewrite S1. ra_ret.
  - exact S10.
  - exact S11.
  - exact S12.
  - lia.
  - lia.
  - lia.
  - intros i Hi. lia.
  - intros i Hi. cbn [length Z.of_nat] in Hi. lia.
  - reflexivity.
  - lia.
  - exact ROOM1.
  - intros L' A' regs' mem' md' want' cap' RP HCJ INV' RT' HARN'.
    assert (Ec : cap' = 2) by (rewrite HCJ; reflexivity). subst cap'.
    rewrite S1.
    apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx' L' A' regs' mem' md' Lam peak
      q want' ENT FL INV').
    + exact (@ra_regs_pres fx rc B API F HSEG FA regs0 regs1 regs' copy _ _ _ _ RR1 RP).
    + exact RT'.
    + exact HARN'.
Qed.

End S.
