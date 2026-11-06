From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YH03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes TxCalls TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PjWriteHyp round_trip_text_c RttDefs fuzz_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import RttGlue RttModel RttBase RttC_Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require RttRunsA strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

(* 0x153e4, the ran-out arm of round_trip_text (ubsan #102): one of the entry flag bytes g_ran_out / g_own_ran_out
   is nonzero.  free (want) (rtt_segO1), fuzz_free (text) (rtt_segO2), s2 := 1 and the epilogue (rtt_seg8o): the
   call returns a0 = 1 with the contract's left arm (both flag bytes kept, the ledger of the write, *copy untouched). *)

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis HFREE : ms_free B = YH03.src0_A_free.
Hypothesis FREEF : forall fx' : YK11.FPState, @free_contract_r fx' rc B API F.
Hypothesis FF : forall fx' : YK11.FPState, @fuzz_free_contract fx' rc B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Theorem stg_oom_holds : stg_oom_st B API F.
Proof.
  unfold stg_oom_st.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A regs mem md Lam peak q want len cap
    s4v s5v.
  cbv zeta. intros ENT FL HRO INV REG TXT HW0 HCAP WBLK HLEN HCAPF WIMG WNB WNL.
  set (p := negb (pretty =? 0)) in *.
  pose proof ENT as (REN & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & _).
  pose proof RS as (MRc & _).
  pose proof REG as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  destruct TXT as (Hq0 & HqL & HqB & _ & _).
  pose proof alloc_ceiling_val as HCV.
  destruct rc_rttk as (HRK & HAS & _).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  (* 0x153e4: a0 := want; jal free *)
  eapply (rc_kA B API HSEG FA fx1 regs _ mem md _ _ Hh Hz).
  { unfold rmk.
    exact (RttRunsA.rtt_segO1 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
      (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
      (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
      (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
      (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  rc_inj HQ R pc' mem1.
  assert (R1 : getr regs1 1 = Z_to_bv 64 0x153ec) by (rewrite HGr; reflexivity).
  assert (R2 : getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; exact G2).
  assert (R4 : getr regs1 4 = getr regs0 4) by (rewrite HGr; exact G4).
  assert (R10 : getr regs1 10 = Z_to_bv 64 want) by (rewrite HGr; exact G19).
  assert (REG1 : rtt_regs regs0 regs1 copy (Z_to_bv 64 q) (Z_to_bv 64 want) s4v s5v).
  { apply (rc_pres regs0 regs regs1 copy _ _ _ _); [intros r Hr; rewrite HGr; revert r Hr; kb_saved | exact REG]. }
  apply (rc_free_want B API F HSEG FA HFREE FREEF L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ENT
    fx1 L A regs1 mem md [(q, wcap t p)] Lam peak (cnt0 + wcalls t p) (rtt_bt F b0 cnt0 t p) want cap _ INV R2 R4
    ltac:(rewrite R1; rc_ret) R10 HW0 HCAP WBLK WIMG WNB WNL).
  intros L2 A2 regs2 mem2 md2 INV2 RR2 _.
  rewrite R1.
  pose proof (rc_pres regs0 regs1 regs2 copy _ _ _ _ RR2 REG1) as REG2.
  pose proof REG2 as (G2b & _ & _ & G18b & _ & _ & _ & _ & G4b & _).
  pose proof INV2 as (RS2 & _). pose proof RS2 as (MR2 & _).
  destruct (kb_md B API L2 A2 mem2 md2 MR2) as (Hh2 & Hz2).
  (* 0x153ec: a0 := text; jal fuzz_free *)
  eapply (rc_kA B API HSEG FA fx1 regs2 _ mem2 md2 _ _ Hh2 Hz2).
  { unfold rmk.
    exact (RttRunsA.rtt_segO2 (getr regs2 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 5)
      (getr regs2 6) (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12)
      (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19)
      (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26)
      (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31) fp_regs fp_csr mem2). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem3 regs3 HQ HGr3.
  rc_inj HQ R pc' mem3.
  assert (R1c : getr regs3 1 = Z_to_bv 64 0x153f4) by (rewrite HGr3; reflexivity).
  assert (R2c : getr regs3 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr3; exact G2b).
  assert (R4c : getr regs3 4 = getr regs0 4) by (rewrite HGr3; exact G4b).
  assert (R10c : getr regs3 10 = Z_to_bv 64 q) by (rewrite HGr3; exact G18b).
  assert (REG3 : rtt_regs regs0 regs3 copy (Z_to_bv 64 q) (Z_to_bv 64 want) s4v s5v).
  { apply (rc_pres regs0 regs2 regs3 copy _ _ _ _); [intros r Hr; rewrite HGr3; revert r Hr; kb_saved | exact REG2]. }
  apply (rc_ffree_text B API F HSEG FA FF L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ENT
    fx1 L2 A2 regs3 mem2 md2 [] Lam peak (cnt0 + wcalls t p) (rf_free F (rtt_bt F b0 cnt0 t p) cap) q (wcap t p) _
    INV2 R2c R4c ltac:(rewrite R1c; rc_ret) R10c Hq0 HqL HqB).
  intros L4 A4 regs4 mem4 md4 Lam4 INV4 RR4 _ _.
  rewrite R1c.
  pose proof (rc_pres regs0 regs3 regs4 copy _ _ _ _ RR4 REG3) as REG4.
  pose proof REG4 as (G2d & _).
  pose proof INV4 as (RS4 & Z4 & _ & RD4 & FRM4 & FREG4 & LED4 & PK4 & PERM4 & NODE4 & RES4 & _ &
    SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & _).
  pose proof RS4 as (MR4 & _).
  destruct (kb_md B API L4 A4 mem4 md4 MR4) as (Hh4 & Hz4).
  assert (K1 : LMem.bytes_at rsegs mem4 (spZ regs0 - 112 + 104) (LMem.le8 (getr regs0 1)))
    by (rewrite <- HSEG; apply (rc_slot _ _ (spZ regs0 - 8)); [lia | exact SL8]).
  assert (K2 : LMem.bytes_at rsegs mem4 (spZ regs0 - 112 + 96) (LMem.le8 (getr regs0 8)))
    by (rewrite <- HSEG; apply (rc_slot _ _ (spZ regs0 - 16)); [lia | exact SL16]).
  assert (K3 : LMem.bytes_at rsegs mem4 (spZ regs0 - 112 + 88) (LMem.le8 (getr regs0 9)))
    by (rewrite <- HSEG; apply (rc_slot _ _ (spZ regs0 - 24)); [lia | exact SL24]).
  assert (K4 : LMem.bytes_at rsegs mem4 (spZ regs0 - 112 + 80) (LMem.le8 (getr regs0 18)))
    by (rewrite <- HSEG; apply (rc_slot _ _ (spZ regs0 - 32)); [lia | exact SL32]).
  assert (K5 : LMem.bytes_at rsegs mem4 (spZ regs0 - 112 + 72) (LMem.le8 (getr regs0 19)))
    by (rewrite <- HSEG; apply (rc_slot _ _ (spZ regs0 - 40)); [lia | exact SL40]).
  assert (K6 : LMem.bytes_at rsegs mem4 (spZ regs0 - 112 + 64) (LMem.le8 (getr regs0 20)))
    by (rewrite <- HSEG; apply (rc_slot _ _ (spZ regs0 - 48)); [lia | exact SL48]).
  assert (K7 : LMem.bytes_at rsegs mem4 (spZ regs0 - 112 + 56) (LMem.le8 (getr regs0 21)))
    by (rewrite <- HSEG; apply (rc_slot _ _ (spZ regs0 - 56)); [lia | exact SL56]).
  (* 0x153f4: s2 := 1; a0 := s2; the epilogue; ret *)
  eapply (rc_kA B API HSEG FA fx1 regs4 _ mem4 md4 _ _ Hh4 Hz4).
  { unfold rmk. rewrite G2d.
    exact (RttRunsA.rtt_seg8o (getr regs4 1) (getr regs4 3) (getr regs4 4) (getr regs4 5) (getr regs4 6)
      (getr regs4 7) (getr regs4 8) (getr regs4 9) (getr regs4 10) (getr regs4 11) (getr regs4 12) (getr regs4 13)
      (getr regs4 14) (getr regs4 15) (getr regs4 16) (getr regs4 17) (getr regs4 18) (getr regs4 19)
      (getr regs4 20) (getr regs4 21) (getr regs4 22) (getr regs4 23) (getr regs4 24) (getr regs4 25)
      (getr regs4 26) (getr regs4 27) (getr regs4 28) (getr regs4 29) (getr regs4 30) (getr regs4 31)
      fp_regs fp_csr mem4 (spZ regs0 - 112) (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18)
      (getr regs0 19) (getr regs0 20) (getr regs0 21) ltac:(lia) ltac:(lia) K1 K2 K3 K4 K5 K6 K7). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem5 regs5 HQ HGr5.
  rc_inj HQ R pc' mem5.
  apply SR_ret. rewrite (kb_ret_pc _ RA0).
  replace (spZ regs0 - 112 + 112) with (spZ regs0) in HGr5 by lia.
  pose proof (rc_ret_pres regs0 regs4 regs5 copy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REG4 HGr5) as RPF.
  destruct (rc_fin B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ENT fx1 L4 A4 mem4 md4
    Lam4 peak (cnt0 + wcalls t p) _ INV4) as (RSC & CPY).
  destruct (rtt_fl_inv B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L4 A4 mem4
    md4 [] Lam4 peak (cnt0 + wcalls t p) _ ENT INV4 FL) as (_ & _ & FRO & FOO).
  rewrite HCAPF in RES4.
  unfold rtt_post. cbv zeta.
  exists fx1, L4, A4, regs5, mem4, md4, Lam4, peak.
  split; [reflexivity|]. split; [exact FRM4|]. split; [exact FREG4|].
  split; [exact (rtt_rel_of_rstep B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes copy) L4 A4 regs5 mem4 md4
    RSC RPF Z4)|].
  split; [exact RD4|]. split; [exact FRO|]. split; [exact FOO|].
  left. split; [exact HRO|]. split; [rewrite HGr5; reflexivity|].
  split; [exact LED4|]. split; [exact PK4|]. split; [exact NODE4|]. split; [exact PERM4|].
  split; [exact RES4 | exact CPY].
Qed.

End S.
