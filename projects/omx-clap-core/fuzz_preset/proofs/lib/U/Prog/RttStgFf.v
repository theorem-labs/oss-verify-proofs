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

(* 0x1544c, round_trip_text (ubsan #102) after parse_noting returned rc = 0 with the read-back node at sp:
   s4 := rc and free (want) (rtt_segF1), fuzz_free (text) (rtt_segF2), on to stg_same's pre at 0x15460. *)

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
Hypothesis NEXT : stg_same_st B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Theorem stg_ff_holds : stg_ff_st B API F.
Proof.
  unfold stg_ff_st.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A regs mem md Lam peak Db q want len
    cap.
  cbv zeta. intros ENT FL HRO HOO INV REG G10z TXT HW0 HCAP WBLK HLEN HCAPF WIMG WNB WNL NODE NEW SUB LSZ NL.
  set (p := negb (pretty =? 0)) in *.
  set (cnt := cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) in *.
  set (w := wcap t p) in *.
  pose proof ENT as (REN & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & _ & _ & _ & _ & _ & LED & _ & PERM & _).
  pose proof RS as (MRc & _).
  pose proof REG as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  destruct TXT as (Hq0 & HqL & HqB & _ & _).
  pose proof alloc_ceiling_val as HCV.
  destruct rc_rttk as (HRK & HAS & _).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  pose proof LED as (_ & _ & _ & _ & ND & _).
  pose proof (rc_nd_perm Lam (Db ++ [(q, w)]) Lam0 PERM ND) as NDX.
  assert (QDb : forall a k, In (a, k) Db -> a <> q).
  { intros a k Ha. rewrite map_app, <- app_assoc in NDX.
    apply (rc_disj Db ([(q, w)] ++ Lam0) a k q w); [exact NDX | exact Ha | left; reflexivity]. }
  destruct (rg_blk B API HSEG AX FG L A mem md want cap 0 MRc WBLK ltac:(lia)) as (_ & WR1 & WR2 & _).
  assert (LAMOK : forall a k, In (a, k) Lam -> a - 16 <> want /\
      forall i, -16 <= i < k -> ~ (want <= a + i < want + cap)).
  { intros a k Hin. split; [exact (WNL a k Hin)|]. intros i Hi Hw.
    destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k MRc LED Hin) as (_ & Hblk & _).
    apply (blocks_apart B API HSEG AX FG L A mem md want cap (a - 16) (k + 16) (a + i) MRc WBLK Hblk
      (fun e => WNL a k Hin (eq_sym e)) Hw). lia. }
  (* 0x1544c: s4 := rc (0); a0 := want; jal free *)
  eapply (rc_kA B API HSEG FA fx1 regs _ mem md _ _ Hh Hz).
  { unfold rmk.
    exact (RttRunsA.rtt_segF1 (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
      (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
      (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
      (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
      (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  rc_inj HQ R pc' mem1.
  assert (R1 : getr regs1 1 = Z_to_bv 64 0x15458) by (rewrite HGr; reflexivity).
  assert (R2 : getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; exact G2).
  assert (R4 : getr regs1 4 = getr regs0 4) by (rewrite HGr; exact G4).
  assert (R10 : getr regs1 10 = Z_to_bv 64 want) by (rewrite HGr; exact G19).
  assert (REG1 : rtt_regs regs0 regs1 copy (Z_to_bv 64 q) (Z_to_bv 64 want) (Z_to_bv 64 0) (Z_to_bv 64 0x353d0)).
  { apply (rc_regs_run regs0 regs regs1 copy _ _ _ _ _ _ _ _ REG);
      [rewrite HGr; reflexivity | rewrite HGr; reflexivity | rewrite HGr; reflexivity |
       rewrite HGr; exact G18 | rewrite HGr; exact G19 | rewrite HGr; exact G10z | rewrite HGr; exact G21 |
       rewrite HGr; reflexivity | rewrite HGr; reflexivity | rc_hi HGr]. }
  apply (rc_free_want B API F HSEG FA HFREE FREEF L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ENT
    fx1 L A regs1 mem md (Db ++ [(q, w)]) Lam peak cnt (rtt_bp F b0 cnt0 t p) want cap _ INV R2 R4
    ltac:(rewrite R1; rc_ret) R10 HW0 HCAP WBLK WIMG WNB WNL).
  intros L2 A2 regs2 mem2 md2 INV2 RR2 ST2.
  rewrite R1.
  pose proof (rc_pres regs0 regs1 regs2 copy _ _ _ _ RR2 REG1) as REG2.
  pose proof REG2 as (G2b & _ & _ & G18b & _ & _ & _ & _ & G4b & _).
  assert (NODE2 : pj_node (ms_segs B) mem2 (lin Lam) (spZ regs0 - 112) t Db).
  { apply (rc_node_keep B API HSEG FA ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap)
      (fun a => a = want) L A mem md L2 A2 mem2 md2 Lam Lam peak cnt (2 ^ 64 - 1) (spZ regs0 - 112) t Db MRc LED NODE
      SUB SUB ST2); [lia | |].
    - intros i Hi. split; [unfold rwin; rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia | lia].
    - intros a k Hb. destruct (LAMOK a k (SUB _ Hb)) as (H1 & H2). split; [exact H1|].
      intros i Hi. apply H2. lia. }
  pose proof INV2 as (RS2 & _ & _ & _ & _ & _ & LED2 & _).
  pose proof RS2 as (MR2 & _).
  destruct (kb_md B API L2 A2 mem2 md2 MR2) as (Hh2 & Hz2).
  (* 0x15458: a0 := text; jal fuzz_free *)
  eapply (rc_kA B API HSEG FA fx1 regs2 _ mem2 md2 _ _ Hh2 Hz2).
  { unfold rmk.
    exact (RttRunsA.rtt_segF2 (getr regs2 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 5)
      (getr regs2 6) (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12)
      (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19)
      (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26)
      (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31) fp_regs fp_csr mem2). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R pc' mem3 regs3 HQ HGr3.
  rc_inj HQ R pc' mem3.
  assert (R1c : getr regs3 1 = Z_to_bv 64 0x15460) by (rewrite HGr3; reflexivity).
  assert (R2c : getr regs3 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr3; exact G2b).
  assert (R4c : getr regs3 4 = getr regs0 4) by (rewrite HGr3; exact G4b).
  assert (R10c : getr regs3 10 = Z_to_bv 64 q) by (rewrite HGr3; exact G18b).
  assert (REG3 : rtt_regs regs0 regs3 copy (Z_to_bv 64 q) (Z_to_bv 64 want) (Z_to_bv 64 0) (Z_to_bv 64 0x353d0)).
  { apply (rc_pres regs0 regs2 regs3 copy _ _ _ _); [intros r Hr; rewrite HGr3; revert r Hr; kb_saved | exact REG2]. }
  apply (rc_ffree_text B API F HSEG FA FF L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ENT
    fx1 L2 A2 regs3 mem2 md2 Db Lam peak cnt (rf_free F (rtt_bp F b0 cnt0 t p) cap) q w _ INV2 R2c R4c
    ltac:(rewrite R1c; rc_ret) R10c Hq0 HqL HqB).
  intros L4 A4 regs4 mem4 md4 Lam4 INV4 RR4 INL ST4.
  rewrite R1c.
  pose proof (rc_pres regs0 regs3 regs4 copy _ _ _ _ RR4 REG3) as REG4.
  rewrite HCAPF in INV4.
  apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L4 A4 regs4 mem4 md4 Lam4 peak Db
    (Z_to_bv 64 q) (Z_to_bv 64 want) ENT FL HRO HOO INV4 REG4).
  - apply (rc_node_keep B API HSEG FA ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16)
      L2 A2 mem2 md2 L4 A4 mem4 md4 Lam Lam4 peak cnt (2 ^ 64 - 1) (spZ regs0 - 112) t Db MR2 LED2 NODE2 SUB);
      [| exact ST4 | lia | |].
    + intros [a k] Hb. apply INL; [exact (SUB _ Hb) | exact (QDb a k Hb)].
    + intros i Hi. split.
      * unfold rwin. intros [Hr|Hr]; [lia | rewrite ERRB in Hr; unfold strtod_c.STRTOD_ERRNO in Hr; lia].
      * intros [Hf|(_ & Hf)]; [unfold G_LIVE in Hf; lia|].
        destruct (rc_lblk B API HSEG FA L2 A2 mem2 md2 Lam peak cnt (2 ^ 64 - 1) q w MR2 LED2 HqL) as (_ & _ & _ & Hq2 & _).
        lia.
    + intros a k Hb. pose proof (QDb a k Hb) as Hn. split; [cbv beta; lia|].
      intros i Hi [Hf|(_ & Hf)].
      * apply (rc_not_statics B API HSEG FA L2 A2 mem2 md2 Lam peak cnt (2 ^ 64 - 1) a k i MR2 LED2 (SUB _ Hb)
          ltac:(lia)).
        unfold alloc_statics. left. exact Hf.
      * apply (rc_apart B API HSEG FA L2 A2 mem2 md2 Lam peak cnt (2 ^ 64 - 1) a k q w (a + i) MR2 LED2 (SUB _ Hb) HqL
          Hn); lia.
  - exact NEW.
  - intros [a k] Hb. apply INL; [exact (SUB _ Hb) | exact (QDb a k Hb)].
  - exact LSZ.
  - exact NL.
Qed.

End S.
