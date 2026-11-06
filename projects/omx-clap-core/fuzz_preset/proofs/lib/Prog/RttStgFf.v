From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes TxCalls TxRet WriterSpec WriterValue PjWriteHyp round_trip_text_c RttDefs fuzz_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import RttGlue RttModel RttBase RttC_Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require RttRunsA strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

(* round_trip_text of the #102 plain twin c8f4d6b8, stage stg_ff_st (RttBase.v) at 0x14ea0, parse_noting's return with
   rc = 0 (fuzz_preset.c of #102 :692-693: the two frees now come BEFORE the rc and same tests).  RttRunsA.rtt_segF1
   (s4 := rc; jal free(want = s3)) and the allocator's free (free_contract_r at ms_free B), then RttRunsA.rtt_segF2
   (jal fuzz_free(text = s2)) and fuzz_free_c's contract; on to 0x14eb4 = stg_same_st with s4 = 0, s5 = 0x34e24. *)
Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis FREEF : forall fx' : YK11.FPState, @free_contract_r fx' rc B API F.
Hypothesis HFREE : ms_free B = 0x17798.
Hypothesis FF : forall fx' : YK11.FPState, @fuzz_free_contract fx' rc B API F.
Hypothesis NEXT : stg_same_st B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Theorem stg_ff_holds : stg_ff_st B API F.
Proof.
  unfold stg_ff_st.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A regs mem md Lam peak Db q want len cap.
  cbv zeta. intros ENT FL Ero Eoo INV RG G10z TXT HW0 HCAP WBLK HLEN HCAPF WIMG WNB WNL NODEb NEWb DbL LSZb NLb.
  set (p := negb (pretty =? 0)) in *.
  set (cnt := cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) in *.
  set (w := wcap t p) in *.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & _ & DNODE & DSUB & DOC0 & DOCS & _ & DEP & _ & COPY & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODED & RES & CP & _).
  pose proof RS as (MRc & WFc & BDc & _).
  pose proof RG as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  destruct TXT as (Hq0 & HqL & HqB & _ & _).
  pose proof alloc_ceiling_val as HCV.
  destruct rc_rttk as (HRK & HAS & _).
  assert (HERR : errno_addr B = strtod_c.STRTOD_ERRNO) by exact ERRB. unfold strtod_c.STRTOD_ERRNO in HERR.
  pose proof rc_stat_rng as HST. unfold GL_FAIL, GL_COUNT in HST.
  destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) q w MRc LED HqL)
    as (Hw0 & Hqblk & Hq1 & Hq2 & Hqimg).
  pose proof (rc_node_top _ _ _ _ _ _ DNODE) as (_ & DOCT).
  pose proof (rc_node_top _ _ _ _ _ _ NODEb) as (_ & BACKT).
  pose proof LED as (_ & _ & _ & _ & ND & _).
  pose proof (rc_nd_perm Lam (Db ++ [(q, w)]) Lam0 PERM ND) as NDX.
  assert (QDb : forall a k, In (a, k) Db -> a <> q).
  { intros a k Ha. rewrite map_app, <- app_assoc in NDX.
    apply (rc_disj Db ([(q, w)] ++ Lam0) a k q w); [exact NDX | exact Ha | left; reflexivity]. }
  assert (QL0 : forall a k, In (a, k) Lam0 -> a <> q).
  { intros a k Ha E. symmetry in E. revert E.
    apply (rc_disj (Db ++ [(q, w)]) Lam0 q w a k NDX); [apply in_or_app; right; left; reflexivity | exact Ha]. }
  assert (DL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (DSUB bk Hb). }
  assert (LAMOK : forall a k, In (a, k) Lam -> a - 16 <> want /\
      forall i, -16 <= i < k -> ~ (want <= a + i < want + cap)).
  { intros a k Hin. split; [exact (WNL a k Hin)|]. intros i Hi Hw.
    pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
    destruct (FB _ Hin) as (_ & Hblk & _ & _). cbn [fst snd] in Hblk.
    apply (blocks_apart B API HSEG AX FG L A mem md want cap (a - 16) (k + 16) (a + i) MRc WBLK Hblk
      (fun e => WNL a k Hin (eq_sym e)) Hw). lia. }
  destruct (rg_blk B API HSEG AX FG L A mem md want cap 0 MRc WBLK ltac:(lia)) as (_ & WR1 & WR2 & _).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  (* 0x14ea0: s4 := rc; mv a0, s3; jal free *)
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
  assert (Q1 : getr regs1 1 = Z_to_bv 64 0x14eac) by (rewrite HGr; reflexivity).
  assert (Q10 : getr regs1 10 = Z_to_bv 64 want) by (rewrite HGr; exact G19).
  assert (RG1 : rtt_regs regs0 regs1 copy (Z_to_bv 64 q) (Z_to_bv 64 want) (Z_to_bv 64 0) (Z_to_bv 64 0x34e24)).
  { split; [rewrite HGr; exact G2|].
    split; [rewrite HGr; exact G8|].
    split; [rewrite HGr; exact G9|].
    split; [rewrite HGr; exact G18|].
    split; [rewrite HGr; exact G19|].
    split; [rewrite HGr; exact G10z|].
    split; [rewrite HGr; exact G21|].
    split; [rewrite HGr; exact G3|].
    split; [rewrite HGr; exact G4|].
    intros r Hr. rewrite HGr, <- (G22 r Hr).
    assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity. }
  pose proof RG1 as (Q2 & _ & _ & _ & _ & _ & _ & _ & Q4 & _).
  assert (SP1 : spZ regs1 = spZ regs0 - 112) by (unfold spZ at 1; rewrite Q2; apply rc_uns; lia).
  destruct (rg_blk_in B API HSEG AX FG L A want cap WBLK) as (qq & Hqq & Eqq).
  pose proof (FREEF fx1) as FREE.
  replace (Z_to_bv 64 0x17798) with (Z_to_bv 64 (ms_free B)) by (rewrite HFREE; reflexivity).
  eapply SR_bind; [apply (FREE L A regs1 mem md qq cap (rtt_bp F b0 cnt0 t p)) |].
  { apply call_pre_k_alloc.
    apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem md regs1 ALLOC_STACK 112
      PRE0 RS INIT); [exact SP1 | rewrite SP1; Z.div_mod_to_equations; lia | rewrite Q4; reflexivity |
       rewrite Q1; rc_ret | lia | lia | lia]. }
  { exact (proj1 RD). }
  { exact Hqq. }
  { rewrite Q10, Eqq. reflexivity. }
  { exact RES. }
  intros c' (L' & A' & regs2 & mem2 & md2 & -> & CPOST & (bf1 & bf2 & EB1 & EB2) & BKEPT & RA2 & _ & _ & INITk & _ &
    RS2).
  rewrite Eqq in CPOST, EB1, BKEPT.
  pose proof CPOST as (MR2 & _ & _ & _ & _ & RR & _).
  assert (ST3 : rstep B API ALLOC_STACK (spZ regs1) (fun a => want <= a < want + cap) (fun a => a = want)
    L A mem md L' A' mem2 md2).
  { apply (rstep_of_call_post_k B API HSEG AX FG ALLOC_STACK L A regs1 mem md _ _ L' A' regs2 mem2 md2 MRc).
    - apply call_post_k_alloc. exact CPOST.
    - exact INITk.
    - intros a k Hin Hk Hne. rewrite EB2. rewrite EB1 in Hin. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; congruence | right; exact H].
    - intros a k i Hin Hne Hi _. exact (BKEPT a k i Hin Hne Hi). }
  rewrite SP1 in ST3.
  assert (INV2 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem2 md2
    (Db ++ [(q, w)]) Lam peak cnt (rf_free F (rtt_bp F b0 cnt0 t p) cap)).
  { apply (@inv_after fx rc B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md
      (Db ++ [(q, w)]) Lam peak cnt (rtt_bp F b0 cnt0 t p)
      ALLOC_STACK (fun a => want <= a < want + cap) (fun a => a = want) fx1 L' A' mem2 md2 (Db ++ [(q, w)]) Lam
      peak cnt (rf_free F (rtt_bp F b0 cnt0 t p) cap) ENT INV ST3).
    - lia.
    - lia.
    - intros a Ha. right. right. split; [lia|]. split.
      + replace a with (want + (a - want)) by lia. apply WIMG. lia.
      + intros b k Hb Hne Hbk.
        exact (blocks_apart B API HSEG AX FG L A mem md want cap b k a MRc WBLK Hb (fun e => Hne (eq_sym e)) Ha Hbk).
    - intros a Ha Hw. lia.
    - intros a k Hb Hk Ea. exact (WNB a k Hb Hk Ea).
    - intros a k Hin Hk. rewrite EB2. rewrite EB1 in Hin. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; lia | right; exact H].
    - exact RA2.
    - exact FRM.
    - intros r _. reflexivity.
    - apply (ledger_rstep B API HSEG AX FG ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap)
        (fun a => a = want) L A mem md L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) MRc LED ST3).
      + intros a Ha. pose proof (HST a Ha). split; [unfold rwin; rewrite HERR; lia|].
        intros Hw. apply (WIMG (a - want)); [lia|]. replace (want + (a - want)) with a by lia.
        exact (proj1 (statics_img B API HSEG AX FG a Ha)).
      + intros a k Hin. destruct (LAMOK a k Hin) as (H1 & H2). split; [exact H1 | exact H2].
    - lia.
    - exact PERM.
    - apply (pj_node_rstep B API HSEG AX FG ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap)
        (fun a => a = want) L A mem md L' A' mem2 md2 Lam Lam peak cnt (2 ^ 64 - 1) doc t D MRc LED
        NODED DL ST3); [lia | exact DOCT | | | exact (fun bk h => h)].
      + intros i Hi. split; [unfold rwin; rewrite HERR; lia | lia].
      + intros a k Hin. destruct (LAMOK a k (DL _ Hin)) as (H1 & H2). split; [exact H1|].
        intros i Hi. apply H2. lia.
    - exact RS2. }
  assert (NODEb2 : pj_node (ms_segs B) mem2 (lin Lam) (spZ regs0 - 112) t Db).
  { apply (pj_node_rstep B API HSEG AX FG ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap)
      (fun a => a = want) L A mem md L' A' mem2 md2 Lam Lam peak cnt (2 ^ 64 - 1) (spZ regs0 - 112) t Db MRc LED
      NODEb DbL ST3); [lia | exact BACKT | | | exact (fun bk h => h)].
    - intros i Hi. split; [unfold rwin; rewrite HERR; lia | lia].
    - intros a k Hin. destruct (LAMOK a k (DbL _ Hin)) as (H1 & H2). split; [exact H1|].
      intros i Hi. apply H2. lia. }
  pose proof (rc_pres regs0 regs1 regs2 copy _ _ _ _ RR RG1) as RG2.
  pose proof INV2 as (RSb & Zb & INITb & RDb & FRMb & FREGb & LEDb & PKb & PERMb & NODEc & RESb & CPb & _).
  pose proof RSb as (MRb & WFb & BDb & _).
  rewrite Q1.
  (* 0x14eac: mv a0, s2; jal fuzz_free *)
  destruct (kb_md B API L' A' mem2 md2 MR2) as (Hh2 & Hz2).
  eapply (rc_kA B API HSEG FA fx1 regs2 _ mem2 md2 _ _ Hh2 Hz2).
  { unfold rmk.
    exact (RttRunsA.rtt_segF2 (getr regs2 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6)
      (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13)
      (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19) (getr regs2 20)
      (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26) (getr regs2 27)
      (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31) fp_regs fp_csr mem2). }
  { intros ms' E. eexists _, _, _. exact E. }
  intros R3 pc3 mem3 regs3 HQ3 HGr3.
  rc_inj HQ3 R3 pc3 mem3.
  assert (T1 : getr regs3 1 = Z_to_bv 64 0x14eb4) by (rewrite HGr3; reflexivity).
  pose proof RG2 as (_ & _ & _ & T18 & _).
  assert (T10 : getr regs3 10 = Z_to_bv 64 q) by (rewrite HGr3; exact T18).
  assert (RP3 : regs_preserved regs2 regs3) by (intros r Hr; rewrite HGr3; revert r Hr; kb_saved).
  pose proof (rc_pres regs0 regs2 regs3 copy _ _ _ _ RP3 RG2) as RG3.
  pose proof RG3 as (U2 & _ & _ & _ & _ & _ & _ & _ & U4 & _).
  assert (SP3 : spZ regs3 = spZ regs0 - 112) by (unfold spZ at 1; rewrite U2; apply rc_uns; lia).
  assert (CPK : call_pre_k B (aa_MR API) ALLOC_STACK L' A' regs3 mem2 md2).
  { apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L' A' mem2 md2 regs3
      ALLOC_STACK 112 PRE0 RSb INITb); [exact SP3 | rewrite SP3; Z.div_mod_to_equations; lia | exact U4 |
      rewrite T1; rc_ret | lia | lia | lia]. }
  destruct (rc_lblk B API HSEG FA L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) q w MRb LEDb HqL)
    as (Hw0' & Hqblk' & Hq1' & Hq2' & Hqimg').
  eapply SR_bind; [exact (FF fx1 L' A' regs3 mem2 md2 q w (rf_free F (rtt_bp F b0 cnt0 t p) cap)
    Lam peak cnt (2 ^ 64 - 1) CPK T10 LEDb (proj1 RDb) (or_intror HqL) RESb)|].
  intros c4 (L'' & A'' & regs4 & mem4 & md4 & -> & RO4 & _ & IN4 & _ & CP4 & _ & KP & _ & Arms).
  destruct Arms as [(Hqz & _) | (_ & (b1 & b2 & EB3 & EB4) & (l1 & l2 & EL & LG4) & RS4)]; [lia|].
  pose proof CP4 as (M4 & _ & _ & _ & _ & RR4 & _).
  rewrite T1.
  assert (INL : forall a k, In (a, k) Lam -> a <> q -> In (a, k) (l1 ++ l2)).
  { intros a k Hin Hn. rewrite EL in Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; exfalso; apply Hn; congruence | right; exact H]. }
  assert (PERM4 : Permutation (l1 ++ l2) (Db ++ Lam0)).
  { assert (H : Permutation ((q, w) :: l1 ++ l2) ((q, w) :: Db ++ Lam0)).
    { apply (Permutation_trans (Permutation_middle l1 l2 (q, w))). rewrite <- EL.
      apply (Permutation_trans PERM). rewrite <- app_assoc. apply Permutation_sym. apply Permutation_middle. }
    exact (Permutation_cons_inv H). }
  assert (STEP4 : rstep B API ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16)
      L' A' mem2 md2 L'' A'' mem4 md4).
  { rewrite <- SP3. apply (rstep_of_call_post_k B API HSEG AX FG ALLOC_STACK L' A' regs3 mem2 md2 _ _ L'' A'' regs4 mem4 md4
      MRb CP4 IN4).
    - intros a k Hin Hk Hg. cbv beta in Hg. rewrite EB3 in Hin. rewrite EB4. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; exfalso; apply Hg; lia | right; exact H].
    - intros a k i Hin Hg Hi _. exact (KP a k i Hin Hg Hi). }
  assert (FWq : forall a k i, In (a, k) Lam -> a <> q -> 0 <= i < k -> ~ free_writes q w (a + i)).
  { intros a k i Hin Hn Hi [Hf|(_ & Hf)].
    - apply (rc_not_statics B API HSEG FA L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) a k i MRb LEDb Hin ltac:(lia)).
      unfold alloc_statics. left. exact Hf.
    - apply (rc_apart B API HSEG FA L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) a k q w (a + i) MRb LEDb Hin HqL Hn); lia. }
  assert (FWhi : forall x, alloc_ceiling <= x -> ~ free_writes q w x).
  { intros x Hx [Hf|(_ & Hf)]; [unfold G_LIVE in Hf; lia | lia]. }
  assert (RWhi : forall x, spZ regs0 - 112 <= x < 2 ^ 64 -> ~ rwin B ALLOC_STACK (spZ regs0 - 112) x).
  { intros x Hx [Hr|Hr]; [lia | rewrite HERR in Hr; lia]. }
  pose proof (rc_pres regs0 regs3 regs4 copy _ _ _ _ RR4 RG3) as RG4.
  apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L'' A'' regs4 mem4 md4 (l1 ++ l2) peak
    Db (Z_to_bv 64 q) (Z_to_bv 64 want) ENT FL Ero Eoo).
  - apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L' A' mem2 md2
      (Db ++ [(q, w)]) Lam peak cnt (rf_free F (rtt_bp F b0 cnt0 t p) cap) ALLOC_STACK
      (free_writes q w) (fun a => a = q - 16) fx1 L'' A'' mem4 md4 Db (l1 ++ l2) peak cnt (rtt_bf F b0 cnt0 t p)
      ENT INV2 STEP4); try lia.
    + intros a [Ha|(_ & Ha)].
      * left. unfold alloc_statics. left. exact Ha.
      * right. right. split; [lia|]. split.
        -- intros Hi. apply (Hqimg' (a - q) ltac:(lia)). replace (q + (a - q)) with a by lia. exact Hi.
        -- intros b k Hb Hg. cbv beta in Hg.
           exact (blocks_apart B API HSEG AX FG L' A' mem2 md2 (q - 16) (w + 16) b k a MRb Hqblk' Hb
             (fun E => Hg (eq_sym E)) ltac:(lia)).
    + intros a Ha Hf. exfalso. apply (FWhi a); [lia | exact Hf].
    + intros a k Hin Hk. exact (HqB a k Hin Hk).
    + intros a k Hin Hk. rewrite EB3 in Hin. rewrite EB4. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; lia | right; exact H].
    + exact RO4.
    + exact FRM.
    + intros r Hr. reflexivity.
    + exact LG4.
    + exact PERM4.
    + apply (rc_node_keep B API HSEG FA ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16)
        L' A' mem2 md2 L'' A'' mem4 md4 Lam (l1 ++ l2) peak cnt (2 ^ 64 - 1) doc t D MRb LEDb NODEc DL);
        [| exact STEP4 | lia | |].
      * intros [a k] Hb. apply INL; [exact (DL _ Hb) | exact (QL0 a k (DSUB _ Hb))].
      * intros i Hi. split; [apply RWhi; lia | apply FWhi; lia].
      * intros a k Hb. pose proof (QL0 a k (DSUB _ Hb)) as Hn. split; [cbv beta; lia|].
        intros i Hi. exact (FWq a k i (DL _ Hb) Hn Hi).
    + unfold rtt_bf. rewrite <- HCAPF. exact RS4.
  - exact RG4.
  - apply (rc_node_keep B API HSEG FA ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16)
      L' A' mem2 md2 L'' A'' mem4 md4 Lam (l1 ++ l2) peak cnt (2 ^ 64 - 1) (spZ regs0 - 112) t Db MRb LEDb NODEb2 DbL);
      [| exact STEP4 | lia | |].
    + intros [a k] Hb. apply INL; [exact (DbL _ Hb) | exact (QDb a k Hb)].
    + intros i Hi. split; [apply RWhi; lia | apply FWhi; lia].
    + intros a k Hb. pose proof (QDb a k Hb) as Hn. split; [cbv beta; lia|].
      intros i Hi. exact (FWq a k i (DbL _ Hb) Hn Hi).
  - exact NEWb.
  - intros [a k] Hb. apply INL; [exact (DbL _ Hb) | exact (QDb a k Hb)].
  - exact LSZb.
  - exact NLb.
Qed.

End S.
