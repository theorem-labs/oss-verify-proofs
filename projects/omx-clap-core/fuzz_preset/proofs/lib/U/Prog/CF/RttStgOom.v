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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import PjWriteHyp round_trip_text_c fuzz_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import RttGlue RttModel RttBase RttC_Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require RttRunsA strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* round_trip_text's ran-out arm (#102 ubsan twin, CF form), stg_oom_st of RttBase at 0x153e4: a flag byte was
   nonzero at the first out_of_memory() test (fuzz_preset.c:675).  The runs are the U twins of lib/U/Prog/RttRunsA.v:
   rtt_segO1 (jal free (want = s3), ra 0x153ec), rtt_segO2 (jal fuzz_free (text = s2), ra 0x153f4) and rtt_seg8o
   (s2 := 1; a0 := s2; ld ra s0 .. s5 from [S - 56, S); sp += 0x70; ret).  The post is the contract's left arm: a0 = 1,
   the ledger list back to Lam0 (up to permutation), the resource rtt_bo, both flag bytes and *copy unchanged.
   free is ms_free B = 0x18250 (the new twin's symtab; lib/U/FrameAPI.v frame_ubsan states the same value). *)

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis FREEF : forall fx' : YK11.FPState, @free_contract_r fx' rc B API F.
Hypothesis HFREE : ms_free B = 0x18250.
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
  cbv zeta. intros ENT FL RO INV REG TXT HW0 HCAP WBLK HLEN HCAPF WIMG WNB WNL.
  set (p := negb (pretty =? 0)) in *.
  set (cnt := cnt0 + wcalls t p) in *.
  set (w := wcap t p) in *.
  pose proof ENT as (REN & INIT0 & LED0 & CNT0 & RES0 & G10d & G11p & G12c & PR & DNODE & DSUB & DOC0 & DOCS & WF &
    DEP & WLEN & COPY & ROOM).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODED & RES & CP & _).
  pose proof RS as (MRc & WFc & BDc & _).
  pose proof REG as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  pose proof TXT as (Hq0 & HqL & HqB & _ & _).
  pose proof alloc_ceiling_val as HCV.
  assert (HAS : ALLOC_STACK = 8192) by reflexivity.
  assert (HRK : 112 + ALLOC_STACK <= RTT_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (HERRc : errno_addr B + 4 <= alloc_ceiling) by (rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia).
  (* the alloc.c words (LedgerCells' GL_ cells) lie below the ceiling and away from errno *)
  assert (HSE : forall a, alloc_statics a -> ~ (errno_addr B <= a < errno_addr B + 4) /\ a < alloc_ceiling).
  { intros a Ha. rewrite ERRB. unfold strtod_c.STRTOD_ERRNO.
    unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, GL_LIVE, GL_PEAK, GL_COUNT, GL_FAIL in Ha. lia. }
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  destruct (rg_blk B API HSEG AX FG L A mem md want cap 0 MRc WBLK ltac:(lia)) as (_ & WR1 & WR2 & _).
  pose proof (rc_node_top _ _ _ _ _ _ DNODE) as (_ & DOCT).
  assert (DL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (DSUB bk Hb). }
  assert (LAMOK : forall a k, In (a, k) Lam -> a - 16 <> want /\
      forall i, -16 <= i < k -> ~ (want <= a + i < want + cap)).
  { intros a k Hin. split; [exact (WNL a k Hin)|]. intros i Hi Hw.
    pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
    destruct (FB _ Hin) as (_ & Hblk & _ & _). cbn [fst snd] in Hblk.
    apply (blocks_apart B API HSEG AX FG L A mem md want cap (a - 16) (k + 16) (a + i) MRc WBLK Hblk
      (fun e => WNL a k Hin (eq_sym e)) Hw). lia. }
  assert (QL0 : forall a k, In (a, k) Lam0 -> a <> q).
  { pose proof LED as (_ & _ & _ & _ & ND & _).
    pose proof (rc_nd_perm Lam [(q, w)] Lam0 PERM ND) as NDX.
    intros a k Ha E. symmetry in E. revert E.
    apply (rc_disj [(q, w)] Lam0 q w a k NDX); [left; reflexivity | exact Ha]. }
  (* 0x153e4: jal free (want = s3) *)
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
  assert (R2 : getr regs1 2 = getr regs 2) by (rewrite HGr; reflexivity).
  assert (R4 : getr regs1 4 = getr regs0 4) by (rewrite HGr; exact G4).
  assert (R10 : getr regs1 10 = Z_to_bv 64 want) by (rewrite HGr; exact G19).
  assert (RP1 : regs_preserved regs regs1) by (intros r Hr; rewrite HGr; revert r Hr; kb_saved).
  assert (SP1 : spZ regs1 = spZ regs0 - 112) by (unfold spZ at 1; rewrite R2, G2; apply rc_uns; lia).
  pose proof (rc_pres regs0 regs regs1 copy (Z_to_bv 64 q) (Z_to_bv 64 want) s4v s5v RP1 REG) as REG1.
  assert (CPK1 : call_pre_k B (aa_MR API) ALLOC_STACK L A regs1 mem md).
  { apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem md regs1
      ALLOC_STACK 112 PRE0 RS INIT); [exact SP1 | rewrite SP1; Z.div_mod_to_equations; lia | exact R4 |
      rewrite R1; rc_ret | lia | lia | lia]. }
  destruct (rg_blk_in B API HSEG AX FG L A want cap WBLK) as (qq & Hqq & Eqq).
  replace (Z_to_bv 64 0x18250) with (Z_to_bv 64 (ms_free B)) by (rewrite HFREE; reflexivity).
  eapply SR_bind; [apply (FREEF fx1 L A regs1 mem md qq cap (rtt_bt F b0 cnt0 t p)) |].
  - apply call_pre_k_alloc. exact CPK1.
  - exact (proj1 RD).
  - exact Hqq.
  - rewrite R10, Eqq. reflexivity.
  - exact RES.
  - intros c' (L' & A' & regs2 & mem2 & md2 & -> & CPOST & (b1 & b2 & EB1 & EB2) & BKEPT & RA2 & _ & _ & INITk & _ &
      RS2).
    rewrite Eqq in CPOST, EB1, BKEPT.
    pose proof CPOST as (MR2 & _ & _ & _ & _ & RR2 & _).
    assert (ST2 : rstep B API ALLOC_STACK (spZ regs1) (fun a => want <= a < want + cap) (fun a => a = want)
      L A mem md L' A' mem2 md2).
    { apply (rstep_of_call_post_k B API HSEG AX FG ALLOC_STACK L A regs1 mem md _ _ L' A' regs2 mem2 md2 MRc).
      - apply call_post_k_alloc. exact CPOST.
      - exact INITk.
      - intros a k Hin Hk Hne. rewrite EB2. rewrite EB1 in Hin. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; congruence | right; exact H].
      - intros a k i Hin Hne Hi _. exact (BKEPT a k i Hin Hne Hi). }
    rewrite SP1 in ST2.
    assert (INV2 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem2 md2
      [(q, w)] Lam peak cnt (rf_free F (rtt_bt F b0 cnt0 t p) cap)).
    { apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md
        [(q, w)] Lam peak cnt (rtt_bt F b0 cnt0 t p) ALLOC_STACK (fun a => want <= a < want + cap) (fun a => a = want)
        fx1 L' A' mem2 md2 [(q, w)] Lam peak cnt (rf_free F (rtt_bt F b0 cnt0 t p) cap) ENT INV ST2).
      - lia.
      - lia.
      - intros a Ha. cbv beta in Ha. right. right. split; [lia|]. split.
        + replace a with (want + (a - want)) by lia. apply WIMG. lia.
        + intros b k Hb Hne Hbk.
          exact (blocks_apart B API HSEG AX FG L A mem md want cap b k a MRc WBLK Hb (fun e => Hne (eq_sym e)) Ha Hbk).
      - intros a Ha Hw. cbv beta in Hw. lia.
      - intros a k Hb Hk Ea. exact (WNB a k Hb Hk Ea).
      - intros a k Hin Hk. rewrite EB2. rewrite EB1 in Hin. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; lia | right; exact H].
      - exact RA2.
      - exact FRM.
      - intros r _. reflexivity.
      - apply (ledger_rstep B API HSEG AX FG ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap)
          (fun a => a = want) L A mem md L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) MRc LED ST2).
        + intros a Ha. destruct (HSE a Ha) as (He & Hc). split; [unfold rwin; lia|].
          intros Hw. apply (WIMG (a - want)); [lia|]. replace (want + (a - want)) with a by lia.
          exact (proj1 (statics_img B API HSEG AX FG a Ha)).
        + intros a k Hin. destruct (LAMOK a k Hin) as (H1 & H2). split; [exact H1 | exact H2].
      - lia.
      - exact PERM.
      - apply (pj_node_rstep B API HSEG AX FG ALLOC_STACK (spZ regs0 - 112) (fun a => want <= a < want + cap)
          (fun a => a = want) L A mem md L' A' mem2 md2 Lam Lam peak cnt (2 ^ 64 - 1) doc t D MRc LED NODED DL ST2);
          [lia | exact DOCT | | | exact (fun bk h => h)].
        + intros i Hi. split; [unfold rwin; lia | lia].
        + intros a k Hin. destruct (LAMOK a k (DL _ Hin)) as (H1 & H2). split; [exact H1|].
          intros i Hi. apply H2. lia.
      - exact RS2. }
    pose proof INV2 as (RS2' & Z2 & INIT2 & RD2 & _ & _ & LED2 & _ & _ & NODE2 & RES2 & _).
    pose proof (rc_pres regs0 regs1 regs2 copy (Z_to_bv 64 q) (Z_to_bv 64 want) s4v s5v RR2 REG1) as REG2.
    pose proof REG2 as (H2 & _ & _ & H18 & _ & _ & _ & _ & H4 & _).
    destruct (kb_md B API L' A' mem2 md2 MR2) as (Hh2 & Hz2).
    destruct (rc_lblk B API HSEG FA L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) q w MR2 LED2 HqL)
      as (Hw0 & Hqblk & Hq1 & Hq2 & Hqimg).
    rewrite R1.
    (* 0x153ec: jal fuzz_free (text = s2) *)
    eapply (rc_kA B API HSEG FA fx1 regs2 _ mem2 md2 _ _ Hh2 Hz2).
    { unfold rmk.
      exact (RttRunsA.rtt_segO2 (getr regs2 1) (getr regs2 2) (getr regs2 3) (getr regs2 4) (getr regs2 5)
        (getr regs2 6) (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12)
        (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18)
        (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
        (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30)
        (getr regs2 31) fp_regs fp_csr mem2). }
    { intros ms' E. eexists _, _, _. exact E. }
    intros R pc' mem3 regs3 HQ HGr3.
    rc_inj HQ R pc' mem3.
    assert (R31 : getr regs3 1 = Z_to_bv 64 0x153f4) by (rewrite HGr3; reflexivity).
    assert (R32 : getr regs3 2 = getr regs2 2) by (rewrite HGr3; reflexivity).
    assert (R34 : getr regs3 4 = getr regs0 4) by (rewrite HGr3; exact H4).
    assert (R310 : getr regs3 10 = Z_to_bv 64 q) by (rewrite HGr3; exact H18).
    assert (RP3 : regs_preserved regs2 regs3) by (intros r Hr; rewrite HGr3; revert r Hr; kb_saved).
    assert (SP3 : spZ regs3 = spZ regs0 - 112) by (unfold spZ at 1; rewrite R32, H2; apply rc_uns; lia).
    assert (CPK3 : call_pre_k B (aa_MR API) ALLOC_STACK L' A' regs3 mem2 md2).
    { apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L' A' mem2 md2 regs3
        ALLOC_STACK 112 PRE0 RS2' INIT2); [exact SP3 | rewrite SP3; Z.div_mod_to_equations; lia | exact R34 |
        rewrite R31; rc_ret | lia | lia | lia]. }
    eapply SR_bind; [exact (FF fx1 L' A' regs3 mem2 md2 q w (rf_free F (rtt_bt F b0 cnt0 t p) cap)
      Lam peak cnt (2 ^ 64 - 1) CPK3 R310 LED2 (proj1 RD2) (or_intror HqL) RES2)|].
    intros c' (L'' & A'' & regs4 & mem4 & md4 & -> & RO4 & _ & IN4 & _ & CP4 & _ & KP & _ & Arms).
    destruct Arms as [(Hqz & _) | (_ & (b3 & b4 & EB3 & EB4) & (l1 & l2 & EL & LG4) & RS4)]; [lia|].
    pose proof CP4 as (M4 & _ & _ & _ & _ & RR4 & _).
    rewrite R31.
    assert (INL : forall a k, In (a, k) Lam -> a <> q -> In (a, k) (l1 ++ l2)).
    { intros a k Hin Hn. rewrite EL in Hin. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; exfalso; apply Hn; congruence | right; exact H]. }
    assert (PERM4 : Permutation (l1 ++ l2) ([] ++ Lam0)).
    { assert (H : Permutation ((q, w) :: l1 ++ l2) ((q, w) :: Lam0)).
      { apply (Permutation_trans (Permutation_middle l1 l2 (q, w))). rewrite <- EL. exact PERM. }
      exact (Permutation_cons_inv H). }
    assert (STEP4 : rstep B API ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16)
        L' A' mem2 md2 L'' A'' mem4 md4).
    { rewrite <- SP3.
      apply (rstep_of_call_post_k B API HSEG AX FG ALLOC_STACK L' A' regs3 mem2 md2 _ _ L'' A'' regs4 mem4 md4
        MR2 CP4 IN4).
      - intros a k Hin Hk Hg. cbv beta in Hg. rewrite EB3 in Hin. rewrite EB4. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; exfalso; apply Hg; lia | right; exact H].
      - intros a k i Hin Hg Hi _. exact (KP a k i Hin Hg Hi). }
    assert (FWq : forall a k i, In (a, k) Lam -> a <> q -> 0 <= i < k -> ~ free_writes q w (a + i)).
    { intros a k i Hin Hn Hi [Hf|(_ & Hf)].
      - apply (rc_not_statics B API HSEG FA L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) a k i MR2 LED2 Hin ltac:(lia)).
        unfold alloc_statics. left. exact Hf.
      - apply (rc_apart B API HSEG FA L' A' mem2 md2 Lam peak cnt (2 ^ 64 - 1) a k q w (a + i) MR2 LED2 Hin HqL Hn); lia. }
    assert (FWhi : forall x, alloc_ceiling <= x -> ~ free_writes q w x).
    { intros x Hx [Hf|(_ & Hf)]; [|lia].
      assert (Hs : alloc_statics x) by (unfold alloc_statics; left; exact Hf).
      pose proof (proj2 (HSE x Hs)). lia. }
    assert (RWhi : forall x, spZ regs0 - 112 <= x < 2 ^ 64 -> ~ rwin B ALLOC_STACK (spZ regs0 - 112) x).
    { intros x Hx [Hr|Hr]; lia. }
    assert (INV4 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L'' A'' mem4 md4
        [] (l1 ++ l2) peak cnt (rtt_bo F b0 cnt0 t p)).
    { apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L' A' mem2 md2
        [(q, w)] Lam peak cnt (rf_free F (rtt_bt F b0 cnt0 t p) cap) ALLOC_STACK (free_writes q w)
        (fun a => a = q - 16) fx1 L'' A'' mem4 md4 [] (l1 ++ l2) peak cnt (rtt_bo F b0 cnt0 t p) ENT INV2 STEP4).
      - lia.
      - lia.
      - intros a [Ha|(_ & Ha)].
        + left. unfold alloc_statics. left. exact Ha.
        + right. right. split; [lia|]. split.
          * intros Hi. apply (Hqimg (a - q) ltac:(lia)). replace (q + (a - q)) with a by lia. exact Hi.
          * intros b k Hb Hg. cbv beta in Hg.
            exact (blocks_apart B API HSEG AX FG L' A' mem2 md2 (q - 16) (w + 16) b k a MR2 Hqblk Hb
              (fun E => Hg (eq_sym E)) ltac:(lia)).
      - intros a Ha Hf. exfalso. apply (FWhi a); [lia | exact Hf].
      - intros a k Hin Hk. exact (HqB a k Hin Hk).
      - intros a k Hin Hk. rewrite EB3 in Hin. rewrite EB4. apply in_app_or in Hin. apply in_or_app.
        destruct Hin as [H|[H|H]]; [left; exact H | injection H as E1 E2; lia | right; exact H].
      - exact RO4.
      - exact FRM.
      - intros r _. reflexivity.
      - exact LG4.
      - lia.
      - exact PERM4.
      - apply (rc_node_keep B API HSEG FA ALLOC_STACK (spZ regs0 - 112) (free_writes q w) (fun a => a = q - 16)
          L' A' mem2 md2 L'' A'' mem4 md4 Lam (l1 ++ l2) peak cnt (2 ^ 64 - 1) doc t D MR2 LED2 NODE2 DL);
          [| exact STEP4 | lia | |].
        + intros [a k] Hb. apply INL; [exact (DL _ Hb) | exact (QL0 a k (DSUB _ Hb))].
        + intros i Hi. split; [apply RWhi; lia | apply FWhi; lia].
        + intros a k Hb. pose proof (QL0 a k (DSUB _ Hb)) as Hn. split; [cbv beta; lia|].
          intros i Hi. exact (FWq a k i (DL _ Hb) Hn Hi).
      - unfold rtt_bo. rewrite <- HCAPF. exact RS4. }
    pose proof INV4 as (RS4' & Z4 & _ & RD4 & _ & _ & LED4 & PK4 & _ & NODE4 & RES4 & _ &
      SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & _).
    destruct (kb_md B API L'' A'' mem4 md4 M4) as (Hh4 & Hz4).
    pose proof (rc_pres regs0 regs3 regs4 copy (Z_to_bv 64 q) (Z_to_bv 64 want) s4v s5v RR4
      (rc_pres regs0 regs2 regs3 copy (Z_to_bv 64 q) (Z_to_bv 64 want) s4v s5v RP3 REG2)) as REG4.
    pose proof REG4 as (G2'' & _).
    (* the seven save slots, as the epilogue reads them: [S - 56, S) = P + 56 .. P + 112, P = S - 112 *)
    replace (spZ regs0 - 8) with (spZ regs0 - 112 + 104) in SL8 by lia.
    replace (spZ regs0 - 16) with (spZ regs0 - 112 + 96) in SL16 by lia.
    replace (spZ regs0 - 24) with (spZ regs0 - 112 + 88) in SL24 by lia.
    replace (spZ regs0 - 32) with (spZ regs0 - 112 + 80) in SL32 by lia.
    replace (spZ regs0 - 40) with (spZ regs0 - 112 + 72) in SL40 by lia.
    replace (spZ regs0 - 48) with (spZ regs0 - 112 + 64) in SL48 by lia.
    replace (spZ regs0 - 56) with (spZ regs0 - 112 + 56) in SL56 by lia.
    rewrite HSEG in SL8, SL16, SL24, SL32, SL40, SL48, SL56.
    (* 0x153f4: s2 := 1; a0 := s2; restore ra s0 .. s5; sp += 112; ret *)
    eapply (rc_kA B API HSEG FA fx1 regs4 _ mem4 md4 _ _ Hh4 Hz4).
    { unfold rmk. rewrite G2''.
      exact (RttRunsA.rtt_seg8o (getr regs4 1) (getr regs4 3) (getr regs4 4) (getr regs4 5) (getr regs4 6)
        (getr regs4 7) (getr regs4 8) (getr regs4 9) (getr regs4 10) (getr regs4 11) (getr regs4 12) (getr regs4 13)
        (getr regs4 14) (getr regs4 15) (getr regs4 16) (getr regs4 17) (getr regs4 18) (getr regs4 19)
        (getr regs4 20) (getr regs4 21) (getr regs4 22) (getr regs4 23) (getr regs4 24) (getr regs4 25)
        (getr regs4 26) (getr regs4 27) (getr regs4 28) (getr regs4 29) (getr regs4 30) (getr regs4 31)
        fp_regs fp_csr mem4 (spZ regs0 - 112) (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18)
        (getr regs0 19) (getr regs0 20) (getr regs0 21) ltac:(lia) ltac:(lia) SL8 SL16 SL24 SL32 SL40 SL48 SL56). }
    { intros ms' E. eexists _, _, _. exact E. }
    intros R pc' mem5 regs5 HQ HGr5.
    rc_inj HQ R pc' mem5.
    apply SR_ret. rewrite (kb_ret_pc _ RA0).
    replace (spZ regs0 - 112 + 112) with (spZ regs0) in HGr5 by lia.
    pose proof (rc_ret_pres regs0 regs4 regs5 copy (Z_to_bv 64 q) (Z_to_bv 64 want) s4v s5v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      REG4 HGr5) as RPF.
    pose proof (rtt_fl_inv B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
      fx1 L'' A'' mem4 md4 [] (l1 ++ l2) peak cnt (rtt_bo F b0 cnt0 t p) ENT INV4 FL) as (_ & _ & FB1 & FB2).
    unfold rtt_post. cbv zeta.
    exists fx1, L'', A'', regs5, mem4, md4, (l1 ++ l2), peak.
    split; [reflexivity|]. split; [exact FRM|]. split; [exact FREG|].
    split.
    { apply (rtt_rel_of_rstep B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes copy) L'' A'' regs5 mem4 md4);
        [| exact RPF | exact Z4].
      apply (rstep_E B API HSEG AX FG RTT_K (spZ regs0) (rtt_writes 0) (rtt_writes copy) (fun _ => False) (fun _ => False)
        L0 A0 mem0 md0 L'' A'' mem4 md4 RS4'); [| intros a H; exact H].
      intros a [[H _]|H]; [exfalso; apply H; reflexivity | right; exact H]. }
    split; [exact RD4|]. split; [exact FB1|]. split; [exact FB2|].
    left.
    split; [exact RO|].
    split; [rewrite HGr5; reflexivity|].
    split; [exact LED4|].
    split; [exact PK4|].
    split; [exact NODE4|].
    split; [exact PERM4|].
    split; [exact RES4|].
    (* *copy: outside the write set rtt_writes 0 of the whole walk, above the stack window *)
    intros Hc i Hi.
    destruct COPY as [C0|(_ & (_ & _ & Hhi & _) & Hcs & _)]; [contradiction|].
    pose proof RS4' as (_ & _ & _ & _ & _ & _ & AC4 & _).
    assert (Hr : ~ rwin B RTT_K (spZ regs0) (copy + i)) by (unfold rwin; lia).
    assert (He : ~ rtt_writes 0 (copy + i)).
    { unfold rtt_writes. intros [[H _]|H]; [apply H; reflexivity | pose proof (proj2 (HSE _ H)); lia]. }
    exact (proj1 (AC4 (copy + i) ltac:(lia) Hr He)).
Qed.

End S.
