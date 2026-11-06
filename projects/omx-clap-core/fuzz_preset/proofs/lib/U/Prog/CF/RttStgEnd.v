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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import RttDefs memcpy_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import PjWriteHyp round_trip_text_c pj_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import RttGlue RttModel RttBase RttC_Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require RttRunsA RttRunsB strtod_c fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* round_trip_text of the #102 ubsan twin 27566683 (round_trip_text_c.v, 0x15334), the CF form: stg_end at 0x15488 (the
   stage after same() returned nonzero, RttBase.stg_end_st).  `beqz s0` splits on copy:
     copy <> 0: memcpy(copy, &back = sp, 56); j; s2 := 0; j 0x153f8 (the shared exit): a0 := s2 = 0, ld ra s0 .. s5,
       sp += 0x70, ret  -- RttRunsB.rtt_seg7a, over memcpy_contract;
     copy = 0: pj_free(&back = sp) (RttRunsA.rtt_seg7b, then pj_free_contract), ret to 0x154a8; s2 := 0; the shared exit
       (RttRunsA.rtt_seg8z).
   Both end in the contract's normal arm (ro = 0, oo = 0, a0 = 0); the two flag bytes are the entry bytes
   (RttBase.rtt_fl_inv), and memcpy writes only [copy, copy + 56), above alloc_ceiling, while the flags are image bytes. *)

Module CMem := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Mem.

Lemma rce_slot : forall segs m x y v, x = y -> CMem.bytes_at segs m x (CMem.le8 v) -> LMem.bytes_at segs m y (LMem.le8 v).
Proof. intros segs m x y v -> H. exact H. Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis MC : memcpy_contract.
Hypothesis PJF : forall fx' : YK11.FPState, @pj_free_contract fx' rc B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Theorem stg_end_holds : stg_end_st B API F.
Proof.
  unfold stg_end_st.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A regs mem md Lam peak Db
    s2v s3v s4v s5v ENT FL0 Ero Eoo INV REG NODE NEW SUB LSZ NL.
  subst ro oo.
  set (p := negb (pretty =? 0)) in *.
  set (cnt := cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) in *.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & _ & DNODE & DSUB & DOC0 & DOCS & _ & DEP & _ & COPY & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODED & RES & CP &
    SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & _).
  pose proof RS as (MRc & WFc & BDc & _ & PSc & _ & _ & _ & _ & WRc).
  pose proof REG as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  pose proof alloc_ceiling_val as HCV.
  pose proof (rtt_img_low B API HSEG FA) as (HIL & _).
  destruct rc_rttk as (HRK & HAS & HPF).
  destruct (HPF (depth t) DEP) as (HPF0 & HPF1). try unfold RTT_F in HPF1.
  (* the errno word, the ledger words and the two flag bytes are image bytes, below alloc_ceiling (by name) *)
  assert (HERR : forall a, errno_addr B <= a < errno_addr B + 4 -> a < alloc_ceiling).
  { intros a Ha. pose proof (errno_img B API HSEG AX FG ERRB (a - errno_addr B) ltac:(lia)) as Hi.
    replace (errno_addr B + (a - errno_addr B)) with a in Hi by lia. pose proof (HIL a Hi). lia. }
  assert (HSTE : forall a, alloc_statics a -> a < alloc_ceiling /\ ~ (errno_addr B <= a < errno_addr B + 4)).
  { intros a Ha. split.
    - destruct (statics_img B API HSEG AX FG a Ha) as [Hi _]. pose proof (HIL a Hi). lia.
    - rewrite ERRB. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. unfold strtod_c.STRTOD_ERRNO. lia. }
  assert (HFL : forall a, (fuzz_alloc_ran_out_c.G_RAN_OUT <= a < fuzz_alloc_ran_out_c.G_RAN_OUT + 1 \/
      GL_OWN_RAN_OUT <= a < GL_OWN_RAN_OUT + 1) -> a < alloc_ceiling).
  { intros a Ha. destruct (rtt_flag_img B API HSEG FA a Ha) as (Hi & _). pose proof (HIL a Hi). lia. }
  (* the two flag bytes at 0x15488 are the entry bytes (both 0 on this arm) *)
  pose proof (rtt_fl_inv B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D 0 0 fx1 L A mem md
    Db Lam peak cnt (rtt_bf F b0 cnt0 t p) ENT INV FL0) as (_ & _ & FB1 & FB2).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  pose proof (rc_node_top _ _ _ _ _ _ DNODE) as (_ & DOCT).
  pose proof LED as (_ & _ & _ & _ & ND & _).
  pose proof (rc_nd_perm Lam Db Lam0 PERM ND) as NDX.
  assert (DL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (DSUB bk Hb). }
  assert (DbD : forall a k a' k', In (a, k) Db -> In (a', k') D -> a <> a').
  { intros a k a' k' H1 H2. exact (rc_disj Db Lam0 a k a' k' NDX H1 (DSUB _ H2)). }
  destruct (Z.eq_dec copy 0) as [C0|C1].
  - (* copy = 0: 0x15488 beqz s0; jal pj_free(&back); 0x154a8 s2 := 0; the shared exit 0x153f8, a0 := 0 *)
    subst copy.
    assert (G8' : getr regs 8 = Z_to_bv 64 0) by exact G8.
    eapply (rc_kA B API HSEG FA fx1 regs _ mem md _ _ Hh Hz).
    { unfold rmk. rewrite G2, G8'.
      exact (RttRunsA.rtt_seg7b (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
        (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
        (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
        (getr regs 30) (getr regs 31) fp_regs fp_csr mem (spZ regs0 - 112)). }
    { intros ms' E. eexists _, _, _. exact E. }
    intros R pc' mem1 regs1 HQ HGr.
    rc_inj HQ R pc' mem1.
    assert (R1 : getr regs1 1 = Z_to_bv 64 0x154a8) by (rewrite HGr; reflexivity).
    assert (R2 : getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; reflexivity).
    assert (R4 : getr regs1 4 = getr regs0 4) by (rewrite HGr; exact G4).
    assert (R10 : getr regs1 10 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; reflexivity).
    assert (REG1 : rtt_regs regs0 regs1 0 s2v s3v s4v s5v).
    { refine (conj R2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj R4 _))))))))).
      - rewrite HGr. reflexivity.
      - rewrite HGr. exact G9.
      - rewrite HGr. exact G18.
      - rewrite HGr. exact G19.
      - rewrite HGr. exact G20.
      - rewrite HGr. exact G21.
      - rewrite HGr. exact G3.
      - intros r Hr. rewrite HGr, <- (G22 r Hr).
        assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity. }
    assert (SPr : spZ regs1 = spZ regs0 - 112) by (unfold spZ at 1; rewrite R2; apply rc_uns; lia).
    pose proof (pj_node_fd (ms_segs B) t mem (lin Lam) (spZ regs0 - 112) Db NODE) as HFD.
    assert (REN1 : @reader_env fx1 rc B API RTT_K L0 A0 regs0 mem0 md0)
      by exact (conj SEGB (conj TPB (conj ERRB (conj GOTB (conj GUARDB (conj PRE0 (conj SP47 (conj GT
        (conj FRM RD0))))))))).
    assert (REN2 : @reader_env fx1 rc B API (PJ_FREE_K (depth t)) L A regs1 mem md).
    { apply (reader_env_mid (fx := fx1) B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem md regs1
        (PJ_FREE_K (depth t)) 112 REN1 RS INIT RD FRM);
        [exact SPr | rewrite SPr; Z.div_mod_to_equations; lia | exact R4 | rewrite R1; rc_ret | lia | lia | lia]. }
    assert (RPL : rplace B L A Lam regs1 mem (spZ regs0 - 112)).
    { split; [left; rewrite SPr; lia|].
      split; [intros _ Hf; rewrite INIT in Hf; discriminate|].
      intros i Hi. split; [|split; [|split]].
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ MRc Ho). lia.
      - intros Hs. pose proof (proj1 (HSTE _ Hs)). lia.
      - intros Hr. pose proof (HERR _ Hr). lia.
      - intros Hi'. pose proof (HIL _ Hi'). lia. }
    eapply SR_bind.
    { apply (PJF fx1 L A regs1 mem md Lam peak cnt (2 ^ 64 - 1) (rtt_bf F b0 cnt0 t p) (spZ regs0 - 112) (depth t) Db
        REN2 LED RES R10).
      right. split; [lia|]. split; [exact HFD|]. split; [exact RPL|].
      rewrite SPr. cbn [LFrame.disjoint_from]. split; [lia | exact I]. }
    intros c' (L' & A' & regs2 & mem2 & md2 & Lam' & -> & RP2 & RD2 & PERMF & LED2 & (Df & PDf & RES2) & _ & HZR).
    rewrite R1.
    pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & RR2 & _).
    pose proof (rstep_of_rpost B API HSEG AX FG (PJ_FREE_K (depth t)) L A regs1 mem md
      (pj_free_writes (spZ regs0 - 112) Db) (freed Db) L' A' regs2 mem2 md2 RP2) as STEP.
    rewrite SPr in STEP.
    destruct (HZR ltac:(lia)) as ((_ & ZSTK) & _).
    assert (PL' : Permutation Lam' Lam0).
    { apply (Permutation_app_inv_l Db). exact (Permutation_trans (Permutation_sym PERMF) PERM). }
    assert (FWd : forall a k i, In (a, k) Lam -> (forall n, ~ In (a, n) Db) -> 0 <= i < k ->
        ~ pj_free_writes (spZ regs0 - 112) Db (a + i)).
    { intros a k i Hin Hn Hi (_ & [Hf|[Hf|Hf]]).
      - destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k MRc LED Hin) as (_ & _ & _ & Ha2 & _).
        lia.
      - destruct Hf as (a' & k' & Hin' & Hf).
        assert (Hne : a <> a') by (intros E; subst a'; exact (Hn k' Hin')).
        apply (rc_apart B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k a' k' (a + i) MRc LED Hin (SUB _ Hin')
          Hne); lia.
      - exact (rc_not_statics B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k i MRc LED Hin ltac:(lia) Hf). }
    assert (FWhi : forall x, spZ regs0 <= x -> ~ pj_free_writes (spZ regs0 - 112) Db x).
    { intros x Hx (_ & [Hf|[Hf|Hf]]).
      - lia.
      - destruct Hf as (a' & k' & Hin' & Hf).
        destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a' k' MRc LED (SUB _ Hin'))
          as (_ & _ & _ & Ha2 & _).
        lia.
      - pose proof (proj1 (HSTE _ Hf)). lia. }
    assert (RWhi : forall x, spZ regs0 - 112 <= x < 2 ^ 64 -> ~ rwin B (PJ_FREE_K (depth t)) (spZ regs0 - 112) x).
    { intros x Hx [Hr|Hr]; [lia | pose proof (HERR _ Hr); lia]. }
    assert (INV2 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc 0 t D fx1 L' A' mem2 md2 [] Lam' peak
        cnt (rf_frees F (rtt_bf F b0 cnt0 t p) Df)).
    { apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty 0 t D fx1 L A mem md Db Lam peak
        cnt (rtt_bf F b0 cnt0 t p) (PJ_FREE_K (depth t)) (pj_free_writes (spZ regs0 - 112) Db)
        (fun a => exists n, freed Db a n) fx1 L' A' mem2 md2 [] Lam' peak cnt (rf_frees F (rtt_bf F b0 cnt0 t p) Df)
        ENT INV STEP); try lia.
      - intros a (_ & [Ha|[Ha|Ha]]).
        + right. left. lia.
        + right. right. destruct Ha as (a' & k' & Hin' & Hr).
          destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a' k' MRc LED (SUB _ Hin'))
            as (Hk' & Hb' & H1' & H2' & NI').
          split; [lia|]. split.
          * intros Hi. apply (NI' (a - a') ltac:(lia)). replace (a' + (a - a')) with a by lia. exact Hi.
          * intros b k Hb Hg. destruct (Z.eq_dec b (a' - 16)) as [->|Hne].
            -- exfalso. apply Hg. exists (k' + 16). unfold freed.
               replace (a' - 16 + 16) with a' by lia. replace (k' + 16 - 16) with k' by lia. exact Hin'.
            -- exact (blocks_apart B API HSEG AX FG L A mem md (a' - 16) (k' + 16) b k a MRc Hb' Hb
                 (fun E => Hne (eq_sym E)) ltac:(lia)).
        + left. exact Ha.
      - intros a Ha Hw. destruct ZSTK as (_ & _ & ZS). exact (proj1 (ZS a ltac:(lia))).
      - intros a k Hin Hk (n & Hn). unfold freed in Hn.
        pose proof (PSc a k Hin Hk (fun h => h)) as HinL.
        destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) (a + 16) (n - 16) MRc LED (SUB _ Hn))
          as (Hn0 & Hbn & _).
        replace (a + 16 - 16) with a in Hbn by lia. replace (n - 16 + 16) with n in Hbn by lia.
        pose proof (blocks_same_addr B API HSEG AX FG L A mem md a k n MRc HinL Hbn Hk ltac:(lia)) as Ek. subst n.
        apply (NEW (a + 16) (k - 16) Hn). replace (a + 16 - 16) with a by lia. replace (k - 16 + 16) with k by lia.
        exact Hin.
      - intros a k Hin Hk. apply (rc_rpost_blocks B API HSEG FA _ _ _ _ _ _ _ _ _ _ _ _ _ RP2 a k Hin).
        intros Hf. unfold freed in Hf.
        destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) (a + 16) (k - 16) MRc LED (SUB _ Hf))
          as (Hk0 & _).
        lia.
      - exact (proj1 RD2).
      - exact FRM.
      - intros r Hr. reflexivity.
      - exact LED2.
      - exact PL'.
      - apply (rc_node_keep B API HSEG FA (PJ_FREE_K (depth t)) (spZ regs0 - 112) (pj_free_writes (spZ regs0 - 112) Db)
          (fun a => exists n, freed Db a n) L A mem md L' A' mem2 md2 Lam Lam' peak cnt (2 ^ 64 - 1) doc t D MRc LED
          NODED DL); [| exact STEP | lia | |].
        + intros bk Hb. apply (Permutation_in _ (Permutation_sym PL')). exact (DSUB _ Hb).
        + intros i Hi. split; [apply RWhi; lia | apply FWhi; lia].
        + intros a k Hb. split.
          * intros (n & Hn). unfold freed in Hn. replace (a - 16 + 16) with a in Hn by lia.
            exact (DbD a (n - 16) a k Hn Hb eq_refl).
          * intros i Hi. apply (FWd a k i (DL _ Hb)); [|exact Hi]. intros n Hn. exact (DbD a n a k Hn Hb eq_refl).
      - exact RES2. }
    pose proof INV2 as (RS2 & Z2 & _ & RD3 & _ & _ & LED3 & PK3 & PERM3 & NODE3 & RES3 & _ &
      SL8' & SL16' & SL24' & SL32' & SL40' & SL48' & SL56' & _).
    pose proof (rtt_fl_inv B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty 0 t D 0 0 fx1 L' A' mem2
      md2 [] Lam' peak cnt (rf_frees F (rtt_bf F b0 cnt0 t p) Df) ENT INV2 FL0) as (_ & _ & FB1' & FB2').
    destruct (kb_md B API L' A' mem2 md2 M2) as (Hh2 & Hz2).
    pose proof (rc_pres regs0 regs1 regs2 0 s2v s3v s4v s5v RR2 REG1) as REG2.
    pose proof REG2 as (G2'' & _).
    assert (K1 : LMem.bytes_at rsegs mem2 (spZ regs0 - 112 + 104) (LMem.le8 (getr regs0 1)))
      by (rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 8)); [lia | exact SL8']).
    assert (K2 : LMem.bytes_at rsegs mem2 (spZ regs0 - 112 + 96) (LMem.le8 (getr regs0 8)))
      by (rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 16)); [lia | exact SL16']).
    assert (K3 : LMem.bytes_at rsegs mem2 (spZ regs0 - 112 + 88) (LMem.le8 (getr regs0 9)))
      by (rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 24)); [lia | exact SL24']).
    assert (K4 : LMem.bytes_at rsegs mem2 (spZ regs0 - 112 + 80) (LMem.le8 (getr regs0 18)))
      by (rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 32)); [lia | exact SL32']).
    assert (K5 : LMem.bytes_at rsegs mem2 (spZ regs0 - 112 + 72) (LMem.le8 (getr regs0 19)))
      by (rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 40)); [lia | exact SL40']).
    assert (K6 : LMem.bytes_at rsegs mem2 (spZ regs0 - 112 + 64) (LMem.le8 (getr regs0 20)))
      by (rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 48)); [lia | exact SL48']).
    assert (K7 : LMem.bytes_at rsegs mem2 (spZ regs0 - 112 + 56) (LMem.le8 (getr regs0 21)))
      by (rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 56)); [lia | exact SL56']).
    eapply (rc_kA B API HSEG FA fx1 regs2 _ mem2 md2 _ _ Hh2 Hz2).
    { unfold rmk. rewrite G2''.
      exact (RttRunsA.rtt_seg8z (getr regs2 1) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6)
        (getr regs2 7) (getr regs2 8) (getr regs2 9) (getr regs2 10) (getr regs2 11) (getr regs2 12) (getr regs2 13)
        (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19)
        (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25)
        (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31) fp_regs fp_csr
        mem2 (spZ regs0 - 112) (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19)
        (getr regs0 20) (getr regs0 21) ltac:(lia) ltac:(lia) K1 K2 K3 K4 K5 K6 K7). }
    { intros ms' E. eexists _, _, _. exact E. }
    intros R pc' mem3 regs3 HQ HGr3.
    rc_inj HQ R pc' mem3.
    apply SR_ret. rewrite (kb_ret_pc _ RA0).
    replace (spZ regs0 - 112 + 112) with (spZ regs0) in HGr3 by lia.
    pose proof (rc_ret_pres regs0 regs2 regs3 0 s2v s3v s4v s5v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REG2 HGr3) as RPF.
    unfold rtt_post. cbv zeta.
    exists fx1, L', A', regs3, mem2, md2, Lam', peak.
    split; [reflexivity|]. split; [exact FRM|]. split; [exact FREG|].
    split; [exact (rtt_rel_of_rstep B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L' A' regs3 mem2 md2
      RS2 RPF Z2)|].
    split; [exact RD3|]. split; [exact FB1'|]. split; [exact FB2'|].
    right. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite HGr3; reflexivity|].
    split; [exact LED3|]. split; [exact PK3|].
    split; [exact NODE3|].
    split.
    { intros _. split; [exact PERM3|]. exists Db, Df.
      split; [exact PDf|]. split; [exact LSZ|]. split; [exact NL | exact RES3]. }
    intros Hc. exfalso. apply Hc. reflexivity.
  - (* copy <> 0: 0x15488 jal memcpy(copy, &back, 56); 0x154a8 s2 := 0; the shared exit 0x153f8, a0 := 0 *)
    destruct COPY as [C0|(_ & _ & HCs & HCd)]; [contradiction|].
    destruct (CP C1) as (Hc8 & HCstk).
    pose proof HCstk as (HC1 & HC2 & _).
    pose proof (rc_node_rw _ _ _ _ _ _ NODE) as (_ & HPstk).
    destruct (LFrame.stk_bytes (ms_segs B) mem (spZ regs0 - 112) (spZ regs0 - 112 + 56) HPstk ltac:(lia))
      as (bs & Hlen & Hbs).
    replace (spZ regs0 - 112 + 56 - (spZ regs0 - 112)) with 56 in Hlen by lia.
    change (Z.to_nat 56) with 56%nat in Hlen.
    assert (RO : MemNorm.ro_agree rsegs mem) by (rewrite <- HSEG; exact (proj1 RD)).
    pose proof (rc_stk_norm B API HSEG FA mem copy (copy + 56) HCstk ltac:(lia)) as HCn.
    rewrite HSEG in HCn.
    destruct (LFrame.stk_carve rsegs (MemNorm.normalize rsegs mem) copy (copy + 56) 56 HCn ltac:(lia))
      as (_ & junk & HJ).
    replace (copy + 56 - Z.of_nat 56) with copy in HJ by lia.
    assert (Hbsn : LMem.bytes_at rsegs (MemNorm.normalize rsegs mem) (spZ regs0 - 112) bs)
      by (apply MemNorm.bytes_at_normalize; [exact RO | rewrite <- HSEG; exact Hbs]).
    assert (K1 : LMem.bytes_at rsegs (MemNorm.normalize rsegs mem) (spZ regs0 - 112 + 104) (LMem.le8 (getr regs0 1)))
      by (apply MemNorm.bytes_at_normalize; [exact RO | rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 8));
          [lia | exact SL8]]).
    assert (K2 : LMem.bytes_at rsegs (MemNorm.normalize rsegs mem) (spZ regs0 - 112 + 96) (LMem.le8 (getr regs0 8)))
      by (apply MemNorm.bytes_at_normalize; [exact RO | rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 16));
          [lia | exact SL16]]).
    assert (K3 : LMem.bytes_at rsegs (MemNorm.normalize rsegs mem) (spZ regs0 - 112 + 88) (LMem.le8 (getr regs0 9)))
      by (apply MemNorm.bytes_at_normalize; [exact RO | rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 24));
          [lia | exact SL24]]).
    assert (K4 : LMem.bytes_at rsegs (MemNorm.normalize rsegs mem) (spZ regs0 - 112 + 80) (LMem.le8 (getr regs0 18)))
      by (apply MemNorm.bytes_at_normalize; [exact RO | rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 32));
          [lia | exact SL32]]).
    assert (K5 : LMem.bytes_at rsegs (MemNorm.normalize rsegs mem) (spZ regs0 - 112 + 72) (LMem.le8 (getr regs0 19)))
      by (apply MemNorm.bytes_at_normalize; [exact RO | rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 40));
          [lia | exact SL40]]).
    assert (K6 : LMem.bytes_at rsegs (MemNorm.normalize rsegs mem) (spZ regs0 - 112 + 64) (LMem.le8 (getr regs0 20)))
      by (apply MemNorm.bytes_at_normalize; [exact RO | rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 48));
          [lia | exact SL48]]).
    assert (K7 : LMem.bytes_at rsegs (MemNorm.normalize rsegs mem) (spZ regs0 - 112 + 56) (LMem.le8 (getr regs0 21)))
      by (apply MemNorm.bytes_at_normalize; [exact RO | rewrite <- HSEG; apply (rce_slot _ _ (spZ regs0 - 56));
          [lia | exact SL56]]).
    eapply (rc_kAn B API HSEG FA fx1 regs _ mem md _ _ Hh Hz RO).
    { unfold rmk. rewrite G2, G8.
      exact (RttRunsB.rtt_seg7a MC (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
        (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
        (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
        (getr regs 30) (getr regs 31) fp_regs fp_csr (MemNorm.normalize rsegs mem) (spZ regs0 - 112) copy bs junk
        (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20) (getr regs0 21)
        ltac:(lia) ltac:(lia) ltac:(lia) Hlen Hbsn HJ K1 K2 K3 K4 K5 K6 K7 (MemNorm.mem_inv_normalize rsegs mem)). }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
        _ & _ & _ & _ & E).
      eexists _, _, _. exact E. }
    intros R pc' mem1 m0 regs3 HQ MREL ROS HGr3.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      MU & WM & MI & BC & E).
    rc_inj E R pc' m0.
    assert (MU1 : LFrame.munch [(copy, copy + 56)] mem mem1)
      by exact (MemNorm.munch_rel rsegs _ mem (MemNorm.normalize rsegs mem) mem1 m'
        (MemNorm.mem_rel_normalize rsegs mem RO) MREL ROS MU).
    assert (WM1 : LFrame.wmono rsegs mem mem1)
      by exact (MemNorm.wmono_rel rsegs mem (MemNorm.normalize rsegs mem) mem1 m'
        (MemNorm.mem_rel_normalize rsegs mem RO) MREL ROS WM).
    assert (BC1 : LMem.bytes_at rsegs mem1 copy bs) by exact (proj2 (MemNorm.bytes_at_rel rsegs mem1 m' copy bs MREL) BC).
    assert (RO1 : MemNorm.ro_agree (ms_segs B) mem1) by (rewrite HSEG; exact (MemNorm.ro_agree_same rsegs mem mem1 RO ROS)).
    set (E' := fun x => copy <> 0 /\ copy <= x < copy + 56).
    assert (STM : rstep B API RTT_K (spZ regs0) E' (fun _ => False) L A mem md L A mem1 md).
    { apply (rstep_of_munch B API HSEG AX FG RTT_K (spZ regs0) E' (fun _ => False) L A mem mem1 md [(copy, copy + 56)]
        MRc WFc BDc WRc MU1); [rewrite HSEG; exact WM1 | |].
      - intros x Hx Ho. right. unfold E'. split; [exact C1|].
        destruct (Z_lt_le_dec x copy) as [H1|H1]; [exfalso; apply Ho; apply outside_one; lia|].
        destruct (Z_lt_le_dec x (copy + 56)) as [H2|H2]; [lia | exfalso; apply Ho; apply outside_one; lia].
      - intros x Hx _. apply outside_one. lia. }
    pose proof STM as (M1 & _).
    assert (ST2 : rstep B API RTT_K (spZ regs0) (rtt_writes copy) (fun _ => False) L0 A0 mem0 md0 L A mem1 md).
    { apply (rstep_E B API HSEG AX FG RTT_K (spZ regs0) (fun x => rtt_writes 0 x \/ E' x) (rtt_writes copy)
        (fun _ => False) (fun _ => False) L0 A0 mem0 md0 L A mem1 md).
      - apply (rstep_seq B API HSEG AX FG RTT_K (spZ regs0) (rtt_writes 0) E' (fun _ => False) (fun _ => False)
          L0 A0 mem0 md0 L A mem md L A mem1 md RS STM).
        intros a k _ _ _ [].
      - intros a [[[H _]|Ha]|Ha]; [exfalso; apply H; reflexivity | right; exact Ha | left; exact Ha].
      - intros a Ha. exact Ha. }
    assert (LED1 : ledger B L A mem1 Lam peak cnt (2 ^ 64 - 1)).
    { apply (ledger_rstep B API HSEG AX FG RTT_K (spZ regs0) E' (fun _ => False) L A mem md L A mem1 md Lam peak cnt
        (2 ^ 64 - 1) MRc LED STM).
      - intros a Ha. destruct (HSTE a Ha) as (Hlo & Hne).
        split; [unfold rwin; intros [Hr|Hr]; [lia | exact (Hne Hr)] | unfold E'; lia].
      - intros a k Hin.
        destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k MRc LED Hin) as (_ & _ & _ & Ha2 & _).
        split; [intros [] | intros i Hi; unfold E'; lia]. }
    assert (NODE1 : pj_node (ms_segs B) mem1 (lin Lam) doc t D).
    { apply (pj_node_rstep B API HSEG AX FG RTT_K (spZ regs0) E' (fun _ => False) L A mem md L A mem1 md Lam Lam peak
        cnt (2 ^ 64 - 1) doc t D MRc LED NODED DL STM); [lia | exact DOCT | | | exact (fun bk h => h)].
      - intros i Hi. split; [unfold rwin; intros [Hr|Hr]; [lia | pose proof (HERR _ Hr); lia] | unfold E'; lia].
      - intros a k Hb.
        destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k MRc LED (DL _ Hb))
          as (_ & _ & _ & Ha2 & _).
        split; [intros [] | intros i Hi; unfold E'; lia]. }
    assert (NODEP : pj_node (ms_segs B) mem1 (lin Lam) (spZ regs0 - 112) t Db).
    { apply (pj_node_munch (ms_segs B) [(copy, copy + 56)] mem (lin Lam) mem1 (lin Lam) (spZ regs0 - 112) t Db NODE
        (fun a k h => SUB (a, k) h) MU1).
      intros z [Hz'|(b & Hb & Hz')]; apply outside_one.
      - lia.
      - destruct b as [a k]. unfold pj_holds in Hz'. cbn [fst snd] in Hz'.
        destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k MRc LED (SUB _ Hb))
          as (_ & _ & _ & Ha2 & _).
        lia. }
    assert (HSTK1 : LFrame.stk (ms_segs B) mem1 copy (copy + 56)).
    { pose proof (rc_stk_after (ms_segs B) mem mem1 copy bs) as H. rewrite Hlen in H. change (Z.of_nat 56) with 56 in H.
      apply H; [exact HCstk | rewrite HSEG; exact WM1 | rewrite HSEG; exact BC1]. }
    assert (HBP1 : LMem.bytes_at (ms_segs B) mem1 (spZ regs0 - 112) bs).
    { apply (LFrame.bytes_at_transport (ms_segs B) [(copy, copy + 56)] mem mem1 (spZ regs0 - 112) bs Hbs MU1).
      cbn [LFrame.disjoint_from]. rewrite Hlen. split; [lia | exact I]. }
    assert (NODEC : pj_node (ms_segs B) mem1 (lin Lam) copy t Db).
    { apply (pj_node_move (ms_segs B) mem1 (lin Lam) (spZ regs0 - 112) copy t Db bs NODEP Hc8 HSTK1 Hlen HBP1).
      - rewrite HSEG. exact BC1.
      - intros [a k] x Hb Hx. unfold pj_holds in Hx. cbn [fst snd] in Hx.
        destruct (rc_lblk B API HSEG FA L A mem md Lam peak cnt (2 ^ 64 - 1) a k MRc LED (SUB _ Hb))
          as (_ & _ & _ & Ha2 & _).
        lia. }
    (* memcpy writes only [copy, copy + 56): the flag bytes (image bytes, below alloc_ceiling <= copy) stay *)
    assert (FB1' : LMem.bytes_at (ms_segs B) mem1 fuzz_alloc_ran_out_c.G_RAN_OUT (LMem.le1 (Z_to_bv 64 0))).
    { apply (LFrame.bytes_at_transport (ms_segs B) [(copy, copy + 56)] mem mem1 fuzz_alloc_ran_out_c.G_RAN_OUT
        (LMem.le1 (Z_to_bv 64 0)) FB1 MU1).
      assert (Hg : fuzz_alloc_ran_out_c.G_RAN_OUT < alloc_ceiling) by (apply HFL; left; lia).
      cbn [LFrame.disjoint_from]. rewrite LMem.length_le1. split; [left; lia | exact I]. }
    assert (FB2' : LMem.bytes_at (ms_segs B) mem1 GL_OWN_RAN_OUT (LMem.le1 (Z_to_bv 64 0))).
    { apply (LFrame.bytes_at_transport (ms_segs B) [(copy, copy + 56)] mem mem1 GL_OWN_RAN_OUT
        (LMem.le1 (Z_to_bv 64 0)) FB2 MU1).
      assert (Hg : GL_OWN_RAN_OUT < alloc_ceiling) by (apply HFL; right; lia).
      cbn [LFrame.disjoint_from]. rewrite LMem.length_le1. split; [left; lia | exact I]. }
    apply SR_ret. rewrite (kb_ret_pc _ RA0).
    replace (spZ regs0 - 112 + 112) with (spZ regs0) in HGr3 by lia.
    pose proof (rc_ret_pres regs0 regs regs3 copy s2v s3v s4v s5v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REG HGr3) as RPF.
    unfold rtt_post. cbv zeta.
    exists fx1, L, A, regs3, mem1, md, Lam, peak.
    split; [reflexivity|]. split; [exact FRM|]. split; [exact FREG|].
    split; [exact (rtt_rel_of_rstep B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes copy) L A regs3 mem1 md
      ST2 RPF Z0)|].
    split; [exact (rd_cells_of_MR B API HSEG AX FG L A mem1 md M1 RO1)|].
    split; [exact FB1'|]. split; [exact FB2'|].
    right. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite HGr3; reflexivity|].
    split; [exact LED1|]. split; [exact PK|].
    split; [exact NODE1|].
    split; [intros Hc; contradiction|].
    intros _. split; [exact RES|]. exists Db. split; [exact PERM|]. split; [exact NEW|].
    split; [exact NODEC|]. split; assumption.
Qed.

End S.
