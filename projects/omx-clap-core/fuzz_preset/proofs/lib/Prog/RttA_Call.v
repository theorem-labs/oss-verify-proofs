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
Ledger PjStruct ReaderRes tx_put_c TxCalls TxRet WriterSpec WriterValue PjWriteHyp
round_trip_text_c RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import RttGlue RttModel RttBase RttA_Lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Lemma ra_put : (forall fx' : YK11.FPState, @tx_put_contract fx' rc B API F) ->
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D
    fx1 L A mem md X Lam peak cnt bnd q want len cap txt regs1 s n src (Pc : config -> Prop),
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  rt_text B L0 A0 mem Lam t (negb (pretty =? 0)) q ->
  rt_harn B L0 A0 L A mem Lam (spZ regs0 - 112) want len cap txt ->
  getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs1 4 = getr regs0 4 -> YK0s.ret_ok (getr regs1 1) ->
  getr regs1 10 = Z_to_bv 64 (spZ regs0 - 112) -> getr regs1 11 = Z_to_bv 64 s -> getr regs1 12 = Z_to_bv 64 n ->
  0 <= s -> 0 <= n -> s + n <= 2 ^ 40 ->
  (forall i, 0 <= i < n -> in_img B (s + i) /\ LM.ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true) ->
  mbytes B mem s src -> Z.of_nat (length src) = n ->
  len + n + 1 <= 2 ^ 28 -> (cap < len + n + 1 -> rf_room F bnd (2 * (len + n + 1))) ->
  (forall L' A' regs' mem' md' want' cap',
     regs_preserved regs1 regs' -> cap' = tx_cap1 len cap n ->
     @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L' A' mem' md' X Lam peak cnt
       (tx_next F bnd len cap n) ->
     rt_text B L0 A0 mem' Lam t (negb (pretty =? 0)) q ->
     rt_harn B L0 A0 L' A' mem' Lam (spZ regs0 - 112) want' (len + n) cap' (txt ++ src) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' (getr regs1 1) mem' (seg_rom (ms_segs B))) md') Pc) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 TX_PUT) mem (seg_rom (ms_segs B))) md) Pc.
Proof.
  intros TXP L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd q
    want len cap txt regs1 s n src Pc ENT INV RT HARN G2 G4 GRA G10 G11 G12 Hs Hn Hsn HSRC SRC SL HLN ROOM K.
  pose proof ENT as (REN & _).
  pose proof REN as (_ & _ & ERRB & _ & _ & PRE0 & _).
  pose proof PRE0 as (_ & _ & _ & _ & SP16 & SPC & SP63 & _).
  pose proof INV as (RS & _ & INIT & RD & _ & _ & _ & _ & _ & _ & RES & _).
  pose proof RS as (MRc & _).
  pose proof HARN as (HW0 & HL0 & HC0 & REC & TW & TI0 & HB0 & HLam).
  pose proof alloc_ceiling_val as HCV.
  destruct (rtt_img_low B API HSEG FA) as (HIL & _).
  assert (HTX : TX_STACK + 112 <= RTT_K) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (HTX0 : 0 <= TX_STACK) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (SP1 : spZ regs1 = spZ regs0 - 112) by (unfold spZ at 1; rewrite G2; apply ra_uns; lia).
  assert (PREc : call_pre_k B (aa_MR API) TX_STACK L A regs1 mem md).
  { apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem md regs1 TX_STACK 112
      PRE0 RS INIT).
    - exact SP1.
    - rewrite SP1. apply ra_mod16. exact SP16.
    - exact G4.
    - exact GRA.
    - lia.
    - exact HTX0.
    - lia. }
  eapply SR_bind.
  { apply (TXP fx1 L A regs1 mem md (spZ regs0 - 112) s n want len cap txt src bnd PREc INIT (proj1 RD) G10 G11 G12).
    - lia.
    - lia.
    - apply ra_mod8. exact SP16.
    - exact TW.
    - exact HW0.
    - exact HL0.
    - exact HC0.
    - exact REC.
    - exact TI0.
    - lia.
    - exact Hn.
    - lia.
    - exact SRC.
    - exact SL.
    - intros i Hi. destruct (HSRC i Hi) as [Himg Hro]. pose proof (HIL _ Himg) as Hlow.
      split; [lia|]. split; [rewrite SP1; lia|]. split.
      + intros Hx. destruct TI0 as (_ & [(C0 & _) | (Cp & _ & _ & _ & NI)]); [lia|].
        apply (NI (s + i - want)); [lia|]. replace (want + (s + i - want)) with (s + i) by lia. exact Himg.
      + right. right. left. exact Hro.
    - exact HLN.
    - exact RES.
    - exact ROOM. }
  intros c' (L' & A' & regs' & mem' & md' & b1 & cap1 & bnd' & -> & FR & RP & BK & REC' & TW' & TI1 & _ & RA' & _ &
    IN' & _ & RES' & ARMS).
  pose proof FR as (MR' & _).
  assert (TXR : txr B API TX_STACK regs1 (spZ regs0 - 112) want cap L A mem md L' A' mem' md' b1 (len + n) cap1
      (txt ++ src) /\
    cap1 = tx_cap1 len cap n /\ rf_ok F A' (tx_next F bnd len cap n)).
  { destruct ARMS as [(FIT & -> & -> & -> & -> & -> & ->) | (GROW & EC & AL & EB & bl1 & bl2 & bm1 & bm2 & E1 & E2 & E3)].
    - split.
      + split; [exact FR|]. split; [exact BK|].
        split; [intros a k Hin Hne; split; assumption|].
        split; [intros a k Hin Hk Hne; exact Hne|].
        split; [exact REC'|]. split; [exact TW'|]. split; [exact TI1|]. split; [exact RA' | exact IN'].
      + unfold tx_cap1, tx_next. rewrite (proj2 (Z.leb_le _ _)) by lia. split; [reflexivity | exact RES'].
    - pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ MR') as PW. rewrite E1 in PW.
      assert (PC : 0 < cap1) by lia.
      assert (OLDB : forall a k, In (a, k) (blocks L A) -> (a, k) <> (want, cap) -> In (a, k) (bm1 ++ bm2)).
      { intros a k Hin Hne. rewrite E2. destruct E3 as [(C0 & E3)|(C0 & E3)]; rewrite E3 in Hin; [exact Hin|].
        apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|[H|H]]; [left; exact H | | right; exact H].
        exfalso. apply Hne. symmetry. exact H. }
      split.
      + split; [exact FR|]. split; [exact BK|].
        split.
        { intros a k Hin Hne. pose proof (OLDB a k Hin Hne) as Hin'. split.
          - rewrite E1. apply in_app_or in Hin'. apply in_or_app.
            destruct Hin' as [H|H]; [left; exact H | right; right; exact H].
          - intros Xe. injection Xe as Xa Xk. subst a k.
            destruct (ra_pw_mid _ _ _ _ _ PW Hin') as [Dj|Dj]; unfold ranges_disjoint in Dj; cbn [fst snd] in Dj; lia. }
        split.
        { intros a k Hin Hk Hne Xe. subst a.
          assert (Hin' : In (b1, k) (bm1 ++ bm2)) by (apply OLDB; [exact Hin | intros Xe; apply Hne; congruence]).
          destruct (ra_pw_mid _ _ _ _ _ PW Hin') as [Dj|Dj]; unfold ranges_disjoint in Dj; cbn [fst snd] in Dj; lia. }
        split; [exact REC'|]. split; [exact TW'|]. split; [exact TI1|]. split; [exact RA' | exact IN'].
      + unfold tx_cap1, tx_next. rewrite (proj2 (Z.leb_gt _ _)) by lia. split; [exact EC|].
        rewrite <- EC. subst bnd'. exact RES'. }
  destruct TXR as (TXR & HCJ & RESJ).
  destruct (@ra_after fx rc B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X
    Lam peak cnt bnd q want len cap txt TX_STACK regs1 L' A' mem' md' b1 (len + n) cap1 (txt ++ src)
    (tx_next F bnd len cap n) ENT INV RT HARN SP1 HTX0 ltac:(lia) TXR RESJ) as (INV' & RT' & HARN').
  exact (K L' A' regs' mem' md' b1 cap1 RP HCJ INV' RT' HARN').
Qed.

End C.
