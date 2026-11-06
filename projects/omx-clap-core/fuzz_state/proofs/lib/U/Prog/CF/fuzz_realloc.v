From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import fuzz_malloc_c fuzz_realloc_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import ReallocFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require ReallocRuns MallocRuns.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Section FR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis HERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis HG : globals_free B API omx_G.
Hypothesis REALLOC : realloc_contract_r B API F 0x184e8.
Hypothesis FMALLOC : fuzz_malloc_contract B API F.

Theorem fuzz_realloc_holds_s : fuzz_realloc_contract B API F.
Proof.
  unfold fuzz_realloc_contract.
  intros L A regs mem md p k n old b Lam peak cnt fail Hpre Ha0 Ha1 Hn0 HL Hro HP Hlen Hold Hres Hroom Hn.
  pose proof (rf_img B HSEG) as HIL.
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  assert (HRS : REALLOC_STACK = 8256) by reflexivity.
  assert (HAS : ALLOC_STACK = 8192) by reflexivity.
  set (S := spZ regs) in *.
  assert (Hsp : getr regs 2 = Z_to_bv 64 S) by (unfold S, spZ; symmetry; apply Step.Z_to_bv_lit_self).
  pose proof HL as (HW0 & Hpk & Hc & Hf & HND & HFL).
  pose proof HW0 as (HLv & HPk & HCt & HFl).
  assert (Hls : 0 <= lsum Lam).
  { apply rf_lsum_nonneg. eapply Forall_impl; [|exact HFL]. intros [a kk] (Hk & _). exact Hk. }
  assert (HK : Frame.stk (ms_segs B) mem (S - (REALLOC_STACK + 48)) S)
    by (apply (kb_stk B API HIL _ L A regs mem md Hpre); lia).
  assert (HK48 : Frame.stk rsegs mem (S + -48) S).
  { destruct (Frame.stk_split _ mem _ (S + -48) S HK ltac:(lia)) as [_ H]. rewrite <- HSEG. exact H. }
  assert (Hwmk : forall a, (S - (REALLOC_STACK + 48) <= a < S) \/ (errno_addr B <= a < errno_addr B + 4) ->
      writable_at (ms_segs B) mem a) by (intros a [Ha|Ha]; [apply Hstk; exact Ha | apply Herr; exact Ha]).
  assert (Hwrm : forall a, S + -48 <= a < S -> writable_at (ms_segs B) mem a) by (intros a Ha; apply Hstk; lia).
  assert (Hlblk : forall L2 A2 m2, (forall a kk, In (a, kk) (blocks L A) -> In (a, kk) (blocks L2 A2)) ->
      (forall a kk i, In (a, kk) (blocks L A) -> 0 <= i < kk ->
         mbyte (ms_segs B) m2 (a + i) = mbyte (ms_segs B) mem (a + i)) ->
      forall Lam', (forall x, In x Lam' -> In x Lam) -> Forall (fun ak => lblock B L2 A2 m2 (fst ak) (snd ak)) Lam').
  { intros L2 A2 m2 Hsub Hkm Lam' HLam'. apply Forall_forall. intros [a kk] Hx.
    rewrite Forall_forall in HFL. destruct (HFL _ (HLam' _ Hx)) as (Hk & Hin & Hw & Himg). cbn [fst snd] in *.
    split; [exact Hk|]. split; [exact (Hsub _ _ Hin)|]. split; [|exact Himg].
    apply (word_mem_frame (ms_segs B) mem m2 (a - 16) kk Hw). intros k0 Hk0.
    exact (Hkm (a - 16) (kk + 16) k0 Hin ltac:(lia)). }
  destruct (Z.eq_dec p 0) as [Hp0|Hp0].
  - subst p.
    assert (Hk0 : k = 0).
    { destruct HP as [(_ & Hk)|Hin]; [exact Hk|]. exfalso.
      pose proof (ledger_block_range B API L A mem md Lam peak cnt fail 0 k HMR HL Hin). lia. }
    subst k.
    apply (kb_run B regs _ mem md
      (fun R pc' mem' => ReallocRuns.run0_post (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
         (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
         (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
         (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
         (getr regs 30) (getr regs 31) fp_regs fp_csr mem S n (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)))).
    { exact (proj1 (kb_md B API L A mem md HMR)). }
    { exact (proj2 (kb_md B API L A mem md HMR)). }
    { unfold rmk. rewrite Hsp, Ha0, Ha1, HSEG. unfold FUZZ_REALLOC.
      eapply Exec.evt_mono.
      - apply (ReallocRuns.run0 (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
          (getr regs 8) (getr regs 9) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16)
          (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
          (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
          (getr regs 31) fp_regs fp_csr mem S n); [lia | lia | lia | exact HK48].
      - intros ms Hp. pose proof Hp as (m' & _ & _ & E). subst ms.
        do 3 eexists. split; [reflexivity | exact Hp]. }
    intros R pc0 mem0 regs0 HK0 Hg0.
    destruct HK0 as (m0 & HM0 & HW0' & E).
    rewrite <- HSEG in HW0'.
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM. subst R pc0 mem0. clear E.
    assert (Hcond0 : forall x, 0 <= x < alloc_ceiling ->
        (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) -> Frame.outside [(S + -48, S)] x)
      by (intros x Hx _; rf_out).
    assert (Hro0 : ro_agree (ms_segs B) m0).
    { apply (rf_ro_agree_munch B _ mem m0 Hro HM0). intros a Ha Ho. destruct (rf_not_out _ _ Ho) as (lo & hi & Hin & Hb).
      cbn in Hin. destruct Hin as [E|[]]; injection E as <- <-. apply (rf_ro_false_low B HSEG). lia. }
    assert (Hown0 : forall x, owned B L A x -> mbyte (ms_segs B) m0 x = mbyte (ms_segs B) mem x).
    { intros x Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md _ HMR Ho).
      eapply (mbyte_munch (ms_segs B) _ mem m0); [exact HM0 | pose proof alloc_ceiling_lt; lia | rf_out]. }
    assert (Hkeep0 : forall a kk i, In (a, kk) (blocks L A) -> 0 <= i < kk ->
        mbyte (ms_segs B) m0 (a + i) = mbyte (ms_segs B) mem (a + i))
      by exact (kb_blocks_munch B API L A mem m0 md _ HMR HM0 Hcond0).
    assert (Hglob0 : forall a, in_globals omx_G a -> mbyte (ms_segs B) m0 a = mbyte (ms_segs B) mem a).
    { intros a Ha. destruct (HG a Ha) as (_ & Hl & _).
      eapply (mbyte_munch (ms_segs B) _ mem m0); [exact HM0 | pose proof alloc_ceiling_lt; lia | rf_out]. }
    assert (HL0 : ledger B L A m0 Lam peak cnt fail).
    { split; [|split; [exact Hpk|split; [exact Hc|split; [exact Hf|split; [exact HND|]]]]].
      - split; [|split; [|split]];
          (eapply (rf_word_frame B); [eassumption | intros i Hi; apply Hglob0, rf_in_G;
             unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia]).
      - apply (Hlblk L A m0); [tauto | exact Hkeep0 | tauto]. }
    assert (G0_1 : getr regs0 1 = getr regs 1) by (rewrite Hg0; reflexivity).
    assert (G0_2 : getr regs0 2 = Z_to_bv 64 S) by (rewrite Hg0; reflexivity).
    assert (G0_10 : getr regs0 10 = Z_to_bv 64 n) by (rewrite Hg0; reflexivity).
    assert (Hs0 : spZ regs0 = S) by (unfold spZ; rewrite G0_2, MState.unsigned_lit by lia; reflexivity).
    assert (Hpre0 : call_pre_k B (aa_MR API) (ALLOC_STACK + 32) L A regs0 m0 md).
    { eapply (kb_pre_A B API (REALLOC_STACK + 48) 0 (ALLOC_STACK + 32) L A regs mem md regs0 m0);
        [exact Hpre | lia | lia | lia | rewrite Hs0; lia | rewrite Hs0; exact Hsp16 | rewrite Hg0; reflexivity
        | rewrite G0_1; exact Hra | exact HM0 | exact HW0' | | exact Hcond0].
      intros x Hx Hs. rf_out. }
    eapply SR_mono; [apply (FMALLOC L A regs0 m0 md n b Lam peak cnt fail Hpre0 G0_10 Hn0 HL0 Hro0 Hres Hroom Hn) |].
    intros c' Hc'.
    destruct Hc' as (L' & A' & regs' & m' & md' & res & -> & Hro' & Hgk' & Hinit' & Hlibc' & Hpost & Hreg & Hra0 &
                     Hkp' & Hub' & Harm).
    pose proof Hpost as (HMR' & _).
    assert (Hres_le : res <= alloc_ceiling).
    { destruct Harm as [(_ & -> & _)|(_ & _ & _ & _ & _ & _ & _ & (b1 & b2 & Hbl' & _) & _)]; [lia|].
      assert (Hin : In (res - 16, n + 16) (blocks L' A')) by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
      pose proof (rf_blk_range B API L' A' m' md' _ _ HMR' Hin). lia. }
    exists L', A', regs', m', md', res.
    rewrite G0_1. split; [reflexivity|].
    split; [exact Hro'|].
    split; [intros i Hi; rewrite (Hgk' i Hi); apply Hown0, rf_guard_owned; lia|].
    split; [exact Hinit'|].
    split; [intros Hd i Hi; rewrite (Hlibc' Hd i Hi); apply Hown0, rf_libc_owned; lia|].
    split.
    { apply (kb_post B API).
      - eapply (kb_mid_E B API).
        + eapply (kb_mid_seqAX B API).
          * eapply (kb_mid_A B API HIL _ _ _ _ _ _ _ _ (fun _ => False));
              [exact HMR | exact HWF | exact Hbd | exact Hwmk | exact HM0 | exact HW0' | | exact Hcond0].
            intros x Hx Hs He. rf_out.
          * exact (proj1 (kb_mid_call B API _ L A regs0 m0 md _ L' A' regs' m' md' Hpost)).
          * rewrite Hs0. lia.
          * rewrite Hs0. lia.
          * lia.
          * lia.
          * rewrite Hs0. intros a Ha Hn' He. unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in He.
            lia.
        + intros a Ha. cbv beta in Ha. unfold alloc_writes in Ha. unfold realloc_writes.
          destruct Ha as [[]|[Ha|Ha]]; [left; exact Ha | right; right; exact Ha].
      - apply (kb_preserved_trans regs regs0 regs').
        + rf_cs_cases ltac:(rewrite Hg0; first [reflexivity | exact (eq_sym Hsp)]).
        + exact (proj2 (kb_mid_call B API _ L A regs0 m0 md _ L' A' regs' m' md' Hpost)). }
    split; [exact Hreg|].
    split; [exact Hra0|].
    destruct Harm as [(Hcf & -> & EL & EA & Emd & Hrok & Hwo & Hbl & HL') |
                      (Hcf & Hrnz & Hr16 & Hres' & Hst & Himg & Hnin & (b1 & b2 & Hbl' & Hbl) & HL')].
    + left. split; [exact Hcf|]. split; [reflexivity|]. split; [exact EL|]. split; [exact EA|]. split; [exact Emd|].
      split; [exact Hrok|].
      split.
      { intros a Ha Hna. cbv beta in Hna. change (bv_unsigned (getr regs 2)) with S in Hna.
        assert (Hs0' : ~ (alloc_statics a \/ bv_unsigned (getr regs0 2) - (ALLOC_STACK + 32) <= a < bv_unsigned (getr regs0 2))).
        { rewrite G0_2, MState.unsigned_lit by lia. intros [Hs|Hs]; apply Hna; [left; exact Hs | right; lia]. }
        rewrite (Hwo a Ha Hs0').
        unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hna.
        eapply (mbyte_munch (ms_segs B) _ mem m0); [exact HM0 | exact Ha | rf_out]. }
      split; [exact Hbl|].
      split; [intros a kk i Hin Ha Hi; rewrite (Hkp' a kk i Hin Ha Hi); exact (Hkeep0 a kk i Hin Hi)|].
      split; [exact Hub'|]. exact HL'.
    + right. split; [exact Hcf|]. split; [exact Hrnz|]. split; [exact Hr16|]. split; [exact Hst|].
      split; [exact Himg|].
      split.
      { intros a kk i Hin Ha Hi. pose proof (rf_blk_range B API L A mem md a kk HMR Hin).
        rewrite (Hkp' a kk i Hin ltac:(lia) Hi). exact (Hkeep0 a kk i Hin Hi). }
      split.
      { intros q kk Hq Hne. apply Hub'; [exact Hq|]. intros E. injection E as E1 E2.
        pose proof (mr_blocks_range _ _ (aa_laws API) L A mem md q kk HMR Hq). lia. }
      split; [intros i Hi; lia|].
      exists [], Lam. split.
      { left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hres'|].
        exists b1, b2. split; assumption. }
      cbn [app]. split; [exact Hnin | exact HL'].
  - assert (HinL : In (p, k) Lam) by (destruct HP as [(E & _)|H]; [contradiction | exact H]).
    assert (Hlb : lblock B L A mem p k) by (rewrite Forall_forall in HFL; exact (HFL _ HinL)).
    destruct Hlb as (Hk0 & Hinb & Hhd & Himgb).
    destruct (rf_blocks_user L A (p - 16) (k + 16) Hinb) as (ps & Hps & Eps).
    pose proof (rf_blk_range B API L A mem md (p - 16) (k + 16) HMR Hinb) as Hpr.
    destruct (in_split _ _ HinL) as (l1 & l2 & HLam).
    assert (HND12 : NoDup (map fst (l1 ++ l2)) /\ ~ In p (map fst (l1 ++ l2))).
    { apply (rf_nodup_mid l1 l2 p k). rewrite <- HLam. exact HND. }
    destruct HND12 as (HND12 & Hpnot).
    assert (Hsum : lsum Lam = lsum (l1 ++ l2) + k) by (rewrite HLam, !rf_lsum_app; cbn [lsum]; lia).
    assert (Hsum0 : 0 <= lsum (l1 ++ l2)).
    { apply rf_lsum_nonneg. apply Forall_forall. intros [a kk] Hx. rewrite Forall_forall in HFL.
      destruct (HFL (a, kk) ltac:(rewrite HLam; apply rf_in_mid; exact Hx)) as (Hk & _). exact Hk. }
    assert (Hpg1 : p - 16 + 8 <= 0x33b40 \/ 0x33b40 + 24 <= p - 16).
    { apply (rf_sep (in_img B) (p - 16) 8 0x33b40 24); [lia | lia | | intros i Hi; apply Himgb; lia].
      intros x Hx. apply (rf_glob_img B API HG), rf_in_G. lia. }
    assert (Hpg2 : p - 16 + 8 <= 0x238c8 \/ 0x238c8 + 8 <= p - 16).
    { apply (rf_sep (in_img B) (p - 16) 8 0x238c8 8); [lia | lia | | intros i Hi; apply Himgb; lia].
      intros x Hx. apply (rf_glob_img B API HG), rf_in_G. lia. }
    assert (BL : Mem.bytes_at rsegs mem 0x33b40 (Mem.le8 (Z_to_bv 64 (lsum Lam))))
      by (rewrite <- HSEG; apply word_mem_le8; [exact HLv | lia | lia | lia]).
    assert (WL : Mem.wr_at rsegs mem 0x33b40 8)
      by (rewrite <- HSEG; apply (globals_wr_at B API omx_G mem 0x33b40 (lsum Lam) HG);
          [intros k' Hk'; apply rf_in_G; lia | exact HLv]).
    assert (BC : Mem.bytes_at rsegs mem 0x33b50 (Mem.le8 (Z_to_bv 64 cnt)))
      by (rewrite <- HSEG; apply word_mem_le8; [exact HCt | lia | lia | lia]).
    assert (WC : Mem.wr_at rsegs mem 0x33b50 8)
      by (rewrite <- HSEG; apply (globals_wr_at B API omx_G mem 0x33b50 cnt HG); [intros k' Hk'; apply rf_in_G; lia | exact HCt]).
    assert (BF : Mem.bytes_at rsegs mem 0x238c8 (Mem.le8 (Z_to_bv 64 fail)))
      by (rewrite <- HSEG; apply word_mem_le8; [exact HFl | lia | lia | lia]).
    assert (WF : Mem.wr_at rsegs mem 0x238c8 8)
      by (rewrite <- HSEG; apply (globals_wr_at B API omx_G mem 0x238c8 fail HG); [intros k' Hk'; apply rf_in_G; lia | exact HFl]).
    assert (BH : Mem.bytes_at rsegs mem (p + -16) (ReallocRuns.hd8 k))
      by (rewrite <- HSEG; apply (rf_word_hd8 B mem (p - 16) k Hhd); lia).
    apply (kb_run B regs _ mem md
      (fun R pc' mem' => ReallocRuns.run1_post (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
         (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
         (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
         (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem S p n k (lsum Lam) cnt fail
         (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)))).
    { exact (proj1 (kb_md B API L A mem md HMR)). }
    { exact (proj2 (kb_md B API L A mem md HMR)). }
    { unfold rmk. rewrite Hsp, Ha0, Ha1, HSEG. unfold FUZZ_REALLOC.
      eapply Exec.evt_mono.
      - apply (ReallocRuns.run1 (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
          (getr regs 8) (getr regs 9) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16)
          (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
          (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
          (getr regs 31) fp_regs fp_csr mem S p n k (lsum Lam) cnt fail); try assumption; lia.
      - intros ms Hp. pose proof Hp as (c1 & c2 & c3 & c4 & c5 & c6 & m' & _ & _ & _ & Harm).
        destruct Harm as [(_ & _ & _ & E) | (_ & _ & _ & _ & _ & _ & _ & _ & E)]; subst ms;
          do 3 eexists; (split; [reflexivity | exact Hp]). }
    intros R pc1 mem1 regs1 HK1 Hg1.
    destruct HK1 as (a1' & a2' & a3' & a4' & a5' & a6' & m1 & HM1 & HW1 & HC1 & Harm).
    rewrite <- HSEG in HW1, HC1.
    assert (Hcond1 : forall x, 0 <= x < alloc_ceiling ->
        (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
        Frame.outside [(S + -48, S); (0x33b40, 0x33b48); (0x33b50, 0x33b58); (0x238c8, 0x238d0)] x).
    { intros x Hx Ho. apply (rf_avoid B API HG L A mem md _ x HMR); [| exact Hx | exact Ho].
      intros lo hi Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-;
        [left; lia | right; intros y Hy; apply rf_in_G; lia ..]. }
    assert (Hro1 : ro_agree (ms_segs B) m1).
    { apply (rf_ro_agree_munch B _ mem m1 Hro HM1). intros a Ha Ho. destruct (rf_not_out _ _ Ho) as (lo & hi & Hin & Hb).
      cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-;
        [apply (rf_ro_false_low B HSEG); lia | apply (rf_ro_false_glob B API HG), rf_in_G; lia ..]. }
    assert (Hown1 : forall x, owned B L A x -> mbyte (ms_segs B) m1 x = mbyte (ms_segs B) mem x).
    { intros x Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md _ HMR Ho).
      eapply (mbyte_munch (ms_segs B) _ mem m1); [exact HM1 | pose proof alloc_ceiling_lt; lia |].
      apply Hcond1; [lia | left; exact Ho]. }
    assert (HMR1 : aa_MR API L A m1 md) by exact (kb_MR_A B API L A mem m1 md _ HMR HM1 Hcond1).
    assert (Hkeep1 : forall a kk i, In (a, kk) (blocks L A) -> 0 <= i < kk ->
        mbyte (ms_segs B) m1 (a + i) = mbyte (ms_segs B) mem (a + i))
      by exact (kb_blocks_munch B API L A mem m1 md _ HMR HM1 Hcond1).
    assert (Hpk1 : word_mem (ms_segs B) m1 G_PEAK peak)
      by (apply (kb_word_munch (ms_segs B) mem m1 _ G_PEAK peak HPk HM1); intros k' Hk'; unfold G_PEAK; split; [lia | rf_out]).
    assert (Hct1 : word_mem (ms_segs B) m1 G_COUNT ((cnt + 1) mod 2 ^ 64)) by exact (rf_bytes_word B m1 _ _ HC1).
    destruct Harm as [(Hcf & HF1 & HL1 & E) | (Hcf & HF1 & HL1 & HS8 & HS16 & HS24 & HS32 & HS40 & E)].
    + rewrite <- HSEG in HF1, HL1.
      pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
      cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM. subst R pc1 mem1. clear E.
      apply SR_ret. exists L, A, regs1, m1, md, 0.
      rewrite (kb_ret_pc _ Hra).
      split; [reflexivity|].
      split; [exact Hro1|].
      split; [intros i Hi; apply Hown1, rf_guard_owned; lia|].
      split; [tauto|].
      split; [intros _ i Hi; apply Hown1, rf_libc_owned; lia|].
      split.
      { apply (kb_post B API).
        - eapply (kb_mid_A B API HIL);
            [exact HMR | exact HWF | exact Hbd | exact Hwmk | exact HM1 | exact HW1 | | exact Hcond1].
          intros x Hx Hs He. unfold realloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in He. rf_out.
        - rf_cs_cases ltac:(rewrite Hg1; first [reflexivity | exact (eq_sym Hsp)]). }
      split; [lia|].
      split; [rewrite Hg1; reflexivity|].
      left. split; [exact Hcf|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [exact Hres|].
      split.
      { intros a Ha Hna. cbv beta in Hna. change (bv_unsigned (getr regs 2)) with S in Hna.
        unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hna.
        eapply (mbyte_munch (ms_segs B) _ mem m1); [exact HM1 | exact Ha | rf_out]. }
      split; [reflexivity|].
      split; [intros a kk i Hin _ Hi; exact (Hkeep1 a kk i Hin Hi)|].
      split; [intros q kk Hq _; exact Hq|].
      split.
      { split; [|split; [|split]].
        - pose proof (rf_bytes_word B m1 _ _ HL1) as H. rewrite Z.mod_small in H by lia. exact H.
        - exact Hpk1.
        - exact Hct1.
        - pose proof (rf_bytes_word B m1 _ _ HF1) as H. rewrite Z.mod_small in H by lia. exact H. }
      split; [exact Hpk|]. split; [pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64)); lia|]. split; [lia|].
      split; [exact HND|]. apply (Hlblk L A m1); [tauto | exact Hkeep1 | tauto].
    + rewrite <- HSEG in HF1, HL1, HS8, HS16, HS24, HS32, HS40.
      pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
      cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM. subst R pc1 mem1. clear E.
      assert (G1 : getr regs1 1 = Z_to_bv 64 0x14238) by (rewrite Hg1; reflexivity).
      assert (G2 : getr regs1 2 = Z_to_bv 64 (S + -48)) by (rewrite Hg1; reflexivity).
      assert (G8 : getr regs1 8 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
      assert (G10 : getr regs1 10 = Z_to_bv 64 (p + -16)) by (rewrite Hg1; reflexivity).
      assert (G11 : getr regs1 11 = Z_to_bv 64 (n + 16)) by (rewrite Hg1; reflexivity).
      assert (G18 : getr regs1 18 = Z_to_bv 64 0x33b40) by (rewrite Hg1; reflexivity).
      assert (Hs1 : spZ regs1 = S - 48) by (unfold spZ; rewrite G2, MState.unsigned_lit by lia; lia).
      assert (Hhp : forall i, 0 <= i < 16 -> mbyte (ms_segs B) mem (p - 16 + i) <> None).
      { intros i Hi. apply (rf_present_some B). rewrite <- Eps.
        exact (proj1 (mr_blocks _ _ (aa_laws API) L A mem md ps (k + 16) i HMR Hps ltac:(lia))). }
      destruct (rf_bytes_list B mem (p - 16) 16 ltac:(lia) Hhp) as (hd & Hhdl & Hhdb).
      set (old' := hd ++ old).
      assert (Hold' : forall i, 0 <= i < k + 16 ->
          mbyte (ms_segs B) m1 (ptr_addr L ps + i) = nth_error old' (Z.to_nat i)).
      { intros i Hi. rewrite Eps, (Hkeep1 (p - 16) (k + 16) i Hinb Hi). unfold old'.
        destruct (Z_lt_le_dec i 16) as [Hi16|Hi16].
        - rewrite nth_error_app1 by lia. exact (Hhdb i ltac:(lia)).
        - rewrite nth_error_app2 by lia. replace (Z.to_nat i - length hd)%nat with (Z.to_nat (i - 16)) by lia.
          replace (p - 16 + i) with (p + (i - 16)) by lia. exact (Hold (i - 16) ltac:(lia)). }
      assert (Hlen' : Z.of_nat (length old') = k + 16) by (unfold old'; rewrite length_app; lia).
      assert (Hpre1 : call_pre_k B (aa_MR API) REALLOC_STACK L A regs1 m1 md).
      { eapply (kb_pre_A B API (REALLOC_STACK + 48) 48 REALLOC_STACK L A regs mem md regs1 m1);
          [exact Hpre | lia | lia | lia | rewrite Hs1; reflexivity | | rewrite Hg1; reflexivity | | exact HM1 | exact HW1
          | | exact Hcond1].
        - rewrite Hs1. replace (S - 48) with (S + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
        - rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
        - intros x Hx Hs. rf_out. }
      eapply SR_bind; [apply (REALLOC L A regs1 m1 md ps (k + 16) (n + 16) old' b) |].
      { exact Hpre1. }
      { exact Hro1. }
      { exact Hps. }
      { rewrite G10, Eps. reflexivity. }
      { exact G11. }
      { exact Hold'. }
      { exact Hlen'. }
      { exact Hres. }
      { exact Hroom. }
      intros cfg2 Hc2.
      destruct Hc2 as (L' & A' & regs2 & m2 & md' & r & -> & Hpost & Hr0 & Hrnz & Hr16 & Hfresh &
                       (b1 & b2 & c1 & c2 & Hbl & Hbl' & Hc12) & Hkept & Hro2 & Hgk2 & Hub & Hcopy & Hinit & Hreg & Hres').
      pose proof Hpost as (HMR2 & HWF2 & Hbd2 & Hle2 & Hptr2 & Hp12 & (vm' & Emd) & Hfr2 & Hblk2 & Hscr2).
      destruct Hfresh as (Hr4096 & Hrceil & Hrimg).
      rewrite Eps in Hbl, Hkept.
      assert (Hnb : In (r, n + 16) (blocks L' A')) by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
      destruct (rf_blocks_user L' A' r (n + 16) Hnb) as (q & Hq & Eq).
      assert (Hpres : forall i, 0 <= i < n + 16 -> present m2 (r + i) /\ ~ owned B L' A' (r + i)).
      { intros i Hi. destruct (mr_blocks _ _ (aa_laws API) L' A' m2 md' q (n + 16) i HMR2 Hq Hi) as (P1 & _ & _ & P4).
        rewrite Eq in P1, P4. split; assumption. }
      assert (Hfs : forall a, S + -48 <= a < S ->
          mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\ (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { intros a Ha. apply Hfr2.
        - left. lia.
        - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A m1 md a HMR1 Ho). lia.
        - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' a HMR2 Ho). lia.
        - unfold scratch_k. rewrite Hs1. lia.
        - cbv beta. lia. }
      assert (Hwm1 : forall a, S + -48 <= a < S -> writable_at (ms_segs B) m1 a) by (intros a Ha; apply HW1, Hwrm; exact Ha).
      assert (Hwm2 : forall a, S + -48 <= a < S -> writable_at (ms_segs B) m2 a)
        by (intros a Ha; apply (proj2 (Hfs a Ha)), Hwm1; exact Ha).
      assert (Hg12 : forall a, in_globals omx_G a -> mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a).
      { intros a Ha. apply (kb_post_globals B API omx_G REALLOC_STACK L A regs1 m1 md _ L' A' regs2 m2 md' a HG HMR1 Hpost);
          [rewrite Hs1; lia | exact Ha |].
        cbv beta. intros He. pose proof (rf_glob_img B API HG a Ha) as Hai.
        apply (Himgb (a - (p - 16))); [lia|]. replace (p - 16 + (a - (p - 16))) with a by lia. exact Hai. }
      assert (Hw12 : forall a v, word_mem (ms_segs B) m1 a v -> (forall k', 0 <= k' < 8 -> in_globals omx_G (a + k')) ->
          word_mem (ms_segs B) m2 a v).
      { intros a v Hw Hk'. apply (word_mem_frame (ms_segs B) m1 m2 a v Hw). intros k' Hkk. apply Hg12, Hk', Hkk. }
      assert (Hlv1 : word_mem (ms_segs B) m1 G_LIVE (lsum (l1 ++ l2))).
      { pose proof (rf_bytes_word B m1 _ _ HL1) as H. rewrite Hsum in H.
        replace (lsum (l1 ++ l2) + k - k) with (lsum (l1 ++ l2)) in H by lia.
        rewrite Z.mod_small in H by lia. exact H. }
      assert (Hlv2 : word_mem (ms_segs B) m2 G_LIVE (lsum (l1 ++ l2)))
        by (apply Hw12; [exact Hlv1 | intros k' Hk'; apply rf_in_G; unfold G_LIVE; lia]).
      assert (Hpk2 : word_mem (ms_segs B) m2 G_PEAK peak)
        by (apply Hw12; [exact Hpk1 | intros k' Hk'; apply rf_in_G; unfold G_PEAK; lia]).
      assert (Hct2 : word_mem (ms_segs B) m2 G_COUNT ((cnt + 1) mod 2 ^ 64))
        by (apply Hw12; [exact Hct1 | intros k' Hk'; apply rf_in_G; unfold G_COUNT; lia]).
      assert (Hfl1 : word_mem (ms_segs B) m1 G_FAIL fail).
      { pose proof (rf_bytes_word B m1 _ _ HF1) as H. rewrite Z.mod_small in H by lia. exact H. }
      assert (Hfl2 : word_mem (ms_segs B) m2 G_FAIL fail)
        by (apply Hw12; [exact Hfl1 | intros k' Hk'; apply rf_in_G; unfold G_FAIL; lia]).
      assert (Hsb : forall a v, S + -48 <= a -> a + 8 <= S -> Mem.bytes_at (ms_segs B) m1 a (Mem.le8 v) ->
          Mem.bytes_at rsegs m2 a (Mem.le8 v) /\ Mem.wr_at rsegs m2 a 8).
      { intros a v Hx1 Hx2 Hb. rewrite <- HSEG. split.
        - apply (rf_bytes_frame B m1 m2 a _ Hb). intros i Hi. rewrite Mem.length_le8 in Hi. apply Hfs. lia.
        - apply (rf_wr_at B); [lia | lia | intros i Hi; apply Hwm2; lia]. }
      destruct (Hsb (S + -8) _ ltac:(lia) ltac:(lia) HS8) as (B8 & W8).
      destruct (Hsb (S + -16) _ ltac:(lia) ltac:(lia) HS16) as (B16 & W16).
      destruct (Hsb (S + -24) _ ltac:(lia) ltac:(lia) HS24) as (B24 & W24).
      destruct (Hsb (S + -32) _ ltac:(lia) ltac:(lia) HS32) as (B32 & W32).
      destruct (Hsb (S + -40) _ ltac:(lia) ltac:(lia) HS40) as (B40 & W40).
      assert (Hlam : lsum (l1 ++ l2) + n + 16 <= alloc_ceiling - 4096 /\ ~ In (r + 16) (map fst (l1 ++ l2))).
      { apply (MallocRuns.lam_room c1 c2 r n (l1 ++ l2) 4096 alloc_ceiling).
        - rewrite <- Hbl'. exact (mr_blocks_disjoint _ _ (aa_laws API) L' A' m2 md' HMR2).
        - rewrite <- Hbl'. intros [a kk] Hin. exact (rf_blk_range B API L' A' m2 md' a kk HMR2 Hin).
        - lia.
        - exact Hn0.
        - exact HND12.
        - apply Forall_forall. intros [a kk] Hx. rewrite Forall_forall in HFL.
          destruct (HFL (a, kk) ltac:(rewrite HLam; apply rf_in_mid; exact Hx)) as (Hk & Hin & _ & _). cbn [fst snd] in *.
          split; [exact Hk|]. rewrite Hc12. rewrite Hbl in Hin. apply (rf_in_drop _ _ _ _ Hin).
          intros E. injection E as E1 E2. apply Hpnot. apply in_map_iff. exists (a, kk). split; [cbn; lia | exact Hx]. }
      destruct Hlam as (Hlam & Hnin).
      assert (Hhs : r + 8 <= 0x33b40 \/ 0x33b40 + 24 <= r).
      { apply (rf_sep (in_img B) r 8 0x33b40 24); [lia | lia | | intros i Hi; apply Hrimg; lia].
        intros y Hy. apply (rf_glob_img B API HG), rf_in_G. lia. }
      assert (Hhf : r + 8 <= G_FAIL \/ G_FAIL + 8 <= r).
      { apply (rf_sep (in_img B) r 8 G_FAIL 8); [lia | lia | | intros i Hi; apply Hrimg; lia].
        intros y Hy. apply (rf_glob_img B API HG), rf_in_G. unfold G_FAIL in Hy. lia. }
      unfold G_FAIL in Hhf.
      assert (Hstk2 : Frame.stk rsegs m2 r (r + 8)).
      { rewrite <- HSEG. apply (rf_stk_present B); [lia | lia | intros i Hi; exact (proj1 (Hpres i ltac:(lia)))]. }
      assert (G2' : getr regs2 2 = Z_to_bv 64 (S + -48)) by (rewrite <- G2; apply (Hp12 2); unfold callee_saved; lia).
      assert (G8' : getr regs2 8 = Z_to_bv 64 n) by (rewrite <- G8; apply (Hp12 8); unfold callee_saved; lia).
      assert (G18' : getr regs2 18 = Z_to_bv 64 0x33b40) by (rewrite <- G18; apply (Hp12 18); unfold callee_saved; lia).
      rewrite G1.
      destruct (kb_md B API L' A' m2 md' HMR2) as (Hh2 & Hz2).
      apply (kb_run B regs2 _ m2 md'
        (fun R pc' mem' => ReallocRuns.run2_post (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
           (getr regs2 17) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25)
           (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)
           fp_regs fp_csr m2 S n r (lsum (l1 ++ l2)) peak (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
           (getr regs 19) (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh2 Hz2).
      { unfold rmk. rewrite G2', G8', G18', Hr0, HSEG.
        eapply Exec.evt_mono.
        - apply (ReallocRuns.run2 (getr regs2 1) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
            (getr regs2 9) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16)
            (getr regs2 17) (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
            (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)
            fp_regs fp_csr m2 S n r (lsum (l1 ++ l2)) peak (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
            (getr regs 19)); try assumption; try lia.
          + rewrite <- HSEG. apply word_mem_le8; [exact Hlv2 | lia | lia | lia].
          + rewrite <- HSEG. apply (globals_wr_at B API omx_G m2 _ (lsum (l1 ++ l2)) HG);
              [intros k' Hk'; apply rf_in_G; lia | exact Hlv2].
          + rewrite <- HSEG. apply word_mem_le8; [exact Hpk2 | lia | lia | lia].
          + rewrite <- HSEG. apply (globals_wr_at B API omx_G m2 _ peak HG); [intros k' Hk'; apply rf_in_G; lia | exact Hpk2].
        - intros ms Hp. pose proof Hp as (d1 & d2 & d3 & d4 & d5 & d6 & m' & _ & _ & _ & _ & _ & _ & E). subst ms.
          do 3 eexists. split; [reflexivity | exact Hp]. }
      intros R pc3 mem3 regs3 HK3 Hg3.
      destruct HK3 as (d1 & d2 & d3 & d4 & d5 & d6 & m3 & HM3 & HW3 & HP3 & HH3 & HL3 & HPk3 & E).
      rewrite <- HSEG in HW3, HH3, HL3, HPk3.
      pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
      cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM. subst R pc3 mem3. clear E.
      pose proof (mr_blocks_disjoint _ _ (aa_laws API) L' A' m2 md' HMR2) as Hdisj. rewrite Hbl' in Hdisj.
      destruct (MallocRuns.pairwise_mid _ c1 (r, n + 16) c2 Hdisj) as (Hz & _).
      assert (Hold3 : forall a kk i, In (a, kk) (blocks L A) -> a <> p - 16 -> 0 <= i < kk ->
          0 <= a + i < 2 ^ 64 /\ Frame.outside [(r, r + 8); (0x33b40, 0x33b50)] (a + i)).
      { intros a kk i Hin Hne Hi. pose proof (rf_blk_range B API L A mem md a kk HMR Hin) as Hrg. split; [lia|].
        apply kb_outside. intros lo hi Hw Hx. cbn in Hw. destruct Hw as [E|[E|[]]]; injection E as <- <-.
        - assert (Hin' : In (a, kk) (c1 ++ c2)).
          { rewrite Hc12. rewrite Hbl in Hin. apply (rf_in_drop _ _ _ _ Hin). intros E. injection E. lia. }
          destruct (Hz _ Hin') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
        - apply (rf_glob_free_at B API HG L A mem md (a + i) HMR); [apply rf_in_G; lia | right; exists a, kk; split; [exact Hin | lia]]. }
      assert (Hkeep : forall a kk i, In (a, kk) (blocks L A) -> a <> p - 16 -> 0 <= i < kk ->
          mbyte (ms_segs B) m3 (a + i) = mbyte (ms_segs B) mem (a + i)).
      { intros a kk i Hin Hne Hi. destruct (Hold3 a kk i Hin Hne Hi) as (Hr & Ho).
        rewrite (mbyte_munch (ms_segs B) _ m2 m3 (a + i) HM3 Hr Ho).
        rewrite (Hkept a kk i Hin Hne Hi). exact (Hkeep1 a kk i Hin Hi). }
      assert (Hown3 : forall x, 0 <= x < alloc_ceiling -> owned B L' A' x ->
          Frame.outside [(r, r + 8); (0x33b40, 0x33b50)] x).
      { intros x Hx Ho. apply kb_outside. intros lo hi Hw Hb. cbn in Hw. destruct Hw as [E|[E|[]]]; injection E as <- <-.
        - destruct (Hpres (x - r) ltac:(lia)) as (_ & Hno). replace (r + (x - r)) with x in Hno by lia. exact (Hno Ho).
        - exact (rf_glob_free_at B API HG L' A' m2 md' x HMR2 ltac:(apply rf_in_G; lia) (or_introl Ho)). }
      assert (Hinpl : forall q0 mm i, In (q0, mm) (user_blocks A) -> In (q0, mm) (user_blocks A') -> 0 <= i < mm ->
          mbyte (ms_segs B) m3 (ptr_addr L q0 + i) = mbyte (ms_segs B) m2 (ptr_addr L q0 + i)).
      { intros q0 mm i Hq0 Hq0' Hi.
        pose proof (rf_user_blocks_in L A q0 mm Hq0) as HinA.
        pose proof (rf_blk_range B API L A mem md _ _ HMR HinA) as Hrg.
        destruct (kb_outside_dec [(r, r + 8); (0x33b40, 0x33b50)] (ptr_addr L q0 + i)) as [Ho|Ho].
        - exact (mbyte_munch (ms_segs B) _ m2 m3 (ptr_addr L q0 + i) HM3 ltac:(lia) Ho).
        - destruct (rf_not_out _ _ Ho) as (lo & hi & Hw & Hb). cbn in Hw. destruct Hw as [E|[E|[]]]; injection E as <- <-.
          + assert (Ea : ptr_addr L' q0 = ptr_addr L q0) by exact (Hptr2 q0 mm Hq0 Hq0').
            assert (HinB : In (ptr_addr L q0, mm) (blocks L' A'))
              by (rewrite <- Ea; exact (rf_user_blocks_in L' A' q0 mm Hq0')).
            assert (Heq : (ptr_addr L q0, mm) = (r, n + 16)).
            { rewrite Hbl' in HinB. apply in_app_or in HinB. destruct HinB as [H|[H|H]].
              - exfalso. destruct (Hz _ (in_or_app _ _ _ (or_introl H))) as [D|D];
                  unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
              - symmetry. exact H.
              - exfalso. destruct (Hz _ (in_or_app _ _ _ (or_intror H))) as [D|D];
                  unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
            injection Heq as Ea0 Em. subst mm.
            assert (Hsame : (r, n + 16) = (p - 16, k + 16)).
            { rewrite Ea0, Hbl in HinA. apply in_app_or in HinA. destruct HinA as [H|[H|H]].
              - exfalso. assert (H' : In (r, n + 16) (c1 ++ c2)) by (rewrite Hc12; apply in_or_app; left; exact H).
                destruct (Hz _ H') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
              - symmetry. exact H.
              - exfalso. assert (H' : In (r, n + 16) (c1 ++ c2)) by (rewrite Hc12; apply in_or_app; right; exact H).
                destruct (Hz _ H') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
            injection Hsame as Er En.
            rewrite (Hblk2 q0 (n + 16) i Hq0 Hq0' Hi), Ea0, Er.
            rewrite (Hkeep1 (p - 16) (k + 16) i Hinb ltac:(lia)).
            pose proof (rf_bytes_word B m3 _ _ HH3) as W3. rewrite Z.mod_small in W3 by lia. rewrite Er in W3.
            replace i with (Z.of_nat (Z.to_nat i)) by lia.
            rewrite (W3 (Z.to_nat i) ltac:(lia)), (Hhd (Z.to_nat i) ltac:(lia)).
            replace n with k by lia. reflexivity.
          + exfalso. apply (rf_glob_free_at B API HG L A mem md (ptr_addr L q0 + i) HMR);
              [apply rf_in_G; lia | right; exists (ptr_addr L q0), mm; split; [exact HinA | lia]]. }
      apply SR_ret. exists L', A', regs3, m3, md', (r + 16).
      rewrite (kb_ret_pc _ Hra).
      split; [reflexivity|].
      split.
      { apply (rf_ro_agree_munch B _ m2 m3 Hro2 HM3). intros a Ha Ho. destruct (rf_not_out _ _ Ho) as (lo & hi & Hin & Hb).
        cbn in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
        - apply (rf_ro_false_notimg B HSEG); [lia|]. replace a with (r + (a - r)) by lia. apply Hrimg. lia.
        - apply (rf_ro_false_glob B API HG), rf_in_G. lia. }
      split.
      { intros i Hi. rewrite <- (Hown1 _ (rf_guard_owned B L A (ms_got_guard B + i) ltac:(lia))), <- (Hgk2 i Hi).
        pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' _ HMR2
          (rf_guard_owned B L' A' (ms_got_guard B + i) ltac:(lia))) as Hlow.
        eapply (mbyte_munch (ms_segs B) _ m2 m3); [exact HM3 | pose proof alloc_ceiling_lt; lia |].
        apply Hown3; [exact Hlow | apply rf_guard_owned; lia]. }
      split; [intros _; exact Hinit|].
      split; [intros Hd; rewrite Hinit in Hd; discriminate|].
      split.
      { apply (kb_post B API).
        - eapply (kb_mid_E B API).
          + eapply (rf_kb_mid_tail2 B API HIL _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a => alloc_statics a \/ r <= a < r + 8)).
            * eapply (kb_mid_seqAX B API).
              -- eapply (kb_mid_A B API HIL _ _ _ _ _ _ _ _ alloc_statics);
                   [exact HMR | exact HWF | exact Hbd | exact Hwmk | exact HM1 | exact HW1 | | exact Hcond1].
                 intros x Hx Hs He. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in He. rf_out.
              -- exact (proj1 (kb_mid_call B API _ L A regs1 m1 md _ L' A' regs2 m2 md' Hpost)).
              -- rewrite Hs1. lia.
              -- rewrite Hs1. lia.
              -- lia.
              -- lia.
              -- rewrite Hs1. intros a Ha Hn' He. cbv beta in He. lia.
            * exact HM3.
            * exact HW3.
            * exact HP3.
            * intros x Hx Hs He. cbv beta in He. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in He. rf_out.
            * exact Hown3.
            * exact Hinpl.
          + intros a Ha. cbv beta in Ha. unfold realloc_writes.
            destruct Ha as [[Ha|Ha]|[Ha|Ha]]; [left; exact Ha | right; left; split; [exact Hp0 | lia] | left; exact Ha
              | right; right; lia].
        - rf_cs_cases ltac:(rewrite Hg3; first
            [ reflexivity
            | exact (eq_sym Hsp)
            | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
                transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
                rewrite (Hp12 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
      split; [exact Hreg|].
      split; [rewrite Hg3; reflexivity|].
      right. split; [exact Hcf|]. split; [lia|].
      split; [replace (r + 16) with (r + 1 * 16) by lia; rewrite Z_mod_plus_full; exact Hr16|].
      split.
      { intros i Hi Hs. apply (Hrimg i Hi). replace (r + i) with (r + 16 - 16 + i) by lia.
        apply (rf_glob_img B API HG), rf_statics_G. exact Hs. }
      split; [intros i Hi; replace (r + 16 - 16 + i) with (r + i) by lia; exact (Hrimg i Hi)|].
      split; [intros a kk i Hin Hne Hi; exact (Hkeep a kk i Hin Hne Hi)|].
      split.
      { intros q0 kk Hq0 Hne. apply Hub; [exact Hq0|]. intros ->.
        apply Hne. f_equal; [exact Eps|].
        exact (rf_nodup_fst (user_blocks A) ps kk (k + 16) (proj2 (NoDup_ListNoDup _) (YO10.user_block_ptrs_NoDup A HWF)) Hq0 Hps). }
      split.
      { intros i Hi. replace (r + 16 + i) with (r + (16 + i)) by lia.
        rewrite (mbyte_munch (ms_segs B) _ m2 m3 (r + (16 + i)) HM3 ltac:(lia)).
        - rewrite (Hcopy (16 + i) ltac:(lia)). unfold old'. rewrite nth_error_app2 by lia.
          replace (Z.to_nat (16 + i) - length hd)%nat with (Z.to_nat i) by lia. reflexivity.
        - apply kb_outside. intros lo hi Hw Hx. cbn in Hw. destruct Hw as [E|[E|[]]]; injection E as <- <-; [lia|].
          apply (rf_glob_free_at B API HG L' A' m2 md' (r + (16 + i)) HMR2);
            [apply rf_in_G; lia | right; exists r, (n + 16); split; [exact Hnb | lia]]. }
      exists l1, l2. split.
      { right. split; [exact Hp0|]. split; [exact HLam|]. split; [exact Hres'|].
        exists b1, b2, c1, c2. split; [exact Hbl|]. split; [replace (r + 16 - 16) with r by lia; exact Hbl' | exact Hc12]. }
      split; [exact Hnin|].
      assert (Hsumn : (lsum (l1 ++ l2) + n) mod 2 ^ 64 = lsum (l1 ++ l2) + n)
        by (apply Z.mod_small; pose proof alloc_ceiling_lt; lia).
      rewrite Hsumn in HL3, HPk3.
      split.
      { split; [|split; [|split]].
        - cbn [lsum]. pose proof (rf_bytes_word B m3 _ _ HL3) as H. rewrite Z.mod_small in H by lia.
          replace (n + lsum (l1 ++ l2)) with (lsum (l1 ++ l2) + n) by lia. exact H.
        - pose proof (rf_bytes_word B m3 _ _ HPk3) as H. rewrite Z.mod_small in H by lia. exact H.
        - apply (kb_word_munch (ms_segs B) m2 m3 _ G_COUNT _ Hct2 HM3). intros k' Hk'. unfold G_COUNT. split; [lia | rf_out].
        - apply (kb_word_munch (ms_segs B) m2 m3 _ G_FAIL _ Hfl2 HM3). intros k' Hk'. unfold G_FAIL. split; [lia | rf_out]. }
      split; [cbn [lsum]; lia|].
      split; [pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64)); lia|].
      split; [lia|].
      split.
      { apply (proj2 (NoDup_ListNoDup _)). cbn [map fst]. constructor; [exact Hnin|].
        apply (proj1 (NoDup_ListNoDup _)). exact HND12. }
      constructor.
      * cbn [fst snd]. split; [lia|]. replace (r + 16 - 16) with r by lia. split; [exact Hnb|]. split.
        ** pose proof (rf_bytes_word B m3 _ _ HH3) as H. rewrite Z.mod_small in H by lia. exact H.
        ** exact Hrimg.
      * apply Forall_forall. intros [a kk] Hx. rewrite Forall_forall in HFL.
        assert (HxL : In (a, kk) Lam) by (rewrite HLam; apply rf_in_mid; exact Hx).
        destruct (HFL _ HxL) as (Hk & Hin & Hw & Himg). cbn [fst snd] in *.
        assert (Hne : a - 16 <> p - 16)
          by (intros E; apply Hpnot; apply in_map_iff; exists (a, kk); split; [cbn; lia | exact Hx]).
        split; [exact Hk|]. split.
        ** rewrite Hbl'. apply rf_in_mid. rewrite Hc12. rewrite Hbl in Hin. apply (rf_in_drop _ _ _ _ Hin).
          intros E. injection E. lia.
        ** split; [|exact Himg]. apply (word_mem_frame (ms_segs B) mem m3 (a - 16) kk Hw). intros k0 Hkk.
          exact (Hkeep (a - 16) (kk + 16) k0 Hin Hne ltac:(lia)).
Qed.

End FR.

Theorem fuzz_realloc_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> errno_addr B + 4 <= alloc_ceiling -> globals_free B API omx_G ->
  forall F : ResForm, realloc_contract_r B API F 0x184e8 -> fuzz_malloc_contract B API F -> fuzz_realloc_contract B API F.
Proof. intros fx rc B API H1 H2 H3 F H4 H5. exact (fuzz_realloc_holds_s B API F H1 H2 H3 H4 H5). Qed.
