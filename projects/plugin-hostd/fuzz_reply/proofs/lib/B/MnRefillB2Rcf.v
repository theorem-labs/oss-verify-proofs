(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillB2Rcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 8d5ac2d4be23) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane for a Theorem Labs lane, lane refill-b2): the B2 ENTRY of the cf refill walk at cgif's image,
   MnRefillSeamcf.refill_B2_entry_cf (the inited cache with at least max_cached / 2 free chunks), over the layer's
   call-site-generic machine leaf YGcfInstRefill.refill_leaf_core_cf at the window REP_STACK.
   The twin of c5 MnRefillR.refill_B2R (MnRefillR.v:119-178): the same composition, YFkwcf.seg2J then YFkwcf.segB2,
   then YFkzcf.LEAF_B2, from the call state (no tick: the tree is refill_tree_cf c S at the call's S).  The steps the
   cf form adds to c5's:
   - the window: the B2 walk runs in the RSTACK window, and REP_STACK_le (RSTACK <= REP_STACK) gives its stack premise
     and its window's presence from the call's, and widens its frames to the REP_STACK window; the presence of the
     part [sp - REP_STACK, sp - RSTACK) after the walk comes from the entry presence and the walk's machine frame (that
     part is stack, so it is not owned, YG0scf.AR_stack_law_ok_cf, and not in the walk's write set, YFkzcf.WR_owned);
   - the exception set: the B2 tree reports nothing, so LEAF_B2's empty exception gives refill_exc_cf's;
   - xs_mapped_cf at the result from ARX_cf's (YGcfXsMapped.xs_mapped_cf_wvb; the refill keeps the secondary list);
   - errno's view and the raw frame from at_RET2's memory clause off the walk's write set (c5 MnRefillR.v:157-165);
   - the memnorm keep as c5 MnRefillR.v:166-177;
   - the seed byte RI+68 is the junk value jex (YFkxcf.junk_exR).
   The unit facts are Section hypotheses: TS (the symbol record), IOK_ok (the instance object is cgif's allocator).
   EVENT-FREE.  rule 24: no function proved (kind: composition of the re-based refill walk's B2 segments). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFhy YFis YFhz YFkpcf YFkrcf YFhmcf YFkscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0qcf YG0scf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif2reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstRefill MnRefillSeamcf YGcfRefillCells.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFkocf YFkxcf YFkwcf YFkzcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT MemnormLoc MnRefillLocreply.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

Section b.
Variable B : asyms.
Variable IOK : Z -> Prop.
Hypothesis TS : TfibSyms B.
Hypothesis IOK_ok : forall i, IOK i -> i = A_ALLOCATOR.

(* cgif's image cover from the cf ledger (YF0x.img_cover_of_ledger's proof over ALedger_cf's alc_img). *)
Lemma img_cover_of_ledger_cgif_cf : forall ly S md, ALedger_cf tfibsegs ly S md -> img_cover ly.
Proof.
intros ly S md L. split.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFIB_IMG_END. lia.
Qed.

(* The B2 core: from the state after the B2 seed segment (at_R RJ2) to the layer's machine leaf at S.  Shared by the
   inited B2 entry (after YFkwcf.seg2J) and the uninit B2 case (after YFkycf.segU and the cache-init transport). *)
Section core.
Variables (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
  (md0 : Model) (c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex : Z) (matJ : list word) (msJ : machine_state).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Hypothesis HAR : ARcf tfibsegs B ly S Hp W mem0 md0.
Hypothesis HXM : xs_mapped_cf ly S md0.
Hypothesis HcR : 1 <= c <= 31.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hchunks : pc_chunks (cache S c) = [].
Hypotheses (Hmax : maxc = max_cached c) (Hn : n = maxc / 2) (Hcsz : csz = class_size c).
Hypotheses (Hnf_def : nf = fa_len (rg_free (reg S c))) (Hmf_def : mf = rg_mapped_fa (reg S c))
  (Hau_def : au = rg_alloc_user (reg S c)) (Hmu_def : mu = rg_mapped_user (reg S c)).
Hypothesis Hnle : n <= nf.
Hypothesis Hsp : ly_stk_lo ly + YFl1.RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis HloR : ly_stk_lo ly + REP_W c <= sp0.
Hypothesis HpresR : forall a, sp0 - REP_W c <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypotheses (Hj64 : 0 <= j64 < 2 ^ 32) (Hjna : 0 <= jna < 2 ^ 64) (Hjnf : 0 <= jnf < 2 ^ 64) (Hjsm : 0 <= jsm < 2 ^ 64)
  (Hjm1 : 0 <= jm1 < 2 ^ 64) (Hjm2 : 0 <= jm2 < 2 ^ 64) (Hjex : 0 <= jex < 2 ^ 8).
Hypothesis Hjexv : val_mem tfibsegs (mrestrict (w_H W) mem0) (@YFkocf.RGv ly c + 68) 1 jex.
Hypothesis HslotPres : forall a, @YFkocf.DSTv ly c <= a < @YFkocf.DSTv ly c + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, @YFkocf.FAv ly c <= a < @YFkocf.FAv ly c + mf -> apresent (w_H W) mem0 a.
Hypothesis HJ : @YFkocf.at_R _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex YFkrcf.RJ2 W
  (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0)).

Lemma refill_B2_core_reply : amreal tfibsegs (refill_tree_cf c S) W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))
  (refill_leaf_core_cf B Hp ly S c W regs0 mem0 md0).
Proof.
assert (SP0 : sp0 = bv_unsigned (getr regs0 2)) by reflexivity.
pose proof (proj1 HAR) as HARm.
pose proof REP_STACK_le as (RS0 & RS1 & RS2). pose proof (REP_W_le c) as (RW1 & RW2).
assert (RSW : YFl1.RSTACK <= REP_W c) by (clear - RW1; unfold YFl1.RSTACK; unfold ImgBaseAG.RSTACK in RW1; lia).
assert (LY : layout_ok ly) by exact (amc_layout _ _ _ _ _ HARm).
assert (IMG : img_cover ly) by exact (img_cover_of_ledger_cgif_cf ly S md0 (proj1 (proj2 HAR))).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (amc_tsd _ _ _ _ _ HARm); exact (ts_tsd B TS)).
assert (Hpres0R : forall a, sp0 - YFl1.RSTACK <= a < sp0 -> apresent (w_H W) mem0 a) by (intros a Ha; apply HpresR; clear - Ha RSW; lia).
pose proof (@YFkxcf.Hnf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@YFkxcf.Hmf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@YFkxcf.Hmu' _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex HcR Hjex Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
destruct (@YFkzcf.refill_B2_model _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex HcR Hmax Hn Hcsz Hnf Hmf Hmu Hjex Hsp B S Hp HARm Hinited Hchunks
  Hnf_def Hmf_def Hau_def Hmu_def Hnle) as (tops & rest & EP & RUN & WFR & E1 & E2 & E3 & E4).
rewrite RUN. cbn [amreal].
eapply SRr_mono.
{ exact (@YFkwcf.segB2 _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
    Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Hra Htp matJ msJ HJ HslotPres HfaPres Hnle). }
intros W'' c'' _ HR.
pose proof (@YFkzcf.LEAF_B2 _ _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
  Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp matJ msJ HJ HfaPres B S Hp TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hjexv
  HAR Hnle tops rest W'' c'' WFR E1 E2 E3 E4 HR) as (regs' & mem' & md' & Ec & POST & A0).
pose proof Ec as Ec0.
destruct HR as (-> & regs2 & mem2 & mat & Ec2 & _ & _ & MEQ' & _ & _ & _ & VR).
cbv zeta in VR. destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VJ).
assert (Hm : mem2 = mem') by (rewrite Ec2 in Ec0; unfold cfg_at in Ec0; inversion Ec0; reflexivity).
assert (Hmd : md' = with_vm_backing (m_vm_lazy md0) mat md0) by (rewrite Ec2 in Ec0; unfold cfg_at in Ec0; inversion Ec0; reflexivity).
subst mem2.
(* the walk's write set is the RSTACK window or owned at S (YFkzcf.WR_owned) *)
assert (WRO : forall x : word, YFkocf.WINR ly regs0 c n (bv_unsigned x) -> (sp0 - YFl1.RSTACK <= bv_unsigned x < sp0) \/ aowned B ly S (bv_unsigned x)).
{ intros x Hw. assert (Rx : 0 <= bv_unsigned x < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 x) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
  exact (@YFkzcf.WR_owned _ _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
    Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp B S Hp HAR (bv_unsigned x) Rx Hw). }
(* the raw frame off the REP_W c window and the owned set at S *)
assert (RAWF : forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ (sp0 - REP_W c <= bv_unsigned x < sp0) -> mem' x = mem0 x).
{ intros x NO NS. apply MEQ'. intros Hw. destruct (WRO x Hw) as [Hs|Ho]; [apply NS; clear - Hs RSW; lia | exact (NO Ho)]. }
(* the same, off the walk's own RSTACK window *)
assert (RAWR : forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ (sp0 - YFl1.RSTACK <= bv_unsigned x < sp0) -> mem' x = mem0 x).
{ intros x NO NS. apply MEQ'. intros Hw. destruct (WRO x Hw) as [Hs|Ho]; [exact (NS Hs) | exact (NO Ho)]. }
destruct POST as (AR' & LE & WLE & RP & IO & FRV & PRS).
exists ly, regs', mem', md'. split; [exact Ec|].
split.
{ (* acall_post_cf over REP_W c and refill_exc_cf *)
  split; [exact AR'|]. split; [exact LE|]. split; [exact WLE|]. split; [exact RP|]. split; [exact IO|]. split.
  - intros a Ra NO NO' NS NE. apply FRV; [exact Ra | exact NO | exact NO' | | intros []].
    intros [Hs|He]; apply NS; [left; change (sp0 - YFl1.RSTACK <= a < sp0) in Hs; change (sp0 - REP_W c <= a < sp0); clear - Hs RSW; lia | right; exact He].
  - intros a Ha. pose proof (lo_top ly LY) as LT. unfold kHighMemBeg, kHighMemEnd in LT.
    assert (Ha' : sp0 - REP_W c <= a < sp0) by exact Ha.
    destruct (Z_lt_le_dec a (sp0 - YFl1.RSTACK)) as [Hlt|Hge]; [|apply PRS; exact (conj Hge (proj2 Ha'))].
    assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; pose proof (u64_range (getr regs0 2)) as U64; clear - Ha' LT HloR SP0 U64 RSW; lia).
    assert (NOa : ~ aowned B ly S a) by (apply (AR_stack_law_ok_cf tfibsegs B ly S Hp W mem0 md0 a HAR); clear - Ha' HloR Hsp Hlt SP0 RSW; destruct Hsp; lia).
    pose proof (HpresR a Ha') as [Hh [b Hb]].
    split; [exact Hh|]. exists b. rewrite (RAWR (Z_to_bv 64 a)); [exact Hb | rewrite Ex; exact NOa | rewrite Ex; clear - Hlt; lia]. }
split; [exact A0|].
split; [intros _; reflexivity|].
split; [rewrite Hmd; exact (xs_mapped_cf_wvb ly S md0 (m_vm_lazy md0) mat HXM) |].
(* the two result cells: round 2 carries them in the result's ARmcf (YFkzcf.AR_transport) *)
split; [exact (amc_exh_cell _ _ _ _ _ (proj1 AR'))|].
split; [exact (amc_errb_cells _ _ _ _ _ (proj1 AR'))|].
split.
{ intros a Ra Herr NO NO' NS NE. apply aview_same. apply RAWF; rewrite unsigned_lit_small by exact Ra; [exact NO | exact NS]. }
split.
{ intros x NO NO' NS NE. apply RAWF; [exact NO | exact NS]. }
pose proof (@YFkocf.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DRk.
pose proof (class_ok c ltac:(clear - HcR; lia)) as (_ & _ & _ & KMC & _).
split.
{ (* the stack below the window, [sp - REP_STACK, sp - REP_W c): not in the walk's write set, so its bytes and their
     presence are the call's *)
  intros a HlS Ha Hp0. pose proof (lo_top ly LY) as LT. unfold spZ in Ha. pose proof (u64_range (getr regs0 2)).
  assert (Ex : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; clear - Ha HlS LT H RW1 RS0; unfold kHighMemBeg, kHighMemEnd in LT; unfold ImgBaseAG.RSTACK in *; lia).
  apply (apresent_same _ mem0 mem' a); [|exact Hp0]. apply MEQ'. rewrite Ex.
  pose proof (@YFkocf.high_factsR _ ly regs0 maxc mf au mu LY IMG Hmf Hmu) as HF.
  destruct HF as (_ & _ & _ & _ & HPR & _ & _ & _ & _ & HST).
  assert (HSa : ly_stk_lo ly <= a < ly_stk_hi ly) by (clear - Ha HlS Hsp RW1 RS0 SP0; destruct Hsp as (_ & ? & _); unfold ImgBaseAG.RSTACK in *; lia).
  destruct (HST a HSa) as [NT NP].
  destruct DRk as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & _ & _ & _ & _ & _ & _ & D16 & D17 & _ & _ & D20 & _).
  pose proof (YFkocf.class_facts ly regs0 c maxc n mf au mu csz HcR Hmax Hn Hcsz Hmf Hmu) as CF.
  unfold YFkocf.WINR, YFkocf.WINR0. intros Hw.
  destruct Hw as [[Hw|[Hw|[Hw|[Hw|Hw]]]]|Hw].
  - clear - Hw Ha RSW. lia.
  - apply NT. clear - Hw D2 D4. unfold YFkocf.Pr, t_cache, kThreadObjSize in *. lia.
  - apply NP. clear - Hw D8 D17 HPR. lia.
  - apply NT. clear - Hw. unfold kThreadObjSize. lia.
  - apply NT. clear - Hw. unfold kThreadObjSize. lia.
  - apply NT. clear - Hw D2 D4 D20 CF. rewrite D20 in Hw. unfold YFkocf.Pr, t_cache, kThreadObjSize in *. lia. }
(* the memnorm keep (c5 MnRefillR.v:166-177) *)
eapply MemnormT.memnorm_frame; [| exact MEQ'].
intros x Hw. unfold YFkocf.WINR, YFkocf.WINR0, YFkocf.DSTv in Hw.
destruct Hw as [[Hw|[Hw|[Hw|[Hw|Hw]]]]|Hw].
- apply (MnRefillLocreply.mn_safe_stack ly x LY). destruct Hsp as (Q1 & Q3 & _). clear - Hw Q1 Q3 SP0. unfold RSTACK in *. lia.
- apply (MnRefillLocreply.mn_safe_thread ly x LY IMG). clear - Hw DRk. unfold YFkocf.Pr, t_cache, kThreadObjSize in *. lia.
- apply MemnormLoc.mn_safe_ceil. clear - Hw DRk. unfold kHighMemBeg, kImgEnd in *. lia.
- apply (MnRefillLocreply.mn_safe_thread ly x LY IMG). clear - Hw. unfold kThreadObjSize in *. lia.
- apply (MnRefillLocreply.mn_safe_thread ly x LY IMG). clear - Hw. unfold kThreadObjSize in *. lia.
- apply (MnRefillLocreply.mn_safe_thread ly x LY IMG). clear - Hw DRk KMC Hn Hmax. unfold YFkocf.Pr, t_cache, kThreadObjSize in *. lia.
Qed.
End core.

Theorem refill_B2_entry_reply : refill_B2_entry_cf B IOK.
Proof.
intros Hp inst ly S W regs0 mem0 md0 c HS _ _ HC [Hinited Henough].
destruct HS as (HARX & HWF1 & HQL & HBR & HER & HcR & Hchunks).
pose proof (ARX_cf_ARcf B IOK Hp inst ly S W mem0 md0 HARX) as HAR.
pose proof (ARX_cf_xsm B IOK Hp inst ly S W mem0 md0 HARX) as HXM.
pose proof (IOK_ok inst (ARX_cf_iok B IOK Hp inst ly S W mem0 md0 HARX)) as Hinst.
destruct HC as (Hra & Hra4096 & Hal & Hlo & Hhi & HpresR & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
pose proof (proj1 HAR) as HARm.
pose proof (REP_W_le c) as (RW1 & RW2).
(* REP_W_le speaks of ImgBaseAG.RSTACK; the B2 walk's window is YFl1.RSTACK (both 1024) *)
assert (RSW : YFl1.RSTACK <= REP_W c) by (unfold YFl1.RSTACK; unfold ImgBaseAG.RSTACK in RW1; lia).
assert (LY : layout_ok ly) by exact (amc_layout _ _ _ _ _ HARm).
assert (IMG : img_cover ly) by exact (img_cover_of_ledger_cgif_cf ly S md0 (proj1 (proj2 HAR))).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (amc_tsd _ _ _ _ _ HARm); exact (ts_tsd B TS)).
rewrite Hinst in Ha2.
unfold spZ, raZ in *.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + YFl1.RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (repeat split; lia).
assert (Hpres0R : forall a, sp0 - YFl1.RSTACK <= a < sp0 -> apresent (w_H W) mem0 a) by (intros a Ha; apply HpresR; lia).
set (maxc := max_cached c). set (n := maxc / 2). set (nf := fa_len (rg_free (reg S c))). set (mf := rg_mapped_fa (reg S c)).
set (au := rg_alloc_user (reg S c)). set (mu := rg_mapped_user (reg S c)). set (csz := class_size c). set (mat0 := m_vm_materialized md0).
assert (Hmax : maxc = max_cached c) by reflexivity. assert (Hn : n = maxc / 2) by reflexivity. assert (Hcsz : csz = class_size c) by reflexivity.
assert (Hnf_def : nf = fa_len (rg_free (reg S c))) by reflexivity. assert (Hmf_def : mf = rg_mapped_fa (reg S c)) by reflexivity.
assert (Hau_def : au = rg_alloc_user (reg S c)) by reflexivity. assert (Hmu_def : mu = rg_mapped_user (reg S c)) by reflexivity.
assert (Hnle : n <= nf) by exact Henough.
assert (J0 : 0 <= 0 < 2 ^ 8) by lia.
pose proof (@YFkxcf.Hnf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@YFkxcf.Hmf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@YFkxcf.Hmu' _ _ _ W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
destruct (@YFkxcf.junk_valuesR _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz 0 LY IMG HcR Hmax Hn Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def)
  as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
destruct (@YFkxcf.junk_exR _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz 0 LY IMG HcR Hmax Hn Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def)
  as (jex & Hjex & Hjexv).
pose proof (@YFkxcf.HslotPres' _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex LY IMG HcR Hmax Hn Hcsz Hjex Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPres.
pose proof (@YFkxcf.HfaPres' _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz jex LY IMG HcR Hmax Hn Hcsz Hjex Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPres.
pose proof (@YFkxcf.SEEDR_ok _ _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
  Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S Hp TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def
  Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv) as SEEDR.
replace (cfg_at im_segs ag_refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x36a20) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
  by (unfold cfg_at; subst mat0; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@YFkwcf.seg2J _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp mat0 SEEDR). }
intros W' c' _ HJ. pose proof HJ as [EW (msJ & matJ & E' & EcJ & _)]. subst W'. rewrite EcJ in HJ |- *.
eapply (refill_B2_core_reply Hp ly S W regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex matJ msJ); eassumption.
Qed.
End b.
End a.

Print Assumptions refill_B2_entry_reply.
About refill_B2_entry_reply.
