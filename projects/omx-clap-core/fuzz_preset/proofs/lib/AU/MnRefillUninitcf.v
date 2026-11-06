(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillUninitcf.v (commit 3cae605a900a, file sha256 f0e91c9ada62) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; cgif's image-instance names kept where preset's B' instance carries them (AGif2cgif, AImg_cgif), CfImg_cgif -> CfImg_B, cgif's image rows mapped to preset's (YGcfImgcgif.* -> CfImgB / PresetImgRefillB / PresetImgRowsB, *cgif -> *preset); its 2 image numerals moved by symbol from cgif_file_fuzzer.asan-ubsan (pin 1c29845fe605, unstripped twin of the same build) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets, derived counts and list indices by the same stage map), 0 list indices re-picked, and 0 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker for a Theorem Labs lane, lane refill-b2): the UNINIT ENTRY of the cf refill walk at cgif's
   image, MnRefillSeamcf.refill_uninit_entry_cf (the caches not yet inited), over the layer's machine leaf
   YGcfInstRefill.refill_leaf_core_cf.  The twin of c5 MnRefillR Section d (refill_uninit_B3R / refill_uninit_B2R /
   refill_uninitR, MnRefillR.v:180-396): the cache-init segment (YFkycf.segU for the B2 path, YFklcf.segU for B3), the
   relation moved to the post-init state S1 = YFhn.S1 S at the post-init memory memR (YFhncf.ARcf_init, PRES_MONO,
   VIS_MONO, val_mem_R), then the inited case at S1 (B2: MnRefillB2Rcf.refill_B2_core_cgif; B3: the seam's
   refill_B3_inner_cf, a premise: CfW's lane proves it), and the leaf moved back from (S1, memR) to (S, mem0)
   (refill_leaf_core_init_cf: memR differs from mem0 only on the thread object's cache table TABW, which is owned).
   The unit facts are Section hypotheses: TS, IOK_ok (field round 2 carries the cells and their image rows in ARmcf).
   Field round 3 (part 3c: no memnorm): the entry has arodata_ok_cf and the hull admission at the call state (the
   seam's refill_case_cf); the B3 case gives them to the inner walk at the post-init state (S1, memR): arodata_ok_cf
   from the entry's by the init segment's frame (memR differs from mem0 only on TABW, inside the thread object, apart
   from every non-owned RELRO byte, YG0dcf.relro_apart_cf at cgif's RELRO row YGcfImgcgif.relro_seg_cgif, so the file
   is at cgif's CfImg_cgif), the admission by cf_hull_counts (S1 keeps st_secs).
   EVENT-FREE.  rule 24: no function proved (kind: composition of the re-based refill walk's segments). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhy YFis YFhz. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YFkpcf YFkrcf YFhmcf YFkscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0qcf YG0scf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import MnRefillSeamcf YGcfRefillCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFhn. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFhncf YFkocf YFkxcf YFkycf YFkzcf MnRefillB2Rcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFk5cf YFk8cf YFkkcf YFklcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormLoc MnRefillLocpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRodata. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PresetImgRefillB PresetImgRowsB. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
(* cgif's image constants: the RELRO row of the post-init arodata_ok_cf is cgif's (YGcfImgcgif.relro_seg_cgif) *)
#[local] Existing Instance CfImgB.CfImg_B.
Local Open Scope am_scope.

(* The cf tree at an uninit state is the tree at the post-init state (YFhn.refill_tree_init for the cf tree). *)
Lemma refill_tree_cf_init : forall c S, st_cache_inited S = false -> refill_tree_cf c S = refill_tree_cf c (YFhn.S1 S).
Proof.
intros c S HU. unfold refill_tree_cf, init_cache_if_needed, bind, get, put, ret, YFhn.S1.
cbn [ibind st_cache_inited set_cache_inited set_cache]. rewrite HU. cbn [ibind]. reflexivity.
Qed.

(* The post-init memory: the call's memory with the init segment's bytes of the thread object's cache table. *)
Definition memR (T : Z) (mem0 mJ : word -> option byte) : word -> option byte :=
fun x => if tabwb T (bv_unsigned x) then mJ x else mem0 x.
Lemma memR_off : forall T mem0 mJ x, ~ TABW T (bv_unsigned x) -> memR T mem0 mJ x = mem0 x.
Proof. intros T mem0 mJ x Hx. unfold memR. destruct (tabwb T (bv_unsigned x)) eqn:E; [|reflexivity]. exfalso. apply Hx. apply tabwb_spec. exact E. Qed.
Lemma memR_on : forall T mem0 mJ x, TABW T (bv_unsigned x) -> memR T mem0 mJ x = mJ x.
Proof. intros T mem0 mJ x Hx. unfold memR. apply tabwb_spec in Hx. rewrite Hx. reflexivity. Qed.

Section b.
Variable B : asyms.
Variable IOK : Z -> Prop.
Hypothesis TS : TfibSyms B.
Hypothesis IOK_ok : forall i, IOK i -> i = A_ALLOCATOR.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The leaf back across the init step (c5 MnRefillR.refill_leaf_initR for refill_leaf_core_cf).                   *)
Lemma refill_leaf_core_init_cf : forall Hp ly S W memU memR' md c regs r W' c',
  ARcf tfibsegs B ly S Hp W memU md -> img_cover ly ->
  (forall x : word, ~ TABW (ly_T ly) (bv_unsigned x) -> memR' x = memU x) ->
  (forall a, TABW (ly_T ly) a -> apresent (w_H W) memR' a) ->
  refill_leaf_core_cf B Hp ly (YFhn.S1 S) c W regs memR' md r W' c' ->
  refill_leaf_core_cf B Hp ly S c W regs memU md r W' c'.
Proof.
intros Hp ly S W memU memR' md c regs r W' c' HAR IMG MEQ TPR
  (ly' & regs' & mem' & md' & Ec & (AR' & LE & WLE & RP & IO & FR & PR) & A0 & A0L & XM & EXC & ERC & ERV & RAW & KEEP & MNK).
pose proof (proj1 HAR) as HARm.
assert (LY : layout_ok ly) by exact (amc_layout _ _ _ _ _ HARm).
(* every TABW byte is owned at S (the thread object is a core extent) *)
assert (OWN : forall a, TABW (ly_T ly) a -> aowned B ly S a).
{ intros a Ht. apply (own_core_cf B ly S Hp _ (ly_T ly, kThreadObjSize) a HARm); [unfold core_extents; cbn; tauto | cbn [fst snd]].
  apply TABW_range in Ht. unfold kThreadObjSize. lia. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> aview tfibsegs (w_H W) memR' a = aview tfibsegs (w_H W) memU a).
{ intros a Ra NO. apply aview_same. apply MEQ. rewrite unsigned_lit_small by exact Ra. intros Ht. exact (NO (OWN a Ht)). }
exists ly', regs', mem', md'. split; [exact Ec|].
split.
{ split; [exact AR'|]. split; [exact LE|]. split; [exact WLE|]. split; [exact RP|]. split; [exact IO|]. split; [|exact PR].
  intros a Ra NO NO' NS NE. rewrite (FR a Ra NO NO' NS NE). exact (AG a Ra NO). }
split; [exact A0|]. split; [exact A0L|]. split; [exact XM|]. split; [exact EXC|]. split; [exact ERC|].
split.
{ intros a Ra He NO NO' NS NE. rewrite (ERV a Ra He NO NO' NS NE). exact (AG a Ra NO). }
split.
{ intros x NO NO' NS NE. rewrite (RAW x NO NO' NS NE). apply MEQ. intros Ht. exact (NO (OWN _ Ht)). }
split.
{ intros a HlS Ha Hp0. apply (KEEP a HlS Ha).
  destruct (TABW_dec (ly_T ly) a) as [Ht|Ht]; [exact (TPR a Ht)|].
  assert (Ra : 0 <= a < 2 ^ 64).
  { pose proof (lo_top ly LY) as (_ & _ & _ & HT & _ & _ & HB). unfold spZ in Ha. pose proof (u64_range (getr regs 2)).
    pose proof (REP_W_le c) as [RW1 _]. pose proof REP_STACK_le as (RS0 & _ & _).
    clear - Ha HlS HB H RW1 RS0. unfold kHighMemBeg in *. lia. }
  apply (apresent_same _ memU memR' a); [|exact Hp0]. apply MEQ. rewrite unsigned_lit_small by exact Ra. exact Ht. }
assert (IMG' : img_cover ly) by exact IMG.
apply (MemnormLoc.memnorm_keep_trans tfibsegs memU memR' mem'); [|exact MNK].
apply (MemnormT.memnorm_frame tfibsegs (fun z => TABW (ly_T ly) z) memU memR').
- intros x Ht. apply (MnRefillLocpreset.mn_safe_thread ly x LY IMG'). apply TABW_range in Ht. unfold kThreadObjSize. lia.
- intros x Hx. exact (MEQ x Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The uninit B2 case (c5 MnRefillR.refill_uninit_B2R): YFkycf.segU, the cache-init transport, the B2 core at S1.  *)
Lemma uninit_B2_preset : forall Hp inst ly S W regs0 mem0 md0 c,
  refill_state_gen_cf B IOK Hp inst ly S W mem0 md0 c -> refill_call_gen_cf B inst ly W regs0 mem0 c ->
  st_cache_inited S = false -> max_cached c / 2 <= fa_len (rg_free (reg S c)) ->
  amreal im_segs (refill_tree_cf c S) W (cfg_at im_segs ag_refill regs0 mem0 md0) (refill_leaf_core_cf B Hp ly S c W regs0 mem0 md0).
Proof.
intros Hp inst ly S W regs0 mem0 md0 c HS HC Huninit Henough.
destruct HS as (HARX & HWF1 & HQL & HBR & HER & HcR & Hchunks).
pose proof (ARX_cf_ARcf B IOK Hp inst ly S W mem0 md0 HARX) as HAR.
pose proof (ARX_cf_xsm B IOK Hp inst ly S W mem0 md0 HARX) as HXM.
pose proof (IOK_ok inst (ARX_cf_iok B IOK Hp inst ly S W mem0 md0 HARX)) as Hinst.
destruct HC as (Hra & Hra4096 & Hal & Hlo & Hhi & HpresR & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
pose proof (proj1 HAR) as HARm.
pose proof (REP_W_le c) as (RW1 & RW2).
(* REP_W_le speaks of ImgBaseAG.RSTACK; the B2 walk's window is YFl1.RSTACK (both 1024) *)
assert (RSW : YFl1.RSTACK <= REP_W c) by (unfold YFl1.RSTACK; unfold ImgBaseAG.RSTACK in RW1; lia).
pose proof (ARX_cf_exh B IOK Hp inst ly S W mem0 md0 HARX) as HEXC.
pose proof (ARX_cf_errb B IOK Hp inst ly S W mem0 md0 HARX) as HERC.
assert (LY : layout_ok ly) by exact (amc_layout _ _ _ _ _ HARm).
assert (IMG : img_cover ly) by exact (MnRefillB2Rcf.img_cover_of_ledger_cgif_cf ly S md0 (proj1 (proj2 HAR))).
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
pose proof (@YFkxcf.thread_present _ _ _ W ly regs0 mem0 c maxc nf mf au mu jex LY IMG HcR Hjex Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as HTP.
pose proof (@YFkxcf.SPAN_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp) as HSPAN.
pose proof (@YFkxcf.SEEDU_ok _ _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
  Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S Hp TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def
  Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv Huninit) as SEEDU.
replace (cfg_at im_segs ag_refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x37494) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
  by (unfold cfg_at; subst mat0; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@YFkycf.segU _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu
    Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp mat0 HTP HSPAN SEEDU). }
intros W' c' _ HP. destruct HP as (-> & msJ & matJ & E' & -> & HE & HSJ & MEQ & PRS & TBF & TPR).
set (T := ly_T ly).
set (mR := memR T mem0 (ms_mem msJ)).
assert (R64 : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. unfold T.
  pose proof (lo_stk_ceil ly LY) as HC. pose proof (lo_top ly LY) as (L1 & L2 & L3 & HT & _ & _ & HB). clear - IT HC L1 L2 L3 HT HB.
  ceil; unfold kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
assert (CEIL64 : ASAN_CEIL <= 2 ^ 64) by (pose proof (lo_stk_ceil ly LY) as HC; pose proof (lo_top ly LY) as (L1 & L2 & L3 & HT & _); clear - HC L1 L2 L3 HT; unfold kHighMemEnd in HT; lia).
assert (MEQR : forall x : word, ~ TABW T (bv_unsigned x) -> mR x = mem0 x) by (intros x Hx; exact (memR_off T mem0 (ms_mem msJ) x Hx)).
assert (TBFR : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) mR) T i).
{ intros i Hi. destruct (TBF i Hi) as [M1 M2].
  split; (eapply val_mem_frame; [|eassumption]); intros k Hk; unfold mR; apply memR_on; rewrite unsigned_lit_small by (clear - Hi Hk R64 CEIL64; unfold kThreadObjSize in R64; lia); exists i; clear - Hi Hk; lia. }
assert (TPRR : forall a, TABW T a -> apresent (w_H W) mR a).
{ intros a Ha. pose proof (TABW_range T a Ha).
  eapply apresent_same; [|exact (TPR a Ha)]. unfold mR. apply memR_on. rewrite unsigned_lit_small by (clear - H R64 CEIL64; unfold kThreadObjSize in R64; lia). exact Ha. }
pose proof (YFhncf.ARcf_init B ly S Hp W mem0 mR md0 TS HAR Huninit MEQR TBFR TPRR IMG) as HAR1.
assert (PRESR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mR a) by (intros a; exact (YFhncf.PRES_MONO ly W mem0 mR MEQR TPRR a)).
assert (Hinited1 : st_cache_inited (YFhn.S1 S) = true) by reflexivity.
assert (Hchunks1 : pc_chunks (cache (YFhn.S1 S) c) = []) by (rewrite (YFhncf.cache_S1 B ly S Hp W mem0 md0 HAR Huninit c HcR); reflexivity).
assert (Hnf_def1 : nf = fa_len (rg_free (reg (YFhn.S1 S) c))) by exact Hnf_def.
assert (Hmf_def1 : mf = rg_mapped_fa (reg (YFhn.S1 S) c)) by exact Hmf_def.
assert (Hau_def1 : au = rg_alloc_user (reg (YFhn.S1 S) c)) by exact Hau_def.
assert (Hmu_def1 : mu = rg_mapped_user (reg (YFhn.S1 S) c)) by exact Hmu_def.
pose proof (@YFkocf.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
(* the region info, the thread object's tail and the errbuf / exh bytes are off TABW *)
assert (NTRG : forall a, @YFkocf.RGv ly c <= a < @YFkocf.RGv ly c + 128 -> ~ TABW T a).
{ intros a Ha Ht. apply TABW_range in Ht. destruct DR as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & _ & _ & _ & _ & _ & _ & D17 & _).
  pose proof (lo_space_in ly LY) as [SP1 SP2].
  clear - Ha Ht D8 D17 SP2 PT. unfold T in *. unfold kThreadObjSize in *. lia. }
assert (NTT : forall a, T + 2768 <= a -> ~ TABW T a) by (intros a Ha Ht; apply TABW_range in Ht; clear - Ha Ht; lia).
assert (JV : forall a (w : nat) v, ~ (exists k, 0 <= k < Z.of_nat w /\ TABW T (a + k)) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) a w v -> val_mem tfibsegs (mrestrict (w_H W) mR) a w v).
{ intros a w v NT A0 A1 HV. apply (YFhncf.val_mem_R ly W mem0 mR MEQR a w v); [intros k Hk Ht; apply NT; exists k; tauto | exact A0 | exact A1 | exact HV]. }
destruct DR as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & _ & _ & _ & _ & _ & _ & D16 & D17 & _).
assert (Hj64v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (@YFkocf.RGv ly c + 64) 4 j64)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTRG; clear - Hk; cbn in Hk; lia | clear - D5; unfold kHighMemBeg in D5; lia | clear - D6 CEIL64; cbn; lia | exact Hj64v]).
assert (Hjnav1 : val_mem tfibsegs (mrestrict (w_H W) mR) (@YFkocf.RGv ly c + 72) 8 jna)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTRG; clear - Hk; cbn in Hk; lia | clear - D5; unfold kHighMemBeg in D5; lia | clear - D6 CEIL64; cbn; lia | exact Hjnav]).
assert (Hjnfv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (@YFkocf.RGv ly c + 80) 8 jnf)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTRG; clear - Hk; cbn in Hk; lia | clear - D5; unfold kHighMemBeg in D5; lia | clear - D6 CEIL64; cbn; lia | exact Hjnfv]).
assert (Hjexv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (@YFkocf.RGv ly c + 68) 1 jex)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTRG; clear - Hk; cbn in Hk; lia | clear - D5; unfold kHighMemBeg in D5; lia | clear - D6 CEIL64; cbn; lia | exact Hjexv]).
assert (Hjsmv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2792) 8 jsm)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTT; clear - Hk; cbn in Hk; lia | clear - R64; lia | clear - R64 CEIL64; unfold kThreadObjSize in R64; cbn; lia | exact Hjsmv]).
assert (Hjm1v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2872) 8 jm1)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTT; clear - Hk; cbn in Hk; lia | clear - R64; lia | clear - R64 CEIL64; unfold kThreadObjSize in R64; cbn; lia | exact Hjm1v]).
assert (Hjm2v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2880) 8 jm2)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTT; clear - Hk; cbn in Hk; lia | clear - R64; lia | clear - R64 CEIL64; unfold kThreadObjSize in R64; cbn; lia | exact Hjm2v]).
assert (HslotPres1 : forall a, @YFkocf.DSTv ly c <= a < @YFkocf.DSTv ly c + 64 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HslotPres, Ha).
assert (HfaPres1 : forall a, @YFkocf.FAv ly c <= a < @YFkocf.FAv ly c + mf -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HfaPres, Ha).
assert (HpresR1 : forall a, sp0 - REP_W c <= a < sp0 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HpresR, Ha).
assert (HXM1 : xs_mapped_cf ly (YFhn.S1 S) md0) by exact HXM.
(* the entry cells at the post-init state: round 2 carries them in ARmcf (YFhncf.ARcf_init) *)
assert (HEXC1 := amc_exh_cell _ _ _ _ _ (proj1 HAR1)).
assert (HERC1 := amc_errb_cells _ _ _ _ _ (proj1 HAR1)).
(* the at_R seed of the B2 core at the post-init memory *)
assert (HJ : @YFkocf.at_R _ W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex YFkrcf.RJ2 W
  (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))).
{ split; [reflexivity|]. exists msJ, matJ, E'. split; [reflexivity|]. split; [exact (proj1 HE)|]. split; [exact HSJ|]. split; [|exact PRS].
  intros x Hx. destruct (TABW_dec T (bv_unsigned x)) as [Ht|Ht]; [unfold mR; rewrite (memR_on _ _ _ x Ht); reflexivity | rewrite (MEQR x Ht); exact (MEQ x Hx Ht)]. }
rewrite (refill_tree_cf_init c S Huninit).
eapply amreal_mono; [intros r W'' c'' HL; eapply refill_leaf_core_init_cf; [exact HAR | exact IMG | exact MEQR | exact TPRR | exact HL]|].
eapply MnRefillB2Rcf.refill_B2_core_preset with (Hp := Hp) (ly := ly) (S := YFhn.S1 S) (W := W) (regs0 := regs0) (mem0 := mR)
  (md0 := md0) (c := c) (maxc := maxc) (n := n) (nf := nf) (mf := mf) (au := au) (mu := mu) (csz := csz) (j64 := j64) (jna := jna)
  (jnf := jnf) (jsm := jsm) (jm1 := jm1) (jm2 := jm2) (jex := jex) (matJ := matJ) (msJ := msJ); eassumption.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The uninit B3 case (c5 MnRefillR.refill_uninit_B3R): YFklcf.segU, the cache-init transport, the inner B3 walk at S1
   (refill_B3_inner_cf, the premise HIN, with the three round-3 facts at (S1, memR)), the leaf back to S. *)
Section u3.
Hypothesis HIN : refill_B3_inner_cf.
Lemma uninit_B3_preset : forall Hp inst ly S W regs0 mem0 md0 c,
  refill_state_gen_cf B IOK Hp inst ly S W mem0 md0 c ->
  arodata_ok_cf tfibsegs B mem0 -> cf_hull_ok S ->
  refill_call_gen_cf B inst ly W regs0 mem0 c ->
  st_cache_inited S = false -> fa_len (rg_free (reg S c)) < max_cached c / 2 ->
  amreal im_segs (refill_tree_cf c S) W (cfg_at im_segs ag_refill regs0 mem0 md0) (refill_leaf_core_cf B Hp ly S c W regs0 mem0 md0).
Proof.
intros Hp inst ly S W regs0 mem0 md0 c HS AD HO HC Huninit Hfew.
destruct HS as (HARX & HWT & HQL & HBR & HER & HcR & Hchunks).
destruct HC as (Hra & Hra4096 & Hal & HloW & Hhi & HpresW & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
pose proof (ARX_cf_iok B IOK Hp inst ly S W mem0 md0 HARX) as HI. rewrite (IOK_ok inst HI) in Ha2.
pose proof (ARX_cf_ARcf B IOK Hp inst ly S W mem0 md0 HARX) as HAR.
pose proof (ARX_cf_xsm B IOK Hp inst ly S W mem0 md0 HARX) as HXSM.
pose proof (ARX_cf_exh B IOK Hp inst ly S W mem0 md0 HARX) as HEXH.
pose proof (ARX_cf_errb B IOK Hp inst ly S W mem0 md0 HARX) as HERRB.
change (YG0ncf.ARcf tfibsegs B ly S Hp W mem0 md0) in HAR.
pose proof (proj1 HAR) as HARm.
assert (LY : layout_ok ly) by exact (amc_layout _ _ _ _ _ HARm).
assert (IMG : img_cover ly) by exact (MnRefillB2Rcf.img_cover_of_ledger_cgif_cf ly S md0 (proj1 (proj2 HAR))).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (amc_tsd _ _ _ _ _ HARm); exact (ts_tsd B TS)).
change (getr regs0 4 = w64 TFIB_TP) in Htp.
unfold spZ, raZ in *.
pose proof (REP_W_le c) as [RW0 RW1].
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (repeat split; lia).
assert (Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a) by (intros a Ha; apply HpresW; lia).
set (maxc := max_cached c). set (n := maxc / 2). set (nf := fa_len (rg_free (reg S c))). set (mf := rg_mapped_fa (reg S c)).
set (au := rg_alloc_user (reg S c)). set (mu := rg_mapped_user (reg S c)). set (csz := class_size c). set (mat0 := m_vm_materialized md0).
assert (Hmax : maxc = max_cached c) by reflexivity. assert (Hn : n = maxc / 2) by reflexivity. assert (Hcsz : csz = class_size c) by reflexivity.
assert (Hnf_def : nf = fa_len (rg_free (reg S c))) by reflexivity. assert (Hmf_def : mf = rg_mapped_fa (reg S c)) by reflexivity.
assert (Hau_def : au = rg_alloc_user (reg S c)) by reflexivity. assert (Hmu_def : mu = rg_mapped_user (reg S c)) by reflexivity.
assert (Hnlt : nf < n) by exact Hfew.
assert (J0 : 0 <= 0 < 2 ^ 8) by lia.
pose proof (@YFkkcf.Hnf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@YFkkcf.Hmf' _ _ _ W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@YFkkcf.Hmu' _ _ _ W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
pose proof (@YFkkcf.Hcarved' _ _ _ W ly mem0 c au mu HcR B S Hp HARm Hau_def Hmu_def) as Hcarved.
pose proof (@YFkkcf.Hau_al' _ _ _ W ly mem0 c au csz HcR Hcsz B S Hp HARm Hau_def) as Hau_al.
set (need := n - nf). set (tot := au + need * csz). set (adr := @YFk5cf.RBv ly c + mu). set (sha := YFk5cf.SHBv + adr / 8).
set (mu2 := mu + kUserMapSize). set (nce := (mu - au) / csz). set (ncg := (mu2 - au) / csz). set (nfe := nf + nce). set (nfg := nf + ncg).
set (fadr := @YFk5cf.FAv ly c + mf). set (shf := YFk5cf.SHBv + fadr / 8). set (mf2 := mf + kFreeArrayMapSize).
set (aue := au + nce * csz). set (aug := au + ncg * csz).
assert (Hneed : need = n - nf) by reflexivity. assert (Htot : tot = au + need * csz) by reflexivity.
assert (Hadr : adr = @YFk5cf.RBv ly c + mu) by reflexivity.
assert (Hsha : sha = YFk5cf.SHBv + adr / 8) by reflexivity. assert (Hmu2 : mu2 = mu + kUserMapSize) by reflexivity.
assert (Hnce : nce = (mu - au) / csz) by reflexivity. assert (Hncg : ncg = (mu2 - au) / csz) by reflexivity.
assert (Hnfe : nfe = nf + nce) by reflexivity. assert (Hnfg : nfg = nf + ncg) by reflexivity.
assert (Hfadr : fadr = @YFk5cf.FAv ly c + mf) by reflexivity. assert (Hshf : shf = YFk5cf.SHBv + fadr / 8) by reflexivity.
assert (Hmf2 : mf2 = mf + kFreeArrayMapSize) by reflexivity. assert (Haue : aue = au + nce * csz) by reflexivity.
assert (Haug : aug = au + ncg * csz) by reflexivity.
destruct (@YFkkcf.junk_valuesR _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz 0 IMG LY HcR Hmax Hn Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def)
as (j64 & jna & jnf & jsm & jm1 & jm2 & jex & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v] & [Hjex Hjexv]).
pose proof (fun a => @YFkkcf.HslotPres' _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz 0 IMG LY HcR Hmax Hn Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def a) as HslotPres.
pose proof (fun a => @YFkkcf.HfaPres' _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz 0 IMG LY HcR Hmax Hn Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def a) as HfaPres.
assert (Ha1' : getr regs0 11 = w64 (@YFk5cf.Pr ly c)) by (rewrite Ha1; reflexivity).
pose proof (fun a => @YFkkcf.thread_present _ _ _ W ly regs0 mem0 c maxc nf mf au mu csz 0 IMG LY HcR Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def a) as HTP.
pose proof (@YFkkcf.SPAN3_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp) as HSPAN.
pose proof (@YFkkcf.SEEDU3_ok _ _ _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1' Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2
  Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD Hp HARm Hnf_def Hmf_def Hau_def Hmu_def
  Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv Huninit) as SEEDU.
replace (cfg_at im_segs ag_refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x37494) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
  by (unfold cfg_at; subst mat0; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@YFklcf.segU _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
    IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp mat0 HTP HSPAN SEEDU). }
intros W' c' _ HP. destruct HP as (-> & msJ & matJ & E' & -> & HE & HSJ & MEQ & PRS & TBF & TPR).
set (T := ly_T ly).
set (mR := memR T mem0 (ms_mem msJ)).
assert (R64 : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. unfold T.
  pose proof (lo_stk_ceil ly LY) as HC. pose proof (lo_top ly LY) as (L1 & L2 & L3 & HT & _ & _ & HB). clear - IT HC L1 L2 L3 HT HB.
  ceil; unfold kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
assert (CEIL64 : ASAN_CEIL <= 2 ^ 64) by (pose proof (lo_stk_ceil ly LY) as HC; pose proof (lo_top ly LY) as (L1 & L2 & L3 & HT & _); clear - HC L1 L2 L3 HT; unfold kHighMemEnd in HT; lia).
assert (MEQR : forall x : word, ~ TABW T (bv_unsigned x) -> mR x = mem0 x) by (intros x Hx; exact (memR_off T mem0 (ms_mem msJ) x Hx)).
assert (TBFR : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) mR) T i).
{ intros i Hi. destruct (TBF i Hi) as [M1 M2].
  split; (eapply val_mem_frame; [|eassumption]); intros k Hk; unfold mR; apply memR_on; rewrite unsigned_lit_small by (clear - Hi Hk R64 CEIL64; unfold kThreadObjSize in R64; lia); exists i; clear - Hi Hk; lia. }
assert (TPRR : forall a, TABW T a -> apresent (w_H W) mR a).
{ intros a Ha. pose proof (TABW_range T a Ha).
  eapply apresent_same; [|exact (TPR a Ha)]. unfold mR. apply memR_on. rewrite unsigned_lit_small by (clear - H R64 CEIL64; unfold kThreadObjSize in R64; lia). exact Ha. }
pose proof (YFhncf.ARcf_init B ly S Hp W mem0 mR md0 TS HAR Huninit MEQR TBFR TPRR IMG) as HAR1.
assert (PRESR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mR a) by (intros a; exact (YFhncf.PRES_MONO ly W mem0 mR MEQR TPRR a)).
(* the call-state facts at the post-init state (S1, memR) (header): memR is mem0 off TABW, the thread object's cache
   table, whose bytes are owned at S (a core extent), so apart from every non-owned RELRO byte (YG0dcf.relro_apart_cf
   at cgif's row); S1 keeps st_secs, so both meters *)
assert (OWNT : forall a, TABW T a -> aowned B ly S a).
{ intros a Ht. apply (own_core_cf B ly S Hp _ (ly_T ly, kThreadObjSize) a HARm); [unfold core_extents; cbn; tauto | cbn [fst snd]].
  apply TABW_range in Ht. unfold T in Ht. unfold kThreadObjSize. lia. }
assert (AD1 : arodata_ok_cf tfibsegs B mR).
{ apply (arodata_frame_cf tfibsegs B (fun z => TABW T z) mem0 mR); [exact MEQR | | exact AD].
  intros a Ha NO.
  destruct (YG0dcf.relro_apart_cf tfibsegs B ly S Hp W mem0 md0 a HAR CfAroPresetB.relro_seg_preset_AU Ha NO) as (RNG & _ & NA & _).
  split; [unfold kImgLo, kImgEnd in RNG; lia | intros Ht; exact (NA (OWNT a Ht))]. }
assert (HO1 : cf_hull_ok (YFhn.S1 S)) by exact (cf_hull_counts (YFhn.S1 S) S eq_refl eq_refl HO).
assert (Hinited1 : st_cache_inited (YFhn.S1 S) = true) by reflexivity.
assert (Hchunks1 : pc_chunks (cache (YFhn.S1 S) c) = []) by (rewrite (YFhncf.cache_S1 B ly S Hp W mem0 md0 HAR Huninit c HcR); reflexivity).
assert (Hnf_def1 : nf = fa_len (rg_free (reg (YFhn.S1 S) c))) by exact Hnf_def.
assert (Hmf_def1 : mf = rg_mapped_fa (reg (YFhn.S1 S) c)) by exact Hmf_def.
assert (Hau_def1 : au = rg_alloc_user (reg (YFhn.S1 S) c)) by exact Hau_def.
assert (Hmu_def1 : mu = rg_mapped_user (reg (YFhn.S1 S) c)) by exact Hmu_def.
pose proof (@YFk5cf.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
(* the region info, the thread object's tail and the errbuf / exh bytes are off TABW *)
assert (NTRG : forall a, @YFk5cf.RGv ly c <= a < @YFk5cf.RGv ly c + 128 -> ~ TABW T a).
{ intros a Ha Ht. apply TABW_range in Ht. destruct DR as (_ & _ & _ & _ & _ & _ & _ & D8 & _ & _ & _ & _ & _ & _ & _ & _ & D17 & _).
  pose proof (lo_space_in ly LY) as [SP1 SP2].
  clear - Ha Ht D8 D17 SP2 PT. unfold T in *. unfold kThreadObjSize in *. lia. }
assert (NTT : forall a, T + 2768 <= a -> ~ TABW T a) by (intros a Ha Ht; apply TABW_range in Ht; clear - Ha Ht; lia).
assert (JV : forall a (w : nat) v, ~ (exists k, 0 <= k < Z.of_nat w /\ TABW T (a + k)) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem0) a w v -> val_mem tfibsegs (mrestrict (w_H W) mR) a w v).
{ intros a w v NT A0 A1 HV. apply (YFhncf.val_mem_R ly W mem0 mR MEQR a w v); [intros k Hk Ht; apply NT; exists k; tauto | exact A0 | exact A1 | exact HV]. }
destruct DR as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & _ & _ & _ & _ & _ & _ & D16 & D17 & _).
assert (Hj64v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (@YFk5cf.RGv ly c + 64) 4 j64)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTRG; clear - Hk; cbn in Hk; lia | clear - D5; unfold kHighMemBeg in D5; lia | clear - D6 CEIL64; cbn; lia | exact Hj64v]).
assert (Hjnav1 : val_mem tfibsegs (mrestrict (w_H W) mR) (@YFk5cf.RGv ly c + 72) 8 jna)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTRG; clear - Hk; cbn in Hk; lia | clear - D5; unfold kHighMemBeg in D5; lia | clear - D6 CEIL64; cbn; lia | exact Hjnav]).
assert (Hjnfv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (@YFk5cf.RGv ly c + 80) 8 jnf)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTRG; clear - Hk; cbn in Hk; lia | clear - D5; unfold kHighMemBeg in D5; lia | clear - D6 CEIL64; cbn; lia | exact Hjnfv]).
assert (Hjexv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (@YFk5cf.RGv ly c + 68) 1 jex)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTRG; clear - Hk; cbn in Hk; lia | clear - D5; unfold kHighMemBeg in D5; lia | clear - D6 CEIL64; cbn; lia | exact Hjexv]).
assert (Hjsmv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2792) 8 jsm)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTT; clear - Hk; cbn in Hk; lia | clear - R64; lia | clear - R64 CEIL64; unfold kThreadObjSize in R64; cbn; lia | exact Hjsmv]).
assert (Hjm1v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2872) 8 jm1)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTT; clear - Hk; cbn in Hk; lia | clear - R64; lia | clear - R64 CEIL64; unfold kThreadObjSize in R64; cbn; lia | exact Hjm1v]).
assert (Hjm2v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2880) 8 jm2)
  by (apply JV; [intros (k & Hk & Ht); revert Ht; apply NTT; clear - Hk; cbn in Hk; lia | clear - R64; lia | clear - R64 CEIL64; unfold kThreadObjSize in R64; cbn; lia | exact Hjm2v]).
assert (HslotPres1 : forall a, @YFk5cf.DSTv ly c <= a < @YFk5cf.DSTv ly c + 64 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HslotPres, Ha).
assert (HfaPres1 : forall a, @YFk5cf.FAv ly c <= a < @YFk5cf.FAv ly c + mf -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HfaPres, Ha).
assert (HpresR1 : forall a, sp0 - REP_W c <= a < sp0 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HpresW, Ha).
assert (Hpres0R1 : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, Hpres0R, Ha).
assert (HXM1 : xs_mapped_cf ly (YFhn.S1 S) md0) by exact HXSM.
(* the entry cells at the post-init state: round 2 carries them in ARmcf (YFhncf.ARcf_init) *)
assert (HEXC1 := amc_exh_cell _ _ _ _ _ (proj1 HAR1)).
assert (HERC1 := amc_errb_cells _ _ _ _ _ (proj1 HAR1)).
assert (HARm1 := proj1 HAR1).
assert (HQL1 : qloose (YFhn.S1 S)) by exact HQL.
assert (HWT1 : WfP_cf (as_universe B) 1 0 0 (YFhn.S1 S)) by exact (WfP_cf_init_caches _ 1 0 0 S HWT Huninit).
assert (HBR1 : c = kBatchClass -> batch_room_cf (YFhn.S1 S)) by exact HBR.
assert (HER1 : c <> kBatchClass -> ERRB_ROOM (YFhn.S1 S) /\ WfP_cf (as_universe B) 1 1 0 (YFhn.S1 S)).
{ intros Hnb. destruct (HER Hnb) as [E1' W1']. split; [exact E1' | exact (WfP_cf_init_caches _ 1 1 0 S W1' Huninit)]. }
(* the B3 join state at the post-init memory *)
assert (HJ : @YFk5cf.at_R3 _ ly regs0 mR c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg
  fadr shf mf2 aue aug W md0 (@YFk5cf.WINR0 ly regs0 c) (fun _ => True) YFk8cf.R3_J W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))).
{ split; [reflexivity|]. exists msJ, matJ, E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HSJ|]. split; [|split; [exact PRS | exact I]].
  intros x Hx. destruct (TABW_dec T (bv_unsigned x)) as [Ht|Ht]; [unfold mR; rewrite (memR_on _ _ _ x Ht); reflexivity | rewrite (MEQR x Ht); exact (MEQ x Hx Ht)]. }
rewrite (refill_tree_cf_init c S Huninit).
eapply amreal_mono; [intros r W'' c'' HL; eapply refill_leaf_core_init_cf; [exact HAR | exact IMG | exact MEQR | exact TPRR | exact HL]|].
exact (HIN Hp W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  matJ msJ B (YFhn.S1 S) IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp HloW Hra Hra4096 Htp Ha0 Ha1' Ha2 Ha3
  Hnlt Hcarved Hau_al Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug HJ Hpres0R1 HpresR1 HslotPres1 HfaPres1
  TS HTSD HARm1 Hgp Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 Hj64v1 Hjnav1 Hjnfv1 Hjsmv1 Hjm1v1 Hjm2v1 Hjexv1 HEXC1 HERC1
  HQL1 HAR1 HXM1 HBR1 HER1 HWT1 AD1 HO1 I).
Qed.

(* THE UNINIT ENTRY. *)
Theorem refill_uninit_entry_preset : refill_uninit_entry_cf B IOK.
Proof.
intros Hp inst ly S W regs mem md c HS AD HO HC Huninit.
destruct (Z_lt_le_dec (fa_len (rg_free (reg S c))) (max_cached c / 2)) as [Hfew|Henough].
- exact (uninit_B3_preset Hp inst ly S W regs mem md c HS AD HO HC Huninit Hfew).
- exact (uninit_B2_preset Hp inst ly S W regs mem md c HS HC Huninit Henough).
Qed.
End u3.
End b.
End a.

Print Assumptions refill_uninit_entry_preset.
About refill_uninit_entry_preset.
