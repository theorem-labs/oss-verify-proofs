(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF4q YF8g YF7x YF8i YF7z YF3i YF8j YF81 YF8f YF7w YF8o YF8b YF8n YF8q YF82 YF8e YF8p YF8c YF3j YF8k YF8l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Section d. Context {imgk : img}.
Variable B : asyms.
Hypothesis TS : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Hypothesis PRE : refill_pre B ly S W regs0 mem0 md0 c.
Hypothesis Huninit : st_cache_inited S = false.
Let S1 : astate := YF3j.S1 S.
Let T : Z := ly_T ly.
Definition memR (mJ : word -> option byte) : word -> option byte := fun x => if tabwb T (bv_unsigned x) then mJ x else mem0 x.
Lemma memR_off : forall mJ x, ~ TABW T (bv_unsigned x) -> memR mJ x = mem0 x.
Proof. intros mJ x Hx. unfold memR. destruct (tabwb T (bv_unsigned x)) eqn:E; [|img_refl]. exfalso. img_apply Hx. img_apply tabwb_spec. img_exact E. Qed.
Lemma memR_on : forall mJ x, TABW T (bv_unsigned x) -> memR mJ x = mJ x.
Proof. intros mJ x Hx. unfold memR. apply tabwb_spec in Hx. rewrite Hx. img_refl. Qed.
Theorem refill_uninit_B3 : fa_len (rg_free (reg S c)) < max_cached c / 2 ->
amreal tfxsegs (refill_tree c S) W (cfg_at tfxsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
intros Hfew.
destruct PRE as (HAR & Hslack & Hpum & HQL & Hra & Hra4096 & Hal & Hlo & Hhi & Hpres0R & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3 & HcR & Hchunks).
pose proof (proj1 HAR) as HARm. unfold spZ, raZ in *.
assert (LY : layout_ok ly) by img_exact (am_layout _ _ _ _ HARm).
assert (IMG : img_cover ly) by img_exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))).
assert (HTSD : ly_tsd ly = TFX_TSD) by (img_try (rewrite (am_tsd _ _ _ _ HARm); img_exact (ts_tsd B TS))).
rewrite (ts_tp B TS) in Htp.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (img_try (repeat split; assumption)).
set (maxc := max_cached c). set (n := maxc / 2). set (nf := fa_len (rg_free (reg S c))). set (mf := rg_mapped_fa (reg S c)).
set (au := rg_alloc_user (reg S c)). set (mu := rg_mapped_user (reg S c)). set (csz := class_size c). set (mat0 := m_vm_materialized md0).
assert (Hmax : maxc = max_cached c) by img_refl. assert (Hn : n = maxc / 2) by img_refl. assert (Hcsz : csz = class_size c) by img_refl.
assert (Hnf_def : nf = fa_len (rg_free (reg S c))) by img_refl. assert (Hmf_def : mf = rg_mapped_fa (reg S c)) by img_refl.
assert (Hau_def : au = rg_alloc_user (reg S c)) by img_refl. assert (Hmu_def : mu = rg_mapped_user (reg S c)) by img_refl.
assert (Hnlt : nf < n) by img_exact Hfew.
pose proof (@YF8b.Hnf' _ imgk W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@YF8b.Hmf' _ imgk W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@YF8b.Hmu' _ imgk W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
pose proof (@YF8b.Hcarved' _ imgk W ly mem0 c au mu HcR B S HARm Hau_def Hmu_def) as Hcarved.
pose proof (@YF8b.Hau_al' _ imgk W ly mem0 c au csz HcR Hcsz B S HARm Hau_def) as Hau_al.
set (need := n - nf). set (tot := au + need * csz). set (adr := YF7w.RBv ly c + mu). set (sha := YF7w.SHBv + adr / 8).
set (mu2 := mu + kUserMapSize). set (nce := (mu - au) / csz). set (ncg := (mu2 - au) / csz). set (nfe := nf + nce). set (nfg := nf + ncg).
set (fadr := YF7w.FAv ly c + mf). set (shf := YF7w.SHBv + fadr / 8). set (mf2 := mf + kFreeArrayMapSize).
set (aue := au + nce * csz). set (aug := au + ncg * csz).
assert (Hneed : need = n - nf) by img_refl. assert (Htot : tot = au + need * csz) by img_refl. assert (Hadr : adr = YF7w.RBv ly c + mu) by img_refl.
assert (Hsha : sha = YF7w.SHBv + adr / 8) by img_refl. assert (Hmu2 : mu2 = mu + kUserMapSize) by img_refl.
assert (Hnce : nce = (mu - au) / csz) by img_refl. assert (Hncg : ncg = (mu2 - au) / csz) by img_refl.
assert (Hnfe : nfe = nf + nce) by img_refl. assert (Hnfg : nfg = nf + ncg) by img_refl.
assert (Hfadr : fadr = YF7w.FAv ly c + mf) by img_refl. assert (Hshf : shf = YF7w.SHBv + fadr / 8) by img_refl.
assert (Hmf2 : mf2 = mf + kFreeArrayMapSize) by img_refl. assert (Haue : aue = au + nce * csz) by img_refl. assert (Haug : aug = au + ncg * csz) by img_refl.
destruct (@YF8b.junk_valuesR _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def)
as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
pose proof (@YF8b.HslotPres' _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPres.
pose proof (@YF8b.HfaPres' _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPres.
pose proof (@YF8b.thread_present _ imgk W ly regs0 mem0 c maxc nf mf au mu csz IMG LY HcR Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HTP.
pose proof (@YF8b.SPAN3_disj _ imgk ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp) as HSPAN.
pose proof (@YF8b.SEEDU3_ok _ _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Huninit) as SEEDU.
replace (cfg_at tfxsegs A_Refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
by (img_try (unfold cfg_at, A_Refill; (subst mat0; cbv beta); rewrite with_vm_backing_id; img_refl)).
eapply amreal_SRr_pre.
{ img_exact (@YF8c.segU _ _ imgk W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp mat0 HTP HSPAN SEEDU). }
intros W' c' _ HP. destruct HP as (-> & msJ & matJ & E' & -> & HE & HSJ & MEQ & PRS & TBF & TPR).
set (mR := memR (ms_mem msJ)).
assert (MEQR : forall x : word, ~ TABW T (bv_unsigned x) -> mR x = mem0 x) by (img_try (intros x Hx; img_exact (memR_off (ms_mem msJ) x Hx))).
assert (TBFR : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) mR) T i).
{ intros i Hi. destruct (TBF i Hi) as [M1 M2]. pose proof (TABW_range T).
assert (R64 : 0 <= T /\ T + kThreadObjSize <= 2 ^ 64).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. ceil; unfold T, kThreadObjSize, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. img_lia.     }
split; (eapply val_mem_frame; [|img_try (eassumption)]); intros k Hk; unfold mR; img_apply memR_on; rewrite unsigned_lit_small by (img_try (unfold kThreadObjSize in R64; img_lia)); exists i; img_lia. }
assert (TPRR : forall a, TABW T a -> apresent (w_H W) mR a).
{ intros a Ha. pose proof (TABW_range T a Ha).
assert (R64 : 0 <= T /\ T + kThreadObjSize <= 2 ^ 64).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. ceil; unfold T, kThreadObjSize, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. img_lia.     }
eapply apresent_same; [|img_try (img_exact (TPR a Ha))]. unfold mR. img_apply memR_on. rewrite unsigned_lit_small by (img_try (unfold kThreadObjSize in R64; img_lia)). img_exact Ha. }
pose proof (YF3j.AR_init B ly S W mem0 mR md0 TS HAR Huninit MEQR TBFR TPRR IMG) as HAR1. fold S1 in HAR1.
pose proof (proj1 HAR1) as HARm1.
assert (PRESR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mR a) by (img_try (intros a; img_exact (YF3j.PRES_MONO ly W mem0 mR MEQR TPRR a))).
assert (Hinited1 : st_cache_inited S1 = true) by img_refl.
assert (Hchunks1 : pc_chunks (cache S1 c) = []) by (img_try (unfold S1; rewrite (YF3j.cache_S1 B ly S W mem0 md0 HAR Huninit c HcR); img_refl)).
assert (Hnf_def1 : nf = fa_len (rg_free (reg S1 c))) by img_exact Hnf_def. assert (Hmf_def1 : mf = rg_mapped_fa (reg S1 c)) by img_exact Hmf_def.
assert (Hau_def1 : au = rg_alloc_user (reg S1 c)) by img_exact Hau_def. assert (Hmu_def1 : mu = rg_mapped_user (reg S1 c)) by img_exact Hmu_def.
assert (Hpum1 : refill_reg S1 c) by img_exact (refill_reg_init S c ltac:(img_try (clear - HcR; img_lia)) Hpum).
assert (Hslack1 : A_bytes (w_A W) + EV_A <= abudget S1) by img_exact Hslack.
assert (HQL1 : qloose S1) by img_exact HQL.
assert (R64 : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. unfold T. ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. img_lia.     }
pose proof (@YF7w.derived_rangesR _ imgk ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
assert (JV : forall a (w : nat) v, (YF7w.RGv ly c <= a /\ a + Z.of_nat w <= YF7w.RGv ly c + 128) \/ (T + 2768 <= a /\ a + Z.of_nat w <= T + kThreadObjSize) ->
val_mem tfxsegs (mrestrict (w_H W) mem0) a w v -> val_mem tfxsegs (mrestrict (w_H W) mR) a w v).
{ intros a w v Ha HV. pose proof (lo_space_in ly LY) as SP. unfold zdisjoint in SP.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
img_apply (YF3j.val_mem_R ly W mem0 mR MEQR a w v); [| img_try (clear - Ha DR R64; unfold YF7w.RGv in *; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff in *; img_lia)
| img_try (clear - Ha DR R64; unfold YF7w.RGv in *; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff in *; img_lia) | img_try (img_exact HV)].
intros k Hk Ht. apply TABW_range in Ht. clear - Ha Hk Ht DR R64 SP PT HcR. unfold YF7w.RGv in *. unfold T in *.
ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff, kSpaceSize, kPrimResvSize in *. img_lia. }
assert (Hj64v1 : val_mem tfxsegs (mrestrict (w_H W) mR) (YF7w.RGv ly c + 64) 4 j64) by (img_try (img_apply JV; [img_try (left; cbn; img_lia) | img_try (img_exact Hj64v)])).
assert (Hjnav1 : val_mem tfxsegs (mrestrict (w_H W) mR) (YF7w.RGv ly c + 72) 8 jna) by (img_try (img_apply JV; [img_try (left; cbn; img_lia) | img_try (img_exact Hjnav)])).
assert (Hjnfv1 : val_mem tfxsegs (mrestrict (w_H W) mR) (YF7w.RGv ly c + 80) 8 jnf) by (img_try (img_apply JV; [img_try (left; cbn; img_lia) | img_try (img_exact Hjnfv)])).
assert (Hjsmv1 : val_mem tfxsegs (mrestrict (w_H W) mR) (T + 2792) 8 jsm) by (img_try (img_apply JV; [img_try (right; cbn; unfold kThreadObjSize; img_lia) | img_try (img_exact Hjsmv)])).
assert (Hjm1v1 : val_mem tfxsegs (mrestrict (w_H W) mR) (T + 2872) 8 jm1) by (img_try (img_apply JV; [img_try (right; cbn; unfold kThreadObjSize; img_lia) | img_try (img_exact Hjm1v)])).
assert (Hjm2v1 : val_mem tfxsegs (mrestrict (w_H W) mR) (T + 2880) 8 jm2) by (img_try (img_apply JV; [img_try (right; cbn; unfold kThreadObjSize; img_lia) | img_try (img_exact Hjm2v)])).
assert (HslotPres1 : forall a, YF7w.DSTv ly c <= a < YF7w.DSTv ly c + 64 -> apresent (w_H W) mR a) by (img_try (intros a Ha; apply PRESR, HslotPres, Ha)).
assert (HfaPres1 : forall a, YF7w.FAv ly c <= a < YF7w.FAv ly c + mf -> apresent (w_H W) mR a) by (img_try (intros a Ha; apply PRESR, HfaPres, Ha)).
assert (HJ : @YF7w.at_R3 _ imgk ly regs0 mR c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
W md0 (@YF7w.WINR0 ly regs0 c) YF82.PT R3_J W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))).
{ split; [img_refl|]. exists msJ, matJ, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HSJ)|]. split; [|img_try (split; [img_exact PRS | img_exact I])].
intros x Hx. destruct (TABW_dec T (bv_unsigned x)) as [Ht|Ht]; [img_try (unfold mR; rewrite (memR_on _ x Ht); img_refl) | img_try (rewrite (MEQR x Ht); img_exact (MEQ x Hx Ht))]. }
rewrite (YF3j.refill_tree_init c S Huninit). fold (YF3j.S1 S). fold S1.
eapply amreal_mono; [img_try (intros r W'' c''; img_exact (YF3j.refill_leaf_init B ly S W mem0 mR md0 HAR MEQR regs0 c r W'' c''))|].
img_exact (@YF8e.refill_B3 _ _ imgk W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug matJ msJ HJ HslotPres1 HfaPres1 B S1 TS HTSD HARm1 Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 HAR1 Hpum1 Hslack1 HQL1).
Qed.
Theorem refill_uninit_B2 : max_cached c / 2 <= fa_len (rg_free (reg S c)) ->
amreal tfxsegs (refill_tree c S) W (cfg_at tfxsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
intros Henough.
destruct PRE as (HAR & Hslack & Hpum & HQL & Hra & Hra4096 & Hal & Hlo & Hhi & Hpres0R & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3 & HcR & Hchunks).
pose proof (proj1 HAR) as HARm. unfold spZ, raZ in *.
assert (LY : layout_ok ly) by img_exact (am_layout _ _ _ _ HARm).
assert (IMG : img_cover ly) by img_exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))).
assert (HTSD : ly_tsd ly = TFX_TSD) by (img_try (rewrite (am_tsd _ _ _ _ HARm); img_exact (ts_tsd B TS))).
rewrite (ts_tp B TS) in Htp.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (img_try (repeat split; assumption)).
set (maxc := max_cached c). set (n := maxc / 2). set (nf := fa_len (rg_free (reg S c))). set (mf := rg_mapped_fa (reg S c)).
set (au := rg_alloc_user (reg S c)). set (mu := rg_mapped_user (reg S c)). set (csz := class_size c). set (mat0 := m_vm_materialized md0).
assert (Hmax : maxc = max_cached c) by img_refl. assert (Hn : n = maxc / 2) by img_refl. assert (Hcsz : csz = class_size c) by img_refl.
assert (Hnf_def : nf = fa_len (rg_free (reg S c))) by img_refl. assert (Hmf_def : mf = rg_mapped_fa (reg S c)) by img_refl.
assert (Hau_def : au = rg_alloc_user (reg S c)) by img_refl. assert (Hmu_def : mu = rg_mapped_user (reg S c)) by img_refl.
assert (Hnle : n <= nf) by img_exact Henough.
pose proof (@YF8o.Hnf' _ imgk W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@YF8o.Hmf' _ imgk W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@YF8o.Hmu' _ imgk W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
destruct (@YF8o.junk_valuesR _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def)
as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
pose proof (@YF8o.HslotPres' _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPres.
pose proof (@YF8o.HfaPres' _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPres.
pose proof (@YF8o.thread_present _ imgk W ly regs0 mem0 c maxc nf mf au mu LY IMG HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HTP.
pose proof (@YF8o.SPAN_disj _ imgk ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp) as HSPAN.
pose proof (@YF8o.SEEDU_ok _ _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Huninit) as SEEDU.
replace (cfg_at tfxsegs A_Refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
by (img_try (unfold cfg_at, A_Refill; (subst mat0; cbv beta); rewrite with_vm_backing_id; img_refl)).
eapply amreal_SRr_pre.
{ img_exact (@YF8p.segU _ _ imgk W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp mat0 HTP HSPAN SEEDU). }
intros W' c' _ HP. destruct HP as (-> & msJ & matJ & E' & -> & HE & HSJ & MEQ & PRS & TBF & TPR).
set (mR := memR (ms_mem msJ)).
assert (R64 : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. unfold T. ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. img_lia.     }
assert (MEQR : forall x : word, ~ TABW T (bv_unsigned x) -> mR x = mem0 x) by (img_try (intros x Hx; img_exact (memR_off (ms_mem msJ) x Hx))).
assert (TBFR : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) mR) T i).
{ intros i Hi. destruct (TBF i Hi) as [M1 M2].
split; (eapply val_mem_frame; [|img_try (eassumption)]); intros k Hk; unfold mR; img_apply memR_on; rewrite unsigned_lit_small by (img_try (clear - Hi Hk R64; ceil; unfold kThreadObjSize, kHighMemBeg, ASAN_CEIL in R64; img_lia)); exists i; img_lia. }
assert (TPRR : forall a, TABW T a -> apresent (w_H W) mR a).
{ intros a Ha. pose proof (TABW_range T a Ha).
eapply apresent_same; [|img_try (img_exact (TPR a Ha))]. unfold mR. img_apply memR_on. rewrite unsigned_lit_small by (img_try (clear - H R64; ceil; unfold kThreadObjSize, kHighMemBeg, ASAN_CEIL in R64; img_lia)). img_exact Ha. }
pose proof (YF3j.AR_init B ly S W mem0 mR md0 TS HAR Huninit MEQR TBFR TPRR IMG) as HAR1. fold S1 in HAR1.
pose proof (proj1 HAR1) as HARm1.
assert (PRESR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mR a) by (img_try (intros a; img_exact (YF3j.PRES_MONO ly W mem0 mR MEQR TPRR a))).
assert (Hinited1 : st_cache_inited S1 = true) by img_refl.
assert (Hchunks1 : pc_chunks (cache S1 c) = []) by (img_try (unfold S1; rewrite (YF3j.cache_S1 B ly S W mem0 md0 HAR Huninit c HcR); img_refl)).
assert (Hnf_def1 : nf = fa_len (rg_free (reg S1 c))) by img_exact Hnf_def. assert (Hmf_def1 : mf = rg_mapped_fa (reg S1 c)) by img_exact Hmf_def.
assert (Hau_def1 : au = rg_alloc_user (reg S1 c)) by img_exact Hau_def. assert (Hmu_def1 : mu = rg_mapped_user (reg S1 c)) by img_exact Hmu_def.
assert (Hnle1 : n <= fa_len (rg_free (reg S1 c))) by img_exact Hnle.
pose proof (@YF8f.derived_rangesR _ imgk ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
assert (JV : forall a (w : nat) v, (YF8f.RGv ly c <= a /\ a + Z.of_nat w <= YF8f.RGv ly c + 128) \/ (T + 2768 <= a /\ a + Z.of_nat w <= T + kThreadObjSize) ->
val_mem tfxsegs (mrestrict (w_H W) mem0) a w v -> val_mem tfxsegs (mrestrict (w_H W) mR) a w v).
{ intros a w v Ha HV. pose proof (lo_space_in ly LY) as SP. unfold zdisjoint in SP.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
img_apply (YF3j.val_mem_R ly W mem0 mR MEQR a w v); [| img_try (clear - Ha DR R64; unfold YF8f.RGv in *; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff in *; img_lia)
| img_try (clear - Ha DR R64; unfold YF8f.RGv in *; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff in *; img_lia) | img_try (img_exact HV)].
intros k Hk Ht. apply TABW_range in Ht. clear - Ha Hk Ht DR R64 SP PT HcR. unfold YF8f.RGv in *. unfold T in *.
ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff, kSpaceSize, kPrimResvSize in *. img_lia. }
assert (Hj64v1 : val_mem tfxsegs (mrestrict (w_H W) mR) (YF8f.RGv ly c + 64) 4 j64) by (img_try (img_apply JV; [img_try (left; cbn; img_lia) | img_try (img_exact Hj64v)])).
assert (Hjnav1 : val_mem tfxsegs (mrestrict (w_H W) mR) (YF8f.RGv ly c + 72) 8 jna) by (img_try (img_apply JV; [img_try (left; cbn; img_lia) | img_try (img_exact Hjnav)])).
assert (Hjnfv1 : val_mem tfxsegs (mrestrict (w_H W) mR) (YF8f.RGv ly c + 80) 8 jnf) by (img_try (img_apply JV; [img_try (left; cbn; img_lia) | img_try (img_exact Hjnfv)])).
assert (Hjsmv1 : val_mem tfxsegs (mrestrict (w_H W) mR) (T + 2792) 8 jsm) by (img_try (img_apply JV; [img_try (right; cbn; unfold kThreadObjSize; img_lia) | img_try (img_exact Hjsmv)])).
assert (Hjm1v1 : val_mem tfxsegs (mrestrict (w_H W) mR) (T + 2872) 8 jm1) by (img_try (img_apply JV; [img_try (right; cbn; unfold kThreadObjSize; img_lia) | img_try (img_exact Hjm1v)])).
assert (Hjm2v1 : val_mem tfxsegs (mrestrict (w_H W) mR) (T + 2880) 8 jm2) by (img_try (img_apply JV; [img_try (right; cbn; unfold kThreadObjSize; img_lia) | img_try (img_exact Hjm2v)])).
assert (HslotPres1 : forall a, YF8f.DSTv ly c <= a < YF8f.DSTv ly c + 64 -> apresent (w_H W) mR a) by (img_try (intros a Ha; apply PRESR, HslotPres, Ha)).
assert (HfaPres1 : forall a, YF8f.FAv ly c <= a < YF8f.FAv ly c + mf -> apresent (w_H W) mR a) by (img_try (intros a Ha; apply PRESR, HfaPres, Ha)).
assert (HJ : @YF8f.at_R _ imgk W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 RJ2 W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))).
{ split; [img_refl|]. exists msJ, matJ, E'. split; [img_refl|]. split; [img_try (img_exact (proj1 HE))|]. split; [img_try (img_exact HSJ)|]. split; [|img_try (img_exact PRS)].
intros x Hx. destruct (TABW_dec T (bv_unsigned x)) as [Ht|Ht]; [img_try (unfold mR; rewrite (memR_on _ x Ht); img_refl) | img_try (rewrite (MEQR x Ht); img_exact (MEQ x Hx Ht))]. }
rewrite (YF3j.refill_tree_init c S Huninit). fold (YF3j.S1 S). fold S1.
eapply amreal_mono; [img_try (intros r W'' c''; img_exact (YF3j.refill_leaf_init B ly S W mem0 mR md0 HAR MEQR regs0 c r W'' c''))|].
destruct (@YF8q.refill_B2_model _ imgk W ly regs0 mR c maxc n nf mf au mu csz HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S1 HARm1 Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 Hnle1)
as (tops & rest & EP & RUN & WFR & E1 & E2 & E3 & E4).
rewrite RUN. cbn [amreal].
eapply SRr_mono.
{ img_exact (@YF8n.segB2 _ _ imgk W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp matJ msJ HJ HslotPres1 HfaPres1 Hnle1). }
intros W'' c'' _ HR.
img_exact (@YF8q.LEAF_B2 _ _ imgk W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp matJ msJ HJ HfaPres1 B S1 TS HTSD HARm1 Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 HAR1 Hnle1 tops rest W'' c'' WFR E1 E2 E3 E4 HR).
Qed.
Theorem refill_uninit :
amreal tfxsegs (refill_tree c S) W (cfg_at tfxsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
destruct (Z_lt_le_dec (fa_len (rg_free (reg S c))) (max_cached c / 2)) as [Hfew|Henough].
- img_exact (refill_uninit_B3 Hfew).
- img_exact (refill_uninit_B2 Henough).
Qed.
End d.
Theorem tfx_refill_ok {imgk : img} : forall B, TfxSyms B -> tfx_refill_spec B.
Proof.
intros B TS ly S W regs mem md c PRE. destruct (st_cache_inited S) eqn:Hi.
- img_exact (YF8l.refill_inited B TS ly S W regs mem md c PRE Hi).
- img_exact (refill_uninit B TS ly S W regs mem md c PRE Hi).
Qed.
End b.
