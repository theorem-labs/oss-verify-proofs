(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhy AFis AFkp AFk6 AFkr AFk8 AFhm AFks AFka AFko AFk5 AFkx AFkk AFkw AFkz AFkb AFkn AFky AFkl AFhn AFkt AFku.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section d.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Hypothesis PRE : refill_pre B ly S W regs0 mem0 md0 c.
Hypothesis Huninit : st_cache_inited S = false.
Let S1 : astate := AFhn.S1 S.
Let T : Z := ly_T ly.
Definition memR (mJ : word -> option byte) : word -> option byte := fun x => if tabwb T (bv_unsigned x) then mJ x else mem0 x.
Lemma memR_off : forall mJ x, ~ TABW T (bv_unsigned x) -> memR mJ x = mem0 x.
Proof. intros mJ x Hx. unfold memR. destruct (tabwb T (bv_unsigned x)) eqn:E; [|reflexivity]. exfalso. apply Hx. apply tabwb_spec. exact E. Qed.
Lemma memR_on : forall mJ x, TABW T (bv_unsigned x) -> memR mJ x = mJ x.
Proof. intros mJ x Hx. unfold memR. apply tabwb_spec in Hx. rewrite Hx. reflexivity. Qed.
Theorem refill_uninit_B3 : fa_len (rg_free (reg S c)) < max_cached c / 2 ->
amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
intros Hfew.
destruct PRE as (HAR & Hslack & Hpum & HQL & Hra & Hra4096 & Hal & Hlo & Hhi & Hpres0R & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3 & HcR & Hchunks).
pose proof (proj1 HAR) as HARm. unfold spZ, raZ in *.
assert (LY : layout_ok ly) by exact (am_layout _ _ _ _ HARm).
assert (IMG : img_cover ly) by exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS)).
rewrite (ts_tp B TS) in Htp.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (repeat split; assumption).
set (maxc := max_cached c). set (n := maxc / 2). set (nf := fa_len (rg_free (reg S c))). set (mf := rg_mapped_fa (reg S c)).
set (au := rg_alloc_user (reg S c)). set (mu := rg_mapped_user (reg S c)). set (csz := class_size c). set (mat0 := m_vm_materialized md0).
assert (Hmax : maxc = max_cached c) by reflexivity. assert (Hn : n = maxc / 2) by reflexivity. assert (Hcsz : csz = class_size c) by reflexivity.
assert (Hnf_def : nf = fa_len (rg_free (reg S c))) by reflexivity. assert (Hmf_def : mf = rg_mapped_fa (reg S c)) by reflexivity.
assert (Hau_def : au = rg_alloc_user (reg S c)) by reflexivity. assert (Hmu_def : mu = rg_mapped_user (reg S c)) by reflexivity.
assert (Hnlt : nf < n) by exact Hfew.
pose proof (@AFkk.Hnf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@AFkk.Hmf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@AFkk.Hmu' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
pose proof (@AFkk.Hcarved' _ W ly mem0 c au mu HcR B S HARm Hau_def Hmu_def) as Hcarved.
pose proof (@AFkk.Hau_al' _ W ly mem0 c au csz HcR Hcsz B S HARm Hau_def) as Hau_al.
set (need := n - nf). set (tot := au + need * csz). set (adr := AFk5.RBv ly c + mu). set (sha := AFk5.SHBv + adr / 8).
set (mu2 := mu + kUserMapSize). set (nce := (mu - au) / csz). set (ncg := (mu2 - au) / csz). set (nfe := nf + nce). set (nfg := nf + ncg).
set (fadr := AFk5.FAv ly c + mf). set (shf := AFk5.SHBv + fadr / 8). set (mf2 := mf + kFreeArrayMapSize).
set (aue := au + nce * csz). set (aug := au + ncg * csz).
assert (Hneed : need = n - nf) by reflexivity. assert (Htot : tot = au + need * csz) by reflexivity. assert (Hadr : adr = AFk5.RBv ly c + mu) by reflexivity.
assert (Hsha : sha = AFk5.SHBv + adr / 8) by reflexivity. assert (Hmu2 : mu2 = mu + kUserMapSize) by reflexivity.
assert (Hnce : nce = (mu - au) / csz) by reflexivity. assert (Hncg : ncg = (mu2 - au) / csz) by reflexivity.
assert (Hnfe : nfe = nf + nce) by reflexivity. assert (Hnfg : nfg = nf + ncg) by reflexivity.
assert (Hfadr : fadr = AFk5.FAv ly c + mf) by reflexivity. assert (Hshf : shf = AFk5.SHBv + fadr / 8) by reflexivity.
assert (Hmf2 : mf2 = mf + kFreeArrayMapSize) by reflexivity. assert (Haue : aue = au + nce * csz) by reflexivity. assert (Haug : aug = au + ncg * csz) by reflexivity.
destruct (@AFkk.junk_valuesR _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def)
as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
pose proof (@AFkk.HslotPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPres.
pose proof (@AFkk.HfaPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPres.
pose proof (@AFkk.thread_present _ W ly regs0 mem0 c maxc nf mf au mu csz IMG LY HcR Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HTP.
pose proof (@AFkk.SPAN3_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp) as HSPAN.
pose proof (@AFkk.SEEDU3_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Huninit) as SEEDU.
replace (cfg_at tfibsegs A_Refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
by (unfold cfg_at, A_Refill; subst mat0; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@AFkl.segU _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp mat0 HTP HSPAN SEEDU). }
intros W' c' _ HP. destruct HP as (-> & msJ & matJ & E' & -> & HE & HSJ & MEQ & PRS & TBF & TPR).
set (mR := memR (ms_mem msJ)).
assert (MEQR : forall x : word, ~ TABW T (bv_unsigned x) -> mR x = mem0 x) by (intros x Hx; exact (memR_off (ms_mem msJ) x Hx)).
assert (TBFR : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) mR) T i).
{ intros i Hi. destruct (TBF i Hi) as [M1 M2]. pose proof (TABW_range T).
assert (R64 : 0 <= T /\ T + kThreadObjSize <= 2 ^ 64).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. ceil; unfold T, kThreadObjSize, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.     }
split; (eapply val_mem_frame; [|eassumption]); intros k Hk; unfold mR; apply memR_on; rewrite unsigned_lit_small by (unfold kThreadObjSize in R64; lia); exists i; lia. }
assert (TPRR : forall a, TABW T a -> apresent (w_H W) mR a).
{ intros a Ha. pose proof (TABW_range T a Ha).
assert (R64 : 0 <= T /\ T + kThreadObjSize <= 2 ^ 64).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. ceil; unfold T, kThreadObjSize, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.     }
eapply apresent_same; [|exact (TPR a Ha)]. unfold mR. apply memR_on. rewrite unsigned_lit_small by (unfold kThreadObjSize in R64; lia). exact Ha. }
pose proof (AFhn.AR_init B ly S W mem0 mR md0 TS HAR Huninit MEQR TBFR TPRR IMG) as HAR1. fold S1 in HAR1.
pose proof (proj1 HAR1) as HARm1.
assert (PRESR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mR a) by (intros a; exact (AFhn.PRES_MONO ly W mem0 mR MEQR TPRR a)).
assert (Hinited1 : st_cache_inited S1 = true) by reflexivity.
assert (Hchunks1 : pc_chunks (cache S1 c) = []) by (unfold S1; rewrite (AFhn.cache_S1 B ly S W mem0 md0 HAR Huninit c HcR); reflexivity).
assert (Hnf_def1 : nf = fa_len (rg_free (reg S1 c))) by exact Hnf_def. assert (Hmf_def1 : mf = rg_mapped_fa (reg S1 c)) by exact Hmf_def.
assert (Hau_def1 : au = rg_alloc_user (reg S1 c)) by exact Hau_def. assert (Hmu_def1 : mu = rg_mapped_user (reg S1 c)) by exact Hmu_def.
assert (Hpum1 : refill_reg S1 c) by exact (refill_reg_init S c ltac:(clear - HcR; lia) Hpum).
assert (Hslack1 : A_bytes (w_A W) + EV_A <= abudget S1) by exact Hslack.
assert (HQL1 : qloosem S1) by exact HQL.
assert (R64 : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. unfold T. ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.     }
pose proof (@AFk5.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
assert (JV : forall a (w : nat) v, (AFk5.RGv ly c <= a /\ a + Z.of_nat w <= AFk5.RGv ly c + 128) \/ (T + 2768 <= a /\ a + Z.of_nat w <= T + kThreadObjSize) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) a w v -> val_mem tfibsegs (mrestrict (w_H W) mR) a w v).
{ intros a w v Ha HV. pose proof (lo_space_in ly LY) as SP. unfold zdisjoint in SP.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
apply (AFhn.val_mem_R ly W mem0 mR MEQR a w v); [| clear - Ha DR R64; unfold AFk5.RGv in *; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff in *; lia
| clear - Ha DR R64; unfold AFk5.RGv in *; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff in *; lia | exact HV].
intros k Hk Ht. apply TABW_range in Ht. clear - Ha Hk Ht DR R64 SP PT HcR. unfold AFk5.RGv in *. unfold T in *.
ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff, kSpaceSize, kPrimResvSize in *. lia. }
assert (Hj64v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (AFk5.RGv ly c + 64) 4 j64) by (apply JV; [left; cbn; lia | exact Hj64v]).
assert (Hjnav1 : val_mem tfibsegs (mrestrict (w_H W) mR) (AFk5.RGv ly c + 72) 8 jna) by (apply JV; [left; cbn; lia | exact Hjnav]).
assert (Hjnfv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (AFk5.RGv ly c + 80) 8 jnf) by (apply JV; [left; cbn; lia | exact Hjnfv]).
assert (Hjsmv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2792) 8 jsm) by (apply JV; [right; cbn; unfold kThreadObjSize; lia | exact Hjsmv]).
assert (Hjm1v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2872) 8 jm1) by (apply JV; [right; cbn; unfold kThreadObjSize; lia | exact Hjm1v]).
assert (Hjm2v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2880) 8 jm2) by (apply JV; [right; cbn; unfold kThreadObjSize; lia | exact Hjm2v]).
assert (HslotPres1 : forall a, AFk5.DSTv ly c <= a < AFk5.DSTv ly c + 64 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HslotPres, Ha).
assert (HfaPres1 : forall a, AFk5.FAv ly c <= a < AFk5.FAv ly c + mf -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HfaPres, Ha).
assert (HJ : @AFk5.at_R3 _ ly regs0 mR c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
W md0 (@AFk5.WINR0 ly regs0 c) AFkb.PT R3_J W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))).
{ split; [reflexivity|]. exists msJ, matJ, E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HSJ|]. split; [|split; [exact PRS | exact I]].
intros x Hx. destruct (TABW_dec T (bv_unsigned x)) as [Ht|Ht]; [unfold mR; rewrite (memR_on _ x Ht); reflexivity | rewrite (MEQR x Ht); exact (MEQ x Hx Ht)]. }
rewrite (AFhn.refill_tree_init c S Huninit). fold (AFhn.S1 S). fold S1.
eapply amreal_mono; [intros r W'' c''; exact (AFhn.refill_leaf_init B ly S W mem0 mR md0 HAR MEQR regs0 c r W'' c'')|].
exact (@AFkn.refill_B3 _ _ W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug matJ msJ HJ HslotPres1 HfaPres1 B S1 TS HTSD HARm1 Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 HAR1 Hpum1 Hslack1 HQL1).
Qed.
Theorem refill_uninit_B2 : max_cached c / 2 <= fa_len (rg_free (reg S c)) ->
amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
intros Henough.
destruct PRE as (HAR & Hslack & Hpum & HQL & Hra & Hra4096 & Hal & Hlo & Hhi & Hpres0R & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3 & HcR & Hchunks).
pose proof (proj1 HAR) as HARm. unfold spZ, raZ in *.
assert (LY : layout_ok ly) by exact (am_layout _ _ _ _ HARm).
assert (IMG : img_cover ly) by exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS)).
rewrite (ts_tp B TS) in Htp.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (repeat split; assumption).
set (maxc := max_cached c). set (n := maxc / 2). set (nf := fa_len (rg_free (reg S c))). set (mf := rg_mapped_fa (reg S c)).
set (au := rg_alloc_user (reg S c)). set (mu := rg_mapped_user (reg S c)). set (csz := class_size c). set (mat0 := m_vm_materialized md0).
assert (Hmax : maxc = max_cached c) by reflexivity. assert (Hn : n = maxc / 2) by reflexivity. assert (Hcsz : csz = class_size c) by reflexivity.
assert (Hnf_def : nf = fa_len (rg_free (reg S c))) by reflexivity. assert (Hmf_def : mf = rg_mapped_fa (reg S c)) by reflexivity.
assert (Hau_def : au = rg_alloc_user (reg S c)) by reflexivity. assert (Hmu_def : mu = rg_mapped_user (reg S c)) by reflexivity.
assert (Hnle : n <= nf) by exact Henough.
pose proof (@AFkx.Hnf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (@AFkx.Hmf' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (@AFkx.Hmu' _ W ly regs0 mem0 c maxc nf mf au mu HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
destruct (@AFkx.junk_valuesR _ W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def)
as (j64 & jna & jnf & jsm & jm1 & jm2 & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v]).
pose proof (@AFkx.HslotPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HslotPres.
pose proof (@AFkx.HfaPres' _ W ly regs0 mem0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HfaPres.
pose proof (@AFkx.thread_present _ W ly regs0 mem0 c maxc nf mf au mu LY IMG HcR Hsp B S HARm Hnf_def Hmf_def Hau_def Hmu_def) as HTP.
pose proof (@AFkx.SPAN_disj _ ly regs0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp) as HSPAN.
pose proof (@AFkx.SEEDU_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Huninit) as SEEDU.
replace (cfg_at tfibsegs A_Refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
by (unfold cfg_at, A_Refill; subst mat0; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@AFky.segU _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp mat0 HTP HSPAN SEEDU). }
intros W' c' _ HP. destruct HP as (-> & msJ & matJ & E' & -> & HE & HSJ & MEQ & PRS & TBF & TPR).
set (mR := memR (ms_mem msJ)).
assert (R64 : 4096 <= T /\ T + kThreadObjSize <= ASAN_CEIL).
{ pose proof (Forall_nth' _ _ 2 _ (lo_app ly LY) eq_refl) as IT. cbv beta in IT. unfold in_app in IT. cbn [fst snd] in IT. unfold T. ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.     }
assert (MEQR : forall x : word, ~ TABW T (bv_unsigned x) -> mR x = mem0 x) by (intros x Hx; exact (memR_off (ms_mem msJ) x Hx)).
assert (TBFR : forall i, 1 <= i <= 31 -> tbl_facts (mrestrict (w_H W) mR) T i).
{ intros i Hi. destruct (TBF i Hi) as [M1 M2].
split; (eapply val_mem_frame; [|eassumption]); intros k Hk; unfold mR; apply memR_on; rewrite unsigned_lit_small by (clear - Hi Hk R64; ceil; unfold kThreadObjSize, kHighMemBeg, ASAN_CEIL in R64; lia); exists i; lia. }
assert (TPRR : forall a, TABW T a -> apresent (w_H W) mR a).
{ intros a Ha. pose proof (TABW_range T a Ha).
eapply apresent_same; [|exact (TPR a Ha)]. unfold mR. apply memR_on. rewrite unsigned_lit_small by (clear - H R64; ceil; unfold kThreadObjSize, kHighMemBeg, ASAN_CEIL in R64; lia). exact Ha. }
pose proof (AFhn.AR_init B ly S W mem0 mR md0 TS HAR Huninit MEQR TBFR TPRR IMG) as HAR1. fold S1 in HAR1.
pose proof (proj1 HAR1) as HARm1.
assert (PRESR : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mR a) by (intros a; exact (AFhn.PRES_MONO ly W mem0 mR MEQR TPRR a)).
assert (Hinited1 : st_cache_inited S1 = true) by reflexivity.
assert (Hchunks1 : pc_chunks (cache S1 c) = []) by (unfold S1; rewrite (AFhn.cache_S1 B ly S W mem0 md0 HAR Huninit c HcR); reflexivity).
assert (Hnf_def1 : nf = fa_len (rg_free (reg S1 c))) by exact Hnf_def. assert (Hmf_def1 : mf = rg_mapped_fa (reg S1 c)) by exact Hmf_def.
assert (Hau_def1 : au = rg_alloc_user (reg S1 c)) by exact Hau_def. assert (Hmu_def1 : mu = rg_mapped_user (reg S1 c)) by exact Hmu_def.
assert (Hnle1 : n <= fa_len (rg_free (reg S1 c))) by exact Hnle.
pose proof (@AFko.derived_rangesR _ ly regs0 c maxc n nf mf au mu csz LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu) as DR.
assert (JV : forall a (w : nat) v, (AFko.RGv ly c <= a /\ a + Z.of_nat w <= AFko.RGv ly c + 128) \/ (T + 2768 <= a /\ a + Z.of_nat w <= T + kThreadObjSize) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) a w v -> val_mem tfibsegs (mrestrict (w_H W) mR) a w v).
{ intros a w v Ha HV. pose proof (lo_space_in ly LY) as SP. unfold zdisjoint in SP.
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
apply (AFhn.val_mem_R ly W mem0 mR MEQR a w v); [| clear - Ha DR R64; unfold AFko.RGv in *; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff in *; lia
| clear - Ha DR R64; unfold AFko.RGv in *; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff in *; lia | exact HV].
intros k Hk Ht. apply TABW_range in Ht. clear - Ha Hk Ht DR R64 SP PT HcR. unfold AFko.RGv in *. unfold T in *.
ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kRegionInfoOff, kSpaceSize, kPrimResvSize in *. lia. }
assert (Hj64v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (AFko.RGv ly c + 64) 4 j64) by (apply JV; [left; cbn; lia | exact Hj64v]).
assert (Hjnav1 : val_mem tfibsegs (mrestrict (w_H W) mR) (AFko.RGv ly c + 72) 8 jna) by (apply JV; [left; cbn; lia | exact Hjnav]).
assert (Hjnfv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (AFko.RGv ly c + 80) 8 jnf) by (apply JV; [left; cbn; lia | exact Hjnfv]).
assert (Hjsmv1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2792) 8 jsm) by (apply JV; [right; cbn; unfold kThreadObjSize; lia | exact Hjsmv]).
assert (Hjm1v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2872) 8 jm1) by (apply JV; [right; cbn; unfold kThreadObjSize; lia | exact Hjm1v]).
assert (Hjm2v1 : val_mem tfibsegs (mrestrict (w_H W) mR) (T + 2880) 8 jm2) by (apply JV; [right; cbn; unfold kThreadObjSize; lia | exact Hjm2v]).
assert (HslotPres1 : forall a, AFko.DSTv ly c <= a < AFko.DSTv ly c + 64 -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HslotPres, Ha).
assert (HfaPres1 : forall a, AFko.FAv ly c <= a < AFko.FAv ly c + mf -> apresent (w_H W) mR a) by (intros a Ha; apply PRESR, HfaPres, Ha).
assert (HJ : @AFko.at_R _ W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 RJ2 W (mkCfg msJ (with_vm_backing (m_vm_lazy md0) matJ md0))).
{ split; [reflexivity|]. exists msJ, matJ, E'. split; [reflexivity|]. split; [exact (proj1 HE)|]. split; [exact HSJ|]. split; [|exact PRS].
intros x Hx. destruct (TABW_dec T (bv_unsigned x)) as [Ht|Ht]; [unfold mR; rewrite (memR_on _ x Ht); reflexivity | rewrite (MEQR x Ht); exact (MEQ x Hx Ht)]. }
rewrite (AFhn.refill_tree_init c S Huninit). fold (AFhn.S1 S). fold S1.
eapply amreal_mono; [intros r W'' c''; exact (AFhn.refill_leaf_init B ly S W mem0 mR md0 HAR MEQR regs0 c r W'' c'')|].
destruct (@AFkz.refill_B2_model _ W ly regs0 mR c maxc n nf mf au mu csz HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S1 HARm1 Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 Hnle1)
as (tops & rest & EP & RUN & WFR & E1 & E2 & E3 & E4).
rewrite RUN. cbn [amreal].
eapply SRr_mono.
{ exact (@AFkw.segB2 _ _ W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp matJ msJ HJ HslotPres1 HfaPres1 Hnle1). }
intros W'' c'' _ HR.
exact (@AFkz.LEAF_B2 _ _ W ly regs0 mR md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp matJ msJ HJ HfaPres1 B S1 TS HTSD HARm1 Hinited1 Hchunks1 Hnf_def1 Hmf_def1 Hau_def1 Hmu_def1 HAR1 Hnle1 tops rest W'' c'' WFR E1 E2 E3 E4 HR).
Qed.
Theorem refill_uninit :
amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
destruct (Z_lt_le_dec (fa_len (rg_free (reg S c))) (max_cached c / 2)) as [Hfew|Henough].
- exact (refill_uninit_B3 Hfew).
- exact (refill_uninit_B2 Henough).
Qed.
End d.
Theorem tfib_refill_ok : forall B, TfibSyms B -> tfib_refill_spec B.
Proof.
intros B TS ly S W regs mem md c PRE. destruct (st_cache_inited S) eqn:Hi.
- exact (AFku.refill_inited B TS ly S W regs mem md c PRE Hi).
- exact (refill_uninit B TS ly S W regs mem md c PRE Hi).
Qed.
End b.
