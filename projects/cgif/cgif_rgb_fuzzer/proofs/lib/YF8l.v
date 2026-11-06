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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8g YF7x YF7z YF7w YF8b YF82 YF8e YF8k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Section b. Context {imgk : img}.
Variable B : asyms.
Hypothesis TS : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Hypothesis PRE : refill_pre B ly S W regs0 mem0 md0 c.
Hypothesis Hinited : st_cache_inited S = true.
Theorem refill_B3 : fa_len (rg_free (reg S c)) < max_cached c / 2 ->
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
pose proof (@YF8b.SEEDR3_ok _ _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) as SEEDR.
replace (cfg_at tfxsegs A_Refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
by (img_try (unfold cfg_at, A_Refill; (subst mat0; cbv beta); rewrite with_vm_backing_id; img_refl)).
eapply amreal_SRr_pre.
{ img_exact (@YF82.seg3J _ _ imgk W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hpres0R mat0 SEEDR). }
intros W' c' _ HJ. pose proof HJ as [EW (msJ & matJ & E' & EcJ & HJrest)]. (subst W'; cbv beta). rewrite EcJ in HJ |- *.
img_exact (@YF8e.refill_B3 _ _ imgk W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug matJ msJ HJ HslotPres HfaPres B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def HAR Hpum Hslack HQL).
Qed.
Theorem refill_inited :
amreal tfxsegs (refill_tree c S) W (cfg_at tfxsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
destruct (Z_lt_le_dec (fa_len (rg_free (reg S c))) (max_cached c / 2)) as [Hfew|Henough].
- img_exact (refill_B3 Hfew).
- img_exact (YF8k.refill_B2 B TS ly S W regs0 mem0 md0 c PRE Hinited Henough).
Qed.
End b.
End a.
