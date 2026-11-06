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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3w YF8g YF8i YF8f YF8n YF8o YF8q.
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
Hypothesis Henough : max_cached c / 2 <= fa_len (rg_free (reg S c)).
Theorem refill_B2 :
amreal tfxsegs (refill_tree c S) W (cfg_at tfxsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
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
pose proof (@YF8o.SEEDR_ok _ _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) as SEEDR.
destruct (@YF8q.refill_B2_model _ imgk W ly regs0 mem0 c maxc n nf mf au mu csz HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp B S HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hnle)
as (tops & rest & EP & RUN & WFR & E1 & E2 & E3 & E4).
replace (cfg_at tfxsegs A_Refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 (0x3670c + D_150)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
by (img_try (unfold cfg_at, A_Refill; (subst mat0; cbv beta); rewrite with_vm_backing_id; img_refl)).
eapply amreal_SRr_pre.
{ img_exact (@YF8n.seg2J _ _ imgk W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp mat0 SEEDR). }
intros W' c' _ HJ. pose proof HJ as [EW (msJ & matJ & E' & EcJ & _)]. (subst W'; cbv beta). rewrite EcJ in HJ |- *.
rewrite RUN. cbn [amreal].
eapply SRr_mono.
{ img_exact (@YF8n.segB2 _ _ imgk W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp matJ msJ HJ HslotPres HfaPres Hnle). }
intros W'' c'' _ HR.
img_exact (@YF8q.LEAF_B2 _ _ imgk W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 LY IMG HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp matJ msJ HJ HfaPres B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def HAR Hnle tops rest W'' c'' WFR E1 E2 E3 E4 HR).
Qed.
End b.
End a.
