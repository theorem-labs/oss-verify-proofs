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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFkp AFk6 AFk8 AFk5 AFkk AFkb AFkn AFkt.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Hypothesis PRE : refill_pre B ly S W regs0 mem0 md0 c.
Hypothesis Hinited : st_cache_inited S = true.
Theorem refill_B3 : fa_len (rg_free (reg S c)) < max_cached c / 2 ->
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
pose proof (@AFkk.SEEDR3_ok _ _ W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Htp Ha0 Ha1 Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v) as SEEDR.
replace (cfg_at tfibsegs A_Refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x36104) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
by (unfold cfg_at, A_Refill; subst mat0; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@AFkb.seg3J _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hpres0R mat0 SEEDR). }
intros W' c' _ HJ. pose proof HJ as [EW (msJ & matJ & E' & EcJ & HJrest)]. subst W'. rewrite EcJ in HJ |- *.
exact (@AFkn.refill_B3 _ _ W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hsp Hra Htp Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug matJ msJ HJ HslotPres HfaPres B S TS HTSD HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def HAR Hpum Hslack HQL).
Qed.
Theorem refill_inited :
amreal tfibsegs (refill_tree c S) W (cfg_at tfibsegs A_Refill regs0 mem0 md0) (refill_leaf B ly S W regs0 mem0 md0 c).
Proof.
destruct (Z_lt_le_dec (fa_len (rg_free (reg S c))) (max_cached c / 2)) as [Hfew|Henough].
- exact (refill_B3 Hfew).
- exact (AFkt.refill_B2 B TS ly S W regs0 mem0 md0 c PRE Hinited Henough).
Qed.
End b.
End a.
