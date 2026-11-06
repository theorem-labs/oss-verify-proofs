(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFil.v (donor image sha256 1c29845fe605), with its module paths changed, names TfibSyms -> UciSyms and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/YFil.v (donor image sha256 fde52226dc48), with its module paths changed, names GrantSyms -> UciSyms and its addresses moved to reac-repacer/fuzz_uci's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG07. From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YFl1.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0a. From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1w YE3d YFhy YFi1.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YFj6 YFi3 YFjc YFje YFjb YFjg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TS : UciSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly 0x51a24 regs0 ch.
Hypothesis PRE : acall_pre tfibsegs B ly S W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Variables (l : list Z) (off : Z).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S (chunk_class n)) = l ++ [off].
Theorem malloc_hitk :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs 0x51788 regs0 mem0 md0) (malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n).
Proof.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & CH & HQT).
pose proof (proj1 HAR) as HARm0. unfold spZ in *.
set (S1 := set_nev (st_nev S + 1) S).
pose proof (ARm_tick B ly S _ HARm0 Hev) as HARm. fold S1 in HARm.
pose proof (AR_tick B ly S W mem0 md0 HAR Hev) as HAR1. fold S1 in HAR1.
assert (Hinited1 : st_cache_inited S1 = true) by exact Hinited.
assert (Hcache1 : pc_chunks (cache S1 (chunk_class n)) = l ++ [off]) by exact Hcache.
assert (HQT1 : qtight S1) by exact (qmeter_tight _ HQT).
assert (LY : layout_ok ly) by exact (am_layout _ _ _ _ HARm).
assert (IMG : img_cover ly) by exact (img_cover_of_ledger ly S1 md0 (proj1 (proj2 HAR1))).
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ HARm); exact (ts_tsd B TS)).
rewrite (ts_tp B TS) in Htp.
destruct CH as [Hra4096 Hch]. unfold raZ in Hra4096. unfold frame0_ok, spZ, s0Z in Hch.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (repeat split; assumption).
set (cl := chunk_class n) in *. set (cnt := Z.of_nat (length (l ++ [off]))). set (v := off / 16). set (csz := class_size cl).
set (DPOST := fun z m => YFjb.DPOST3 W ly regs0 ch B S1 z m). set (mat0 := m_vm_materialized md0).
assert (Hcl_class : cl = chunk_class n) by reflexivity.
assert (Hcnt_def : cnt = Z.of_nat (length (l ++ [off]))) by reflexivity.
assert (Hcsz_def : csz = class_size cl) by reflexivity.
assert (Hcl : 1 <= cl <= 31) by exact (@YFjc.Hcl' ly regs0 mem0 n cl v DPOST Nrange l off Hcl_class).
assert (Hoffv : off = 16 * v /\ v mod 2 = 0).
{ pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm) cl Hcl) as CL. pose proof (wr_elems _ _ _ _ _ _ CL) as EL. rewrite Hcache1 in EL.
pose proof (proj1 (Forall_forall _ _) EL off ltac:(rewrite !in_app_iff; cbn; tauto)) as [_ O2].
pose proof (class_ok cl Hcl) as (K1 & K2 & _). apply Z.mod_divide in O2 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [r Hr]; [|lia].
subst v. rewrite Hq, Hr. replace (q * (r * 32)) with ((2 * q * r) * 16) by lia. rewrite Z.div_mul by lia. split; [lia|].
rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. }
destruct Hoffv as [Hoff_def Hv2].
assert (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32)
by exact (@YFjc.Hv' _ W ly regs0 mem0 n cl cnt v Hv2 DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def).
assert (Hcnt : 1 <= cnt <= 16)
by exact (@YFjc.Hcnt' _ W ly regs0 mem0 n cl cnt v Hv2 Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def).
destruct (@YFjc.junk_values _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
pose proof (@YFjc.KPRES _ W ly regs0 mem0 n cl cnt v csz Hv2 LY Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def) as HKpres.
pose proof (@YFjc.SKPRES _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def) as HSKpres.
pose proof (@YFjc.PB250 _ W ly regs0 mem0 n cl cnt v csz Hv2 LY IMG Hsp DPOST Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def) as HPB250.
pose proof (@YFj6.case0_sizes n Nrange) as (L & RS & R8 & NP & FP & NS & RQ).
assert (Hcl_def : cl = class_id (YFj6.R8v n + YFj6.RZ)) by (subst cl; unfold chunk_class; rewrite NS, <- RS; reflexivity).
pose proof (@YFje.SEED_ok _ _ W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hsp DPOST Nrange Hcl_def B S1 l off TS HTSD HARm Hpres0 Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def) as SEED.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) (am_wf _ _ _ _ HARm0) Hev); [unfold MALLOC_MAX; lia | exact Hlive | exact Htr]. }
rewrite (malloc_primary_eq n tr S FP). eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
fold S1. rewrite <- Hcl_class.
eapply amreal_pure; [apply refill_tree_ready; [exact Hinited1 | rewrite Hcache1; destruct l; discriminate]|].
eapply amreal_mono; [| exact (@YFjg.hitk_inner _ _ W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hra Hra4096 Hsp Hch DPOST HKpres HSKpres HPB250 Nrange Hcl_def mat0 U1 SEED B S1 l off TS HTSD HARm Hgp Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def Htr HAR1 D1 (fun z m H => H) (fun z m H => H) eq_refl)].
intros [p s'] W' c' H [ns MP]. cbn [fst snd] in H, MP. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (H (conj WF' (QT (qmeter_tight _ HQT)))).
Qed.
End b.
End a.
