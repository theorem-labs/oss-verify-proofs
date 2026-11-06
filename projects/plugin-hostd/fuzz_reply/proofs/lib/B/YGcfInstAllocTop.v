(* CARRIED from commit 9e2e0be6e3e5010921fb7ec0e30341da3a6c3da2,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstAllocTop.v, sha256 8a8dcf4d199e8c7fb09841836a7ef2cd1655a16d9802ffae55d81be7ab393535 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the
   module paths only: OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib M -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable M, except lib.B (the asan-ubsan image twin of lib/A/YGcfInstAllocTop.v)
   for: YGcfRmodel YGcfMallocCompose YGcfMallocComposeE MemnormT AllocG AllocGtopM AGtop YGcfInstBase YGcfInstWalkSig. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The cf layer's Allocate TOP (lane M, a working branch): YGcfMallocComposeE's three Allocate Props at the
   call-site relation ARXq_cf, from a unit's walk tops (YGcfInstWalkSig.WalkSigA at every ghost set).

   rule 24: no function proved (kind: top-level composition over the unit's walk tops).  The case split is
   MemnormAtop.aalloc_prim_realizes_em_of_arms's (A/MemnormAtop.v:81-103, itself AGtopE.v:85-102), with cgif's
   [tfibsegs] / 0x31550 replaced by [im_segs] / CfImg's [cf_pc_allocate], and its UNINIT hypothesis PROVED from
   ARcf's Wf_cf (the class records' wrc_cache: an uninited cache is pclass0).

   Fixed arguments, as YGcfMallocComposeE.v:94-110 states the Props: U := the universe trace premise, mt := malloc_cf,
   AOX := AOXm_cf B, rpre := rpre_cfr B (ROOM_cf is the caller's), nmax := cf_malloc_max, lmax := LIVE_MAX,
   lpost := qtight, pcA := cf_pc_allocate, oomb := as_oom_byte B, al / atp := 8 / 1, can_fill [cf] in {0, 1}.
   EVENT-FREE and MT-FREE. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK0j YK15 YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import MemnormT AllocG AllocGtopM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGtop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstWalkSig.
Import ListNotations.
Open Scope Z_scope.
(* cgif's YM05 / YM03 redefine [lia] for the run-ceiling goals; this file's arithmetic is plain. *)
Local Ltac zl := YM03.lf_lia_orig.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Section b.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable cf : Z.
Hypothesis HCF : cf = 0 \/ cf = 1.

(* The unit's Allocate walk tops, at the call-site relation, at every ghost set.  This is the seam: a unit proves it
   by instantiating its relocated walk tops with the layer's interface instances (YGcfInstHit / Miss / Sec). *)
Hypothesis WS : forall Hp, WalkSigA im_segs B (U_cf B) malloc_cf (ARXq_cf B IOK Hp)
  (AOXm_cf B) (YGcfRmodel.rpre_cfr B) cf_malloc_max LIVE_MAX qtight cf.

(* MemnormAtop's UNINIT, proved: an uninited cache is pclass0 (Wf_cf's class record, wrc_cache). *)
Lemma uninit_cf : forall Hp inst ly S W mem md c, ARXq_cf B IOK Hp inst ly S W mem md -> 1 <= c <= 31 ->
  st_cache_inited S = false -> pc_chunks (cache S c) = [].
Proof.
intros Hp inst ly S W mem md c H Hc HI.
pose proof (ARX_cf_wf B IOK Hp inst ly S W mem md (ARXq_cf_ARX B IOK Hp inst ly S W mem md H)) as WF.
pose proof (wfc_classes _ _ _ _ _ WF c Hc) as C. unfold wf_class_cf in C.
pose proof (wrc_cache _ _ _ _ _ _ C) as K. rewrite HI in K. rewrite K. reflexivity.
Qed.

(* The primary sizes: the four arms, split as MemnormAtop splits them.  Part 3b / 3c: the contract's MP (arodata_ok_cf
   at Allocate's entry memory) goes to the two miss arms. *)
Theorem aalloc_prim_realizes_cf_em_m_cf :
  aalloc_prim_realizes_cf_em_m im_segs B cf_malloc_max 8 1 cf (ARXq_cf B IOK).
Proof.
intros Hp. destruct (WS Hp) as [HITG HITK MISSG MISSK _].
intros inst so bp ly S W regs mem md n tr HPRE HRO Hn64.
pose proof (proj1 HPRE) as HAR.
assert (Hn0 : 0 <= n) by (clear - HPRE; unfold alloc_pre in HPRE; decompose [and] HPRE; zl).
assert (Nrange : 0 <= n <= 64512) by zl.
pose proof (primary_geometry n Hn0 (AGtop.prim_fp_g n Nrange)) as (Hcl & _).
destruct (pc_chunks (cache S (chunk_class n))) as [|x t] eqn:El.
- destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
  + exact (MISSG inst so bp ly S W regs mem md n tr HCF HPRE HRO ltac:(zl) El).
  + exact (MISSK inst so bp ly S W regs mem md n tr HCF HPRE HRO ltac:(zl) El).
- assert (LX : exists l off, x :: t = l ++ [off])
    by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
  destruct LX as (l & off & LX). rewrite LX in El.
  destruct (st_cache_inited S) eqn:CI.
  + destruct (Z_lt_le_dec 48 n) as [Hbig|Hsmall].
    * exact (HITG inst so bp ly S W regs mem md n tr l off HCF HPRE ltac:(zl) CI El).
    * exact (HITK inst so bp ly S W regs mem md n tr l off HCF HPRE ltac:(zl) CI El).
  + exfalso. rewrite (uninit_cf Hp inst ly S W mem md (chunk_class n) HAR ltac:(zl) CI) in El.
    destruct l; discriminate El.
Qed.

(* The secondary sizes: the unit's secondary walk top. *)
Theorem aalloc_sec_realizes_cf_em_m_cf :
  aalloc_sec_realizes_cf_em_m im_segs B cf_malloc_max 8 1 cf (ARXq_cf B IOK).
Proof.
intros Hp. destruct (WS Hp) as [_ _ _ _ SEC].
intros inst so bp ly S W regs mem md n tr HPRE Hn.
exact (SEC inst so bp ly S W regs mem md n tr HCF HPRE Hn).
Qed.

(* Every size: YGcfMallocComposeE's own split. *)
Theorem aalloc_realizes_cf_em_m_cf :
  aalloc_realizes_cf_em_m im_segs B cf_malloc_max 8 1 cf (ARXq_cf B IOK).
Proof.
exact (aalloc_realizes_cf_em_m_of_prim_sec im_segs B cf_malloc_max 8 1 cf (ARXq_cf B IOK)
  aalloc_prim_realizes_cf_em_m_cf aalloc_sec_realizes_cf_em_m_cf).
Qed.

End b.
End a.
