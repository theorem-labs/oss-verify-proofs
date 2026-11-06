(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN23.v, with its module paths changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YO0i YO0f YO0a YO0g YO0w YO0s YO0x YO0y YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN03 YN02_cf YN2b YN2f_cf YN0e_cf
YN1z_cf YN2z_cf YN1p_cf YN1r_cf YN1s_cf YN1u_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Abbreviation B := src0_msyms.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem src0_malloc_small : alloc_slot_hyp_cf B -> malloc_small_hyp_cf B.
Proof.
intros ASH L A regs mem md n PRE R10 Hn.
change (ms_segs B) with src0segs. change (ms_malloc B) with src0_A_malloc.
pose proof PRE as (MX & HW & _).
apply (mreal_cf_by_itok src0segs (malloc n A) _ _ (malloc_post [] U0 A n)).
{ apply (malloc_spec U0 A n); [exact HW | lia | intros r H; exact H]. }
rewrite (malloc_small_unfold n A) by (try lia; unfold size_overflows; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia).
rewrite malloc_small_body_shape.
eapply mreal_cf_SR_pre; [apply (T0_SR L A regs mem md n PRE Hn R10)|]. intros c1 (regs1 & mem1 & -> & AT).
eapply mreal_cf_SR_pre; [apply (T1_SR L A regs mem md n PRE Hn regs1 mem1 AT)|]. intros c2 (regs2 & -> & PBS).
change (msc A n) with (sc A n).
destruct (active_hd A (sc A n)) as [gm|] eqn:Hhd.
- destruct (sc_head L A regs mem md n PRE Hn gm Hhd) as (am & Hu & Hsc & Mg). rewrite Mg.
destruct (am_avail am =? 0) eqn:Eav.
+ apply Z.eqb_eq in Eav. apply (slow_path L A regs mem md n PRE Hn regs1 mem1 AT regs2 PBS ASH).
unfold gmask. rewrite Hhd. unfold avail_of, amo. rewrite Mg, Eav. reflexivity.
+ apply Z.eqb_neq in Eav. exact (fast_path L A regs mem md n PRE Hn regs1 mem1 AT regs2 PBS gm am Hhd Mg Eav).
- apply (slow_path L A regs mem md n PRE Hn regs1 mem1 AT regs2 PBS ASH).
unfold gmask. rewrite Hhd. reflexivity.
Qed.
Corollary src0_malloc_realizes_of_hyps :
alloc_meta_hyp_cf B -> alloc_slot_hyp_cf B -> malloc_realizes_cf B (MRx B).
Proof. intros AMH ASH. apply (src0_malloc_realizes AMH). apply src0_malloc_small. exact ASH. Qed.
End a.
