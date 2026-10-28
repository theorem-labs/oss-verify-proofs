(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YO0i YO0f YO0a YO0g YO0w YO0s YO0x YO0y YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YM06 YK0s YM02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN03 YN02 YN2b YN2f UN0e
UN1z YN2z UN1p UN1r UN1s UN1u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Abbreviation B := ubs0_msyms.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem ubs0_malloc_small : alloc_slot_hyp B -> malloc_small_hyp B.
Proof using.
intros ASH L A regs mem md n PRE R10 Hn.
change (ms_segs B) with ubs0segs. change (ms_malloc B) with ubs0_A_malloc.
pose proof PRE as (MX & HW & _).
apply (mreal_by_itok ubs0segs (malloc n A) _ _ (malloc_post [] U0 A n)).
{ apply (malloc_spec U0 A n); [exact HW | lia | intros r H; exact H]. }
rewrite (malloc_small_unfold n A) by (try lia; unfold size_overflows; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia).
rewrite malloc_small_body_shape.
eapply mreal_SR_pre; [apply (T0_SR L A regs mem md n PRE Hn R10)|]. intros c1 (regs1 & mem1 & -> & AT).
eapply mreal_SR_pre; [apply (T1_SR L A regs mem md n PRE Hn regs1 mem1 AT)|]. intros c2 (regs2 & -> & PBS).
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
Corollary ubs0_malloc_realizes_of_hyps :
alloc_meta_hyp B -> alloc_slot_hyp B -> malloc_realizes B (MRx B).
Proof using. intros AMH ASH. apply (ubs0_malloc_realizes AMH). apply ubs0_malloc_small. exact ASH. Qed.
End a.
