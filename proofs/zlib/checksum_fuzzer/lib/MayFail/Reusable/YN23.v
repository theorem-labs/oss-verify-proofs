(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN23.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Abbreviation B := src0_msyms.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem src0_malloc_small : alloc_slot_hyp B -> malloc_small_hyp B.
Proof.
intros ASH L A regs mem md n PRE R10 Hn.
change (ms_segs B) with src0segs. change (ms_malloc B) with src0_A_malloc.
pose proof PRE as (MX & HW & _).
apply (mreal_by_itok src0segs (malloc n A) _ _ (malloc_post [] U0 A n)).
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
Corollary src0_malloc_realizes_of_hyps :
alloc_meta_hyp B -> alloc_slot_hyp B -> malloc_realizes B (MRx B).
Proof. intros AMH ASH. apply (src0_malloc_realizes AMH). apply src0_malloc_small. exact ASH. Qed.
End a.
