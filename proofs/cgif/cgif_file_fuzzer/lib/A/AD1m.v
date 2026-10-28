(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0s YK15 YK18 YM02 YP0m YP09 YI00 YI16 YK04 YA0i YA0n
YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m ACeg AD1t AD20 AD1v AD2h AD2f AD1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbq YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn AD1u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBC : tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Lemma layout_of_AR' : forall ly S W mem md, AR tfibsegs B ly S W mem md -> layout_ok ly.
Proof. intros ly S W mem md H. exact (am_layout _ _ _ _ (proj1 H)). Qed.
Theorem tfib_lib_site_x : lib_site_x B.
Proof.
intros ly S W regs mem md p n pl K HPRE R10 R11 Hpn Hlen Hpl Hfr Hev Hlive Hro HFI Hfree Hnames Hsorted HAI CONT.
pose proof HPRE as (HAR & Hret & Hra & Hgp & Htp & Hal & [Wlo Whi] & [Tlo Thi] & Elo & Ehi & Hpres & Hs0 & Hqt).
pose proof (layout_of_AR' _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
destruct HFI as ((M & HAM) & Henv & Hhead).
apply (LIBC ly S W regs mem md p n pl M K HAI).
-
split.
{ split; [exact HAR|]. split; [exact Hret|]. split; [rewrite Hra; cbv; discriminate|]. split; [exact Hgp|]. split; [exact Htp|].
split.
- unfold astk_ok. rewrite Ehi. unfold ly_bot, kHighMemEnd, LLVMF_STK, ASTACK, kStackSpan in *. repeat split; lia.
- split; [exact Hpres|]. split; [| exact Hqt]. apply achain_low. exact Hs0. }
split; [exact Hra|]. split; [exact R10|]. split; [exact R11|]. split; [exact Hpn|].
split; [exact Hlen|]. split; [exact Hpl|]. split; [exact Hfr|]. split; [exact Hev|]. split; [exact Hlive|].
split.
{ intros a Ha Hno Hne. apply Hro; [| exact Hno | exact Hne]. destruct Ha as [Ha | Ha]; [left; exact Ha | exact (RO_IN a Ha)]. }
split; [exact (conj Henv (conj Hhead Hnames))|].
split; [exact Hfree|]. split; [exact Hsorted|]. split; [exact HAM | apply MT_FREE].
-
intros l W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Hc' & HJ & Hk & HP & Ha0 & HPERM & Hfdl & Hmfs & Hret' & Hout & Hsorted' & (Henv' & Hhead' & Hnames') & HAM' & _ & Hplk).
apply (CONT l W' c' Hwle HAI'). exists ly', S', regs', mem', md', k.
split; [exact Hc'|]. split; [exact HJ|]. split; [exact Hk|]. split; [exact HP|]. split; [exact Ha0|]. split; [exact HPERM|].
split; [exact Hfdl|]. split; [exact Hmfs|]. split; [exact Hret'|]. split; [exact Hout|]. split; [exact Hsorted'|]. split; [exact Hnames'|].
split; [| exact Hplk]. split; [exists M; exact HAM' | exact (conj Henv' Hhead')].
Qed.
End c.
End b.
