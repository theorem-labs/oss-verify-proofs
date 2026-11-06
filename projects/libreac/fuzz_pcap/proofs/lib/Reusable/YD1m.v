(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD1m.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms, for libreac/fuzz_pcap's asan-ubsan build (pinned image fuzz_pcap.asan-ubsan sha256 9e66f771f22a, symbols from its unstripped twin fuzz_pcap.asan-ubsan sha256 c969d83cdd59). It is the asan-ubsan twin of a Theorem Labs lane's lib/A/AD1m.v (a working branch 9700d736a50; commit 5bede1a6d6b), every hunk mirrored. ADAPTED to pcap's program contract (porter ruling 1): the donor's LIBC (tfib_lib_contract_x of cgif's YCfn.v) is the image-free lib/A/Prog/PcapEntry.v's tfib_lib_contract_x at the asan-ubsan instance's data, lib/B/Prog/PcapEntry.v (the twin of lib/A/Prog/PcapEntryA.v): the segments tfibsegs (AsanUbsan), the read-only window PCAP_RLO / PCAP_RHI = 0x99198 / 0x9a3f0 (lib/B/Prog/PcapRelro.v: start of .data.rel.ro, end of .got), A_LLVMF / RA_LLVMF / A_EMPTY / LLVMF_STK, the harness globals G_HARNESS_U, and the source record pcap_KS (lib/B/Stdio/PSourceK.v); the sink head SK is passed explicitly and pcap_head (Reusable/YD1u.v) ties it to the measured ofl_head 0x5f4e88. The donor's proof is kept: lib_site_x's pre (FINV over the source, Reusable/YD1u.v) gives the contract's pre (asource_none pcap_KS = FINV's last two conjuncts; the head law from pcap_head; the inert fd-names conjunct from lib_site_x's own premise, as cgif's asink_none gives it), and the contract's post gives lib_site_x's continuation (ajournal_gx unchanged; the fd-names conjunct of the PcapEntry.v post; FINV' from asrc_meta_inv / asource_none). RO_IN is or_intror: in_ro_tfa (Reusable/YCeg.v:54-56) already names the window 0x99198 .. 0x9a3f0 = PCAP_RLO .. PCAP_RHI. The output shape is AgreePcap.ag_out_shape, the one PcapEntry states LIBK at. lib/A/AD1m.v's Require of lib/A/W_journal.v is lib/A/W_journalG.v here (W_journal.v adds only the asan program-walk runner over lib/A/Prog/PcapPa and Exports W_journalG); cgif's YE2k (not ported, porter ruling 6) and YCfn (replaced by PcapEntry) are dropped from the Require. rule 24: no function proved anew. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YM02 YP0m YP09 YI00 YI16 YK04 YA0i YA0n
YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YF0m YCeg YD1t YD20 YD1v YD2h YD2f YD1w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Stdio Require Import PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapRelro PcapEntry.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YD1u.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {PH : pcap_head}.
Section c.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
(* donor AD1m.v:31 LIBC, at pcap's program contract (PcapEntry.v tfib_lib_contract_x, SK explicit). *)
Hypothesis LIBC : tfib_lib_contract_x SK tfibsegs PCAP_RLO PCAP_RHI A_LLVMF RA_LLVMF A_EMPTY LLVMF_STK G_HARNESS_U B MT XM_LIB XN_LIB pcap_KS.
Lemma layout_of_AR' : forall ly S W mem md, AR tfibsegs B ly S W mem md -> layout_ok ly.
Proof. intros ly S W mem md H. exact (am_layout _ _ _ _ (proj1 H)). Qed.
Theorem tfib_lib_site_x : lib_site_x (LS:=AgreePcap.ag_out_shape) B.
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
{ intros a Ha Hno Hne. apply Hro; [| exact Hno | exact Hne]. destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact Ha]. }
split; [exact (conj Henv Hhead)|].
split; [unfold YCbq.AOFL_HEAD; rewrite pcap_head_eq; reflexivity|].
split; [exact Hfree|]. split; [exact Hnames|]. split; [exact Hsorted|]. split; [exact HAM | apply MT_FREE].
-
intros l W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Hc' & HJ & Hk & HP & Ha0 & HPERM & Hfdl & Hnames' & Hmfs & Hret' & Hout & Hsorted' & (Henv' & Hhead') & HAM' & _ & Hplk).
apply (CONT l W' c' Hwle HAI'). exists ly', S', regs', mem', md', k.
split; [exact Hc'|]. split; [exact HJ|]. split; [exact Hk|]. split; [exact HP|]. split; [exact Ha0|]. split; [exact HPERM|].
split; [exact Hfdl|]. split; [exact Hmfs|]. split; [exact Hret'|]. split; [exact Hout|]. split; [exact Hsorted'|]. split; [exact Hnames'|].
split; [| exact Hplk]. split; [exists M; exact HAM' | exact (conj Henv' Hhead')].
Qed.
End c.
End b.
