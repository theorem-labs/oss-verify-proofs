(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1m.v (origin/ossv/recipes c8557374ad2e), with its module paths changed, names TfibSyms -> PcapSyms. ADAPTED to pcap's program contract (porter a Theorem Labs lane ruling 1): the donor's LIBC (tfib_lib_contract_x of cgif's lib/A/ACfn.v) is lib/A/Prog/PcapEntry.v's tfib_lib_contract_x (a working branch 8fe833c8d36) at fuzz_pcap's ASan segments, read-only window PCAP_RLO / PCAP_RHI (PcapRelro.v), A_LLVMF / RA_LLVMF / A_EMPTY / LLVMF_STK, the harness globals G_HARNESS, and the source record pcap_KS (lib/A/Stdio/PSourceK.v); the sink head SK is passed explicitly and pcap_head (lib/A/AD1u.v) ties it to pcap's measured ofl_head. The donor's proof is kept: lib_site_x's pre (FINV over the source, lib/A/AD1u.v) gives the contract's pre (asource_none pcap_KS = FINV's last two conjuncts; the head law from pcap_head; the inert fd-names conjunct from lib_site_x's own premise, as cgif's asink_none gives it, ACfn.v:42), and the contract's post gives lib_site_x's continuation (ajournal_gx unchanged; the fd-names conjunct PcapEntry.v post, cgif ACfn.v:55; FINV' from asrc_meta_inv / asource_none). RO_IN is or_intror: in_ro_tfa (lib/A/ACeg.v:46) already names PCAP_RLO / PCAP_RHI. The output shape is AgreePcap.ag_out_shape, the one PcapEntry states LIBK at. rule 24: no function proved anew. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YM02 YP0m YP09 YI00 YI16 YK04 YA0i YA0n
YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m ACeg AD1t AD20 AD1v AD2h AD2f AD1w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile AD1u LinkLoopKept.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
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
Variable P : YK11.FPState -> Prop.
Hypothesis LIBC : tfib_lib_contract_xP SK tfibsegs PCAP_RLO PCAP_RHI A_LLVMF RA_LLVMF A_EMPTY LLVMF_STK G_HARNESS B MT XM_LIB XN_LIB link_amf LA_NUL P.
Lemma layout_of_AR' : forall ly S W mem md, AR tfibsegs B ly S W mem md -> layout_ok ly.
Proof. intros ly S W mem md H. exact (am_layout _ _ _ _ (proj1 H)). Qed.
Theorem tfib_lib_site_x : lib_site_x (LS:=ZTraceSpec.checksum_shape) B P.
Proof.
intros ly S W regs mem md p n pl T K HPRE R10 R11 Hpn Hlen Hpl Hfr Hev Hlive Hro HFI HTin HpnT Hwild Hfree Hnames Hsorted HAI CONT.
pose proof HPRE as (HAR & Hret & Hra & Hgp & Htp & Hal & [Wlo Whi] & [Tlo Thi] & Elo & Ehi & Hpres & Hs0 & Hqt).
pose proof (layout_of_AR' _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
destruct HFI as (HG & Henv & Hnul & _).
apply (LIBC ly S W regs mem md p n pl T K HAI).
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
split; [exact HG|]. split; [exact HTin|]. split; [exact HpnT|]. split; [exact Henv|].
split; [unfold amf_head_law; rewrite pcap_head_eq; reflexivity|].
split; [exact Hnul|].
split; [exact Hnames|]. split; [exact Hsorted|]. split; [apply MT_FREE | exact Hwild].
-
intros l W' c' Hwle HAI' (fx' & ly' & S' & regs' & mem' & md' & k & T' & -> & HPfx & HJ & Hk & HP & Ha0 & HBP & HG' & Henv' & Hnul' & Hfdl & Hnames' & Hmfs & Hret' & Hout & Hsorted' & _ & Hwc & Hplk).
apply (CONT l W' fx' ly' S' regs' mem' md' k T' HPfx Hwle HAI'). unfold lib_post.
split; [exact HJ|]. split; [exact Hk|]. split; [exact HP|]. split; [exact Ha0|]. split; [exact HBP|].
split; [exact Hfdl|]. split; [exact Hmfs|]. split; [exact Hret'|]. split; [exact Hout|]. split; [exact Hsorted'|]. split; [exact Hnames'|].
split; [| split; [exact Hwc | exact Hplk]].
split; [exact HG'|]. split; [exact Henv'|]. split; [exact Hnul'|].
apply ajournal_gx_inner in HJ as (memS & HJ' & _). destruct HJ' as (HAR' & _).
exact (finv_loc_ledger B ARL ly' S' W' mem' md' T' HAR' (amf_blocks_post_incl T T' _ _ HBP HTin)).
Qed.
End c.
End b.
