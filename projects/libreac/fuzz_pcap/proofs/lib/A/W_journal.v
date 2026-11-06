(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the journal of fuzz_reply's ASan program walks.  It is the donor's
   journal (Reusable/YCbq.v:349 ajournal) with two extensions the donor's programs never needed, and the
   run chain of fuzz_reply's Reusable/YC80.v (file sha256 594ab792bba6; donor not released) restated over it. *)
(* Modified by Theorem Labs, 2026-10: REMAPPED COPY of proofs/plugin-hostd/fuzz_reply/lib/A/W_journal.v at a working branch 6328acea202, blob ecd9547e32fd948d46d4c3a57b60ed540c0c6b0f (NOT that branch's newer commit 134bda805a1, whose allocator rules gained a 'present bytes stay present' conjunct). Renames: module paths OSSVerify.Proofs.plugin_hostd.fuzz_reply -> OSSVerify.Proofs.libreac.fuzz_pcap in every import; imports Reusable.YP0b -> A.Prog.PaTable, Reusable.YP0a -> A.Prog.PaSym (source line 36, moved to their own import line after YCbn), Reusable.YP0d -> A.Prog.PaRun, Reusable.YP0c -> A.Prog.PaShadow, Reusable.YC80 -> A.Prog.PaJournal (source line 42, YC5d kept from Reusable on the next line), A.W_syms / A.W_kit -> A.Prog.PcapSyms / PcapPa / PcapPaLib (source line 43): fuzz_pcap holds the same cgif texts under these names; the listing's symbol type wsym -> psym at source lines 646, 650, 653 (Section g). Kept, with why: Sections a and b (the G / XO journal: inG, gagree, gx_ok, ajournal_g, ajournal_gx, ajournal_gx_nil / pack / init, awr_ok_x, ajournal_gx_exec, G_mono, ajournal_sub_g, ajournal_gx_sub), which fuzz_pcap's entry contract states; Sections e and g (the run chain over ajournal_gx, source lines 521-655: SRr_*_AJX, paj_run_x, paj_run_to_x), because the harness's own runs store g_file / g_file_len (0x80930, 0x80938, 0x80970). Left out: Section h (source lines 657-789, fuzz_reply's live-state allocator site rules; fuzz_pcap's walks use cgif's amalloc04_rule / afree04_rule / afree_null04_rule, Reusable/YC5d.v) and the header comment that announced it (source lines 24-27). No proof text changed. *)
(* (G) WRITES TO THE PROGRAM'S OWN GLOBALS.  The donor's journal keeps every image byte outside the
       allocator's statics and errno unchanged (YCbq.v:361), and its runner admits a write only to an
       awr_byte (YCbq.v:459-463: the frame, a heap block of FP, a block allocated during the call, an own
       fake frame).  A fuzz_reply function writes g_s, g_src, g_out, ...  `ajournal_g G` is the donor's
       journal relative to a START MEMORY that agrees with the true start memory outside the global
       ranges G: so it says exactly "every byte the donor's journal keeps is kept, except the bytes of G".
       G is NOT part of as_owned_static, so its bytes are not aowned (YG0d.v:474-475 with gx_ok below) and
       AR_frame_law (YG0d.v:439-446) keeps AR across a write to G unchanged: no new law of the instance.
   (XO) WRITES THROUGH A POINTER INTO THE CALLER'S FRAME (out-parameters).  The callee's journal window is
       extended upward by XO bytes, [sp - STK, sp + XO), and only the out cells OUT of [sp, sp + XO) may
       change (the out clause of ajournal_gx, lib/A/W_journalG.v).
   At G = [], XO = 0, OUT = [] the journal is the donor's: ajournal_gx_nil.
   A walk names ONE journal, `ajournal_gx G XO OUT`, takes RUN := paj_run_x B LAWS G HG XO OUT and
   RUNTO := paj_run_to_x ..., and proves the run's write obligation `awr_ok_x` (for a walk whose runs
   write no global and no out cell: `apply awr_ok_x_of0; awr_ok_tac`).  At a runtime call site it opens
   the journal (`destruct HJ as (HSTK & HXO & (memS & HJi & HAG) & HOUT)`), applies the donor's site
   lemma (aj_*_at, or a site rule below) to the inner journal HJi at (STK + XO, sp0 + XO), and closes it
   again with ajournal_gx_pack. *)
(* Modified by Theorem Labs, 2026-10: everything but Section g (the paj_run_x / paj_run_to_x instances at the listing,
   which need PcapSyms / PcapPa / PcapPaLib) MOVED unchanged to the image-free lib/A/W_journalG.v (a Theorem Labs lane's
   statement / walk rule; a Theorem Labs lane's measurement); this file Requires Export it, so its users see no
   change, and lib/B Requires W_journalG instead. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSyms PcapPa PcapPaLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Export W_journalG.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* The instances at fuzz_reply's listing, beside W_kit's paj_run / paj_run_to.  A walk writes
   `Let RUN := paj_run_x B LAWS G HG XO OUT.` and `Let RUNTO := paj_run_to_x B LAWS G HG XO OUT.`; the GUIDE's
   tactics (paj_run_tok, paj_run_to_tok, psrr_branch_tok) take them unchanged. *)
Section g.
Context {L : ptable psym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Definition paj_run_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_pi_tok_AJX psym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
Definition paj_run_to_x (G : list (Z * Z)) (HG : gx_ok pa_segs B G) (XO : Z) (OUT : list (Z * Z)) :=
SRr_run_to_pi_tok_AJX psym pa_segs B LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq G HG XO OUT.
End g.

End a.
