(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) segment of the reac_ctrl_parse 0x82774 walk, in the shape of lib/A/Prog/CtrlParseTail.v at a working branch 603e40683a4 (image A 0x82000), over image B's listing and walk layer (lib/B/Prog), with image B's addresses and objects; image B's extra UBSan guards are decided by the engine from the atom facts. Source blob 820f6e605fa6 (lib/A/Prog/CtrlParseTail.v at a working branch 603e40683a4; the same blob at 7e98c198edd). *)
(* reac_ctrl_parse, the walk from cut B (0x82970) to cut J: the five classes of frames (pz_cases), each
   walked in CtrlParseTail1..5.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import CtrlParseLib KindOfLink1 GrantRo ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import CtrlParseCut CtrlParseTail1 CtrlParseTail2 CtrlParseTail3 CtrlParseTail4 CtrlParseTail5.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Lemma pz_segC : forall B G, pz_rt B G -> forall c, pz_ok B c -> pz_cutJ_spec B c -> pz_cutB_spec B c.
Proof.
intros B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc.
destruct (pz_cases (cx_fr c)) as [P|[P|[P|[P|P]]]].
- exact (pz_tail1 B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
- exact (pz_tail2 B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
- exact (pz_tail3 B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
- exact (pz_tail4 B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
- exact (pz_tail5 B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
Qed.
End d.
End b.
