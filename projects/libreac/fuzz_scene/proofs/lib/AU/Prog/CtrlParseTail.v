(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from cgif's lib/A/ACgq.v and lib/A/ACk8.v (file header, walk tactic forms) for reac_ctrl_parse of libreac's fuzz_grant. *)
(* reac_ctrl_parse of fuzz_scene's ASan+UBSan build (fuzz_scene.asan-ubsan, sha256
   e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f), the walk from cut B (0x84224) to cut J (0x84448):
   the five classes of frames (pz_cases), each walked in CtrlParseTail1..5.v. Ported from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParseTail.v at 603e40683a4
   (CtrlParseTail.v (sha256 72185ce2d606; internal record), the same at 7e98c198edd) as the asan-ubsan twin of lib/A/Prog/CtrlParseTail.v: the listing modules are
   lib.AU.Prog's and YCbq lib.AU's (MERGE-GATES 6o), Grant* -> Scene*, grant_listing -> scene_listing,
   KindOfLink1 -> P_kind_of_link1, and the contract's names are P_reac_ctrl_parse.v's; the sink head SK is passed
   explicitly to the cut predicates in pz_segC's statement and to the five class lemmas it applies. The join only composes
   segment lemmas: it walks no instruction and refutes no UBSan guard. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow PaJournal SceneSyms SceneList ScenePa ScenePaLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneBase YC81 YC4b YC1g YC1h YC45 YC85 SceneFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_parse CtrlParseLib P_kind_of_link1 SceneRo ACj1 SceneACja.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import CtrlParseCut CtrlParseTail1 CtrlParseTail2 CtrlParseTail3 CtrlParseTail4 CtrlParseTail5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg scene_listing}.
Context {RO : ro_below_ofl (SK := SK) (@pa_segs _ scene_listing PI) (@pa_relro_lo _ scene_listing PI) (@pa_relro_hi _ scene_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Lemma pz_segC : forall B G, pz_rt (SK := SK) B G -> forall c, pz_ok (SK := SK) B c -> pz_cutJ_spec (SK := SK) B c ->
pz_cutB_spec (SK := SK) B c.
Proof.
intros B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc.
destruct (pz_cases (cx_fr c)) as [P|[P|[P|[P|P]]]].
- exact (pz_tail1 (SK := SK) B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
- exact (pz_tail2 (SK := SK) B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
- exact (pz_tail3 (SK := SK) B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
- exact (pz_tail4 (SK := SK) B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
- exact (pz_tail5 (SK := SK) B G RT c Hok HJ E ms md Hcur HS SHOK Hhdr Hbc P).
Qed.
End d.
End b.
