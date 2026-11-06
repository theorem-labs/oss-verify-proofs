(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PvB_NA.v, with its module paths and module names changed; 22 of its 51 lines of code are new or changed and 930 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): the bound on the starved reading's injection count `took` that
   the walk of check_reject_clean_starved (kit lib/B/Prog/CrsKitBp.v) passes to its segment lanes as HB_took.
   DONOR (rule 24, reuse): the A' lemma lib/A/Prog/CrsBoundAp.v blob 3dc975588195 (a working branch
   preset-tree-at-2026-10-29T18-57-49Z.tsv (sha256 820bf75b530f; internal record)), restated over the B' kit: crs_ncalls_le_B is the same pure lemma, crs_took_le_B reads crs_pre_B.
   rule 24: proves no function (kind: pure model lemma over the reader grammar, PjGrammar.ncalls; image-free).
   ROUTE. crs_pre_B gives `0 <= took <= ck_ncalls tb` (ck_ncalls x = Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod
   x), lib/A/PRH_FnCheck.v blob 9ecd8eb167c6) and `size <= 3 * 2 ^ 20` (size = length tb). PjGrammar.G7_4
   (lib/Spec/PjGrammar.v blob 5d4026de2876) bounds the reader's calls on ANY strtod model and ANY refusal list by the
   input length: calls <= 2 * length + 2. So took <= 2 * 3 * 2 ^ 20 + 2 < 2 ^ 28.
   Numerals: 2, 3 * 2 ^ 20 and 2 ^ 28 are DERIVED (G7_4's factor, the kit's size bound, the bound passed on). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the reader's calls on any strtod model are at most 2 * length + 2 (PjGrammar.G7_4 at the empty refusal list) *)
Lemma crs_ncalls_le_B : forall x, ck_ncalls x <= 2 * Z.of_nat (length x) + 2.
Proof.
intros x. unfold ck_ncalls, PjGrammar.ncalls.
pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod x []) as G. lia.
Qed.

(* the kit's Sections, as CrsKitBp.v states them *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* HB_took: the starved reading's took, at most 2 * 3 MiB + 2 < 2 ^ 28. The proof splits crs_pre_B's conjunctions
   and takes `cSize_B C <= 3 * 2 ^ 20` and `0 <= cb_took C <= ck_ncalls (cb_tb C)` by type, not by position, so a
   premise added to crs_pre_B leaves it unchanged. *)
Lemma crs_took_le_B : forall CTX0 C, crs_pre_B B ARx CTX0 C -> cb_took C <= 2 ^ 28.
Proof.
intros CTX0 C H. unfold crs_pre_B in H.
repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
pose proof (crs_ncalls_le_B (cb_tb C)) as G.
unfold cSize_B in *. lia.
Qed.

End f.
End d.
