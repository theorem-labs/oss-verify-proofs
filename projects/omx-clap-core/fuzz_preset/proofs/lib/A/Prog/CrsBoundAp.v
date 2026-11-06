(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 671 of its 740 lines of code are new or changed and 859 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/CrsKitAp.v; 15 of its 55 lines of code are new or changed and 700 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 pins): the bound on the starved reading's injection count `took` that the walk of
   check_reject_clean_starved (kit lib/A/Prog/CrsKitAp.v) passes to its segment lanes as HB_took.
   rule 24: proves no function (kind: pure model lemma over the reader grammar, PjGrammar.ncalls; image-free).
   ROUTE. crs_pre gives `0 <= took <= ck_ncalls tb` (ck_ncalls x = Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod x),
   lib/A/PRH_FnCheck.v:181) and `size <= 3 * 2 ^ 20` (size = length tb). PjGrammar.G7_4 (lib/Spec/PjGrammar.v:1370)
   bounds the reader's calls on ANY strtod model and ANY refusal list by the input length: calls <= 2 * length + 2.
   So took <= 2 * 3 * 2 ^ 20 + 2 < 2 ^ 28. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_WalkEnv PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import CrsKitAp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the reader's calls on any strtod model are at most 2 * length + 2 (PjGrammar.G7_4 at the empty refusal list) *)
Lemma crs_ncalls_le : forall x, ck_ncalls x <= 2 * Z.of_nat (length x) + 2.
Proof.
intros x. unfold ck_ncalls, PjGrammar.ncalls.
pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod x []) as G. lia.
Qed.

(* the kit's Sections, as CrsKitAp.v states them *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* HB_took: the starved reading's took, at most 2 * 3 MiB + 2 < 2 ^ 28. The proof splits crs_pre's conjunctions and
   takes `cSize C <= 3 * 2 ^ 20` and `0 <= c_took C <= ck_ncalls (c_tb C)` by type, not by position, so a premise
   added to crs_pre (kit v2) leaves it unchanged. *)
Lemma crs_took_le : forall CTX0 C, crs_pre B ARx CTX0 C -> c_took C <= 2 ^ 28.
Proof.
intros CTX0 C H. unfold crs_pre in H.
repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
pose proof (crs_ncalls_le (c_tb C)) as G.
unfold cSize in *. lia.
Qed.

End f.
End d.
Print Assumptions crs_took_le.
Set Printing Implicit.
About crs_took_le.
