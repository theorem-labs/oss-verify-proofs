(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySweepS3.v; 27 of its 80 lines of code are new or changed and 259 lines of the source are left out. *)
(* The SWEEP phase of fuzz_grant's entry function: its eight segments composed.
   `ge_sweep` is what the phase before it (the admission tests) applies. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo GrantFrame GrantEntryDefs GrantBuildSweep CheckGroupa HeadampDefault CtrlIdentityPollBlock GrantEntrySweepDefs GrantEntrySweepS1 GrantEntrySweepS1b GrantEntrySweepS1s GrantEntrySweepS2 GrantEntrySweepS3 GrantEntrySweepS3a GrantEntrySweepS3b GrantEntrySweepS4.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation GF := (fun GI => ge_from B MT (ge_post B MT) GI).

(* What the segments take beyond the runtime: the image's read-only tables, which
   the image instance gives (GrantClose), and the callees' contracts. *)
Variable GL : list (Z * Z).
Hypothesis HEAD_ACK_bytes : forall (H : word -> bool) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 4)) HEAD_ACK34z.
Hypothesis HEAD_MARK_bytes : forall (H : word -> bool) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 5)) HEAD_MARK34z.
Hypothesis HEAD_ACK_rng : IMG_LO + 64 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 34 + 64 <= IMG_HI.
Hypothesis HEAD_MARK_rng : IMG_LO + 64 <= VAL (A_OBJ 5) /\ VAL (A_OBJ 5) + 34 + 64 <= IMG_HI.
Hypothesis HEADS_marked : globs_marked SEGS B GL.
Hypothesis HEAD_ACK_glob : In (VAL (A_OBJ 4), 34) GL.
Hypothesis HEAD_MARK_glob : In (VAL (A_OBJ 5), 34) GL.
Hypothesis TBSW : treac_grant_build_sweep_spec B.
Hypothesis THD : treac_headamp_default_spec B.
Hypothesis TCG : tcheck_groupa_spec B.
Hypothesis TIPB : tctrl_identity_poll_block_spec B GL.
Hypothesis GROUPB_glob : In (VAL (A_OBJ 19), 204) GL.
Hypothesis GROUPB_lo : IMG_LO + 64 <= VAL (A_OBJ 19).
Hypothesis GROUPB_hi : VAL (A_OBJ 19) + 204 + 64 <= IMG_HI.
Hypothesis GROUPB_bytes : forall (H : word -> bool) (mem : word -> option byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 19)) GBallz.
Hypothesis POLL_glob : In (VAL (A_OBJ 6), 18) GL.
Hypothesis POLL_lo : IMG_LO + 64 <= VAL (A_OBJ 6).
Hypothesis POLL_hi : VAL (A_OBJ 6) + 18 + 64 <= IMG_HI.
Hypothesis POLL_bytes : forall (H : word -> bool) (mem : word -> option byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 6)) POLLz.

Theorem ge_sweep : GSW_RT B MT -> GF (GI_raw B MT) -> GF (GI_sweep B MT).
Proof.
intros HRT HN.
assert (HF : GF (GIS_free1 B MT)) by (eapply gsw_seg_free1; eassumption).
assert (HB : GF (GIS_gbhd B MT)) by (eapply (gsw_seg_gb B MT GL); eassumption).
assert (HG1 : GF (GIS_ga1 B MT)) by (eapply gsw_seg_ga1; eassumption).
assert (HG0 : GF (GIS_ga0 B MT)) by (eapply gsw_seg_ga0; eassumption).
assert (HX : GF (GIS_rowex B MT)) by (eapply (gsw_seg_heads B MT GL); eassumption).
assert (HH : GF (GIS_rowhd B MT)) by (eapply gsw_seg_rows; eassumption).
assert (HM : GF (GIS_mal B MT)) by (eapply gsw_seg_mal; eassumption).
eapply gsw_seg_sweep; eassumption.
Qed.

End c.
End b.
End a.
