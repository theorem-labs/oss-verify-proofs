(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetup), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* The scheduler's setup in fuzz_grant's entry function LLVMFuzzerTestOneInput on the
   ASan build: slots 0x813b8 .. 0x815c4 (fuzz_grant.c:389-396), from the cut GI_sched0 to
   the head of the frame loop (GI_sched) or, when the frame count is 0, to the free of
   the head-amp table (GI_freeT).

   The phase is proved in five segments, cut at the returns of its calls
   (GrantEntrySchedSetupDefs.v):
   - A  (GrantEntrySchedSetupA.v)  0x813b8 -> 0x81464 | 0x81414: `raw` unusable again,
        the scene's base and width, reac_headamp_tx_arm_scene;
   - B1 (GrantEntrySchedSetupB1.v) 0x81464 -> 0x81494: no period byte left, the call of
        reac_headamp_tx_set_resweep with period 0;
   - B2 (GrantEntrySchedSetupB2.v) 0x81414 -> 0x81494: the period's bytes and
        reac_headamp_tx_set_resweep;
   - C  (GrantEntrySchedSetupC.v)  0x81494 -> 0x8153c: the frame count's bytes,
        `unset_sent` usable and zeroed by __asan_memset;
   - D  (GrantEntrySchedSetupD.v)  0x8153c -> 0x815c4 | 0x817c8: the count modulo 4097,
        the loop's spill slots, and the branch on a count of 0. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
YC1g YC1h YC1i YC81 YC4b GrantFrame YC45 YC85 GrantACjr ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective HeadampTxArmScene GrantEntrySetDefs GrantEntrySchedSetupDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantSlotPlan SlotNeeds_c HeadampSched Seg_sched_setup Seg_sched_lib SegSetModel
reac_headamp_tx_set_resweep_c reac_headamp_tx_arm_scene_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
HeadampTxSetResweep GrantEntrySchedSetupA GrantEntrySchedSetupB1 GrantEntrySchedSetupB2
GrantEntrySchedSetupC GrantEntrySchedSetupD.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ARM : theadamp_tx_arm_scene_spec B.
Hypothesis RSW : theadamp_tx_set_resweep_spec B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).

Theorem ge_sched_setup : forall POST,
  ge_from B MT POST (GI_sched B MT) -> ge_from B MT POST (GI_freeT B MT) -> ge_from B MT POST (GI_sched0 B MT).
Proof.
intros POST HN HF.
eapply sch_compose; [ eapply sch_segA | eapply sch_segB1 | eapply sch_segB2 | eapply sch_segC | eapply sch_segD | exact HN | exact HF ].
all: eassumption.
Qed.

End c.
End b.
End a.
