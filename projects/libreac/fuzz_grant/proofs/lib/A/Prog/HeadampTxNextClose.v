(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the composition of reac_headamp_tx_next on fuzz_grant.asan (HeadampTxNextClose), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* reac_headamp_tx_next (fuzz_grant.asan 0x850cc): the ASan build's code meets its
   contract theadamp_tx_next_spec (HeadampTxNext.v). The walk is cut at six slots, each
   segment proved in its own file:
     NextEntry.v        the first slot to the edge scan's head, or the idle return (nx_walk);
     NextEdge.v         the edge scan over the 144 cells, by induction (nx_dloop);
     NextAfter.v        the after-scan: wait, done, or on to the replay scan (nx_after);
     NextReplayScan.v   the replay scan over the cursor, by induction (via nx_rloop);
     NextEmit.v         the emit block of the replay scan (pb_nx_emit);
     NextReplayTail.v,
     NextRearm.v        the re-assert tail and its re-arm (via nx_resweep).
   The function calls nothing, so no contract of the runtime or of the library is assumed. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI67.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase YC1h.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import NextArith HeadampTxEffective HeadampTxNext.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import NextEntry NextEdge NextAfter NextReplayDefs NextReplay NextEmitDefs NextEmit.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.

Theorem pb_reac_headamp_tx_next : theadamp_tx_next_spec B.
Proof.
  pose proof (pb_nx_emit B LAWS) as EM. try specialize (EM TL).
  pose proof (nx_resweep B LAWS) as RSW.
  pose proof (nx_rloop B LAWS EM) as RLP.
  pose proof (nx_dloop B LAWS) as DL. try specialize (DL TL).
  pose proof (nx_after B LAWS) as AF. try specialize (AF TL). specialize (AF RLP RSW).
  exact (nx_walk B LAWS TL DL AF).
Qed.

End h.
End f.
End d.
