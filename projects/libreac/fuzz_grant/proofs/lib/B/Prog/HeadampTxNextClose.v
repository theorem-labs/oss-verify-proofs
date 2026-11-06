(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the composition of reac_headamp_tx_next on fuzz_grant.asan (HeadampTxNextClose), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampTxNextClose.v at a working branch af735a950e2 (blob 41fc606328e; the walk was ported from blob bcb968a739d at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; the composition takes reac_headamp_tx_effective's contract, which image B calls, and destructs IMG_NEXT_DIV3 from hyps_reac_headamp_tx_next *)
(* reac_headamp_tx_next (image B fuzz_grant.asan-ubsan 0x85efc): the code meets the contract
   GrantBContracts.v states (tb_reac_headamp_tx_next_spec), so `walk_reac_headamp_tx_next` holds. The walk is cut at six
   slots, each segment proved in its own file:
     NextEntry.v        the first slot to the edge scan's head, or the idle return (nx_walk);
     NextEdge.v         the edge scan over the 144 cells, by induction (nx_dloop);
     NextAfter.v        the after-scan: wait, done, or on to the replay scan (nx_after);
     NextReplayScan.v   the replay scan over the cursor, by induction (pb_nx_rloop);
     NextEmit.v         the emit block of the replay scan, which CALLS reac_headamp_tx_effective
                        at 0x863dc (pb_nx_emit); image A inlines that leaf, so this is the one
                        segment with no image-A text behind it;
     NextReplayTail.v,
     NextRearm.v        the re-assert tail and its re-arm (pb_nx_resweep, pb_nx_rearm).
   The only program function it calls is reac_headamp_tx_effective, whose contract the walk takes,
   as walk_reac_headamp_tx_next says. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts HeadampTxNext.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
NextEntry NextEdge NextAfter NextReplayScan NextEmit NextReplayTail NextRearm.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).

Section h.
Variable B : asyms.

Theorem pb_reac_headamp_tx_next : walk_reac_headamp_tx_next B.
Proof.
  unfold walk_reac_headamp_tx_next. intros HYPS EFF.
  destruct HYPS as [LAWS [TL DIV3]].
  pose proof (pb_nx_rearm B LAWS) as RA. try specialize (RA TL).
  pose proof (pb_nx_resweep B LAWS) as RSW. try specialize (RSW TL). specialize (RSW RA).
  pose proof (pb_nx_emit B LAWS) as EM. try specialize (EM TL). specialize (EM EFF).
  pose proof (pb_nx_rloop B LAWS) as RLP. try specialize (RLP TL). specialize (RLP EM). specialize (RLP RSW).
  pose proof (nx_after B LAWS) as AF. try specialize (AF TL). specialize (AF RLP). specialize (AF RSW).
  pose proof (nx_dloop B LAWS) as DL. try specialize (DL TL). specialize (DL AF).
  pose proof (nx_walk B LAWS) as WK. try specialize (WK TL). specialize (WK DIV3).
  exact (WK DL AF).
Qed.

End h.
End f.
End d.
