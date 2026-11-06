(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextReplayDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/NextReplayDefs.v, with its numbers changed; 12 of its 67 lines of code are new or changed and 35 lines of the source are left out. *)
(* The cut of reac_headamp_tx_next's walk (fuzz_grant.asan 0x850cc) at the emit block EMIT
   (0x854a0): the replay scan has found the carried cell j, has stored the cursor j + 1, and
   branches here to write the record into the caller's three bytes and to update the
   table's cursor, wait or width, and silence fields, then returns 1. The scan's walk applies
   it; NextEmit.v proves it. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
NextArith HeadampTxEffective HeadampTxNext NextReplayDefs.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* The emit block's first slot, 0x854a0, as an offset from the listing's base. *)
Definition EMIT : Z := AF_reac_headamp_tx_next + 0x3d4.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* The registers the emit block reads, as the replay scan leaves them at EMIT with j the
   cell it found: s0 is j mod 3 (the parameter), s3 the channel tb T 436 + j / 3, t4 three
   times the replay width, t1, t2 and t3 the shadow bytes' addresses of the width (437), the
   wait (444) and the cursor (440), a4, a5, a6 and t6 the addresses of the wait, the width,
   the cursor and the set array (144). *)
Definition nx_at_emit (regs regsj : bvmap 5 word) (tx chp parp valp : Z) (T : list byte) (j : Z)
  : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NEXT_STK) /\
  getr regsj 5 = w64 SB_NX /\
  getr regsj 6 = w64 (SHADOW_OFF + (tx + 437) / 8) /\
  getr regsj 7 = w64 (SHADOW_OFF + (tx + 444) / 8) /\
  getr regsj 28 = w64 (SHADOW_OFF + (tx + 440) / 8) /\
  getr regsj 8 = w64 (j mod 3) /\ getr regsj 19 = w64 (tb T 436 + j / 3) /\
  getr regsj 10 = w64 tx /\ getr regsj 11 = w64 chp /\
  getr regsj 12 = w64 parp /\ getr regsj 13 = w64 valp /\
  getr regsj 14 = w64 (tx + 444) /\ getr regsj 15 = w64 (tx + 437) /\
  getr regsj 16 = w64 (tx + 440) /\ getr regsj 29 = w64 (3 * tb T 437) /\
  getr regsj 31 = w64 (tx + 144).

Section h.
Variable B : asyms.

(* The memory holds the table with the cursor stored (set4 T 440 (j + 1)); the call's answer
   is Pau Aliagas's emit_res for cell j (lib/Prog/NextModel.v). *)
Definition nx_emit_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T : list byte) (j : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 (j + 1))) ->
  0 <= j < 3 * tb T 437 ->
  carried (set4 T 440 (j + 1)) (tb T 436) (tb T 448) j = true ->
  next_model T tx = emit_res (set4 T 440 (j + 1)) tx (tb T 436 + j / 3) (j mod 3) j (3 * tb T 437) ->
  nx_at_emit regs regsj tx chp parp valp T j ->
  SRr SEGS W (cfg_at SEGS (BASE + EMIT) regsj memj mdj)
    (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

End h.
End f.
End d.
