(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextReplayDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* The two cuts of reac_headamp_tx_next's walk (fuzz_grant.asan 0x850cc) from the replay
   scan's head onwards, as statements: the machine at the scan's head LOOPR (0x852e4) and at
   the re-assert tail RSWP (0x85374), and what each must reach (tnext_post). NextReplay.v
   proves both; HeadampTxNext.v applies them. *)
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
NextArith HeadampTxEffective HeadampTxNext.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* gp, tp and s9..s11: the function never writes them, and the prologue does not save them. *)
Definition nx_keep_gp (regs regsj : bvmap 5 word) : Prop :=
  forall r : bv 5, In r [3; 4; 25; 26; 27]%bv -> getr regsj r = getr regs r.

(* The registers at the replay scan's head LOOPR (0x852e4), with j the cursor. *)
Definition nx_at_loopr (regs regsj : bvmap 5 word) (tx chp parp valp : Z) (T : list byte) (j : Z)
  : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NEXT_STK) /\
  getr regsj 5 = w64 SB_NX /\
  getr regsj 6 = w64 (SHADOW_OFF + (tx + 437) / 8) /\
  getr regsj 7 = w64 (SHADOW_OFF + (tx + 444) / 8) /\
  getr regsj 28 = w64 (SHADOW_OFF + (tx + 440) / 8) /\
  getr regsj 8 = w64 j /\ getr regsj 9 = w64 (tb T 436) /\
  getr regsj 10 = w64 tx /\ getr regsj 11 = w64 chp /\
  getr regsj 12 = w64 parp /\ getr regsj 13 = w64 valp /\
  getr regsj 14 = w64 (tx + 444) /\ getr regsj 15 = w64 (tx + 437) /\
  getr regsj 16 = w64 (tx + 440) /\
  getr regsj 18 = w64 (tb T 448) /\ getr regsj 20 = w64 1431655766 /\
  getr regsj 21 = w64 47 /\ getr regsj 29 = w64 (3 * tb T 437) /\
  getr regsj 30 = w64 3 /\ getr regsj 31 = w64 (tx + 144).

(* The registers at the re-assert tail RSWP (0x85374). a1..a3 are dead there (the tail writes
   each before it reads it), and on the scan's way in a1 holds a shadow byte; the three bytes'
   addresses stay in the signature for the callers. *)
Definition nx_at_rswp (regs regsj : bvmap 5 word) (tx chp parp valp : Z) : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NEXT_STK) /\
  getr regsj 5 = w64 SB_NX /\
  getr regsj 6 = w64 (SHADOW_OFF + (tx + 437) / 8) /\
  getr regsj 10 = w64 tx /\
  getr regsj 15 = w64 (tx + 437).

Section h.
Variable B : asyms.

Definition nx_resweep_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T Tj : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals Tj) ->
  length Tj = 460%nat -> I1 Tj -> tb Tj 437 = 0 ->
  (forall l, 0 <= l < 432 -> tb Tj l = tb T l) ->
  next_model T tx = resweep Tj ->
  nx_at_rswp regs regsj tx chp parp valp ->
  SRr SEGS W (cfg_at SEGS (BASE + RSWP) regsj memj mdj)
    (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

Definition nx_rloop_spec : Prop :=
  forall (n : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T : list byte) (j : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  tb T 437 <> 0 -> 0 <= j -> s32 T 440 <= j < 3 * tb T 437 -> Z.of_nat n = 3 * tb T 437 - j ->
  next_model T tx = walk (set4 T 440 j) tx (tb T 436) (tb T 448) (3 * tb T 437) j n ->
  nx_at_loopr regs regsj tx chp parp valp T j ->
  SRr SEGS W (cfg_at SEGS (BASE + LOOPR) regsj memj mdj)
    (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

End h.
End f.
End d.
