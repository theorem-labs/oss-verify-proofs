(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextReplayDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/NextReplayDefs.v; 12 of its 61 lines of code are new or changed and 41 lines of the source are left out. *)
(* The cut of reac_headamp_tx_next's walk (fuzz_grant.asan 0x850cc) at the re-arm block
   REARM (0x85404): the re-assert tail has ticked the silence counter (456) and found the
   period reached, and the block re-arms the remembered scene (HeadampI1.rearm). The tail's
   walk (NextReplayTail.v) applies it; NextRearm.v proves it. *)
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

(* The re-arm block's first slot, 0x85404, as an offset from the listing's base. *)
Definition REARM : Z := AF_reac_headamp_tx_next + 0x338.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* The registers at REARM, as the tail leaves them: a1 is the silence counter's address and
   a4 its shadow byte's address (the counter it just stored; its granule is only partly
   usable, so the shadow check's slow path reads a1), a2 the remembered scene width it
   read (not 0). *)
Definition nx_at_rearm (regs regsj : bvmap 5 word) (tx w : Z) : Prop :=
  nx_keep_gp regs regsj /\
  getr regsj 2 = w64 (spZ regs - NEXT_STK) /\
  getr regsj 5 = w64 SB_NX /\
  getr regsj 6 = w64 (SHADOW_OFF + (tx + 437) / 8) /\
  getr regsj 10 = w64 tx /\
  getr regsj 11 = w64 (tx + 456) /\
  getr regsj 12 = w64 w /\
  getr regsj 14 = w64 (SHADOW_OFF + (tx + 456) / 8).

Section h.
Variable B : asyms.

(* Tj is the table at the re-assert tail's entry; the memory holds it with the silence
   counter ticked, and the call's answer is the re-armed table, silently. *)
Definition nx_rearm_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj
    (tx chp parp valp : Z) (T Tj : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 Tj 456 (u32 Tj 456 + 1))) ->
  length Tj = 460%nat ->
  next_model T tx = silent (rearm Tj) ->
  nx_at_rearm regs regsj tx (tb Tj 450) ->
  SRr SEGS W (cfg_at SEGS (BASE + REARM) regsj memj mdj)
    (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

End h.
End f.
End d.
