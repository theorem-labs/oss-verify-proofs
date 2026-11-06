(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the chain proves malloc at __asan::asan_malloc's entry 0x34528 with the trace its caller built (lib/A/Rt/RtDDefs.v amalloc_inner_realizes, cmd_amalloc_inner); the interceptor body 0x58b58 (lib/A/Rt/RtDMallocBody.v) calls it, and cgif's trampoline form tfib_amalloc_realizes at 0x58984 (lib/A/Rt/RtDMallocTramp.v) follows from the body, so every caller is served by this one chain. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0w.v, with its module paths changed, names TfibSyms -> CmdBSyms and its addresses moved to plugin-hostd/fuzz_command's ASan build; tfib_malloc_sec_spec takes In (call_trace ...) (as_universe B) \/ st_nev S < EV_MAX; the walks get tr_admit (tr_admit_call). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AFij AFio AFl4 AFem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDDefs RtDMallocI RtDMallocRun RtDMallocBody RtDMallocTramp.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YA00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_malloc_sec_spec (B : asyms) : Prop :=
forall ly S (W : world tfibsegs) regs mem md n p tr,
ipre B ly S W regs mem md n p tr ->
64513 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In tr (as_universe B) \/ st_nev S < EV_MAX ->
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs PC_asan_malloc regs mem md) (malloc_leaf_w tfibsegs B MALLOC_ASAN_STK ly S W regs mem md n).
Lemma tr_admit_of : forall B S tr, (length tr <= kUnwindMax)%nat -> In tr (as_universe B) \/ st_nev S < EV_MAX -> tr_admit (as_universe B) S tr.
Proof. intros B S tr L [X|X]; [left; exact X | right; split; [exact L | exact X]]. Qed.
Theorem amalloc_inner_of : forall B, CmdBSyms B -> tfib_depot_spec B -> tfib_malloc_sec_spec B -> amalloc_inner_realizes tfibsegs B PC_asan_malloc.
Proof.
intros B TS D1 SEC ly S W regs mem md n p tr HAR Hev Hra Hal Hlo Hhi Hpres Hgp Htp HQT Hn Hp Hpl Hp8 Hpt Hast L1 L30 Hrange Hlive Htr.
assert (PRE : ipre B ly S W regs mem md n p tr) by exact (conj HAR (conj Hev (conj Hra (conj Hal (conj Hlo (conj Hhi (conj Hpres (conj Hgp (conj Htp (conj HQT (conj Hn (conj Hp (conj Hpl (conj Hp8 (conj Hpt (conj Hast (conj L1 L30))))))))))))))))).
destruct (Z_le_gt_dec n 64512) as [Hs|Hs].
- exact (malloc_prim B TS D1 ly S W regs mem md n p tr PRE ltac:(lia) (tr_admit_of B S tr L30 Htr) Hlive).
- exact (SEC ly S W regs mem md n p tr PRE ltac:(lia) Hlive Htr).
Qed.
Theorem tfib_malloc_sec_ok : forall B, CmdBSyms B -> tfib_depot_spec B -> tfib_malloc_sec_spec B.
Proof.
intros B TS D1 ly S W regs mem md n p tr PRE Hr Hlive Htr.
exact (malloc_sec B TS D1 ly S W regs mem md n p tr PRE Hr (tr_admit_of B S tr ltac:(destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L); exact L) Htr) Hlive).
Qed.
Theorem cmd_amalloc_inner : forall B, CmdBSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> amalloc_inner_realizes tfibsegs B PC_asan_malloc.
Proof.
intros B TS HD. exact (amalloc_inner_of B TS (tfib_depot_ok B TS HD) (tfib_malloc_sec_ok B TS (tfib_depot_ok B TS HD))).
Qed.
(* the interceptor's body 0x58b58 *)
Theorem cmd_amalloc_body_closed : forall B, CmdBSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> amalloc_body_realizes tfibsegs B PC_malloc_body DM_PC0.
Proof. intros B TS HD. exact (cmd_amalloc_body B TS (YG0q.AR_laws_ok tfibsegs B) (cmd_amalloc_inner B TS HD)). Qed.
(* cgif's contract at the trampoline, with cgif's name (its users, e.g. lib/A/CmdTFIBLib.v, are unchanged) *)
Theorem tfib_amalloc_realizes : forall B, CmdBSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> amalloc_realizes tfibsegs B.
Proof. intros B TS HD. exact (cmd_amalloc_of_body B TS (YG0q.AR_laws_ok tfibsegs B) (cmd_amalloc_body_closed B TS HD)). Qed.
End a.
