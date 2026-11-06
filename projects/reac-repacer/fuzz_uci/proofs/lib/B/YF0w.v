(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0w.v (donor image sha256 1c29845fe605), with its module paths changed, names TfibSyms -> UciSyms and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/YF0w.v (donor image sha256 fde52226dc48), with its module paths changed, names GrantSyms -> UciSyms and its addresses moved to reac-repacer/fuzz_uci's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YF0p. From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YFij YFio YFl4 YFem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05. From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YA00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_malloc_sec_spec (B : asyms) : Prop :=
forall ly S (W : world tfibsegs) regs mem md n ch,
acall_pre tfibsegs B ly S W regs mem md ch ->
getr regs 10 = w64 n -> 64513 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In (call_trace ly 0x51a24 regs ch) (as_universe B) ->
amreal tfibsegs (malloc n (call_trace ly 0x51a24 regs ch) S) W (cfg_at tfibsegs 0x51788 regs mem md) (malloc_leaf tfibsegs B ly S W regs mem md n).
Theorem amalloc_realizes_of : forall B, UciSyms B -> tfib_unwind_spec -> tfib_depot_spec B -> tfib_malloc_sec_spec B -> amalloc_realizes tfibsegs B.
Proof.
intros B TS U1 D1 SEC ly S W regs mem md n ch PRE Hn Hrange Hlive Htr.
rewrite (ts_code B TS) in Htr |- *. cbn [pc_malloc_ra0 pc_wrap_malloc Tfib_code] in Htr |- *.
destruct (Z_le_gt_dec n 64512) as [Hp|Hs].
- exact (malloc_prim B TS U1 D1 ly S W regs mem md n ch PRE Hn ltac:(lia) Htr Hlive).
- exact (SEC ly S W regs mem md n ch PRE Hn ltac:(lia) Hlive Htr).
Qed.
Theorem amalloc_realizes_sec : forall B, UciSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> tfib_malloc_sec_spec B -> amalloc_realizes tfibsegs B.
Proof.
intros B TS HD SEC. exact (amalloc_realizes_of B TS tfib_unwind_ok (tfib_depot_ok B TS HD) SEC).
Qed.
Theorem tfib_malloc_sec_ok : forall B, UciSyms B -> tfib_unwind_spec -> tfib_depot_spec B -> tfib_malloc_sec_spec B.
Proof.
intros B TS U1 D1 ly S W regs mem md n ch PRE Hn Hr Hlive Htr. exact (malloc_sec B TS U1 D1 ly S W regs mem md n ch PRE Hn Hr Htr Hlive).
Qed.
Theorem tfib_amalloc_realizes : forall B, UciSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> amalloc_realizes tfibsegs B.
Proof.
intros B TS HD. exact (amalloc_realizes_sec B TS HD (tfib_malloc_sec_ok B TS tfib_unwind_ok (tfib_depot_ok B TS HD))).
Qed.
End a.
