(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0w.v at 25e3d17bdb50 into libreac/fuzz_knock, with its module paths changed, A/AWalkFw0 imported for A/AB1v and its addresses moved to libreac/fuzz_knock's ASan build; its statements and proofs changed for fuzz_knock's depot model, whose StackDepot blocks are mapped at the first Put: the StackDepot Put stated through AD3j (imported for AFem) over the layout relation layout_grow; fuzz_knock derived its lib/AU/YF0w.v from that file, with A -> AU module names and its addresses moved to its ASan+UBSan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/AU/YF0w.v at 88154566652a (donor image sha256 f834165f5002), with its module paths changed, B/YB1v imported for AU/AWalkFw0, names TfibSyms -> WireSyms and its addresses moved to reac-repacer/fuzz_wire's ASan+UBSan build; its other text is also in proofs/libreac/fuzz_grant/lib/B/YF0w.v at 4f87de75d67. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YFij YFio YFl4 YD3j.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YA00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_malloc_sec_spec (B : asyms) : Prop :=
forall ly S (W : world tfibsegs) regs mem md n ch,
acall_pre tfibsegs B ly S W regs mem md ch ->
getr regs 10 = w64 n -> 64513 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In (call_trace ly 0x52334 regs ch) (as_universe B) ->
amreal tfibsegs (malloc n (call_trace ly 0x52334 regs ch) S) W (cfg_at tfibsegs 0x52098 regs mem md) (malloc_leaf tfibsegs B ly S W regs mem md n).
Theorem amalloc_realizes_of : forall B, WireSyms B -> tfib_unwind_spec -> YD3j.tfib_depot_put_any_spec layout_grow depot_ok as_const_g2f B -> tfib_malloc_sec_spec B -> amalloc_realizes tfibsegs B.
Proof.
intros B TS U1 D1 SEC ly S W regs mem md n ch PRE Hn Hrange Hlive Htr.
rewrite (ts_code B TS) in Htr |- *. cbn [pc_malloc_ra0 pc_wrap_malloc Tfib_code] in Htr |- *.
destruct (Z_le_gt_dec n 64512) as [Hp|Hs].
- exact (malloc_prim B TS U1 D1 ly S W regs mem md n ch PRE Hn ltac:(lia) Htr Hlive).
- exact (SEC ly S W regs mem md n ch PRE Hn ltac:(lia) Hlive Htr).
Qed.
Theorem amalloc_realizes_sec : forall B, WireSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> tfib_malloc_sec_spec B -> amalloc_realizes tfibsegs B.
Proof.
intros B TS HD SEC. exact (amalloc_realizes_of B TS tfib_unwind_ok (YD3j.tfib_depot_put_any layout_grow kd_inst_grow_NB kd_inst_grow_SB kd_inst_grow_trans depot_ok kd_inst_depot_ok_pre kd_inst_depot_ok_post as_const_g2f as_const_g2f_def B TS HD) SEC).
Qed.
Theorem tfib_malloc_sec_ok : forall B, WireSyms B -> tfib_unwind_spec -> YD3j.tfib_depot_put_any_spec layout_grow depot_ok as_const_g2f B -> tfib_malloc_sec_spec B.
Proof.
intros B TS U1 D1 ly S W regs mem md n ch PRE Hn Hr Hlive Htr. exact (malloc_sec B TS U1 D1 ly S W regs mem md n ch PRE Hn Hr Htr Hlive).
Qed.
Theorem tfib_amalloc_realizes : forall B, WireSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> amalloc_realizes tfibsegs B.
Proof.
intros B TS HD. exact (amalloc_realizes_sec B TS HD (tfib_malloc_sec_ok B TS tfib_unwind_ok (YD3j.tfib_depot_put_any layout_grow kd_inst_grow_NB kd_inst_grow_SB kd_inst_grow_trans depot_ok kd_inst_depot_ok_pre kd_inst_depot_ok_post as_const_g2f as_const_g2f_def B TS HD))).
Qed.
End a.
