(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0g YF4h YF4m YF8y YF0f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05 YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition tfx_malloc_sec_spec {imgk : img} (B : asyms) : Prop :=
forall ly S (W : world tfxsegs) regs mem md n ch,
acall_pre tfxsegs B ly S W regs mem md ch ->
getr regs 10 = w64 n -> 64513 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In (call_trace ly (0x533a4 + D_2c4) regs ch) (as_universe B) ->
amreal tfxsegs (malloc n (call_trace ly (0x533a4 + D_2c4) regs ch) S) W (cfg_at tfxsegs (0x53104 + D_2c4) regs mem md) (malloc_leaf tfxsegs B ly S W regs mem md n).
Theorem amalloc_realizes_of {imgk : img} : forall B, TfxSyms B -> tfx_unwind_spec -> tfx_depot_spec B -> tfx_malloc_sec_spec B -> amalloc_realizes tfxsegs B.
Proof.
intros B TS U1 D1 SEC ly S W regs mem md n ch PRE Hn Hrange Hlive Htr.
rewrite (ts_code B TS) in Htr |- *. cbn [pc_malloc_ra0 pc_wrap_malloc Tfx_code] in Htr |- *.
destruct (Z_le_gt_dec n 64512) as [Hp|Hs].
- img_exact (malloc_prim B TS U1 D1 ly S W regs mem md n ch PRE Hn ltac:(img_lia) Htr Hlive).
- img_exact (SEC ly S W regs mem md n ch PRE Hn ltac:(img_lia) Hlive Htr).
Qed.
Theorem amalloc_realizes_sec {imgk : img} : forall B, TfxSyms B -> (forall t, as_dhash B t = tfx_dhash t) -> tfx_malloc_sec_spec B -> amalloc_realizes tfxsegs B.
Proof.
intros B TS HD SEC. img_exact (amalloc_realizes_of B TS tfx_unwind_ok (tfx_depot_ok B TS HD) SEC).
Qed.
Theorem tfx_malloc_sec_ok {imgk : img} : forall B, TfxSyms B -> tfx_unwind_spec -> tfx_depot_spec B -> tfx_malloc_sec_spec B.
Proof.
intros B TS U1 D1 ly S W regs mem md n ch PRE Hn Hr Hlive Htr. img_exact (malloc_sec B TS U1 D1 ly S W regs mem md n ch PRE Hn Hr Htr Hlive).
Qed.
Theorem tfx_amalloc_realizes {imgk : img} : forall B, TfxSyms B -> (forall t, as_dhash B t = tfx_dhash t) -> amalloc_realizes tfxsegs B.
Proof.
intros B TS HD. img_exact (amalloc_realizes_sec B TS HD (tfx_malloc_sec_ok B TS tfx_unwind_ok (tfx_depot_ok B TS HD))).
Qed.
End a.
