(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the outer walk of fuzz_reply's list_drop on the ASan image (a Theorem Labs lane W1,
   step 4), in the form of lib/A/W_list_find.v pb_list_find (entry, cut, splice, epilogue, return).  The walk is
   ARx-generic at the caller-context free rule (pb_list_drop_cx_x, route (b), step 3; the template is
   lib/A/W_check_bounded.v); the strong-rule forms pb_list_drop_x / pb_list_drop_ro_x and the context-rule
   G-generic form pb_list_drop_ro_cx_x are corollaries of it, and the AR theorems pb_list_drop and pb_list_drop_ro
   are re-derived from them at ARx := ARi0, PST := []. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_drop_top.v; 12 of its 59 lines of code are new or changed and 839 lines of the source are left out. *)
(* Satisfiability at the real image A of the R contract text of W_contract_xR_g3.v, at R := wle' SEGS RZ_cf: the lemma
   derives the R form from the existing strict walk, under that walk's own Section hypotheses. The import block is the
   walk file's (W_list_drop_top.v), so each hypothesis reads as there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_list_drop.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_list_drop_top.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.

(* pb_list_drop_xR_sat: ldrop_spec_xR at R := wle' SEGS RZ_cf, from W_list_drop_top.pb_list_drop_x by ldrop_spec_xR_of_x
   and YA0nH.wle_wle'. The Section hypotheses are pb_list_drop_x's own (W_list_drop_top.v Sections a / b / d), unchanged. *)
Section sat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis GRT : gx_rt B G.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule_x SEGS B PST ARx MT RP.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis ROMS : forall a, in_rom SEGS a ->
(Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G a.
Theorem pb_list_drop_xR_sat : ldrop_spec_xR B PST ARx (wle' SEGS YGcfRehidePost.RZ_cf) MT RP G A_list_dropP.
Proof.
apply ldrop_spec_xR_of_x; [exact (wle_wle' SEGS YGcfRehidePost.RZ_cf) |].
eapply W_list_drop_top.pb_list_drop_x; eassumption.
Qed.
End sat.
