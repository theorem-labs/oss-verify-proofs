(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fs.asan-ubsan, UBSan trap mode) walk of parse_value against
   lib/B/FSH_Fn_reader.v parse_value_spec (CTX-free; the text of a working branch 035561e0fd4 = a working branch
   311139dc663: skip_ws_spec's post keeps [sp, ot) but [q, q + 8), parse_value_spec's k = 0 arm
   `q = spZ regs + 8 /\ raZ regs <= q`; both rulings a Theorem Labs lane and after the k = 0 gap report): the
   COMPOSITION, parse_value_holds : parse_value_spec tfibsegs B k (stages: FSW_parse_value.v; decode table:
   FSW_parse_value_tbl.v).
   rule 24 (lane brief (internal path), CONFIRM a Theorem Labs lane): proves function
   parse_value - fuzz_state image B asan-ubsan, entry 0x82fcc, level-indexed k = 0..2, narrow success form. Reuse search
   (run by a Theorem Labs lane, verbatim in the lane brief), the three result lines:
     proof-index: parse_value: 14 named, 35 by address, 0 related, 13 released lemma(s), an earlier delivery 58 named and 794
       name(s) holding it, 17 UNRELEASED working-branch file(s) in the lemma index, 0 UNRELEASED hit(s) on live working heads
     proof-index: parse_value_spec: 0 named, 0 by address, 0 related, 6 released lemma(s), 0 by file name, an earlier delivery 51
       named and 12 name(s) holding it, 2 UNRELEASED working-branch file(s) in the lemma index, 0 UNRELEASED hit(s) on live
       working heads
     proof-index: 0x82fcc: 0 named, 0 by address, 0 related, 0 released lemma(s), 0 by file name, an earlier delivery 0 named and
       0 name(s) holding it, 0 UNRELEASED working-branch file(s) in the lemma index, 105 UNRELEASED hit(s) on live working heads
   Port source (Lookup result): ported from a working branch 75e39a1f41d:proofs/omx-clap-core/fuzz_state/lib/
   B/Prog/{parse_value_disp,PvStr,PvItems,PvJoin,PvStep,PvHolds,ParseUnit}.v (COMPLETE old-form image-B walk of
   parse_value: entry/fake frame/skip_ws call pv_pro + pv_disp, parse_string arm pv_str_ok, parse_items arm pv_items_ok,
   epilogue pv_join + pvs_none, composition parse_value_step / parse_value_holds_b; all Qed, no admit), restated against
   parse_value_spec's frame lemma by lemma, NOT Required, NOT bridged; new-frame shape from image A's walk
   a working branch (ebb53c68f7d .. 00c6d1886e6: lib/A/FSH_parse_value.v pv_grant / pv_resume_sm /
   pv_seg0 / pv_sm / pv_epi / pv_strcall, lib/A/FSW_parse_value_calls.v pvc_objcall), copied and re-measured for B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value_holds.v; 27 of its 62 lines of code are new or changed and 2122 lines of the source are left out. *)
(* fuzz_state image B (fs.asan-ubsan): the reader's closing theorem, the B twin of lib/A/FSW_reader_top.v.

   rule 24: proves no function (kind: segment lemma: the descending-depth composition of parse_value / parse_items
   over their holds; the function-level lookups are the holds lanes').
   parse_value at depth k calls parse_items at depth k only when k <= 1, and parse_items at depth k calls
   parse_value at depth k + 1, so the five specs close by descending depth:
     parse_value 2  (needs no parse_items)
     parse_items 1  <- parse_value 2
     parse_value 1  <- parse_items 1
     parse_items 0  <- parse_value 1
     parse_value 0  <- parse_items 0.
   parse_value_holds B is the theorem lib/B/Prog/FSW_parse_value_holds.v:2300 (a working branch
   e2df2faf212): five reader premises plus the nine runtime facts of the class-0 fake frame, which this Section takes.
   parse_items_holds B is the theorem lib/B/Prog/FSW_parse_items_holds.v:431 (a working branch
   f7399137189): the memset contract in place of FsRt, as A's. No Section hypothesis stands for a holds any more. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_frame FSW_frame3 FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require FSW_parse_value_holds FSW_parse_items_holds.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.
Hypothesis HGROW : @grow_spec fx rc SK tfibsegs B.
Hypothesis HPS : @parse_string_spec fx rc SK tfibsegs B.
(* the one runtime contract parse_items uses (memset), not FsRt whole (a Theorem Labs lane 13:43Z; A's c9df5c4a92e) *)
Hypothesis MS : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
(* the runtime facts of parse_value's class-0 fake frame (a Theorem Labs lane 13:29Z) *)
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis SM0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\ FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Let pv (k : nat) (Hk : (k <= 2)%nat) (HI : (k <= 1)%nat -> @parse_items_spec fx rc SK tfibsegs B k) :
  @parse_value_spec fx rc SK tfibsegs B k :=
  @FSW_parse_value_holds.parse_value_holds fx rc SK B k Hk HSS HSW HPS HI IMG HGUAR HUCELL SM0 errno_low ML SMP ASF FFL.

Lemma reader_pv2 : @parse_value_spec fx rc SK tfibsegs B 2.
Proof. apply (pv 2 ltac:(lia)). intros H. lia. Qed.

Lemma reader_pi1 : @parse_items_spec fx rc SK tfibsegs B 1.
Proof. exact (@FSW_parse_items_holds.parse_items_holds fx rc SK B 1 ltac:(lia) HSS HSW HGROW HPS reader_pv2 MS). Qed.

Lemma reader_pv1 : @parse_value_spec fx rc SK tfibsegs B 1.
Proof. exact (pv 1 ltac:(lia) (fun _ => reader_pi1)). Qed.

Lemma reader_pi0 : @parse_items_spec fx rc SK tfibsegs B 0.
Proof. exact (@FSW_parse_items_holds.parse_items_holds fx rc SK B 0 ltac:(lia) HSS HSW HGROW HPS reader_pv1 MS). Qed.

Theorem reader_parse_value_0 : @parse_value_spec fx rc SK tfibsegs B 0.
Proof. exact (pv 0 ltac:(lia) (fun _ => reader_pi0)). Qed.

Theorem reader_parse_items : forall k : nat, (k <= 1)%nat -> @parse_items_spec fx rc SK tfibsegs B k.
Proof.
intros [|[|k]] Hk; [exact reader_pi0 | exact reader_pi1 | lia].
Qed.

Theorem reader_parse_value : forall k : nat, (k <= 2)%nat -> @parse_value_spec fx rc SK tfibsegs B k.
Proof.
intros [|[|[|k]]] Hk; [exact reader_parse_value_0 | exact reader_pv1 | exact reader_pv2 | lia].
Qed.
End T.
