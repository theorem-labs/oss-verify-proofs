(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v; 25 of its 59 lines of code are new or changed and 2652 lines of the source are left out. *)
(* fuzz_state image A (fs.asan): the reader's closing theorem.
   rule 24: no function proved here (composition of reader lemmas; the function-level lookups are a Theorem Labs lane's).
   parse_value and parse_items call each other with the nesting depth k: parse_value at depth k calls
   parse_items at depth k only when k <= 1 (deeper documents are rejected), and parse_items at depth k calls
   parse_value at depth k + 1. So the five specs close by descending depth:
     parse_value 2  (needs no parse_items)
     parse_items 1  <- parse_value 2      (parse_items_holds)
     parse_value 1  <- parse_items 1      (parse_value_holds)
     parse_items 0  <- parse_value 1
     parse_value 0  <- parse_items 0.
   The Section hypotheses below are parse_value_holds's (lib/A/FSW_parse_value_holds.v) plus parse_items_holds's;
   after the Section closes, reader_parse_value_0's type carries them as premises, and ENTRY cites that one term. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_frame FSH_Fn_reader FSH_Fn_entry
FSH_Fn_alloc FSW_parse_items_holds FSW_parse_value_holds.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* parse_value_holds's hypotheses, exactly *)
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
Hypothesis SM0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\
  FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
(* the further hypotheses of parse_items_holds and of both specs' callee contracts *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis HGROW : @grow_spec fx rc SK tfibsegs B.
Hypothesis HPS : @parse_string_spec fx rc SK tfibsegs B.
Hypothesis MS : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

Let PVH := @parse_value_holds fx rc SK B HGUAR HUCELL SM0 errno_low ML SMP IMG ASF FFL.

Lemma reader_pv2 : @parse_value_spec fx rc SK tfibsegs B 2.
Proof. apply (PVH 2 ltac:(lia) HSS HPS). intros H. lia. Qed.

Lemma reader_pi1 : @parse_items_spec fx rc SK tfibsegs B 1.
Proof. exact (@parse_items_holds fx rc SK B 1 ltac:(lia) HSS HGROW HPS reader_pv2 MS). Qed.

Lemma reader_pv1 : @parse_value_spec fx rc SK tfibsegs B 1.
Proof. exact (PVH 1 ltac:(lia) HSS HPS (fun _ => reader_pi1)). Qed.

Lemma reader_pi0 : @parse_items_spec fx rc SK tfibsegs B 0.
Proof. exact (@parse_items_holds fx rc SK B 0 ltac:(lia) HSS HGROW HPS reader_pv1 MS). Qed.

Theorem reader_parse_value_0 : @parse_value_spec fx rc SK tfibsegs B 0.
Proof. exact (PVH 0 ltac:(lia) HSS HPS (fun _ => reader_pi0)). Qed.

Theorem reader_parse_items : forall k : nat, (k <= 1)%nat -> @parse_items_spec fx rc SK tfibsegs B k.
Proof.
intros [|[|k]] Hk; [exact reader_pi0 | exact reader_pi1 | lia].
Qed.

Theorem reader_parse_value : forall k : nat, (k <= 2)%nat -> @parse_value_spec fx rc SK tfibsegs B k.
Proof.
intros [|[|[|k]]] Hk; [exact reader_parse_value_0 | exact reader_pv1 | exact reader_pv2 | lia].
Qed.
End T.
