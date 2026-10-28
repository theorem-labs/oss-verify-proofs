(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import HeapIfaceABxI_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAmc_b PnSpecsAX_b PnSpecsAXR_b PnSpecsAXC_b PnRunA_b PnRunAa_b PnAImgGap_b
     PnAClosePkg_b PnAOpnew_b PnAEmbR_b PnAAnn_b PnAAnnV8_b PnAResetBStmts_b PnAResetB_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNACRS.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Close.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.

Theorem reset_closed : forall ar HIR, PNACP.inst_ok L C IL ar HIR -> PNARBS.reset_spec L ar HIR.
Proof.
  intros ar HIR (HIok & ICok & EXT & GAP).
  assert (PSH : PNSAXR.push_root_fast_spec PNARB.RSEGS PMA.AD L ar HIR 0xacf40) by (eapply PNAER.push_root_fast_ok; eassumption).
  assert (CV8 : PNSAXC.clear_v8_spec PNARB.RSEGS PMA.AD L ar HIR 0xabb00) by (eapply PNAAV8.clear_v8_ok; eassumption).
  assert (VCL : PNSAXC.vec_clear_spec PNARB.RSEGS PMA.AD L ar HIR 0xab740) by (eapply PNAANN.vec_clear_ok; eassumption).
  exact (PNARB.reset_ok L ar C HIR LY HIok CV8 VCL PSH).
Qed.
End Close.
End SCFG_1.
End PNACRS.
