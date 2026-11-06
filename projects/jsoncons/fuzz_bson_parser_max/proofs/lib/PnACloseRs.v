(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5DefsA HeapIfaceABx HeapIfaceABxI
     PmLayout PmLayoutA PnLayout PnLayoutA PmStatics PmStaticsA PnStatics PnStaticsA PmSpecsA PnSpecsAa PnSpecsAmc PnSpecsAX PnRunA PnRunAa PnAImgGap
     PnAClosePkg PnAOpnew PnAEmbR PnAAnn PnAAnnV8 PnAResetBStmts PnAResetB.
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
  assert (OPN : PMA.opnew_spec L ar HIR) by (eapply PMAOPN.opnew_ok; eassumption).
  assert (PSH : PNSAX.push_root_spec PNARB.RSEGS PMA.AD L ar HIR 0xabff8) by (eapply PNAER.push_root_ok; eassumption).
  assert (ASH8 : PNSAX.ann_shrink_v8_spec PNARB.RSEGS PMA.AD L ar HIR 0xab138) by (eapply PNAAV8.ann_shrink_v8_ok; eassumption).
  assert (ASH : PNSAX.ann_shrink_spec PNARB.RSEGS PMA.AD L ar HIR 0xaaecc) by (eapply PNAANN.ann_shrink_ok; eassumption).
  exact (PNARB.reset_ok L ar C HIR LY HIok ASH8 ASH PSH).
Qed.
End Close.
End SCFG_1.
End PNACRS.
