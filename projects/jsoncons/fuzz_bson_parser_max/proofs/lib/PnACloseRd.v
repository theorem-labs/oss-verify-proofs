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
     PnAClosePkg PnAOpnew PnALoc PnAEmbR PnAReaderCtor.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNACR.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Close.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells C.

Theorem reader_ctor_closed : forall ar HIR, PNACP.inst_ok L C IL ar HIR -> PNRAa.reader_ctor_spec L ar HIR.
Proof.
  intros ar HIR (HIok & ICok & EXT & GAP).
  assert (OPN : PMA.opnew_spec L ar HIR) by (eapply PMAOPN.opnew_ok; eassumption).
  assert (LCC : PMA.locale_ctor_spec L ar HIR) by (eapply PMALOC.locale_ctor_ok; eassumption).
  assert (PSH : PNSAX.push_root_spec PNARC.RSEGS PMA.AD L ar HIR 0xabff8) by (eapply PNAER.push_root_ok; eassumption).
  exact (PNARC.reader_ctor_ok L ar C IL HIR LY HIok ICok ILY LCC OPN PSH).
Qed.
End Close.
End SCFG_1.
End PNACR.
