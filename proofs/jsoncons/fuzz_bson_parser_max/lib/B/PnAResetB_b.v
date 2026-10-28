(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b PnSpecsAXR_b PnSpecsAXC_b PnRunA_b PnRunAa_b
     PnAResetBStmts_b PnAResetBGlue_b PnAResetB1_b PnAResetB2_b PnAResetB3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNARB.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Theorem reset_ok : PNSAXC.clear_v8_spec RSEGS PMA.AD L ar HI 0xabb00 -> PNSAXC.vec_clear_spec RSEGS PMA.AD L ar HI 0xab740 ->
  PNSAXR.push_root_fast_spec RSEGS PMA.AD L ar HI 0xacf40 -> PNARBS.reset_spec L ar HI.
Proof.
  exact (PNARBG.reset_of_stages L ar HI (PNARB1.head L ar C HI LY HIok) (PNARB2.mids L ar C HI LY HIok) (PNARB3.tail L ar C HI LY HIok)).
Qed.
End SCFG_1.
End PNARB.
