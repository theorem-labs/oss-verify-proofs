(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core L5DefsA
     PmLayout PmLayoutA PnLayout PnLayoutA PmStatics PmStaticsA PmSpecsA PnSpecsAa PnSpecsAX PnRunA PnRunAa
     PnAResetBStmts PnAResetBGlue PnAResetB1 PnAResetB2 PnAResetB3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNARB.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Theorem reset_ok : PNSAX.ann_shrink_v8_spec RSEGS PMA.AD L ar HI 0xab138 -> PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HI 0xaaecc ->
  PNSAX.push_root_spec RSEGS PMA.AD L ar HI 0xabff8 -> PNARBS.reset_spec L ar HI.
Proof.
  exact (PNARBG.reset_of_stages L ar HI (PNARB1.head L ar C HI LY HIok) (PNARB2.mids L ar C HI LY HIok) (PNARB3.tail L ar C HI LY HIok)).
Qed.
End SCFG_1.
End PNARB.
