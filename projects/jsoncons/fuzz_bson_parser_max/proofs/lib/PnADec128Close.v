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
     PmLayout PmLayoutA PnLayout PnLayoutA PmStatics PmStaticsA PnStatics PnStaticsA PmSpecsA PnSpecsAa PnSpecsAmc PnSpecsAX PnSpecsAXD PnRunA PnRunAa PnAImgGap
     PnAClosePkg PnAPushBackShort PnAFromInt PnADec128K PnADec128 PnADec128Out2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADCL.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Close.
Variables (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout).
Hypothesis LY : PMA.layout L C.
Hypothesis ILY : as0_icpt_layout IL.

Theorem out_closed : forall ar HIR, PNACP.inst_ok L C IL ar HIR -> PNADK.out_stmt L ar HIR.
Proof.
  intros ar HIR IOK. pose proof (proj1 IOK) as HIok.
  exact (PNADO2.out_ok L ar C HIR LY HIok (PNAPBS.str_push_back_short_ok L ar C HIR LY HIok)
           (PNAFI.from_int_ok L ar C HIR LY HIok (PNAPBS.str_push_back_short_ok L ar C HIR LY HIok))).
Qed.

Theorem dec128_closed : forall ar HIR, PNACP.inst_ok L C IL ar HIR -> PNSAXD.dec128_spec RSEGS PMA.AD PMA.AN PMA.AAD L ar HIR.
Proof.
  intros ar HIR IOK.
  exact (PNADEC.dec128_ok_open1 L ar C HIR LY (proj1 IOK) IL (proj1 (proj2 IOK)) ILY (proj1 (proj2 (proj2 IOK))) (out_closed ar HIR IOK)).
Qed.
End Close.
End SCFG_1.
End PNADCL.
