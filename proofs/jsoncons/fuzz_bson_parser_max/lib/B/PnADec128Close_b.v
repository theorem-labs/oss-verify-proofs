(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import HeapIfaceABxI_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAmc_b PnSpecsAX_b PnSpecsAXD_b PnRunA_b PnRunAa_b PnAImgGap_b
     PnAClosePkg_b PnAPushBackShort_b PnAFromInt_b PnADec128K_b PnADec128_b PnADec128Out2_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADCL.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
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
