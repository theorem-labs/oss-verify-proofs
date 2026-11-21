(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import ZTopC BothMain.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg PlainClosed.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF
     AFreeAll AMain_final AClient_inst AMain_u3closed.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import U2BIface InfBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Require LinuxProcessSemantics.LinuxProcessSem.State.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_both_u3 :
  strong_universal_error_free_T_scfg_budgets alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs) (mkImage bsegs b_init_pc b_phdrs).
Proof. exact (base_both plain_implC_closed ASTAGE both_implC_u3). Qed.

Theorem base_both_plain_u3 :
  strong_universal_error_free_T_scfg alloc_forced_cfg (mkImage psegs p_init_pc p_phdrs) (mkImage bsegs b_init_pc b_phdrs).
Proof. exact (base_both_plain plain_implC_closed ASTAGE both_implC_u3). Qed.

Theorem halts_both_u3_core :
  halts_core alloc_forced_cfg LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit AnyExit.codes
    (mkImage bsegs b_init_pc b_phdrs).
Proof. exact (halts_bothC plain_implC_closed ASTAGE both_implC_u3). Qed.

(* tier 1 port: the forced-only entry's halts row (every family forced-only, at the shipped budget),
   read off the core by monotonicity in the configuration. *)
Theorem halts_both_u3 :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source AnyExit.codes (mkImage bsegs b_init_pc b_phdrs).
Proof.
  apply halts_allowed_T_scfg_budgets_of_core.
  exact (halts_core_mono forced_only_cfg alloc_forced_cfg _ _ _ (forced_only_cfg_least _) halts_both_u3_core).
Qed.
