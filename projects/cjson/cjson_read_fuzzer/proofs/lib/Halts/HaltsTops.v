(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/TopHaltsA.v and its sibling
   TopHaltsB.v at commit c395a1e0dfa, lines 4-6 (the Stdlib/LPS import block), lines 14-15 (lim_source_le_target,
   verbatim) and lines 17-19 of each (the halts_allowed_T_scfg_budgets theorem statement), with from_chars's Asan and
   AsanUbsan images replaced by this harness's Plain and Ubsan, SpecHalts.HALT_CODES by this tree's HALT_CODES, and the
   theorem names by halts_skcms_iccprofile_info_plain and _ubsan.  The proof bodies are not copied: from_chars's single
   halts_allowed_lowered_of_realizes call is replaced here by HaltsBridge.halts_of_realizes_spec for the plain build and
   by must_exit_of_realizes_spec composed with Halts.Lim.LimTransfer.lim_transfer_scfg for the UBSan build. *)
(* Modified by gabelogan195, 2026-11: made from projects/skcms/iccprofile_info/proofs/lib/Halts/HaltsTops.v at commit
   f92feaf8b7, lines 20-23 (the Stdlib/LPS import block and the images import) and lines 32-34 and 40-42 (the two
   theorem statements), with skcms's Plain and Ubsan images replaced by cjson/cjson_read_fuzzer's and the theorem names by
   halts_cjson_read_fuzzer_plain and _ubsan.  lim_source_le_target and the proof bodies are not copied: both builds'
   realizations are proved at every budget of at least 2 GiB (Glue.Top04's plain_realizes04_lim and
   ubsan_realizes04_lim), so both theorems are HaltsBridge.must_exit_of_realizes_init at 16 GiB, with no budget
   transfer, and the lemma here is drv_limit_le_lim_source. *)
(** The halting theorems of the plain and UBSan builds, in the form
    [Statements.v] states them.

    Both realizations are proved for every budget of at least
    [Spec.KInv2.drv_limit] (2 GiB), so each is taken directly at the 16 GiB
    the statements name, and the walk of [HaltsBridge] gives the rest.  The
    statement's budget premise is not needed at a budget the realization is
    proved at, so it is dropped. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain Ubsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Glue Require Import Top04.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Halts Require Import SpecHalts HaltsBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma drv_limit_le_lim_source :
  (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit <= ShippedBudgets.lim_source)%Z.
Proof. vm_compute. discriminate. Qed.

Theorem halts_cjson_read_fuzzer_plain :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp _.
  exact (must_exit_of_realizes_init _ _ _ _ sp brk mbase rnd inp
           (plain_realizes04_lim ShippedBudgets.lim_source drv_limit_le_lim_source
              sp brk mbase rnd inp Hen Hinp)).
Qed.

Theorem halts_cjson_read_fuzzer_ubsan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros [sp brk mbase rnd] inp Hen Hinp _.
  exact (must_exit_of_realizes_init _ _ _ _ sp brk mbase rnd inp
           (ubsan_realizes04_lim ShippedBudgets.lim_source drv_limit_le_lim_source
              sp brk mbase rnd inp Hen Hinp)).
Qed.
