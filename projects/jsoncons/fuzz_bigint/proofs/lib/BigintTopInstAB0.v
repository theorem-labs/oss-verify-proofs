(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceA BrtIfaceInst BigintFinal Bo0MainPhaseA Bo0InstA BigintTopAB0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem fuzz_bigint_both_base_abort_inst :
  forall (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) (BUDGET : Z),
    2 ^ 34 <= BUDGET -> BUDGET <= 2 ^ 39 - 2 ^ 35 ->
    as0_icpt_layout IL -> lib_ok_stmt cfg0 art_L art_C IL Lay LSt ->
    drv_main_stmt cfg0 art_L art_C IL Lay LSt -> usage_stmt cfg0 ->
    strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros IL Lay LSt BUDGET B1 B2 ILY LIB DRV USG.
  exact (fuzz_bigint_both_base_abort_modulo art_L art_C IL Lay LSt BUDGET B1 B2 (as0_inst_ok cfg0 BUDGET eq_refl) (as0_free_null cfg0 BUDGET) (as0_h4e BUDGET) (as0_icpt_ok cfg0 IL BUDGET ILY) LIB
           (as0_dla_ok cfg0 IL ILY) (as0_drv_consts IL ILY) DRV USG).
Qed.
