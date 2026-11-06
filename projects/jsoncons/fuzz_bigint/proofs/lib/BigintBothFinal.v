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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceA BrtIfaceInst BigintFinal Bo0MainPhaseA Bo0InstA BigintTopAB0 BigintTopInstAB0 BigintTopAOldB0
  L5TopAB0 Bo0LibOkA Bo0DrvMain Bo0DiagArms Bo0UsageEntry Bo0UsageArm.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition art_IL : icpt_layout :=
  ICL 0x4de30 2304 0x10370 0x10390
      [(0x22960, 39); (0x229c0, 13); (0x22b20, 60); (0x22ba0, 42); (0x22c00, 37); (0x22c60, 51); (0x22cc0, 13)]
      [(0x22960, 0x22ce0); (0xdaeb0, 0xdb070)]
      0x5e350 0x5e34c 0x632cb0 0x4de84 4320 [(0x6118d8, 8, 0x631bd0); (0x631bf8, 8, 0)] 0x10000 0xd8000.
Lemma art_IL_ok : as0_icpt_layout art_IL.
Proof. constructor; reflexivity. Qed.

(* [comment removed for export] *)
Definition BUDGET0 : Z := 2 ^ 34.
Lemma BUDGET0_lo : 2 ^ 34 <= BUDGET0.  Proof. unfold BUDGET0. lia. Qed.
Lemma BUDGET0_hi : BUDGET0 <= 2 ^ 39 - 2 ^ 35.  Proof. unfold BUDGET0. lia. Qed.

Section Final.
  Lemma as0_lib_closed : lib_ok_stmt cfg0 art_L art_C art_IL LayA0 L5TOPA.TopLSA.
  Proof. exact (as0_lib_ok_closed cfg0 art_IL art_IL_ok). Qed.
  Lemma as0_drv_closed : drv_main_stmt cfg0 art_L art_C art_IL LayA0 L5TOPA.TopLSA.
  Proof. exact (as0_drv_main_closed cfg0 art_L art_C art_IL LayA0 L5TOPA.TopLSA as0_lib_layout as0_lib_cells as0_lib_budget). Qed.
  Lemma as0_usage_closed : usage_stmt cfg0.
  Proof.
    exact (as0_usage cfg0 art_L art_C art_IL BUDGET0 BUDGET0_lo BUDGET0_hi (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
             (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok) (as0_dla_ok cfg0 art_IL art_IL_ok) (as0_drv_consts art_IL art_IL_ok) (dg_usage_ok cfg0 art_L art_C art_IL)).
  Qed.

  (* [comment removed for export] *)
  Theorem fuzz_bigint_both_base_abort :
    strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
  Proof. exact (fuzz_bigint_both_base_abort_inst art_IL LayA0 L5TOPA.TopLSA BUDGET0 BUDGET0_lo BUDGET0_hi art_IL_ok as0_lib_closed as0_drv_closed as0_usage_closed). Qed.

  (* [comment removed for export] *)
  Theorem fuzz_bigint_both_base_scfg :
    strong_universal_error_free_T_scfg cfg0
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
  Proof.
    exact (fuzz_bigint_both_base_scfg_modulo art_L art_C art_IL LayA0 L5TOPA.TopLSA BUDGET0 BUDGET0_lo BUDGET0_hi (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
             (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok) as0_lib_closed (as0_dla_ok cfg0 art_IL art_IL_ok) (as0_drv_consts art_IL art_IL_ok) as0_drv_closed as0_usage_closed).
  Qed.
End Final.
