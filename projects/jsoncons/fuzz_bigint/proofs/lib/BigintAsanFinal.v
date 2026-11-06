(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface HeapIfaceA IcptIfaceA LibIface LibIfaceA ArtIfaceInst BigintFinal As0MainPhaseA As0InstA BigintTopA BigintTopInstA BigintTopAOld
  L5TopA As0LibOkA As0DrvMain As0DiagArms As0UsageEntry As0UsageArm.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition art_IL : icpt_layout :=
  ICL 0x4dbb0 2304 0x10370 0x10390
      [(0x22960, 39); (0x229c0, 13); (0x229e0, 60); (0x22a60, 42); (0x22ac0, 37); (0x22b20, 51); (0x22b80, 13)]
      [(0x22960, 0x22ba0); (0xda2a0, 0xda460)]
      0x5e0d0 0x5e0cc 0x6320b0 0x4dc04 4320 [(0x610cd8, 8, 0x630fd0); (0x630ff8, 8, 0)] 0x10000 0xd7000.
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
  Theorem fuzz_bigint_asan_base_abort :
    strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
  Proof. exact (fuzz_bigint_asan_base_abort_inst art_IL LayA0 L5TOPA.TopLSA BUDGET0 BUDGET0_lo BUDGET0_hi art_IL_ok as0_lib_closed as0_drv_closed as0_usage_closed). Qed.

  (* [comment removed for export] *)
  Theorem fuzz_bigint_asan_base_scfg :
    strong_universal_error_free_T_scfg cfg0
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
  Proof.
    exact (fuzz_bigint_asan_base_scfg_modulo art_L art_C art_IL LayA0 L5TOPA.TopLSA BUDGET0 BUDGET0_lo BUDGET0_hi (as0_inst_ok cfg0 BUDGET0 eq_refl) (as0_free_null cfg0 BUDGET0) (as0_h4e BUDGET0)
             (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok) as0_lib_closed (as0_dla_ok cfg0 art_IL art_IL_ok) (as0_drv_consts art_IL art_IL_ok) as0_drv_closed as0_usage_closed).
  Qed.
End Final.
