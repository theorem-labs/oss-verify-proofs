(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling Image Stage Nodes.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG TopRows TopLibPU.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import ClassifierRows.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import BndivModel.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require HxpInst HxpFuzz.
From OSSVerify.Proofs.openssl.bndiv.lib.HXU Require HxuInst HxuFuzzGap HxuFuzz.
From OSSVerify.Proofs.openssl.bndiv.lib.HXU Require Import BndivTopPU.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Impl_closed.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Impl_closed.
Require OSSVerify.openssl.bndiv.images.Plain.
Require OSSVerify.openssl.bndiv.images.Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation imgP := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation imgU := (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs) (only parsing).
(* [comment removed for export] *)

Section Closed.
  Let FUZZu : forall (CE__ : Ceiling) (RN__ : RunRnd), @UL.rfuzz_one_stmt CE__ RN__ LM_bndiv HxuInst.LSP_bndiv :=
    fun CE RN => @HxuFuzz.rfuzz_bndiv CE RN.

  Let FUZZp : forall (CE__ : Ceiling) (RN__ : RunRnd), @PL.rfuzz_one_stmt CE__ RN__ LM_bndiv HxpInst.LSP_bndiv :=
    fun CE RN => @HxpFuzz.rfuzz_bndiv CE RN.

  (* [comment removed for export] *)
  Lemma implG_plain : implG_stmt (LM := LM_bndiv) psegs Plain.M.init_pc Plain.M.phdrs pstage.
  Proof.
    exact (P.Impl_closed.implG_P_stmt_closed LM_bndiv (fun _ _ => HxpInst.LSP_bndiv) (fun _ _ => HxpInst.LL_bndiv)
             (fun CE RN => @HxpInst.rinit_bndiv CE RN) FUZZp).
  Qed.
  Lemma implG_ubsan : implG_stmt (LM := LM_bndiv) usegs Ubsan.M.init_pc Ubsan.M.phdrs ustage.
  Proof.
    exact (U.Impl_closed.implG_U_stmt_closed LM_bndiv (fun _ _ => HxuInst.LSP_bndiv) (fun _ _ => HxuInst.LL_bndiv)
             (fun CE RN => @HxuInst.rinit_bndiv CE RN) FUZZu).
  Qed.

  (* [comment removed for export] *)
  Lemma side_plain : side_canon_off ncfg Tc imgP source_alloc_limit.
  Proof.
    exact (G_side_off (LM := LM_bndiv) Pcap (sizes_of bndiv_ops) BN_NBLK BN_BSZ bn_linv Pcap_nonneg caps H_init H_one bn_H_rc
             psegs _ _ pstage source_alloc_limit image_low_psegs lim_source_ok implG_plain).
  Qed.
  Lemma side_ubsan : side_canon_off ncfg Tc imgU target_alloc_limit.
  Proof.
    exact (G_side_off (LM := LM_bndiv) Pcap (sizes_of bndiv_ops) BN_NBLK BN_BSZ bn_linv Pcap_nonneg caps H_init H_one bn_H_rc
             usegs _ _ ustage target_alloc_limit image_low_usegs lim_target_ok implG_ubsan).
  Qed.

  (* [comment removed for export] *)
  Theorem base_bndiv_ubsan :
    strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
      ShippedBudgets.lim_source ShippedBudgets.lim_target imgP imgU.
  Proof. exact (glue_scfg_budgets ncfg Tc _ _ side_plain side_ubsan). Qed.
End Closed.
