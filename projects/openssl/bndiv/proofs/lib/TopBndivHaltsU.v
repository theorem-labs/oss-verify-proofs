(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling Image Stage Nodes.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG TopHalts TopBndivPlain TopBndivUbsan.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import BndivModel.
Require OSSVerify.openssl.bndiv.images.Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem halts_bndiv_ubsan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2]
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (G_halts (LM := LM_bndiv) Pcap (sizes_of bndiv_ops) BN_NBLK BN_BSZ bn_linv Pcap_nonneg caps H_init H_one bn_H_rc
           usegs _ _ ustage source_alloc_limit image_low_usegs lim_source_ok implG_ubsan).
Qed.
