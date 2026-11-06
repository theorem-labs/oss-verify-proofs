(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ModelInvBg.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling Image Stage Nodes.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG TopHalts TopBignumPlain.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BgState BgLib BgExp BgTree BgBridge.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXP Require Import HxpInstBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require W_mod_exp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnR Require W_fuzz.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Rnd.
Require OSSVerify.openssl.bignum.images.Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem halts_bignum_plain :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2]
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
  exact (G_halts (LM := LM_bignum) PcapBg (sizes_of bignum_ops) BG_NBLKZ BG_BSZZ bg_linv PcapBg_nonneg caps_bg H_init_bg H_one_bg bg_H_rc
           bgpsegs _ _ bgpstage source_alloc_limit image_low_bgpsegs lim_source_ok implG_plain_bg).
Qed.
