(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from projects/openssl/bignum/proofs/lib/TopBignumHaltsP.v at 874e3397a35 and changed to the UBSan build: images.Plain -> images.Ubsan, the BgHXP/BgBnE/BgBnR instantiations -> BgHXU/BgBnEU/BgBnRU, TopBignumPlain -> TopBignumUbsan, bgp* -> bgu* and implG_plain_bg -> implG_ubsan_bg. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ModelInvBg.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling Image Stage Nodes.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG TopHalts TopBignumPlain TopBignumUbsan.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BgState BgLib BgExp BgTree BgBridge.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInstBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnEU Require W_mod_exp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRU Require W_fuzz.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Rnd.
Require OSSVerify.openssl.bignum.images.Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem halts_bignum_ubsan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2]
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (G_halts (LM := LM_bignum) PcapBg (sizes_of bignum_ops) BG_NBLKZ BG_BSZZ bg_linv PcapBg_nonneg caps_bg H_init_bg H_one_bg bg_H_rc
           bgusegs _ _ bgustage source_alloc_limit image_low_bgusegs lim_source_ok implG_ubsan_bg).
Qed.
