(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ModelInvBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling Image Stage Nodes.
From OssFuzzTheorems.Proofs.openssl.bignum.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG TopBignumPlain.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BgState BgLib BgExp BgTree BgBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInstBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require LibInstBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require W_mod_exp W_exp_simple ExpClosed.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_fuzz FuzzTop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Lib_iface Driver_iface Impl_closed.
Require OssFuzzTheorems.openssl.bignum.images.Plain.
Require OssFuzzTheorems.openssl.bignum.images.Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation imgPbg := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation RunRnd := OssFuzzTheorems.Proofs.openssl.bignum.lib.P.Rnd.RunRnd.
Notation imgUbg := (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs) (only parsing).

Lemma STK2u : ExpClosed.SIMPLE_STACK <= W_fuzz.FUZZ_CALLEE_MAX.
Proof. vm_compute. intros X; discriminate X. Qed.

Lemma STK1u : ExpClosed.MEXP_STACK <= W_fuzz.FUZZ_CALLEE_MAX.
Proof. vm_compute. intros X; discriminate X. Qed.

Lemma EXPu : forall (CE__ : Ceiling) (RN__ : RunRnd),
  @W_mod_exp.exp_stmt_f CE__ RN__ W_fuzz.BN_MOD_EXP ExpClosed.MEXP_STACK (BN_mod_exp (tree_ops bptr)) None.
Proof. intros CE RN. exact (@ExpClosed.BN_mod_exp_closed CE RN RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof). Qed.

Lemma implG_ubsan_bg : implG_stmt (LM := LM_bignum) bgusegs Ubsan.M.init_pc Ubsan.M.phdrs bgustage.
Proof.
  exact (BgU.Impl_closed.implG_U_stmt_closed LM_bignum
           (fun CE RN => LibInstBg.LSP_bgr unit tt bg_lib_one)
           (fun CE RN => LibInstBg.LL_bgr unit tt bg_lib_one)
           (fun CE RN => @LibInstBg.rinit_bgr CE RN unit tt bg_lib_one)
           (fun CE RN => @FuzzTop.rfuzz_one_bgr_of_exp CE RN ExpClosed.MEXP_STACK ExpClosed.SIMPLE_STACK STK1u STK2u (EXPu CE RN)
                           (@ExpClosed.BN_mod_exp_simple_closed CE RN RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof))).
Qed.

Lemma side_ubsan_bg : side_canon_off ncfg Tc imgUbg target_alloc_limit.
Proof.
  exact (G_side_off (LM := LM_bignum) PcapBg (sizes_of bignum_ops) BG_NBLKZ BG_BSZZ bg_linv PcapBg_nonneg caps_bg H_init_bg H_one_bg bg_H_rc
           bgusegs _ _ bgustage target_alloc_limit image_low_bgusegs lim_target_ok implG_ubsan_bg).
Qed.

Theorem base_bignum_ubsan :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target imgPbg imgUbg.
Proof. exact (glue_scfg_budgets ncfg Tc _ _ side_plain_bg side_ubsan_bg). Qed.
