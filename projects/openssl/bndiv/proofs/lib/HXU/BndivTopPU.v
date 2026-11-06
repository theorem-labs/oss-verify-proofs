(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling Image Stage.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBaseG TopLibPU.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import BndivModel.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require HxpInst.
From OSSVerify.Proofs.openssl.bndiv.lib.HXU Require HxuInst.
From OSSVerify.openssl.bndiv.images Require Plain.
From OSSVerify.openssl.bndiv.images Require Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition Pcap (c : Z) : Z := if (0 <=? c) && (c <? 48) then (if c <=? 2 then 1600 else 32) else if c =? 63 then 32 else 0.

Lemma Pcap_nonneg : forall c, 0 <= Pcap c.
Proof. intros c. unfold Pcap. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.

Lemma caps : caps_ok Pcap (sizes_of bndiv_ops) BN_NBLK BN_BSZ.
Proof. apply caps_ok_b_ok. vm_compute. reflexivity. Qed.

Lemma ops_checked : ops_wf bndiv_ops [] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma H_init : lwf (okT (sizes_of bndiv_ops)) lib_init [] (fun ls Li => bn_linv ls [] /\ subms (map snd Li) (sizes_of bndiv_ops)).
Proof.
  eapply lwf_mono; [apply (init_of_ops_lwf bndiv_ops (ls_init : @LS LM_bndiv) ops_checked)|]. intros ls Li [E HS]. split; [|exact HS].
  subst ls. exact bn_linv_init.
Qed.

Lemma H_one : forall (ls : @LS LM_bndiv) d X, bn_linv ls X -> zlength d <= MAX_INPUT ->
  lwf (okB BN_NBLK BN_BSZ) (lib_one ls d) X (fun r X' => bn_linv (fst r) X').
Proof. intros ls d X H _. exact (bn_H_one ls d X H). Qed.

Theorem base_bndiv_ubsan_of_fuzz :
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @PL.rfuzz_one_stmt CE__ RN__ LM_bndiv HxpInst.LSP_bndiv) ->
  (forall (CE__ : Ceiling) (RN__ : RunRnd), @UL.rfuzz_one_stmt CE__ RN__ LM_bndiv HxuInst.LSP_bndiv) ->
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros FUZZp FUZZu.
  exact (@base_bndiv_ubsan_of_lib LM_bndiv Pcap (sizes_of bndiv_ops) BN_NBLK BN_BSZ bn_linv Pcap_nonneg caps H_init H_one bn_H_rc
           (fun _ _ => HxpInst.LSP_bndiv) (fun _ _ => HxpInst.LL_bndiv) (fun CE RN => @HxpInst.rinit_bndiv CE RN) FUZZp
           (fun _ _ => HxuInst.LSP_bndiv) (fun _ _ => HxuInst.LL_bndiv) (fun CE RN => @HxuInst.rinit_bndiv CE RN) FUZZu).
Qed.

(* [comment removed for export] *)
