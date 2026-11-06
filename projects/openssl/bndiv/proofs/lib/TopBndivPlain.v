(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling Image Stage Nodes.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBaseG TopE TopSides TopSidesG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Malloc Driver Prog ModelInv Unforced LB_Inv LB_Raw LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import BndivModel.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require HxpInst HxpFuzz.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Rnd Lib_iface Driver_iface Impl_closed.
Require OSSVerify.openssl.bndiv.images.Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation imgP := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).

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

(* [comment removed for export] *)
Lemma implG_plain : implG_stmt (LM := LM_bndiv) psegs Plain.M.init_pc Plain.M.phdrs pstage.
Proof.
  exact (P.Impl_closed.implG_P_stmt_closed LM_bndiv (fun _ _ => HxpInst.LSP_bndiv) (fun _ _ => HxpInst.LL_bndiv)
           (fun CE RN => @HxpInst.rinit_bndiv CE RN) (fun CE RN => @HxpFuzz.rfuzz_bndiv CE RN)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma side_plain_lim : forall lim, KLIM + SMALLREQ <= lim -> side_canon_off ncfg Tc imgP lim.
Proof.
  intros lim Hlim.
  exact (G_side_off (LM := LM_bndiv) Pcap (sizes_of bndiv_ops) BN_NBLK BN_BSZ bn_linv Pcap_nonneg caps H_init H_one bn_H_rc
           psegs _ _ pstage lim image_low_psegs Hlim implG_plain).
Qed.

Lemma side_plain_san : side_canon_off ncfg Tc imgP SanitizerBudgets.lim_source.
Proof. apply side_plain_lim. unfold KLIM, SMALLREQ, SanitizerBudgets.lim_source, sanitizer_source_limit. lia. Qed.

Lemma side_plain : side_canon_off ncfg Tc imgP source_alloc_limit.
Proof.
  exact (G_side_off (LM := LM_bndiv) Pcap (sizes_of bndiv_ops) BN_NBLK BN_BSZ bn_linv Pcap_nonneg caps H_init H_one bn_H_rc
           psegs _ _ pstage source_alloc_limit image_low_psegs lim_source_ok implG_plain).
Qed.
