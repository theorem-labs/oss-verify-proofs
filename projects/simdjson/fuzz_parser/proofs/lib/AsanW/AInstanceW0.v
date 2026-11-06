(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP ARepQ ARepQP ASec ASecFrame
     ADepot_iface ADepot F_adepot ADepotW F_adepotW AFake_iface AFake_arep AInstance.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Definition AHI_k (k : Z) : aholes := mkAHoles AQUAR ASEC_of (ADEPOT (DI_of k)) AFAKE.

Theorem AHI_k_laws : forall k, ahole_laws (AHI_k k).
Proof.
  intros k. constructor; cbn [AHI_k ah_quar ah_sec ah_depot ah_fake].
  - exact AQUAR_frame.
  - exact asec_hs_frame.
  - exact (adi_frame (DI_of k)).
  - intros L LB m m' W HF MU WM UT. eapply afake_frame; [exact HF| exact MU| exact WM| exact UT].
  - intros L LB LB' m HF EQ. eapply afake_blocks; [exact HF| exact EQ].
Qed.

(* [comment removed for export] *)
Lemma AREP_k_weak : forall k L st X m, AREP (AHI_k k) L st X m -> AREP AHI L st X m.
Proof.
  intros k L st X m (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [AHI_k ah_depot ADEPOT DI_of] in HD.
  exact (conj WF (conj RT (conj INST (conj THR (conj CLS (conj HQ (conj HS (conj (adepotk_adepoti L k m HD) (conj HRO (conj RT2 (conj AVL RT3))))))))))).
Qed.
Lemma AREP_k_strong : forall k L st X m, AREP AHI L st X m -> ADEPOTk L k m -> AREP (AHI_k k) L st X m.
Proof.
  intros k L st X m (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3) HK.
  exact (conj WF (conj RT (conj INST (conj THR (conj CLS (conj HQ (conj HS (conj HK (conj HRO (conj RT2 (conj AVL RT3))))))))))).
Qed.
Lemma AREP_k_depot : forall k L st X m, AREP (AHI_k k) L st X m -> ADEPOTk L k m.
Proof. intros k L st X m (_ & _ & _ & _ & _ & _ & _ & HD & _). exact HD. Qed.

Lemma AHEAP_k_weak : forall k L RNG st LB m, AHEAP_P (AHI_k k) L RNG st LB m -> AHEAP_P AHI L RNG st LB m.
Proof.
  intros k L RNG st LB m (ALO & ARNG & [X [AR BL]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact (AREP_k_weak k L st X m AR)| exact BL]| exact HFK].
Qed.

(* [comment removed for export] *)
Lemma AHEAP_k_mono : forall k k' L RNG st LB m, k <= k' <= DWMAX -> AHEAP_P (AHI_k k) L RNG st LB m -> AHEAP_P (AHI_k k') L RNG st LB m.
Proof.
  intros k k' L RNG st LB m Hk (ALO & ARNG & [X [AR BL]] & HFK).
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK]. exists X. split; [| exact BL].
  apply AREP_k_strong; [exact (AREP_k_weak k L st X m AR)|]. exact (adepotk_mono L k k' m Hk (AREP_k_depot k L st X m AR)).
Qed.
End CANSEC1.
