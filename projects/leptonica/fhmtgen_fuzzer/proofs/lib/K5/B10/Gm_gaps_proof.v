(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_rep RT_facts RT_gaps_iface RT_gaps_proof Gm_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma gmA_acc_rmask32 : forall Σ m, ART RTA Σ m -> acc asegs m GM_RMASK32 132.
Proof.
  intros Σ m HA. pose proof (rta_acc_lits Σ m HA) as F. rewrite Forall_forall in F.
  apply (F (GM_RMASK32, 132)). apply pair_inb_sound. vm_compute. reflexivity.
Qed.

Lemma gmA_acc_lmask32 : forall Σ m, ART RTA Σ m -> acc asegs m GM_LMASK32 132.
Proof.
  intros Σ m HA. pose proof (rta_acc_lits Σ m HA) as F. rewrite Forall_forall in F.
  apply (F (GM_LMASK32, 132)). apply pair_inb_sound. vm_compute. reflexivity.
Qed.

Theorem rta_gm_gaps : gm_gaps RTA.
Proof. exact (mkGmGaps RTA gmA_acc_rmask32 gmA_acc_lmask32). Qed.
