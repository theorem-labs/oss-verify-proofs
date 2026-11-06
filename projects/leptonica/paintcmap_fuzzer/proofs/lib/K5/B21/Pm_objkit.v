(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Pm_iface.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma box_obj_keep : forall live (m m' : mem) b x y w h, box_obj live m b x y w h -> keeps_live [(b, 20)] m m' -> box_obj live m' b x y w h.
Proof.
  intros live m m' b x y w h (C & CH) K. split; [| exact CH].
  apply (keeps_live_cells [(b, 20)] m m' b 20 b _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact C].
Qed.

(* [comment removed for export] *)
Lemma pix_obj_cmap_rebuild : forall live (m m' : mem) pix v cv cv',
  pix_obj live m pix v cv -> keeps_live [(pix, 64)] m m' -> p_cmap v <> 0 ->
  cmap_obj live m' (p_cmap v) cv' -> c_arr cv' = c_arr cv -> pix_obj live m' pix v cv'.
Proof.
  intros live m m' pix v cv cv' (Hc & CH & HOK & HD & HCM) K NZ CO EA.
  split; [| split; [exact CH| split; [exact HOK| split; [exact HD|]]]].
  - apply (keeps_live_cells [(pix, 64)] m m' pix 64 pix _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact Hc].
  - right. destruct HCM as [Z0|(_ & N1 & N2 & N3 & N4)]; [contradiction|]. rewrite EA. exact (conj CO (conj N1 (conj N2 (conj N3 N4)))).
Qed.
