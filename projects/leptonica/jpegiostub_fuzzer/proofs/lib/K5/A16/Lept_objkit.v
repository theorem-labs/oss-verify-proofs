(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import ImageA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import Layout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition keeps_live (live : list (Z * Z)) (m m' : mem) : Prop :=
  forall b k, In (b, k) live -> forall a : word, b <= bv_unsigned a < b + k -> m' a = m a.

Lemma keeps_live_refl : forall live m, keeps_live live m m.
Proof. intros live m b k _ a _. reflexivity. Qed.
Lemma keeps_live_trans : forall live m1 m2 m3, keeps_live live m1 m2 -> keeps_live live m2 m3 -> keeps_live live m1 m3.
Proof. intros live m1 m2 m3 H1 H2 b k Hin a Ha. rewrite (H2 b k Hin a Ha). exact (H1 b k Hin a Ha). Qed.

Lemma keeps_live_cells : forall live (m m' : mem) p n A cs, keeps_live live m m' -> In (p, n) live ->
  p <= A -> A + Z.of_nat (cells_size cs) <= p + n -> rw_cells asegs m A cs -> rw_cells asegs m' A cs.
Proof.
  intros live m m' p n A cs K Hin H1 H2 H. apply (rw_cells_agree_nw asegs m m' A cs H). intros a Ha. apply (K p n Hin a). lia.
Qed.

Lemma cmap_obj_keep : forall live (m m' : mem) cmap cv, keeps_live live m m' -> cmap_obj live m cmap cv -> cmap_obj live m' cmap cv.
Proof.
  intros live m m' cmap cv K ((pad & Hc) & CH & R). split; [| exact (conj CH R)].
  exists pad. destruct CH as (Hin & _). apply (keeps_live_cells live m m' cmap 24 cmap _ K Hin); [lia| | exact Hc].
  cbn. lia.
Qed.

Lemma pix_obj_keep : forall live (m m' : mem) pix v cv, keeps_live live m m' -> pix_obj live m pix v cv -> pix_obj live m' pix v cv.
Proof.
  intros live m m' pix v cv K (Hc & CH & HOK & HD & HCM).
  split; [| split; [exact CH| split; [exact HOK| split; [exact HD|]]]].
  - destruct CH as (Hin & _). apply (keeps_live_cells live m m' pix 64 pix _ K Hin); [lia| | exact Hc]. cbn. lia.
  - destruct HCM as [HCM|(HCM & R)]; [left; exact HCM| right]. split; [exact (cmap_obj_keep live m m' _ cv K HCM)| exact R].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_merge_prefix : forall (m : mem) A low rest, rw_cells asegs m A (low ++ rest) ->
  rw_cells asegs m A (CB (cells_size low) (cells_bytes low) :: rest).
Proof.
  intros m A low rest [[Hwf Hb] Hw]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact (cells_bytes_length low W1)| exact W2].
  - cbn [cells_bytes cbytes]. rewrite cells_bytes_app in Hb. exact Hb.
  - cbn [cells_size csize]. rewrite cells_size_app in Hw. exact Hw.
Qed.
