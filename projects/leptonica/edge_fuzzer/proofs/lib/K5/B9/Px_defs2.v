(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Image Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface LeptC_kit LeptL_kit Lept_objkit Ed_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ApartX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma live_chunk_apart : forall Σ' (m : mem) l1 p n l2 live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ (p, n) :: l2 -> (forall e, In e live0 -> In e (l1 ++ l2)) -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m l1 p n l2 live0 frs usp a HA LV SUB FRS SPL Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    pose proof (af_live_disj RT AF Σ' m p n p' n' l1 l2 HA LV (SUB _ Hin)) as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.
End ApartX.

(* [comment removed for export] *)
Lemma cmap_obj_mono : forall live live' (m : mem) c cv, (forall e, In e live -> In e live') -> cmap_obj live m c cv -> cmap_obj live' m c cv.
Proof.
  intros live live' m c cv S (C & (I1 & R1) & (I2 & R2) & R). split; [exact C|]. split; [split; [exact (S _ I1)| exact R1]|].
  split; [split; [exact (S _ I2)| exact R2]| exact R].
Qed.
Lemma pix_obj_mono : forall live live' (m : mem) pix v cv, (forall e, In e live -> In e live') -> pix_obj live m pix v cv -> pix_obj live' m pix v cv.
Proof.
  intros live live' m pix v cv S (C & (I1 & R1) & OK & D & CM). split; [exact C|]. split; [split; [exact (S _ I1)| exact R1]|]. split; [exact OK|].
  split; [destruct D as [D|((I2 & R2) & NE)]; [left; exact D| right; split; [split; [exact (S _ I2)| exact R2]| exact NE]]|].
  destruct CM as [CM|(CO & R)]; [left; exact CM| right]. split; [exact (cmap_obj_mono live live' m _ cv S CO)| exact R].
Qed.

(* [comment removed for export] *)
Lemma keeps_live_of_agree : forall live (P : Z -> Prop) (m m' : mem), agree_on P m m' ->
  (forall b k a, In (b, k) live -> b <= a < b + k -> P a) -> keeps_live live m m'.
Proof. intros live P m m' AG H b k Hb a Ha. apply AG. exact (H b k _ Hb Ha). Qed.
Lemma keeps_live_of_munch : forall live W (m m' : mem), munch W m m' ->
  (forall b k a, In (b, k) live -> b <= a < b + k -> outside W a) -> keeps_live live m m'.
Proof. intros live W m m' MU H b k Hb a Ha. apply MU. exact (H b k _ Hb Ha). Qed.


(* [comment removed for export] *)
Section ChunkOut.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma chunk_vs_frame : forall S (m : mem) f kk b k a, ART RT S m -> In (f, kk) (rt_frames RT S) -> In (b, k) (rt_live RT S) ->
  b <= a < b + k -> (a < f \/ f + fs_size kk <= a) /\ (a < shad f \/ shad (f + fs_size kk) <= a) /\ a < rt_sp0 RT S - STACK_WIN /\ 0 < b.
Proof using AF.
  intros S m f kk b k a A Hf Hb Ha.
  pose proof (af_live_range RT AF S m b k A Hb) as (P0 & PHI & PSEG).
  pose proof (af_frames_range RT AF S m f kk A Hf) as (_ & _ & _ & R). specialize (R b k Hb).
  pose proof (af_fshadow_apart RT AF S m f kk A Hf) as (R2 & _). specialize (R2 b k Hb).
  repeat split; lia.
Qed.
End ChunkOut.

Lemma keeps_live_sub : forall live live0 (m m' : mem), (forall e, In e live0 -> In e live) -> keeps_live live m m' -> keeps_live live0 m m'.
Proof. intros live live0 m m' S K b k Hb a Ha. exact (K b k (S _ Hb) a Ha). Qed.
