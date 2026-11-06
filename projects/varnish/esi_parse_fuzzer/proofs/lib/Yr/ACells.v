(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation b8 z := (Z_to_bv 8 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Cells.
  Context (segs : list Segment).
  Definition u64_at (m : mem) (a v : Z) : Prop := bytes_at segs m a (le8 (wz v)).
  Definition u32_at (m : mem) (a v : Z) : Prop := bytes_at segs m a (le4 (wz v)).
  Definition u16_at (m : mem) (a v : Z) : Prop := bytes_at segs m a (le2 (wz v)).
  Definition u8_at  (m : mem) (a v : Z) : Prop := bytes_at segs m a [b8 v].
  (* [comment removed for export] *)
  Definition junk_at (m : mem) (a n : Z) : Prop := exists bs, Z.of_nat (length bs) = n /\ bytes_at segs m a bs.
  (* [comment removed for export] *)
  Definition fill_at (m : mem) (a n v : Z) : Prop := bytes_at segs m a (repeat (b8 v) (Z.to_nat n)).
End Cells.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition depot_foot (L : alayout) (nodes0 frames0 : Z) (a : Z) : Prop :=
     (al_stackStore L <= a < al_depot_nodes_map1 L + 8 * kDepotNodesL1)
  \/ (nodes0 <= a < nodes0 + kDepotNodesBlock)
  \/ (frames0 <= a < frames0 + kStackStoreBlockBytes).

Class DepotRep := {
  (* [comment removed for export] *)
  depot_rep : alayout -> list Segment -> list (list Z) -> Z -> Z -> mem -> Prop;
  depot_rep_agree : forall L segs D n0 f0 (m m' : mem),
      depot_rep L segs D n0 f0 m ->
      (forall a, depot_foot L n0 f0 a -> m' (wz a) = m (wz a)) ->
      depot_rep L segs D n0 f0 m'
}.

(* [comment removed for export] *)
Definition depot_cells0 (L : alayout) (segs : list Segment) (D : list (list Z)) (n0 f0 : Z) (m : mem) : Prop :=
  u32_at segs m (al_depot_n_uniq_ids L) (depot_n_ D) /\ u64_at segs m (al_depot_nodes_map1 L) n0 /\
  (forall j, 1 <= j < kDepotNodesL1 -> u64_at segs m (al_depot_nodes_map1 L + 8 * j) 0) /\
  mapped m n0 kDepotNodesBlock /\ mapped m f0 kStackStoreBlockBytes /\
  al_stackStore L <= al_depot_n_uniq_ids L /\ al_depot_n_uniq_ids L + 4 <= al_depot_nodes_map1 L.

Lemma bytes_at_agree_gen : forall segs (m m' : mem) a bs,
  bytes_at segs m a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> m' (wz (a + i)) = m (wz (a + i))) -> bytes_at segs m' a bs.
Proof.
  (intros segs m m' a bs; (first [ intro dR_2; dand3 dR_2 as H0 H1 HB | intros (H0 & H1 & HB) ]); intros AG). split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd, wa. rewrite (AG (Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.
Lemma mapped_agree_gen : forall (m m' : mem) a n,
  mapped m a n -> (forall i, 0 <= i < n -> m' (wz (a + i)) = m (wz (a + i))) -> mapped m' a n.
Proof. intros m m' a n M AG i Hi. rewrite (AG i Hi). apply M. exact Hi. Qed.

#[global] Instance DepotRep0 : DepotRep.
Proof.
  refine {| depot_rep := depot_cells0 |}.
  intros L segs D n0 f0 m m' DC AG. unfold depot_cells0 in *. (first [ dand7 DC as A1 A2 A3 A4 A5 B1 B2 | destruct DC as (A1 & A2 & A3 & A4 & A5 & B1 & B2) ]).
  assert (AGs : forall a i, al_stackStore L <= a -> a + i < al_depot_nodes_map1 L + 8 * kDepotNodesL1 -> 0 <= i -> m' (wz (a + i)) = m (wz (a + i))).
  { intros a i H1 H2 H3. apply AG. left. lia. }
  unfold u32_at, u64_at in *. unfold kDepotNodesL1 in *.
  split; [|split; [|split; [|split; [|split; [|split; assumption]]]]].
  - eapply bytes_at_agree_gen; [exact A1|]. intros i Hi. rewrite length_le4 in Hi. apply AGs; lia.
  - eapply bytes_at_agree_gen; [exact A2|]. intros i Hi. rewrite length_le8 in Hi. apply AGs; lia.
  - intros j Hj. eapply bytes_at_agree_gen; [exact (A3 j Hj)|]. intros i Hi. rewrite length_le8 in Hi. apply AGs; lia.
  - eapply mapped_agree_gen; [exact A4|]. intros i Hi. apply AG. right; left. lia.
  - eapply mapped_agree_gen; [exact A5|]. intros i Hi. apply AG. right; right. lia.
Defined.

