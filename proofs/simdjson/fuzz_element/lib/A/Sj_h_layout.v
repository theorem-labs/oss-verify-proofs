(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_h_deldtor Sj_stage2_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma rw_cells_relayout : forall (m : mem) A cs1 cs2,
  rw_cells asegs m A cs1 -> cells_wf cs2 -> cells_bytes cs2 = cells_bytes cs1 -> cells_size cs2 = cells_size cs1 -> rw_cells asegs m A cs2.
Proof.
  intros m A cs1 cs2 ((W1 & B1) & WR) W2 EB ES. split; [split; [exact W2| rewrite EB; exact B1]| rewrite ES; exact WR].
Qed.

Lemma dl_of_s2a : forall (m : mem) THIS vptr n IDX capv OC IA BUF len nxt docv p12 p28 p50,
  rw_cells asegs m THIS (s2a_impl_cells vptr n IDX capv OC IA BUF len nxt docv p12 p28 p50) ->
  exists pre8 mid rest, rw_cells asegs m THIS (dl_cells vptr pre8 (Z_to_bv 64 IDX) mid (Z_to_bv 64 OC) (Z_to_bv 64 IA) rest).
Proof.
  intros m THIS vptr n IDX capv OC IA BUF len nxt docv p12 p28 p50 H.
  pose proof H as ((W & _) & _). unfold s2a_impl_cells in W. cbn [cells_wf cell_wf] in W.
  destruct W as (_ & _ & L12 & _ & _ & L28 & _ & _ & _ & _ & L50 & _).
  exists (cbytes (C4 (wz n)) ++ p12),
         (cbytes (C4 nxt) ++ p28 ++ cbytes (C8 capv) ++ cbytes (C8 (wz 1024)) ++ cbytes (C1 (Z_to_bv 8 0)) ++ cbytes (C1 (Z_to_bv 8 0)) ++ p50),
         (cbytes (C8 (wz BUF)) ++ cbytes (C8 (wz len)) ++ cbytes (C8 docv)).
  apply (rw_cells_relayout m THIS _ _ H).
  - unfold dl_cells. cbn [cells_wf cell_wf]. rewrite !length_app, !cbytes_length by exact I. cbn [csize]. rewrite L12, L28, L50. repeat split; reflexivity.
  - unfold dl_cells, s2a_impl_cells. cbn [cells_bytes]. change (cbytes (CB ?k ?x)) with x. cbn [cbytes]. rewrite <- ?app_assoc. reflexivity.
  - reflexivity.
Qed.
