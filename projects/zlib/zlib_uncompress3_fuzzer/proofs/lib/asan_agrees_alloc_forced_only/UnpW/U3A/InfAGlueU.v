(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Arr Bytes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg ABase ABytes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

Lemma f8arr_blob : forall m A n f,
  f8arr asegs m A n f -> rw_cells asegs m A [CB n (map (fun i => Z_to_bv 8 (f (Z.of_nat i))) (seq 0 n))].
Proof.
  intros m A n f [HB HW]. rewrite length_map, length_seq in HW.
  split; [split|].
  - cbn. split; [rewrite length_map, length_seq; reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma blob_f8arr : forall m A n bs,
  rw_cells asegs m A [CB n bs] -> f8arr asegs m A n (fun i => bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
Proof.
  intros m A n bs [[[WF _] HB] HW]. cbn in WF. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW.
  assert (E : map (fun i => Z_to_bv 8 (bv_unsigned (nth (Z.to_nat (Z.of_nat i)) bs (Z_to_bv 8 0)))) (seq 0 n) = bs).
  { subst n. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0); [rewrite length_map, length_seq; reflexivity|].
    intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite (nth_indep _ _ (Z_to_bv 8 (bv_unsigned (nth (Z.to_nat (Z.of_nat 0)) bs (Z_to_bv 8 0))))) by (rewrite length_map, length_seq; exact Hi).
    rewrite (map_nth (fun i => Z_to_bv 8 (bv_unsigned (nth (Z.to_nat (Z.of_nat i)) bs (Z_to_bv 8 0)))) (seq 0 (length bs)) 0%nat i).
    rewrite seq_nth by exact Hi. rewrite Nat.add_0_l, Nat2Z.id. apply (@definitions.Z_to_bv_bv_unsigned 8). }
  unfold f8arr. rewrite E. split; [exact HB| subst n; exact HW].
Qed.

Lemma blob_join2 : forall m A (a b : nat) b1 b2,
  rw_cells asegs m A [CB a b1] -> rw_cells asegs m (A + Z.of_nat a) [CB b b2] -> rw_cells asegs m A [CB (a + b) (b1 ++ b2)].
Proof.
  intros m A a b b1 b2 H1 H2.
  pose proof H1 as [[[WF1 _] _] _]. pose proof H2 as [[[WF2 _] _] _]. cbn in WF1, WF2.
  assert (H : rw_cells asegs m A ([CB a b1] ++ [CB b b2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  eapply rw_cells_recast; [exact H| | |].
  - cbn. split; [rewrite length_app; lia| exact I].
  - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn [app cells_size csize]. lia.
Qed.
End CANSEC1.
