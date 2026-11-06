(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF BzCLemmasFs.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Points.
  Variables (fm ec bh : zarr) (nb : Z).

  (* [comment removed for export] *)
  Definition fp_ft1 : zarr := fs_ftab_zero 257%nat znew 0.                 (* [comment removed for export] *)
  Definition fp_ft2 : zarr := fs_count (Z.to_nat nb) fp_ft1 ec 0.           (* [comment removed for export] *)
  Definition fp_fc0 : zarr := fs_copy 256%nat znew fp_ft2 0.                (* [comment removed for export] *)
  Definition fp_ft3 : zarr := fs_accum 256%nat fp_ft2 1.                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fp_dist (k : nat) : zarr * zarr := fs_distrib k fp_ft3 fm ec 0.
  Definition fp_ft4 : zarr := fst (fp_dist (Z.to_nat nb)).
  Definition fp_fm1 : zarr := snd (fp_dist (Z.to_nat nb)).
  Definition fp_nB : Z := 2 + nb / 32.
  Definition fp_bh3 : zarr := fs_sentinel 32%nat (fs_bh_init 256%nat (fs_bh_zero (Z.to_nat fp_nB) bh 0) fp_ft4 0) nb 0.
  Definition fp_hs0 : fhs := FHS fp_fm1 ec fp_bh3 znew znew 1 false.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fsf_distrib : Prop :=
    forall i, 0 <= i < nb -> 1 <= zget (fst (fp_dist (Z.to_nat i))) (rd8 ec i) <= nb.
  (* [comment removed for export] *)
  Definition fsf_ft4 : Prop := forall b, 0 <= b < 256 -> 0 <= zget fp_ft4 b <= nb.
  (* [comment removed for export] *)
  Definition fsf_fm1 : Prop := forall x, 0 <= x < nb -> 0 <= rd32 fp_fm1 x < nb.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FSC : nat := Z.to_nat (nb + 70).
  (* [comment removed for export] *)
  Definition bk1 (bh' : zarr) (k0 : Z) : Z :=
    let kA := fs_scan_set_unal FSC bh' k0 in
    if isset_bh bh' kA then fs_scan_set FSC bh' (fs_scan_word_ff FSC bh' kA) else kA.
  Definition bk2 (bh' : zarr) (k1 : Z) : Z :=
    let kD := fs_scan_clr_unal FSC bh' k1 in
    if negb (isset_bh bh' kD) then fs_scan_clr FSC bh' (fs_scan_word_00 FSC bh' kD) else kD.
  (* [comment removed for export] *)
  Definition scan_ok (bh' : zarr) (k0 : Z) : Prop :=
    let kA := fs_scan_set_unal FSC bh' k0 in let kB := fs_scan_word_ff FSC bh' kA in let kC := fs_scan_set FSC bh' kB in
    let k1 := bk1 bh' k0 in
    let kD := fs_scan_clr_unal FSC bh' k1 in let kE := fs_scan_word_00 FSC bh' kD in let kF := fs_scan_clr FSC bh' kE in
    0 <= k0 /\ k0 + 1 <= k1 /\
    isset_bh bh' kA && unaligned_bh kA = false /\ kA <= nb + 64 /\
    (isset_bh bh' kA = true -> (bh_word bh' kB =? 4294967295) = false /\ kB <= nb + 64 /\ isset_bh bh' kC = false /\ kC <= nb + 64) /\
    (k1 - 1 < nb ->
       negb (isset_bh bh' kD) && unaligned_bh kD = false /\ kD <= nb + 64 /\
       (isset_bh bh' kD = false -> (bh_word bh' kE =? 0) = false /\ kE <= nb + 64 /\ isset_bh bh' kF = true /\ kF <= nb + 64)).
  (* [comment removed for export] *)
  Definition qfacts (q : fqs) : Prop :=
    0 < fq_sp q ->
    fq_sp q <= 98 /\
    0 <= zget (fq_slo q) (fq_sp q - 1) /\ zget (fq_slo q) (fq_sp q - 1) - 1 <= zget (fq_shi q) (fq_sp q - 1) /\ zget (fq_shi q) (fq_sp q - 1) < nb.
  Definition qsort_ok (fm' ec' slo shi : zarr) (l r : Z) : Prop :=
    let q0 := FQS fm' 1 (zset slo 0 l) (zset shi 0 r) 0 in
    (forall v, qfacts (fqs_loop v ec' q0)) /\ fq_sp (fqs_loop (fqs_fuel l r) ec' q0) <= 0.
  (* [comment removed for export] *)
  Definition bucket_ok (s : fbs) : Prop :=
    let k0 := fb_r s + 1 in let k1 := bk1 (fb_bh s) k0 in let k2 := bk2 (fb_bh s) k1 in
    scan_ok (fb_bh s) k0 /\
    (k1 - 1 < nb -> k2 - 1 < nb -> k1 - 1 < k2 - 1 -> qsort_ok (fb_fm s) (fb_ec s) (fb_slo s) (fb_shi s) (k1 - 1) (k2 - 1)).
  (* [comment removed for export] *)
  Definition ec_ok (ec' : zarr) : Prop := forall k, 0 <= k < nb -> 0 <= rd32 ec' k < nb.

  (* [comment removed for export] *)
  Definition fp_hs (t : nat) : fhs := fs_H_loop t nb fp_hs0.
  Definition fp_ecT (t : nat) : zarr := let h := fp_hs t in fs_eclass (Z.to_nat nb) (fh_ec h) (fh_fm h) (fh_bh h) (fh_H h) nb 0 0.
  Definition fp_bs (t u : nat) : fbs :=
    let h := fp_hs t in fs_bucket_loop u nb (FBS (fh_fm h) (fp_ecT t) (fh_bh h) (fh_slo h) (fh_shi h) (-1) 0 false).
  (* [comment removed for export] *)
  Definition fsf_ec : Prop := forall t, fh_done (fp_hs t) = false -> ec_ok (fp_ecT t).
  Definition fsf_bucket : Prop := forall t u, fh_done (fp_hs t) = false -> fb_done (fp_bs t u) = false -> bucket_ok (fp_bs t u).

  (* [comment removed for export] *)
  Definition fp_hsF : fhs := fs_H_loop (Z.to_nat 64) nb fp_hs0.
  (* [comment removed for export] *)
  Definition fp_rb (i : nat) : zarr * zarr * Z := fs_rebuild i (fh_ec fp_hsF) fp_fc0 (fh_fm fp_hsF) 0 0.
  (* [comment removed for export] *)
  Definition fsf_rebuild : Prop := forall i, 0 <= i < nb ->
    let eci := fst (fst (fp_rb (Z.to_nat i))) in let fci := snd (fst (fp_rb (Z.to_nat i))) in let ji := snd (fp_rb (Z.to_nat i)) in
    let j' := fs_skip0 258%nat fci ji in
    0 <= ji /\ j' <= 255 /\ (zget fci j' =? 0) = false /\ 1 <= zget fci j' <= nb.
End Points.

(* [comment removed for export] *)
Definition fs_facts (fm ec bh : zarr) (nb : Z) : Prop :=
  fsf_distrib fm ec nb /\ fsf_ft4 fm ec nb /\ fsf_fm1 fm ec nb /\ fsf_ec fm ec bh nb /\ fsf_bucket fm ec bh nb /\ fsf_rebuild fm ec bh nb.

(* [comment removed for export] *)
Lemma fp_dist_step : forall fm ec nb i, 0 <= i ->
  fp_dist fm ec nb (Z.to_nat (i + 1)) =
  (let '(ft, fm') := fp_dist fm ec nb (Z.to_nat i) in
   (zset ft (rd8 ec i) (zget ft (rd8 ec i) - 1), wr32 fm' (zget ft (rd8 ec i) - 1) i)).
Proof.
  intros fm ec nb i Hi. unfold fp_dist. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite fs_distrib_snoc. destruct (fs_distrib (Z.to_nat i) _ fm ec 0) as [ft fm'].
  replace (0 + Z.of_nat (Z.to_nat i)) with i by lia. reflexivity.
Qed.
