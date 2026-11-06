(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface Gm_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma live_remove_head : forall p n (l : list (Z * Z)), live_remove p ((p, n) :: l) = live_remove p l.
Proof.
  intros p n l. unfold live_remove. apply stdpp.list_basics.list.filter_cons_False. cbn [fst]. rewrite Z.eqb_refl. cbn. tauto.
Qed.
Lemma live_remove_other : forall p q n (l : list (Z * Z)), q <> p -> live_remove p ((q, n) :: l) = (q, n) :: live_remove p l.
Proof.
  intros p q n l NE. unfold live_remove. apply stdpp.list_basics.list.filter_cons_True. cbn [fst].
  replace (q =? p) with false by (symmetry; apply Z.eqb_neq; exact NE). exact I.
Qed.
Lemma live_remove_fresh : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l. induction l as [|[q n] l IH]; intros H; [reflexivity|].
  rewrite live_remove_other by (exact (H (q, n) (or_introl eq_refl))). f_equal. apply IH. intros e He. apply H. right. exact He.
Qed.
Lemma rm_opt_0 : forall (l : list (Z * Z)), rm_opt 0 l = l.
Proof. intros l. reflexivity. Qed.
Lemma rm_opt_nz : forall p (l : list (Z * Z)), p <> 0 -> rm_opt p l = live_remove p l.
Proof. intros p l NZ. unfold rm_opt. replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). reflexivity. Qed.
Lemma live_remove_comm : forall p q (l : list (Z * Z)), live_remove p (live_remove q l) = live_remove q (live_remove p l).
Proof.
  intros p q l. induction l as [|[a n] l IH]; [reflexivity|].
  destruct (Z.eq_dec a q) as [Eq|Nq]; destruct (Z.eq_dec a p) as [Ep|Np].
  - subst a. subst q. rewrite !live_remove_head. exact IH.
  - subst a. rewrite (live_remove_head q n l), (live_remove_other p q n l Np), (live_remove_head q n _). exact IH.
  - subst a. rewrite (live_remove_other q p n l Nq), (live_remove_head p n _), (live_remove_head p n l). exact IH.
  - rewrite (live_remove_other q a n l Nq), (live_remove_other p a n _ Np), (live_remove_other p a n l Np), (live_remove_other q a n _ Nq).
    f_equal. exact IH.
Qed.

(* [comment removed for export] *)
Lemma chunk_mono : forall (live live' : list (Z * Z)) p n, (forall e, In e live -> In e live') -> chunk live p n -> chunk live' p n.
Proof. intros live live' p n S (H1 & H2). split; [exact (S _ H1)| exact H2]. Qed.
Lemma cmap_obj_mono : forall (live live' : list (Z * Z)) (m : mem) cmap cv, (forall e, In e live -> In e live') ->
  cmap_obj live m cmap cv -> cmap_obj live' m cmap cv.
Proof.
  intros live live' m cmap cv S (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact (chunk_mono _ _ _ _ S H2)|].
  split; [exact (chunk_mono _ _ _ _ S H3)| exact H4].
Qed.
Lemma pix_obj_mono : forall (live live' : list (Z * Z)) (m : mem) pix v cv, (forall e, In e live -> In e live') ->
  pix_obj live m pix v cv -> pix_obj live' m pix v cv.
Proof.
  intros live live' m pix v cv S (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact (chunk_mono _ _ _ _ S H2)|]. split; [exact H3|].
  split.
  - destruct H4 as [H4|(H4 & H4')]; [left; exact H4| right; split; [exact (chunk_mono _ _ _ _ S H4)| exact H4']].
  - destruct H5 as [H5|(H5 & H5')]; [left; exact H5| right; split; [exact (cmap_obj_mono _ _ _ _ _ S H5)| exact H5']].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_join2 : forall (m : mem) A cs1 B cs2, rw_cells asegs m A cs1 -> rw_cells asegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells asegs m A (cs1 ++ cs2).
Proof. intros m A cs1 B cs2 H1 H2 ->. apply (proj2 (rw_cells_app m A cs1 cs2)). split; assumption. Qed.

(* [comment removed for export] *)
Lemma cmap_part_carry : forall (live0 live1 : list (Z * Z)) (m0 m1 : mem) cmd cvn pixd dat rs (X : Prop),
  (cmd = 0 \/ (cmap_obj live0 m0 cmd cvn /\ X)) ->
  agree_on (fun a : Z => cmd <> 0 /\ cmd <= a < cmd + 24) m0 m1 ->
  (forall e, In e live0 -> In e live1) ->
  (cmd <> 0 -> 0 < 4 * c_nalloc cvn /\ (cmd + 24 <= pixd \/ pixd + 64 <= cmd) /\ (cmd + 24 <= dat \/ dat + rs <= cmd)
               /\ (c_arr cvn + 4 * c_nalloc cvn <= pixd \/ pixd + 64 <= c_arr cvn)
               /\ (c_arr cvn + 4 * c_nalloc cvn <= dat \/ dat + rs <= c_arr cvn)) ->
  0 < rs ->
  cmd = 0 \/ (cmap_obj live1 m1 cmd cvn /\ cmd <> pixd /\ c_arr cvn <> pixd /\ cmd <> dat /\ c_arr cvn <> dat).
Proof.
  intros live0 live1 m0 m1 cmd cvn pixd dat rs X CMO AG SUB AP RS.
  destruct (Z.eq_dec cmd 0) as [Z0|NZ]; [left; exact Z0| right].
  destruct CMO as [Z0|(CO & _)]; [exfalso; exact (NZ Z0)|].
  destruct (AP NZ) as (AN & Q1 & Q2 & Q3 & Q4).
  split; [| repeat split; lia].
  apply (cmap_obj_mono live0 live1 m1 cmd cvn SUB).
  destruct CO as ((pad & CMC) & R). split; [| exact R].
  exists pad. apply (rw_cells_agree_nw asegs m0 m1 _ _ CMC). intros a Ha. apply AG.
  cbn [cells_size cmap_cells csize Nat.add] in Ha. split; [exact NZ| lia].
Qed.

(* [comment removed for export] *)
Lemma live_destroy_tmpl : forall (live : list (Z * Z)) pixd dat rs cmd arr na v cv,
  p_data v = dat -> p_cmap v = cmd -> (cmd <> 0 -> c_arr cv = arr) -> dat <> 0 -> dat <> pixd ->
  (cmd <> 0 -> arr <> 0 /\ cmd <> pixd /\ cmd <> dat /\ arr <> pixd /\ arr <> dat /\ arr <> cmd) ->
  (forall e, In e live -> fst e <> pixd /\ fst e <> dat) ->
  (cmd <> 0 -> forall e, In e live -> fst e <> cmd /\ fst e <> arr) ->
  live_destroy pixd v cv (if cmd =? 0 then (dat, rs) :: (pixd, 64) :: live else (arr, na) :: (cmd, 24) :: (dat, rs) :: (pixd, 64) :: live) = live.
Proof.
  intros live pixd dat rs cmd arr na v cv ED EC EA DNZ DNP CM FR1 FR2.
  unfold live_destroy. rewrite ED, EC. clear ED EC.
  destruct (Z.eq_dec cmd 0) as [Z0|NZ].
  - subst cmd. cbn [Z.eqb]. rewrite !rm_opt_0. rewrite (rm_opt_nz dat _ DNZ).
    rewrite (live_remove_head dat rs). rewrite (live_remove_other dat pixd 64 live) by (intros E; apply DNP; symmetry; exact E).
    rewrite (live_remove_head pixd 64).
    rewrite (live_remove_fresh dat live) by (intros e He; exact (proj2 (FR1 e He))).
    apply live_remove_fresh. intros e He; exact (proj1 (FR1 e He)).
  - replace (cmd =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). cbv iota.
    rewrite (EA NZ). destruct (CM NZ) as (ANZ & C1 & C2 & A1 & A2 & A3).
    rewrite (rm_opt_nz dat _ DNZ), (rm_opt_nz arr _ ANZ), (rm_opt_nz cmd _ NZ).
    rewrite (live_remove_other dat arr na) by exact A2.
    rewrite (live_remove_other dat cmd 24) by exact C2.
    rewrite (live_remove_head dat rs).
    rewrite (live_remove_other dat pixd 64) by (intros E; apply DNP; symmetry; exact E).
    rewrite (live_remove_fresh dat live) by (intros e He; exact (proj2 (FR1 e He))).
    rewrite (live_remove_head arr na).
    rewrite (live_remove_other arr cmd 24) by (intros E; apply A3; symmetry; exact E).
    rewrite (live_remove_other arr pixd 64) by (intros E; apply A1; symmetry; exact E).
    rewrite (live_remove_fresh arr live) by (intros e He; exact (proj2 (FR2 NZ e He))).
    rewrite (live_remove_head cmd 24).
    rewrite (live_remove_other cmd pixd 64) by (intros E; apply C1; symmetry; exact E).
    rewrite (live_remove_fresh cmd live) by (intros e He; exact (proj1 (FR2 NZ e He))).
    rewrite (live_remove_head pixd 64).
    apply live_remove_fresh. intros e He; exact (proj1 (FR1 e He)).
Qed.
