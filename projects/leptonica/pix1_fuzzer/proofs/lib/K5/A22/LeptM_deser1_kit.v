(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit.
Import ListNotations.
Open Scope Z_scope.

Lemma lrm_cons : forall p e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.

Lemma lrm_notin : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l. induction l as [|e l IH]; intros H; [reflexivity|]. rewrite lrm_cons.
  replace (fst e =? p) with false by (symmetry; apply Z.eqb_neq; apply H; left; reflexivity).
  f_equal. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Ltac lrm_simpl FRESH :=
  repeat (first [ rewrite lrm_cons; cbn [fst]
                | match goal with
                  | |- context [?x =? ?x] => rewrite (Z.eqb_refl x)
                  | |- context [?x =? ?y] =>
                      replace (x =? y) with false by (symmetry; apply Z.eqb_neq; first [assumption | intros EE; symmetry in EE; contradiction])
                  end
                | progress cbv iota
                | match goal with
                  | |- context [live_remove ?p ?l] =>
                      is_var l; rewrite (lrm_notin p l); [| let e := fresh "e" in let He := fresh "He" in intros e He; pose proof (FRESH e He); tauto]
                  end ]).

(* [comment removed for export] *)
Lemma live_destroy_new : forall pix v cv data rs (L : list (Z * Z)),
  p_cmap v = 0 -> p_data v = data -> data <> 0 -> pix <> data ->
  (forall e, In e L -> fst e <> pix /\ fst e <> data) ->
  live_destroy pix v cv ((data, rs) :: (pix, 64) :: L) = L.
Proof.
  intros pix v cv data rs L HC HD D0 NE FRESH. unfold live_destroy, rm_opt. rewrite HC, HD. change (0 =? 0) with true. cbv iota.
  replace (data =? 0) with false by (symmetry; apply Z.eqb_neq; exact D0).
  lrm_simpl FRESH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma live_destroy_new_cmap : forall pix v cv cmap arr an data rs (L : list (Z * Z)),
  p_cmap v = cmap -> c_arr cv = arr -> p_data v = data -> cmap <> 0 -> arr <> 0 -> data <> 0 ->
  pix <> data -> cmap <> pix -> cmap <> data -> arr <> pix -> arr <> data -> arr <> cmap ->
  (forall e, In e L -> fst e <> pix /\ fst e <> data /\ fst e <> cmap /\ fst e <> arr) ->
  live_destroy pix v cv ((arr, an) :: (cmap, 24) :: (data, rs) :: (pix, 64) :: L) = L.
Proof.
  intros pix v cv cmap arr an data rs L HC HA HD C0 A0 D0 N1 N2 N3 N4 N5 N6 FRESH. unfold live_destroy, rm_opt. rewrite HC, HA, HD.
  replace (cmap =? 0) with false by (symmetry; apply Z.eqb_neq; exact C0).
  replace (arr =? 0) with false by (symmetry; apply Z.eqb_neq; exact A0).
  replace (data =? 0) with false by (symmetry; apply Z.eqb_neq; exact D0).
  lrm_simpl FRESH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cmap_obj_agree : forall (live : list (Z * Z)) (P : Z -> Prop) (m m' : mem) cmap cv,
  cmap_obj live m cmap cv -> agree_on P m m' -> (forall a, cmap <= a < cmap + 24 -> P a) -> cmap_obj live m' cmap cv.
Proof.
  intros live P m m' cmap cv ((pad & CMC) & R) AG HP. split; [| exact R]. exists pad.
  apply (rw_cells_agree_nw asegs m m' _ _ CMC). intros a Ha. apply AG. apply HP.
  cbn [cells_size cmap_cells csize Nat.add] in Ha. lia.
Qed.

Section Fresh.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
(* [comment removed for export] *)
Lemma live_pos_ne : forall (S : rts RT) (m : mem) l1 p k l2 q j, ART RT S m -> rt_live RT S = l1 ++ (p, k) :: l2 ->
  In (q, j) (l1 ++ l2) -> 0 < k -> 0 < j -> q <> p.
Proof using AF.
  intros S m l1 p k l2 q j HA E Hin K J EQ. pose proof (af_live_disj RT AF S m p k q j l1 l2 HA E Hin) as D. lia.
Qed.
(* [comment removed for export] *)
Lemma later_chunk_apart : forall (S : rts RT) (mc : mem) p k live0 frs usp a,
  ART RT S mc -> In (p, k) (rt_live RT S) -> (forall q j, In (q, j) live0 -> In (q, j) (rt_live RT S) /\ q <> p) ->
  (forall e, In e frs -> In e (rt_frames RT S)) -> rt_sp0 RT S - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + k <= a.
Proof using AF.
  intros S mc p k live0 frs usp a HA INL OLD FSUB SPL Ha.
  pose proof (af_live_range RT AF S mc p k HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB. pose proof (client_static_lo a H) as HL. lia.
  - destruct H as (q & j & Hin & Hq). destruct (OLD q j Hin) as [Hin' NE].
    pose proof (live_apart RT AF S mc p k q j HA INL Hin' ltac:(intros E; apply NE; symmetry; exact E)) as D. lia.
  - destruct H as (f & kk & Hin & Hf). apply FSUB in Hin.
    pose proof (af_frames_range RT AF S mc f kk HA Hin) as (_ & _ & _ & FLV). specialize (FLV p k INL). lia.
  - destruct H as (f & kk & Hin & Hf). apply FSUB in Hin.
    pose proof (af_fshadow_apart RT AF S mc f kk HA Hin) as (SA1 & _). specialize (SA1 p k INL). lia.
Qed.
End Fresh.
