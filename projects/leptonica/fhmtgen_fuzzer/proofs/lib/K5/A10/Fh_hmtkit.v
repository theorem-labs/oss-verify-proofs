(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface LeptC_kit Lept_objkit Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition gop (b : bool) (p : Z) (l : list (Z * Z)) : list (Z * Z) := if b then l else live_remove p l.
Definition app_ops (ops : list (bool * Z)) (l : list (Z * Z)) : list (Z * Z) := fold_right (fun o acc => gop (fst o) (snd o) acc) l ops.
Definition ld_ops (pix : Z) (v : pixv) (cv : cmapv) : list (bool * Z) :=
  [(false, pix); (p_cmap v =? 0, p_cmap v); ((if p_cmap v =? 0 then 0 else c_arr cv) =? 0, if p_cmap v =? 0 then 0 else c_arr cv); (p_data v =? 0, p_data v)].
Lemma live_destroy_ops : forall pix v cv l, live_destroy pix v cv l = app_ops (ld_ops pix v cv) l.
Proof. intros. reflexivity. Qed.

Lemma gop_comm : forall b p c q l, gop b p (gop c q l) = gop c q (gop b p l).
Proof. intros b p c q l. unfold gop. destruct b, c; try reflexivity. apply live_remove_comm. Qed.
Lemma gop_app_ops : forall b p ops l, gop b p (app_ops ops l) = app_ops ops (gop b p l).
Proof.
  intros b p ops l. induction ops as [|[c q] ops IH]; [reflexivity|]. cbn [app_ops fold_right fst snd].
  change (fold_right (fun o acc => gop (fst o) (snd o) acc) ?x ops) with (app_ops ops x). rewrite gop_comm, IH. reflexivity.
Qed.
Lemma app_ops_comm : forall A B l, app_ops A (app_ops B l) = app_ops B (app_ops A l).
Proof.
  induction A as [|[b p] A IH]; intros B l; [reflexivity|]. cbn [app_ops fold_right fst snd].
  change (fold_right (fun o acc => gop (fst o) (snd o) acc) ?x A) with (app_ops A x). rewrite IH, gop_app_ops. reflexivity.
Qed.
Lemma live_destroy_comm : forall p v cv q w cw l,
  live_destroy p v cv (live_destroy q w cw l) = live_destroy q w cw (live_destroy p v cv l).
Proof. intros. rewrite !live_destroy_ops. apply app_ops_comm. Qed.

(* [comment removed for export] *)
Lemma ld_sub : forall pix v cv (l l' : list (Z * Z)), live_destroy pix v cv l' = l -> forall e, In e l -> In e l'.
Proof. intros pix v cv l l' E e He. rewrite <- E in He. exact (proj1 (live_destroy_In _ _ _ _ _ He)). Qed.
Lemma ld_incl : forall pix v cv (l : list (Z * Z)) e, In e (live_destroy pix v cv l) -> In e l.
Proof. intros pix v cv l e He. exact (proj1 (live_destroy_In _ _ _ _ _ He)). Qed.

(* [comment removed for export] *)
Lemma live_remove_len : forall p (l : list (Z * Z)), List.NoDup (map fst l) -> (length l <= length (live_remove p l) + 1)%nat.
Proof.
  intros p. induction l as [|[a n] l IH]; intros ND; [cbn; lia|].
  cbn [map fst] in ND. inversion ND as [|? ? NI ND']; subst.
  destruct (Z.eq_dec a p) as [E|NE].
  - subst a. rewrite live_remove_head. rewrite live_remove_fresh; [cbn [length]; lia|].
    intros e He E. apply NI. apply in_map_iff. exists e. split; [exact E| exact He].
  - rewrite (live_remove_other p a n l NE). cbn [length]. specialize (IH ND'). lia.
Qed.
Lemma live_remove_nodup : forall p (l : list (Z * Z)), List.NoDup (map fst l) -> List.NoDup (map fst (live_remove p l)).
Proof.
  intros p. induction l as [|[a n] l IH]; intros ND; [exact ND|].
  cbn [map fst] in ND. inversion ND as [|? ? NI ND']; subst.
  destruct (Z.eq_dec a p) as [E|NE].
  - subst a. rewrite live_remove_head. exact (IH ND').
  - rewrite (live_remove_other p a n l NE). cbn [map fst]. constructor; [| exact (IH ND')].
    intros C. apply NI. apply in_map_iff in C. destruct C as (y & Ey & Hy). apply in_map_iff. exists y. split; [exact Ey| exact (live_remove_sub l p y Hy)].
Qed.
Lemma app_ops_len : forall ops (l : list (Z * Z)), List.NoDup (map fst l) ->
  List.NoDup (map fst (app_ops ops l)) /\ (length l <= length (app_ops ops l) + length ops)%nat.
Proof.
  induction ops as [|[b p] ops IH]; intros l ND; [split; [exact ND| cbn; lia]|].
  cbn [app_ops fold_right fst snd length]. change (fold_right (fun o acc => gop (fst o) (snd o) acc) l ops) with (app_ops ops l).
  destruct (IH l ND) as [ND1 L1]. unfold gop. destruct b.
  - split; [exact ND1| lia].
  - split; [exact (live_remove_nodup p _ ND1)|]. pose proof (live_remove_len p _ ND1). lia.
Qed.
Lemma live_destroy_len : forall pix v cv (l : list (Z * Z)), List.NoDup (map fst l) ->
  Z.of_nat (length l) <= Z.of_nat (length (live_destroy pix v cv l)) + 4.
Proof. intros pix v cv l ND. rewrite live_destroy_ops. destruct (app_ops_len (ld_ops pix v cv) l ND) as [_ L]. cbn [ld_ops length] in L. lia. Qed.

(* [comment removed for export] *)
Lemma pix_obj_carry_gen : forall (live live' : list (Z * Z)) (m m' : mem) pix v cv,
  pix_obj live m pix v cv -> keeps_live live m m' -> (forall e, In e live -> In e live') -> pix_obj live' m' pix v cv.
Proof. intros live live' m m' pix v cv PO K SUB. exact (pix_obj_mono live live' m' pix v cv SUB (pix_obj_keep live m m' pix v cv K PO)). Qed.

(* [comment removed for export] *)
Definition pchunks (pix : Z) (v : pixv) (cv : cmapv) : list (Z * Z) :=
  (pix, 64) :: (if p_data v =? 0 then [] else [(p_data v, rsize v)])
  ++ (if p_cmap v =? 0 then [] else [(p_cmap v, 24); (c_arr cv, 4 * c_nalloc cv)]).
Definition apart (p : Z) (v : pixv) (cv : cmapv) (q : Z) (w : pixv) (cw : cmapv) : Prop :=
  forall e c, In e (pchunks p v cv) -> In c (pchunks q w cw) -> fst e <> fst c.
Lemma apart_sym : forall p v cv q w cw, apart p v cv q w cw -> apart q w cw p v cv.
Proof. intros p v cv q w cw A e c He Hc E. exact (A c e Hc He (eq_sym E)). Qed.

Lemma pix_obj_pchunks : forall (l : list (Z * Z)) (m : mem) pix v cv, pix_obj l m pix v cv ->
  forall e, In e (pchunks pix v cv) -> In e l /\ 0 < fst e.
Proof.
  intros l m pix v cv (_ & (PIN & P0 & _) & _ & PD & PCM) e He. unfold pchunks in He. cbn [In app] in He.
  destruct He as [<-|He]; [cbn [fst]; split; [exact PIN| exact P0]|]. apply in_app_or in He. destruct He as [He|He].
  - destruct (p_data v =? 0) eqn:E; [destruct He|]. cbn [In] in He. destruct He as [<-|[]]. apply Z.eqb_neq in E.
    destruct PD as [Z0|((DIN & D0 & _) & _)]; [contradiction|]. cbn [fst]. split; [exact DIN| exact D0].
  - destruct (p_cmap v =? 0) eqn:E; [destruct He|]. apply Z.eqb_neq in E.
    destruct PCM as [Z0|((_ & (CIN & C0 & _) & (AIN & A0 & _) & _) & _)]; [contradiction|].
    cbn [In] in He. destruct He as [<-|[<-|[]]]; cbn [fst]; split; assumption.
Qed.

(* [comment removed for export] *)
Lemma ld_notin : forall pix v cv (l : list (Z * Z)) e, In e (live_destroy pix v cv l) -> 0 < fst e ->
  forall c, In c (pchunks pix v cv) -> fst e <> fst c.
Proof.
  intros pix v cv l e He E0 c Hc. destruct (live_destroy_In _ _ _ _ _ He) as (_ & N1 & N2 & N3).
  unfold pchunks in Hc. cbn [In app] in Hc. destruct Hc as [<-|Hc]; [exact N1|]. apply in_app_or in Hc. destruct Hc as [Hc|Hc].
  - destruct (p_data v =? 0) eqn:E; [destruct Hc|]. apply Z.eqb_neq in E. cbn [In] in Hc. destruct Hc as [<-|[]]. exact (N2 E).
  - destruct (p_cmap v =? 0) eqn:E; [destruct Hc|]. apply Z.eqb_neq in E. destruct (N3 E) as [N4 N5].
    cbn [In] in Hc. destruct Hc as [<-|[<-|[]]]; cbn [fst]; [exact N4|].
    destruct (Z.eq_dec (c_arr cv) 0) as [Z0|NZ]; [rewrite Z0; lia| exact (N5 NZ)].
Qed.
(* [comment removed for export] *)
Lemma ld_in : forall pix v cv (l : list (Z * Z)) e, In e l -> (forall c, In c (pchunks pix v cv) -> fst e <> fst c) ->
  In e (live_destroy pix v cv l).
Proof.
  intros pix v cv l e He NE. unfold live_destroy.
  assert (R : forall p (l0 : list (Z * Z)), In e l0 -> (p <> 0 -> fst e <> p) -> In e (rm_opt p l0)).
  { intros p l0 H0 H1. unfold rm_opt. destruct (p =? 0) eqn:E; [exact H0|]. apply Z.eqb_neq in E. exact (live_remove_keep l0 p e H0 (H1 E)). }
  apply live_remove_keep; [| exact (NE (pix, 64) ltac:(unfold pchunks; left; reflexivity))].
  apply R; [apply R; [apply R; [exact He|]|]|].
  - intros NZ. apply (NE (p_data v, rsize v)). unfold pchunks. right. apply in_or_app. left.
    replace (p_data v =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. reflexivity.
  - destruct (p_cmap v =? 0) eqn:E; [intros C; contradiction|]. intros NZ. apply (NE (c_arr cv, 4 * c_nalloc cv)). unfold pchunks. right. apply in_or_app. right.
    rewrite E. right. left. reflexivity.
  - intros NZ. apply (NE (p_cmap v, 24)). unfold pchunks. right. apply in_or_app. right.
    replace (p_cmap v =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma apart_of_alloc : forall (l1 l2 : list (Z * Z)) (m1 : mem) p v cv q w cw,
  pix_obj l1 m1 p v cv -> live_destroy q w cw l2 = l1 -> apart p v cv q w cw.
Proof.
  intros l1 l2 m1 p v cv q w cw PO E e c He Hc. destruct (pix_obj_pchunks l1 m1 p v cv PO e He) as [HI H0].
  rewrite <- E in HI. exact (ld_notin q w cw l2 e HI H0 c Hc).
Qed.

(* [comment removed for export] *)
Lemma chunk_ld : forall pix v cv (l : list (Z * Z)) a n, chunk l a n -> (forall c, In c (pchunks pix v cv) -> a <> fst c) -> chunk (live_destroy pix v cv l) a n.
Proof. intros pix v cv l a n (HI & R) NE. split; [| exact R]. apply ld_in; [exact HI| exact NE]. Qed.
Lemma pix_obj_ld : forall (l : list (Z * Z)) (m : mem) p v cv q w cw,
  pix_obj l m q w cw -> apart q w cw p v cv -> pix_obj (live_destroy p v cv l) m q w cw.
Proof.
  intros l m p v cv q w cw PO AP. pose proof PO as (PXC & PCH & HOK & PD & PCM).
  assert (IQ : forall e, In e (pchunks q w cw) -> forall c, In c (pchunks p v cv) -> fst e <> fst c) by (intros e He c Hc; exact (AP e c He Hc)).
  split; [exact PXC|]. split; [apply chunk_ld; [exact PCH| exact (IQ (q, 64) ltac:(unfold pchunks; left; reflexivity))]|]. split; [exact HOK|]. split.
  - destruct PD as [Z0|(DCH & DNE)]; [left; exact Z0| right]. split; [| exact DNE].
    assert (NZ : p_data w <> 0) by (destruct DCH as (_ & D0 & _); lia).
    apply chunk_ld; [exact DCH|]. apply (IQ (p_data w, rsize w)). unfold pchunks. right. apply in_or_app. left.
    replace (p_data w =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. reflexivity.
  - destruct PCM as [Z0|((CMC & CCH & ACH & R) & NN)]; [left; exact Z0| right]. split; [| exact NN].
    assert (NZ : p_cmap w <> 0) by (destruct CCH as (_ & C0 & _); lia).
    split; [exact CMC|]. split; [| split; [| exact R]].
    + apply chunk_ld; [exact CCH|]. apply (IQ (p_cmap w, 24)). unfold pchunks. right. apply in_or_app. right.
      replace (p_cmap w =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). left. reflexivity.
    + apply chunk_ld; [exact ACH|]. apply (IQ (c_arr cw, 4 * c_nalloc cw)). unfold pchunks. right. apply in_or_app. right.
      replace (p_cmap w =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma live_remove_le : forall p (l : list (Z * Z)), (length (live_remove p l) <= length l)%nat.
Proof.
  intros p. induction l as [|[a n] l IH]; [cbn; lia|]. destruct (Z.eq_dec a p) as [E|NE].
  - subst a. rewrite live_remove_head. cbn [length]. lia.
  - rewrite (live_remove_other p a n l NE). cbn [length]. lia.
Qed.
Lemma live_destroy_le : forall pix v cv (l : list (Z * Z)), Z.of_nat (length (live_destroy pix v cv l)) <= Z.of_nat (length l).
Proof.
  intros pix v cv l. rewrite live_destroy_ops. generalize (ld_ops pix v cv). intros ops.
  induction ops as [|[b p] ops IH]; [cbn; lia|]. cbn [app_ops fold_right fst snd].
  change (fold_right (fun o acc => gop (fst o) (snd o) acc) l ops) with (app_ops ops l). unfold gop. destruct b; [exact IH|].
  pose proof (live_remove_le p (app_ops ops l)). lia.
Qed.

(* [comment removed for export] *)
Lemma ld_transfer : forall pix v cv (l l' : list (Z * Z)) e, In e (live_destroy pix v cv l') -> 0 < fst e -> In e l ->
  In e (live_destroy pix v cv l).
Proof. intros pix v cv l l' e He E0 Hl. apply ld_in; [exact Hl|]. exact (ld_notin pix v cv l' e He E0). Qed.
