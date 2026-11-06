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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Pm_iface Pm_iface2 Pm_okit.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lrm_cons : forall p e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.
Lemma lrm_notin : forall p (l : list (Z * Z)), ~ In p (map fst l) -> live_remove p l = l.
Proof.
  intros p l. induction l as [|e l IH]; intros H; [reflexivity|]. rewrite lrm_cons.
  replace (fst e =? p) with false by (symmetry; apply Z.eqb_neq; intro E; apply H; left; exact E).
  f_equal. apply IH. intros Hx. apply H. right. exact Hx.
Qed.
Lemma lrm_app : forall p (l1 l2 : list (Z * Z)), live_remove p (l1 ++ l2) = live_remove p l1 ++ live_remove p l2.
Proof.
  intros p l1 l2. induction l1 as [|e l1 IH]; [reflexivity|]. cbn [app]. rewrite !lrm_cons.
  destruct (fst e =? p); [exact IH| cbn [app]; f_equal; exact IH].
Qed.
Lemma nodup_app_notin : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND Hx; [intros []|]. cbn [app] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
  intros [E|Hin]; [subst y; apply NI; apply in_or_app; right; exact Hx| exact (IH l2 x ND Hx Hin)].
Qed.
(* [comment removed for export] *)
Lemma lrm_mid : forall p n (l1 l2 : list (Z * Z)), List.NoDup (map fst (l1 ++ (p, n) :: l2)) -> live_remove p (l1 ++ (p, n) :: l2) = l1 ++ l2.
Proof.
  intros p n l1 l2 ND. rewrite map_app in ND. cbn [map fst] in ND.
  assert (N1 : ~ In p (map fst l1)) by (apply (nodup_app_notin _ _ p ND); left; reflexivity).
  assert (N2 : ~ In p (map fst l2)) by (apply List.NoDup_app_remove_l in ND; apply List.NoDup_cons_iff in ND; exact (proj1 ND)).
  rewrite lrm_app, lrm_cons. cbn [fst]. rewrite Z.eqb_refl. rewrite (lrm_notin p l1 N1), (lrm_notin p l2 N2). reflexivity.
Qed.
Lemma nodup_mid_remove : forall (p : Z) (l1 l2 : list Z), List.NoDup (l1 ++ p :: l2) -> List.NoDup (l1 ++ l2).
Proof. intros p l1 l2. apply List.NoDup_remove_1. Qed.

(* [comment removed for export] *)
Lemma pm_copy_live_remove_box : forall b n p v cv (L : list (Z * Z)),
  List.NoDup (map fst (pm_copy_live p v cv ((b, n) :: L))) -> live_remove b (pm_copy_live p v cv ((b, n) :: L)) = pm_copy_live p v cv L.
Proof.
  intros b n p v cv L ND. unfold pm_copy_live in *.
  set (l0 := if p_cmap v =? 0 then [] else [(c_arr cv, 4 * c_nalloc cv); (p_cmap v, 24)]) in *.
  change (l0 ++ (p_data v, rsize v) :: (p, 64) :: (b, n) :: L) with (l0 ++ ([(p_data v, rsize v); (p, 64)] ++ (b, n) :: L)) in *.
  rewrite app_assoc in *. rewrite (lrm_mid b n _ L ND). rewrite <- app_assoc. reflexivity.
Qed.
Lemma pm_copy_live_nodup_box : forall b n p v cv (L : list (Z * Z)),
  List.NoDup (map fst (pm_copy_live p v cv ((b, n) :: L))) -> List.NoDup (map fst (pm_copy_live p v cv L)).
Proof.
  intros b n p v cv L ND. unfold pm_copy_live in *.
  set (l0 := if p_cmap v =? 0 then [] else [(c_arr cv, 4 * c_nalloc cv); (p_cmap v, 24)]) in *.
  change (l0 ++ (p_data v, rsize v) :: (p, 64) :: (b, n) :: L) with (l0 ++ ([(p_data v, rsize v); (p, 64)] ++ (b, n) :: L)) in ND.
  rewrite app_assoc, map_app in ND. cbn [map fst] in ND. apply nodup_mid_remove in ND.
  change (l0 ++ (p_data v, rsize v) :: (p, 64) :: L) with (l0 ++ ([(p_data v, rsize v); (p, 64)] ++ L)).
  rewrite app_assoc, map_app. exact ND.
Qed.

Lemma lrm_head : forall p n (l : list (Z * Z)), List.NoDup (map fst ((p, n) :: l)) -> live_remove p ((p, n) :: l) = l.
Proof. intros p n l ND. exact (lrm_mid p n [] l ND). Qed.

(* [comment removed for export] *)
Lemma pm_copy_roundtrip : forall p v cv cv' (L : list (Z * Z)),
  List.NoDup (map fst (pm_copy_live p v cv L)) -> c_arr cv' = c_arr cv -> p_data v <> 0 -> (p_cmap v <> 0 -> c_arr cv <> 0) ->
  live_destroy p v cv' (pm_copy_live p v cv L) = L.
Proof.
  intros p v cv cv' L ND EA DNZ ANZ. unfold live_destroy, pm_copy_live, rm_opt in *. rewrite EA.
  replace (p_data v =? 0) with false by (symmetry; apply Z.eqb_neq; exact DNZ).
  destruct (Z.eqb_spec (p_cmap v) 0) as [CZ|CNZ]; cbv iota in *; cbn [app] in *.
  - change (0 =? 0) with true. cbv iota.
    rewrite (lrm_head (p_data v) (rsize v) _ ND). cbn [map fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [_ ND].
    exact (lrm_head p 64 L ND).
  - replace (c_arr cv =? 0) with false by (symmetry; apply Z.eqb_neq; exact (ANZ CNZ)).
    change ((c_arr cv, 4 * c_nalloc cv) :: (p_cmap v, 24) :: (p_data v, rsize v) :: (p, 64) :: L)
      with ([(c_arr cv, 4 * c_nalloc cv); (p_cmap v, 24)] ++ (p_data v, rsize v) :: (p, 64) :: L) in *.
    rewrite (lrm_mid (p_data v) (rsize v) _ _ ND). rewrite map_app in ND. cbn [map fst] in ND. apply nodup_mid_remove in ND. cbn [app] in *.
    assert (ND' : List.NoDup (map fst ((c_arr cv, 4 * c_nalloc cv) :: (p_cmap v, 24) :: (p, 64) :: L))) by exact ND.
    rewrite (lrm_head (c_arr cv) (4 * c_nalloc cv) _ ND'). cbn [map fst] in ND'. apply List.NoDup_cons_iff in ND'. destruct ND' as [_ ND'].
    assert (ND2 : List.NoDup (map fst ((p_cmap v, 24) :: (p, 64) :: L))) by exact ND'.
    rewrite (lrm_head (p_cmap v) 24 _ ND2). cbn [map fst] in ND2. apply List.NoDup_cons_iff in ND2. destruct ND2 as [_ ND2].
    exact (lrm_head p 64 L ND2).
Qed.

Lemma rm_opt_sub : forall p (l : list (Z * Z)) e, In e (rm_opt p l) -> In e l.
Proof. intros p l e He. unfold rm_opt in He. destruct (p =? 0); [exact He| exact (live_remove_sub l p e He)]. Qed.
Lemma live_destroy_sub : forall pix v cv (l : list (Z * Z)) e, In e (live_destroy pix v cv l) -> In e l.
Proof.
  intros pix v cv l e He. unfold live_destroy in He. apply live_remove_sub in He.
  apply rm_opt_sub in He. apply rm_opt_sub in He. apply rm_opt_sub in He. exact He.
Qed.

(* [comment removed for export] *)
Definition pix_chunks (pix : Z) (v : pixv) (cv : cmapv) : list (Z * Z) :=
  (pix, 64) :: (if p_data v =? 0 then [] else [(p_data v, rsize v)])
  ++ (if p_cmap v =? 0 then [] else [(p_cmap v, 24); (c_arr cv, 4 * c_nalloc cv)]).
Lemma pix_chunks_in : forall live (m : mem) pix v cv, pix_obj live m pix v cv -> forall e, In e (pix_chunks pix v cv) -> In e live.
Proof.
  intros live m pix v cv (_ & (PIN & _) & _ & HD & HCM) e He. unfold pix_chunks in He. destruct He as [<-|He]; [exact PIN|].
  apply in_app_or in He. destruct He as [He|He].
  - destruct (Z.eqb_spec (p_data v) 0) as [DZ|DNZ]; [destruct He|]. destruct He as [<-|[]].
    destruct HD as [DZ|((DIN & _) & _)]; [contradiction| exact DIN].
  - destruct (Z.eqb_spec (p_cmap v) 0) as [CZ|CNZ]; [destruct He|].
    destruct HCM as [CZ|((_ & (CIN & _) & (AIN & _) & _) & _)]; [contradiction|].
    destruct He as [<-|[<-|[]]]; [exact CIN| exact AIN].
Qed.
Lemma pix_obj_move : forall live live' (m m' : mem) pix v cv,
  pix_obj live m pix v cv -> (forall e, In e (pix_chunks pix v cv) -> In e live') ->
  keeps_live [(pix, 64)] m m' -> (p_cmap v <> 0 -> keeps_live [(p_cmap v, 24)] m m') -> pix_obj live' m' pix v cv.
Proof.
  intros live live' m m' pix v cv (C & (PIN & PR) & HOK & HD & HCM) SUB K1 K2. unfold pix_chunks in SUB.
  split; [| split; [split; [apply SUB; left; reflexivity| exact PR]| split; [exact HOK| split]]].
  - apply (keeps_live_cells [(pix, 64)] m m' pix 64 pix _ K1 ltac:(left; reflexivity)); [lia| cbn; lia| exact C].
  - destruct HD as [DZ|((DIN & DR) & DNE)]; [left; exact DZ| right]. split; [| exact DNE]. split; [| exact DR].
    apply SUB. right. apply in_or_app. left. destruct DR as (D0 & _).
    replace (p_data v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left; reflexivity.
  - destruct HCM as [CZ|(((pad & CC) & (CIN & CR) & (AIN & AR) & OKR) & NER)]; [left; exact CZ| right]. split; [| exact NER].
    assert (CNZ : p_cmap v <> 0) by (destruct CR as (C0 & _); lia).
    assert (E : (p_cmap v =? 0) = false) by (apply Z.eqb_neq; exact CNZ).
    split; [exists pad; apply (keeps_live_cells [(p_cmap v, 24)] m m' (p_cmap v) 24 (p_cmap v) _ (K2 CNZ) ltac:(left; reflexivity)); [lia| cbn; lia| exact CC]|].
    split; [split; [apply SUB; right; apply in_or_app; right; rewrite E; left; reflexivity| exact CR]|].
    split; [split; [apply SUB; right; apply in_or_app; right; rewrite E; right; left; reflexivity| exact AR]| exact OKR].
Qed.

(* [comment removed for export] *)
Definition ivls_in (W : list (Z * Z)) (l : list (Z * Z)) : Prop :=
  Forall (fun iv => exists q k, In (q, k) l /\ q <= fst iv /\ snd iv <= q + k) W.

(* [comment removed for export] *)
Definition pm_copy_new (p : Z) (v : pixv) (cv : cmapv) : list (Z * Z) :=
  (if p_cmap v =? 0 then [] else [(c_arr cv, 4 * c_nalloc cv); (p_cmap v, 24)]) ++ [(p_data v, rsize v); (p, 64)].
Lemma pm_copy_live_app : forall p v cv (L : list (Z * Z)), pm_copy_live p v cv L = pm_copy_new p v cv ++ L.
Proof. intros p v cv L. unfold pm_copy_live, pm_copy_new. rewrite <- app_assoc. reflexivity. Qed.
Lemma pm_copy_new_len : forall p v cv, (length (pm_copy_new p v cv) <= 4)%nat.
Proof. intros p v cv. unfold pm_copy_new. destruct (p_cmap v =? 0); cbn [length app]; lia. Qed.
Lemma pm_copy_new_pos : forall live (m : mem) p v cv, pix_obj live m p v cv -> p_data v <> 0 -> forall q n, In (q, n) (pm_copy_new p v cv) -> 0 < n.
Proof.
  intros live m p v cv (_ & _ & _ & HD & HCM) DNZ q n Hin. unfold pm_copy_new in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (Z.eqb_spec (p_cmap v) 0) as [CZ|CNZ]; [destruct Hin|].
    destruct HCM as [CZ|((_ & _ & (_ & _ & _ & AN) & _) & _)]; [contradiction|].
    destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
  - destruct HD as [DZ|((_ & _ & _ & DN) & _)]; [contradiction|]. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
Qed.
(* [comment removed for export] *)
Lemma pm_fp_in_new : forall p v cv, ivls_in (pm_fp v cv) (pm_copy_new p v cv).
Proof.
  intros p v cv. unfold ivls_in, pm_fp, pm_copy_new. destruct (p_cmap v =? 0); cbn [app].
  - constructor; [| constructor]. exists (p_data v), (rsize v). cbn [fst snd In]. split; [left; reflexivity| lia].
  - constructor; [| constructor; [| constructor; [| constructor]]].
    + exists (p_data v), (rsize v). cbn [fst snd In]. split; [right; right; left; reflexivity| lia].
    + exists (p_cmap v), 24. cbn [fst snd In]. split; [right; left; reflexivity| lia].
    + exists (c_arr cv), (4 * c_nalloc cv). cbn [fst snd In]. split; [left; reflexivity| lia].
Qed.
(* [comment removed for export] *)
Lemma pix_chunks_new : forall p v cv cv', c_arr cv' = c_arr cv -> c_nalloc cv' = c_nalloc cv ->
  forall e, In e (pix_chunks p v cv') -> In e (pm_copy_new p v cv).
Proof.
  intros p v cv cv' EA EN e He. unfold pix_chunks in He. unfold pm_copy_new. rewrite EA, EN in He.
  destruct He as [<-|He]; [apply in_or_app; right; right; left; reflexivity|]. apply in_app_or in He. destruct He as [He|He].
  - destruct (p_data v =? 0); [destruct He|]. destruct He as [<-|[]]. apply in_or_app. right. left. reflexivity.
  - apply in_or_app. left. destruct (p_cmap v =? 0); [destruct He|]. destruct He as [<-|[<-|[]]]; [right; left; reflexivity| left; reflexivity].
Qed.
Lemma box_obj_mono : forall live live' (m : mem) b x y w h, (forall e, In e live -> In e live') -> box_obj live m b x y w h -> box_obj live' m b x y w h.
Proof. intros live live' m b x y w h S (C & (BIN & R)). exact (conj C (conj (S _ BIN) R)). Qed.

Lemma ivls_in_mono : forall (W l l' : list (Z * Z)), ivls_in W l -> (forall e, In e l -> In e l') -> ivls_in W l'.
Proof.
  intros W l l' IV S. unfold ivls_in in *. apply Forall_forall. intros iv Hiv. rewrite Forall_forall in IV.
  destruct (IV iv Hiv) as (q & k & Hq & R). exists q, k. exact (conj (S _ Hq) R).
Qed.
Lemma outside_of_ivls : forall (W l : list (Z * Z)) x, ivls_in W l -> (forall q k, In (q, k) l -> ~ (q <= x < q + k)) -> outside W x.
Proof.
  intros W l x IV NL. induction W as [|[lo hi] W IH]; [exact I|]. cbn [outside].
  apply List.Forall_cons_iff in IV. destruct IV as [(q & k & Hq & L1 & L2) IV]. cbn [fst snd] in L1, L2.
  split; [pose proof (NL q k Hq); lia| exact (IH IV)].
Qed.

Section PmFKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma nodup_of_apart : forall l : list (Z * Z),
  (forall l1 p n l2 q k, l = l1 ++ (p, n) :: l2 -> In (q, k) (l1 ++ l2) -> p + n <= q \/ q + k <= p) ->
  (forall p n, In (p, n) l -> 0 < n) -> List.NoDup (map fst l).
Proof.
  induction l as [|[p n] l IH]; intros D P; cbn [map fst]; [constructor|]. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as ([q k] & E & Hq). cbn [fst] in E. subst q.
    pose proof (D [] p n l p k eq_refl Hq) as A. pose proof (P p n ltac:(left; reflexivity)). pose proof (P p k ltac:(right; exact Hq)). lia.
  - apply IH; [| intros q k Hq; apply (P q k); right; exact Hq].
    intros l1 q k l2 r j E Hr. apply (D ((p, n) :: l1) q k l2 r j); [rewrite E; reflexivity| right; exact Hr].
Qed.
Lemma live_nodup : forall Σ m, ART RT Σ m -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) -> List.NoDup (map fst (rt_live RT Σ)).
Proof using AF.
  intros Σ m HA P. apply nodup_of_apart; [| exact P]. intros l1 p n l2 q k E Hq. exact (af_live_disj RT AF Σ m p n q k l1 l2 HA E Hq).
Qed.

(* [comment removed for export] *)
Lemma inner_chunk_apart : forall Σ' (m : mem) p n live0 frs usp a,
  ART RT Σ' m -> In (p, n) (rt_live RT Σ') ->
  (forall e, In e live0 -> In e (rt_live RT Σ') /\ fst e <> p) -> (forall e, In e frs -> In e (rt_frames RT Σ')) ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m p n live0 frs usp a HA INL SUBL SUBF SPL Ha.
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp). destruct (SUBL _ Hin) as [Hin' NE]. cbn [fst] in NE.
    pose proof (live_apart2 RT AF Σ' m p n p' n' HA INL Hin' ltac:(congruence)) as D. lia.
  - destruct H as (f & k & Hin & Hf). apply SUBF in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). apply SUBF in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

(* [comment removed for export] *)
Lemma chunk_outside_frame : forall Σ (m : mem) fr k q n lo hi a,
  ART RT Σ m -> In (fr, k) (rt_frames RT Σ) -> fr <= lo -> hi <= fr + fs_size k ->
  In (q, n) (rt_live RT Σ) -> q <= a < q + n -> ~ (lo <= a < hi).
Proof using AF.
  intros Σ m fr k q n lo hi a HA FIN L1 L2 QIN Ha.
  pose proof (af_frames_range RT AF Σ m fr k HA FIN) as (_ & _ & _ & FLV). specialize (FLV q n QIN). lia.
Qed.

(* [comment removed for export] *)
Lemma live_apart_app : forall Σ (m : mem) l1 l2 q k p n, ART RT Σ m -> rt_live RT Σ = l1 ++ l2 -> In (q, k) l1 -> In (p, n) l2 ->
  q + k <= p \/ p + n <= q.
Proof using AF.
  intros Σ m l1 l2 q k p n HA E H1 H2. destruct (in_split _ _ H1) as (a & b & E1). subst l1. rewrite <- app_assoc in E. cbn [app] in E.
  apply (af_live_disj RT AF Σ m q k p n a (b ++ l2) HA E). apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.
(* [comment removed for export] *)
Lemma outside_of_tail : forall Σ (m : mem) l1 l2 W p n x, ART RT Σ m -> rt_live RT Σ = l1 ++ l2 -> ivls_in W l1 ->
  In (p, n) l2 -> p <= x < p + n -> outside W x.
Proof using AF.
  intros Σ m l1 l2 W p n x HA E IV H2 Hx. induction W as [|[lo hi] W IH]; [exact I|]. cbn [outside].
  apply List.Forall_cons_iff in IV. destruct IV as [(q & k & Hq & L1 & L2) IV]. cbn [fst snd] in L1, L2. split; [| exact (IH IV)].
  pose proof (live_apart_app Σ m l1 l2 q k p n HA E Hq H2). lia.
Qed.
(* [comment removed for export] *)
Lemma tail_client_apart : forall Σ' (m : mem) l1 l2 live0 frs usp a q k,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ l2 -> In (q, k) l1 -> (forall e, In e live0 -> In e l2) ->
  (forall e, In e frs -> In e (rt_frames RT Σ')) -> rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < q \/ q + k <= a.
Proof using AF.
  intros Σ' m l1 l2 live0 frs usp a q k HA E Hq SUBL SUBF SPL Ha.
  assert (INL : In (q, k) (rt_live RT Σ')) by (rewrite E; apply in_or_app; left; exact Hq).
  pose proof (af_live_range RT AF Σ' m q k HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E0|Hin]; [injection E0 as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp). pose proof (live_apart_app Σ' m l1 l2 q k p' n' HA E Hq (SUBL _ Hin)) as D. lia.
  - destruct H as (f & kk & Hin & Hf). apply SUBF in Hin.
    pose proof (af_frames_range RT AF Σ' m f kk HA Hin) as (_ & _ & _ & FLV). specialize (FLV q k INL). lia.
  - destruct H as (f & kk & Hin & Hf). apply SUBF in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f kk HA Hin) as (SA1 & _). specialize (SA1 q k INL). lia.
Qed.
Lemma tail_client_outside : forall Σ' (m : mem) l1 l2 live0 frs usp a W,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ l2 -> ivls_in W l1 -> (forall e, In e live0 -> In e l2) ->
  (forall e, In e frs -> In e (rt_frames RT Σ')) -> rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> outside W a.
Proof using AF.
  intros Σ' m l1 l2 live0 frs usp a W HA E IV SUBL SUBF SPL Ha. induction W as [|[lo hi] W IH]; [exact I|]. cbn [outside].
  apply List.Forall_cons_iff in IV. destruct IV as [(q & k & Hq & L1 & L2) IV]. cbn [fst snd] in L1, L2. split; [| exact (IH IV)].
  pose proof (tail_client_apart Σ' m l1 l2 live0 frs usp a q k HA E Hq SUBL SUBF SPL Ha). lia.
Qed.

(* [comment removed for export] *)
Lemma live_not_stack : forall Σ (m : mem) q k x, ART RT Σ m -> In (q, k) (rt_live RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= x -> ~ (q <= x < q + k).
Proof using AF. intros Σ m q k x HA Hin Hx. pose proof (af_live_range RT AF Σ m q k HA Hin) as (_ & R & _). lia. Qed.
Lemma live_not_fframe : forall Σ (m : mem) f kk q k x, ART RT Σ m -> In (f, kk) (rt_frames RT Σ) -> In (q, k) (rt_live RT Σ) ->
  f <= x < f + fs_size kk -> ~ (q <= x < q + k).
Proof using AF. intros Σ m f kk q k x HA FIN Hin Hx. pose proof (af_frames_range RT AF Σ m f kk HA FIN) as (_ & _ & _ & FLV). specialize (FLV q k Hin). lia. Qed.
Lemma live_not_fshadow : forall Σ (m : mem) f kk q k x, ART RT Σ m -> In (f, kk) (rt_frames RT Σ) -> In (q, k) (rt_live RT Σ) ->
  shad f <= x < shad (f + fs_size kk) -> ~ (q <= x < q + k).
Proof using AF. intros Σ m f kk q k x HA FIN Hin Hx. pose proof (af_fshadow_apart RT AF Σ m f kk HA FIN) as (SA & _). specialize (SA q k Hin). lia. Qed.
Lemma agree_cells_fp : forall Σ (m : mem) lv frs sp W (ma mb : mem) A cs,
  ART RT Σ m -> ivls_in W (rt_live RT Σ) ->
  agree_on (fun a => aclient lv frs sp a /\ outside W a) ma mb -> rw_cells asegs ma A cs ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient lv frs sp x /\ forall q k, In (q, k) (rt_live RT Σ) -> ~ (q <= x < q + k)) ->
  rw_cells asegs mb A cs.
Proof using AF.
  intros Σ m lv frs sp W ma mb A cs HA IV AG H SIDE. apply (rw_cells_agree_nw asegs ma mb A cs H).
  eapply agree_sub; [exact AG|]. cbv beta. intros x Hx. destruct (SIDE x Hx) as [S1 S2].
  split; [exact S1| exact (outside_of_ivls W _ x IV S2)].
Qed.
End PmFKit.
