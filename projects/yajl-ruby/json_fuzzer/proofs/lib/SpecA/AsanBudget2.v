(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep
     AsanWf1 AsanFrame AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf7 AsanWf8 AsanWf9 AsanWf10 AsanClient AsanBudget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Fixpoint countZ {A} (f : A -> bool) (l : list A) : Z :=
  match l with [] => 0 | x :: t => (if f x then 1 else 0) + countZ f t end.
Lemma countZ_app : forall {A} (f : A -> bool) l1 l2, countZ f (l1 ++ l2) = countZ f l1 + countZ f l2.
Proof. induction l1; intros; cbn; [reflexivity|]. rewrite IHl1. lia. Qed.
Lemma countZ_nonneg : forall {A} (f : A -> bool) l, 0 <= countZ f l.
Proof. induction l; cbn; [lia|]. destruct (f a); lia. Qed.
Lemma countZ_perm : forall {A} (f : A -> bool) l1 l2, Permutation l1 l2 -> countZ f l1 = countZ f l2.
Proof. intros A f l1 l2 P. induction P; cbn; try lia. Qed.
Lemma countZ_le_len : forall {A} (f : A -> bool) l, countZ f l <= zlen l.
Proof. induction l; unfold zlen in *; cbn; [lia|]. destruct (f a); cbn [length] in *; lia. Qed.

Fixpoint sumZ {A} (f : A -> Z) (l : list A) : Z :=
  match l with [] => 0 | x :: t => f x + sumZ f t end.
Lemma sumZ_app : forall {A} (f : A -> Z) l1 l2, sumZ f (l1 ++ l2) = sumZ f l1 + sumZ f l2.
Proof. induction l1; intros; cbn; [reflexivity|]. rewrite IHl1. lia. Qed.
Lemma sumZ_perm : forall {A} (f : A -> Z) l1 l2, Permutation l1 l2 -> sumZ f l1 = sumZ f l2.
Proof. intros A f l1 l2 P. induction P; cbn; try lia. Qed.
Lemma sumZ_nonneg : forall {A} (f : A -> Z) l, (forall x, In x l -> 0 <= f x) -> 0 <= sumZ f l.
Proof. induction l; cbn; intros H; [lia|]. pose proof (H a ltac:(left; reflexivity)). specialize (IHl ltac:(intros; apply H; right; assumption)). lia. Qed.
Lemma sumZ_le : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x <= g x) -> sumZ f l <= sumZ g l.
Proof. induction l; cbn; intros H; [lia|]. pose proof (H a ltac:(left; reflexivity)). specialize (IHl ltac:(intros; apply H; right; assumption)). lia. Qed.
Lemma sumZ_map : forall {A B} (f : B -> Z) (g : A -> B) l, sumZ f (map g l) = sumZ (fun x => f (g x)) l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.
Lemma sumZ_ext : forall {A} (f g : A -> Z) l, (forall x, In x l -> f x = g x) -> sumZ f l = sumZ g l.
Proof. induction l; cbn; intros H; [reflexivity|]. rewrite (H a) by (left; reflexivity). rewrite IHl by (intros; apply H; right; assumption). reflexivity. Qed.
Lemma fold_right_sumZ : forall {A} (f : A -> Z) l, fold_right (fun x acc => f x + acc) 0 l = sumZ f l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sumZ_incl_nodup : forall {A} (f : A -> Z) l l', List.NoDup l -> (forall x, In x l -> In x l') ->
  (forall x, In x l' -> 0 <= f x) -> sumZ f l <= sumZ f l'.
Proof.
  intros A f l. induction l as [|x l IH]; intros l' ND INCL POS; cbn.
  - apply sumZ_nonneg. exact POS.
  - pose proof (INCL x ltac:(left; reflexivity)) as Hx. destruct (in_split _ _ Hx) as (l1 & l2 & ->).
    rewrite (sumZ_perm f (l1 ++ x :: l2) (x :: l1 ++ l2)) by (apply Permutation_sym, Permutation_middle). cbn.
    inversion ND; subst.
    assert (IH' : sumZ f l <= sumZ f (l1 ++ l2)).
    { apply IH; [assumption| |].
      - intros y Hy. pose proof (INCL y ltac:(right; exact Hy)) as H'. apply in_app_iff in H'. apply in_app_iff.
        destruct H' as [H'|[<-|H']]; [left; exact H'| exfalso; auto| right; exact H'].
      - intros y Hy. apply POS. apply in_app_iff in Hy. apply in_app_iff. destruct Hy; [left| right; right]; assumption. }
    lia.
Qed.

Lemma zlen_app : forall {A} (l1 l2 : list A), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros; unfold zlen; rewrite length_app; lia. Qed.
Lemma zlen_nil : forall {A}, zlen (@nil A) = 0. Proof. reflexivity. Qed.
Lemma zlen_cons : forall {A} (x : A) l, zlen (x :: l) = 1 + zlen l. Proof. intros; unfold zlen; cbn [length]; lia. Qed.
Lemma zlen_nonneg : forall {A} (l : list A), 0 <= zlen l. Proof. intros; unfold zlen; lia. Qed.

(* [comment removed for export] *)
Definition fzero : Z -> Z := fun _ => 0.
Definition fadd (c k : Z) (F : Z -> Z) : Z -> Z := fun c' => if c' =? c then F c' + k else F c'.
Lemma fadd_eq : forall c k F, fadd c k F c = F c + k.
Proof. intros. unfold fadd. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma fadd_ne : forall c k F c', c' <> c -> fadd c k F c' = F c'.
Proof. intros. unfold fadd. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; auto). reflexivity. Qed.

Definition kNB : Z := 32896.          (* [comment removed for export] *)
Definition b24 (c : Z) : Z := if c =? kBatchClass then 1 else 0.

Section B2.
Variable E : aenv.
Local Notation SB := (ae_space_beg E).

Definition is_cls (c : Z) (p : Z * chunkmeta) : bool :=
  match cm_prim (snd p) with Some c' => c' =? c | None => false end.
(* [comment removed for export] *)
Definition nchunks (s : astate) (c : Z) : Z := countZ (is_cls c) (chunk_list s).
Definition carved_count (s : astate) (c : Z) : Z := rg_alloc_user (get_region s c) / class_size c.
Definition nfree (s : astate) (c : Z) : Z := zlen (rg_free (get_region s c)).
Definition ncache (s : astate) (c : Z) : Z := zlen (get_cache s c).
Definition nbatch (nd : Z) (s : astate) : Z := zlen (as_tq s) + zlen (as_gq s) + nd.

(* [comment removed for export] *)
Definition BIc_raw (r : region) (l : list Z) (nch ev np nb fc : Z) (c : Z) : Prop :=
  let carved := rg_alloc_user r / class_size c in
  0 <= rg_alloc_user r <= rg_mapped_user r /\ rg_mapped_user r <= kFreeArrayOffset /\ rg_alloc_user r mod class_size c = 0 /\ 0 <= rg_mapped_fa r
  /\ rg_mapped_fa r <= 4 * carved + kFreeArrayMapSize
  /\ rg_mapped_user r <= class_size c * (ev + 8 + b24 c * kNB) + kUserMapSize
  /\ carved = nch + zlen (rg_free r) + zlen l + b24 c * nb + fc
  /\ nch <= ev /\ 0 <= ev <= np /\ 0 <= fc /\ 0 <= nch
  /\ rg_mapped_user r <= rg_alloc_user r + kUserMapSize + kMaxSize.   (* [comment removed for export] *)
Definition BIc (nd : Z) (F : Z -> Z) (s : astate) (c : Z) : Prop :=
  BIc_raw (get_region s c) (get_cache s c) (nchunks s c) (everc s c) (as_nprim_ever s) (nbatch nd s) (F c) c.
Definition seccov (s : astate) (sc : secchunk) : Prop :=
  exists cb cm, as_chunks s !! cb = Some cm /\ cm_prim cm = None /\ cm_alloc_beg cm = sc_map_beg sc + kPageSize
               /\ sc_map_size sc = map_size (cm_n cm).
Definition BI (nd : Z) (F : Z -> Z) (s : astate) : Prop :=
  (forall c, 1 <= c <= kLargestClassID -> BIc nd F s c)
  /\ (forall cb cm, as_chunks s !! cb = Some cm -> 1 <= cm_n cm /\ match cm_prim cm with Some c => 1 <= c <= kLargestClassID | None => True end)
  /\ (forall b, In b (as_tq s ++ as_gq s) -> kBatchSize <= b_size b)
  /\ (forall sc, In sc (as_sec s) -> seccov s sc)
  /\ List.NoDup (map sc_map_beg (as_sec s))
  /\ 0 <= nd.
Definition binv (s : astate) : Prop := BI 0 fzero s.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nchunks_insert : forall s cb cm c, as_chunks s !! cb = None ->
  nchunks (upd_chunks (fun m => <[cb := cm]> m) s) c = nchunks s c + (if is_cls c (cb, cm) then 1 else 0).
Proof.
  intros s cb cm c H. unfold nchunks, chunk_list. cbn [as_chunks upd_chunks].
  rewrite (countZ_perm _ _ _ (map_to_list_insert (as_chunks s) cb cm H)). cbn [countZ]. lia.
Qed.
Lemma nchunks_delete : forall s cb cm c, as_chunks s !! cb = Some cm ->
  nchunks (upd_chunks (delete cb) s) c = nchunks s c - (if is_cls c (cb, cm) then 1 else 0).
Proof.
  intros s cb cm c H. unfold nchunks, chunk_list. cbn [as_chunks upd_chunks].
  rewrite <- (countZ_perm _ _ _ (map_to_list_delete (as_chunks s) cb cm H)). cbn [countZ]. lia.
Qed.
Lemma nchunks_flip : forall s cb cm cm' c, as_chunks s !! cb = Some cm -> cm_prim cm' = cm_prim cm ->
  nchunks (upd_chunks (fun m => <[cb := cm']> m) s) c = nchunks s c.
Proof.
  intros s cb cm cm' c H HP. unfold nchunks, chunk_list. cbn [as_chunks upd_chunks].
  rewrite <- (insert_delete_eq (as_chunks s) cb cm').
  rewrite (countZ_perm _ _ _ (map_to_list_insert (delete cb (as_chunks s)) cb cm' ltac:(apply lookup_delete_eq))).
  rewrite <- (countZ_perm _ _ _ (map_to_list_delete (as_chunks s) cb cm H)). cbn [countZ]. unfold is_cls. cbn [snd]. rewrite HP. lia.
Qed.
Lemma nchunks_nonneg : forall s c, 0 <= nchunks s c.
Proof. intros; unfold nchunks; apply countZ_nonneg. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bview_of (s : astate) :=
  (as_regions s, as_cache s, as_chunks s, as_tq s, as_gq s, as_sec s, as_nprim_ever s, as_everc s).
Definition VS (K : _) (s : astate) : Prop := bview_of s = K.

Lemma BI_view : forall nd F s s', bview_of s' = bview_of s -> BI nd F s -> BI nd F s'.
Proof.
  intros nd F s s' V H. unfold bview_of in V. injection V as V1 V2 V3 V4 V5 V6 V7 V8.
  unfold BI, BIc, seccov, carved_count, nfree, ncache, nbatch, nchunks, chunk_list, everc, get_region, get_cache in *.
  rewrite V1, V2, V3, V4, V5, V6, V7, V8. exact H.
Qed.
Lemma BI_Fext : forall nd F F' s, (forall c, F' c = F c) -> BI nd F s -> BI nd F' s.
Proof.
  intros nd F F' s HF (H1 & H2). split; [| exact H2]. intros c Hc. pose proof (H1 c Hc) as X. unfold BIc in *. rewrite !HF. exact X.
Qed.

(* [comment removed for export] *)
Definition FRM (s0 s' : astate) : Prop :=
  as_chunks s' = as_chunks s0 /\ as_tq s' = as_tq s0 /\ as_gq s' = as_gq s0 /\ as_sec s' = as_sec s0
  /\ as_nprim_ever s' = as_nprim_ever s0 /\ as_everc s' = as_everc s0.
(* [comment removed for export] *)
Definition RCX (c : Z) (r' : region) (l' : list Z) (s0 s' : astate) : Prop :=
  (forall c', get_region s' c' = if Z.eq_dec c' c then r' else get_region s0 c')
  /\ (forall c', get_cache s' c' = if Z.eq_dec c' c then l' else get_cache s0 c')
  /\ FRM s0 s'.

Lemma FRM_refl : forall s, FRM s s. Proof. intros; repeat split; reflexivity. Qed.
Lemma FRM_trans : forall a b c, FRM a b -> FRM b c -> FRM a c.
Proof. intros a b c (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). repeat split; congruence. Qed.
Lemma RCX_refl : forall c s, RCX c (get_region s c) (get_cache s c) s s.
Proof. intros c s. split; [| split; [| apply FRM_refl]]; intros c'; destruct (Z.eq_dec c' c) as [->|]; reflexivity. Qed.
Lemma RCX_trans : forall c r1 l1 r2 l2 s0 s1 s2, RCX c r1 l1 s0 s1 -> RCX c r2 l2 s1 s2 -> RCX c r2 l2 s0 s2.
Proof.
  intros c r1 l1 r2 l2 s0 s1 s2 (A1 & A2 & A3) (B1 & B2 & B3). split; [| split; [| eapply FRM_trans; eassumption]].
  - intros c'. rewrite B1. destruct (Z.eq_dec c' c); [reflexivity| rewrite A1; destruct (Z.eq_dec c' c); [contradiction| reflexivity]].
  - intros c'. rewrite B2. destruct (Z.eq_dec c' c); [reflexivity| rewrite A2; destruct (Z.eq_dec c' c); [contradiction| reflexivity]].
Qed.
(* [comment removed for export] *)
Lemma RCX_view : forall c r l s0 s s', bview_of s' = bview_of s -> RCX c r l s0 s -> RCX c r l s0 s'.
Proof.
  intros c r l s0 s s' V (A1 & A2 & A3). unfold bview_of in V. injection V as V1 V2 V3 V4 V5 V6 V7 V8.
  unfold RCX, FRM, get_region, get_cache in *. rewrite V1, V2, V3, V4, V5, V6, V7, V8. auto.
Qed.

(* [comment removed for export] *)
Lemma BI_local : forall nd F F' s0 s' c r' l', 1 <= c <= kLargestClassID -> BI nd F s0 -> RCX c r' l' s0 s' ->
  BIc_raw r' l' (nchunks s0 c) (everc s0 c) (as_nprim_ever s0) (nbatch nd s0) (F' c) c ->
  (forall c', c' <> c -> F' c' = F c') -> BI nd F' s'.
Proof.
  intros nd F F' s0 s' c r' l' Hc (B1 & B6 & B7 & B8 & B9 & ND) (R1 & R2 & (F1 & F2 & F3 & F4 & F5 & F6)) NEW HF.
  assert (NCH : forall c', nchunks s' c' = nchunks s0 c') by (intros; unfold nchunks, chunk_list; rewrite F1; reflexivity).
  assert (EVC : forall c', everc s' c' = everc s0 c') by (intros; unfold everc; rewrite F6; reflexivity).
  assert (NB : nbatch nd s' = nbatch nd s0) by (unfold nbatch; rewrite F2, F3; reflexivity).
  split; [| split; [| split; [| split; [| split; [| exact ND]]]]].
  - intros c' Hc'. unfold BIc. rewrite R1, R2, NCH, EVC, NB, F5. destruct (Z.eq_dec c' c) as [->|NE]; [exact NEW|].
    rewrite (HF c' NE). exact (B1 c' Hc').
  - rewrite F1. exact B6.
  - rewrite F2, F3. exact B7.
  - rewrite F4. intros sc Hsc. destruct (B8 sc Hsc) as (cb & cm & H & X). exists cb, cm. rewrite F1. auto.
  - rewrite F4. exact B9.
Qed.

Ltac vs_same := lazymatch goal with H : VS ?K ?st |- VS ?K _ => exact H end.
Lemma store_alloc_vs : forall K c, presW (VS K) (store_alloc E c).
Proof. intros; unfold store_alloc, store_alloc_once. pw; try (unfold call_mmap_ordie; pw); vs_same. Qed.
Lemma depot_put_vs : forall K k, presW (VS K) (depot_put E k).
Proof. intros; unfold depot_put. pw; try apply store_alloc_vs; try (unfold call_mmap_ordie; pw); vs_same. Qed.
(* [comment removed for export] *)
Lemma depot_put_view : forall s0 k, hoareW (fun s => s = s0) (depot_put E k) (fun s' _ => bview_of s' = bview_of s0).
Proof. intros. apply (presW_from (fun a b => VS (bview_of a) b)); [intros a; reflexivity| apply depot_put_vs]. Qed.
Lemma poison_zero_view : forall s0 u L, hoareW (fun s => s = s0) (poison_zero u L) (fun s' _ => s' = s0).
Proof. intros. apply (poison_zero_W (fun s => s = s0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hoareW_checkK : forall {S} (P : astate -> Prop) b tag (k : AM S) Q,
  (b = true -> hoareW P k Q) -> hoareW P (abind (acheck b tag) (fun _ => k)) Q.
Proof.
  intros S P b tag k Q H. unfold acheck. destruct b.
  - eapply hoareW_bind; [apply hoareW_ret with (Q := fun s _ => P s); auto| intros []; apply H; reflexivity].
  - eapply hoareW_bind with (Q := fun _ _ => False); [apply hoareW_undef| intros [] s []].
Qed.

Definition rg_setfa (r : region) (x : Z) : region :=
  mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r) x (rg_n_allocated r) (rg_n_freed r).
Definition rg_setmu (r : region) (x : Z) : region :=
  mkRegion x (rg_alloc_user r) (rg_free r) (rg_mapped_fa r) (rg_n_allocated r) (rg_n_freed r).
Lemma rg_setfa_id : forall r, rg_setfa r (rg_mapped_fa r) = r. Proof. intros r; destruct r; reflexivity. Qed.
Lemma rg_setmu_id : forall r, rg_setmu r (rg_mapped_user r) = r. Proof. intros r; destruct r; reflexivity. Qed.

Lemma RCX_set_region : forall c r s, RCX c r (get_cache s c) s (set_region c r s).
Proof.
  intros c r s. split; [| split; [intros c'; rewrite get_cache_set_region; destruct (Z.eq_dec c' c) as [->|]; reflexivity| repeat split; reflexivity]].
  intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite get_set_region_eq; reflexivity| rewrite get_set_region_ne by auto; reflexivity].
Qed.
Lemma RCX_set_cache : forall c l s, RCX c (get_region s c) l s (set_cache c l s).
Proof.
  intros c l s. split; [| split; [| repeat split; reflexivity]].
  - intros c'. rewrite get_region_set_cache. destruct (Z.eq_dec c' c) as [->|]; reflexivity.
  - intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite get_set_cache_eq; reflexivity| rewrite get_set_cache_ne by auto; reflexivity].
Qed.
(* [comment removed for export] *)
Ltac rcx_region_only :=
  eapply RCX_view; [reflexivity|];
  first [ apply RCX_set_region
        | lazymatch goal with H : RCX ?c _ _ ?s0 ?s |- RCX ?c2 _ _ ?s02 (set_region ?c3 _ ?s2) =>
            eapply RCX_trans; [exact H|];
            lazymatch goal with |- RCX ?c4 ?r ?l ?s4 _ => replace l with (get_cache s4 c4); [apply RCX_set_region|] end end ].

Lemma ensure_cnt : forall s0 c nf,
  hoareW (fun s => s = s0) (ensure_free_array_space E c nf)
    (fun s' ok => exists fa', RCX c (rg_setfa (get_region s0 c) fa') (get_cache s0 c) s0 s'
        /\ rg_mapped_fa (get_region s0 c) <= fa' /\ (fa' = rg_mapped_fa (get_region s0 c) \/ fa' < 4 * nf + kFreeArrayMapSize)
        /\ (ok = true -> 4 * nf <= fa') /\ (ok = false -> fa' = rg_mapped_fa (get_region s0 c))).
Proof.
  intros s0 c nf. unfold ensure_free_array_space. apply hoareW_get_bind. intros s ->.
  set (r0 := get_region s0 c).
  destruct (rg_mapped_fa r0 <? 4 * nf) eqn:LT.
  - apply Z.ltb_lt in LT. apply hoareW_checkK. intros _.
    eapply hoareW_bind; [apply call_mmap_fixed_eq|]. intros ok. apply hoareW_pre. intros s ->.
    pose proof (round_up_ge (4 * nf) kFreeArrayMapSize ltac:(unfold kFreeArrayMapSize; lia)) as G1.
    pose proof (round_up_lt (4 * nf) kFreeArrayMapSize ltac:(unfold kFreeArrayMapSize; lia)) as G2.
    destruct ok.
    + apply hoareW_upd_bind. apply hoareW_ret. intros s (sx & -> & ->). exists (round_up (4 * nf) kFreeArrayMapSize).
      split; [| split; [lia| split; [lia| split; [lia| discriminate]]]]. rcx_region_only.
    + apply hoareW_ret. intros s ->. exists (rg_mapped_fa r0). rewrite rg_setfa_id. split; [apply RCX_refl|]. split; [lia|]. split; [left; reflexivity| split; [discriminate| reflexivity]].
  - apply Z.ltb_ge in LT. apply hoareW_ret. intros s ->. exists (rg_mapped_fa r0). rewrite rg_setfa_id. split; [apply RCX_refl|]. split; [lia|]. split; [lia|]. split; [lia| discriminate].
Qed.

Lemma nbatch_nonneg : forall nd s, 0 <= nd -> 0 <= nbatch nd s.
Proof. intros; unfold nbatch, zlen; lia. Qed.
Lemma b24_range : forall c, 0 <= b24 c <= 1.
Proof. intros; unfold b24; destruct (c =? kBatchClass); lia. Qed.

Lemma populate_cnt : forall nd F s0 c requested, 1 <= c <= kLargestClassID -> BI nd F s0 -> F c = 0 -> get_cache s0 c = [] ->
  0 <= requested -> nfree s0 c + requested <= hint c -> nbatch nd s0 <= kNB ->
  hoareW (fun s => s = s0) (populate_free_array E c requested)
    (fun s' _ => BI nd F s' /\ RCX c (get_region s' c) [] s0 s').
Proof.
  intros nd F s0 c requested Hc HBI HF HC Hreq Hhint HNB. unfold kLargestClassID in Hc.
  pose proof HBI as ORIG. destruct HBI as (B1 & B6 & B7 & B8 & B9 & ND).
  pose proof (B1 c ltac:(unfold kLargestClassID; lia)) as BC. unfold BIc, BIc_raw in BC. rewrite HC, HF in BC.
  replace (zlen (@nil Z)) with 0 in BC by reflexivity.
  set (r0 := get_region s0 c) in *.
  destruct BC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof (class_size_mod c Hc) as [_ SZ]. set (size := class_size c) in *.
  pose proof (hint_range c Hc) as HR. pose proof (nbatch_nonneg nd s0 ND) as NBp. pose proof (b24_range c) as B24.
  assert (ALE : rg_alloc_user r0 = size * (rg_alloc_user r0 / size)) by (apply Z.div_exact; lia).
  unfold nfree in Hhint. fold r0 in Hhint.
  assert (RS : requested * size <= kMaxSize).
  { pose proof (hint_size_bound c Hc) as [HS _]. fold size in HS. unfold kMaxSize. unfold zlen in Hhint.
    assert (requested * size <= hint c * size) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  unfold populate_free_array. apply hoareW_get_bind. intros s ->. fold r0. fold size.
  set (total := rg_alloc_user r0 + requested * size).
  assert (TOT : total = rg_alloc_user r0 + requested * size) by reflexivity.
  (* [comment removed for export] *)
  eapply hoareW_bind with (Q := fun s1 ok1 => exists mu', RCX c (rg_setmu r0 mu') [] s0 s1 /\ rg_mapped_user r0 <= mu' /\ mu' <= kFreeArrayOffset
                                    /\ (mu' = rg_mapped_user r0 \/ mu' < total + kUserMapSize)).
  { destruct (rg_mapped_user r0 <? total) eqn:LT.
    - apply Z.ltb_lt in LT. unfold acheck.
      destruct (rg_mapped_user r0 + round_up (total - rg_mapped_user r0) kUserMapSize <=? kFreeArrayOffset) eqn:CK.
      2:{ eapply hoareW_bind with (Q := fun _ _ => False); [apply hoareW_undef| intros [] s []]. }
      apply Z.leb_le in CK.
      eapply hoareW_bind; [apply hoareW_ret with (Q := fun s _ => s = s0); auto|]. intros []. apply hoareW_pre. intros s ->.
      eapply hoareW_bind; [apply call_mmap_fixed_eq|]. intros ok. apply hoareW_pre. intros s ->.
      pose proof (round_up_lt (total - rg_mapped_user r0) kUserMapSize ltac:(unfold kUserMapSize; lia)) as G2.
      pose proof (round_up_ge (total - rg_mapped_user r0) kUserMapSize ltac:(unfold kUserMapSize; lia)) as G1.
      destruct ok.
      + apply hoareW_upd_bind. apply hoareW_ret. intros s (sx & -> & ->). exists (rg_mapped_user r0 + round_up (total - rg_mapped_user r0) kUserMapSize).
        split; [| lia]. rewrite <- HC. rcx_region_only.
      + apply hoareW_ret. intros s ->. exists (rg_mapped_user r0). rewrite rg_setmu_id, <- HC. split; [apply RCX_refl| lia].
    - apply Z.ltb_ge in LT. apply hoareW_ret. intros s ->. exists (rg_mapped_user r0). rewrite rg_setmu_id, <- HC. split; [apply RCX_refl| lia]. }
  intros ok1. apply hoareW_pre. intros s1 (mu' & RC1 & MU1 & MU2 & MU3).
  assert (R1c : get_region s1 c = rg_setmu r0 mu') by (destruct RC1 as (X & _); rewrite X; destruct (Z.eq_dec c c); [reflexivity| contradiction]).
  (* [comment removed for export] *)
  assert (MUB : mu' <= size * (everc s0 c + 8 + b24 c * kNB) + kUserMapSize).
  { destruct MU3 as [->|LTm]; [exact A6|]. subst total.
    assert (rg_alloc_user r0 / size <= everc s0 c + zlen (rg_free r0) + b24 c * kNB) by nia.
    assert (rg_alloc_user r0 + requested * size <= size * (everc s0 c + 8 + b24 c * kNB)) by nia. lia. }
  assert (BI1 : BI nd F s1).
  { eapply (BI_local nd F F s0 s1 c); [unfold kLargestClassID; lia| exact ORIG| exact RC1| | auto].
    unfold BIc_raw. cbn -[Z.mul Z.add Z.div Z.modulo class_size b24 kNB kUserMapSize kFreeArrayMapSize kFreeArrayOffset kMaxSize zlen]. fold size. rewrite HF.
    replace (zlen (@nil Z)) with 0 by reflexivity. repeat split; try lia. }
  destruct (negb ok1); [apply hoareW_ret; intros s ->; split; [exact BI1| rewrite R1c; exact RC1]|].
  apply hoareW_get_bind. intros s ->. rewrite R1c. cbn [rg_mapped_user rg_alloc_user rg_num_freed rg_free rg_setmu].
  set (new := (mu' - rg_alloc_user r0) / size).
  assert (NEW0 : 0 <= new) by (subst new; apply Z.div_pos; lia).
  assert (NEW1 : new * size <= mu' - rg_alloc_user r0) by (subst new; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  assert (NEW2 : mu' - rg_alloc_user r0 < size * Z.succ new) by (subst new; apply Z.mul_succ_div_gt; lia).
  eapply hoareW_bind; [apply ensure_cnt|]. intros ok2. apply hoareW_pre. intros s2 (fa' & RC2 & FA1 & FA2 & FA3 & FA4).
  rewrite R1c in RC2, FA1, FA2. cbn [rg_mapped_fa rg_setmu rg_setfa rg_mapped_user rg_alloc_user rg_free rg_n_allocated rg_n_freed] in RC2, FA1, FA2.
  replace (get_cache s1 c) with (@nil Z) in RC2 by (destruct RC1 as (_ & X & _); rewrite X; destruct (Z.eq_dec c c); [reflexivity| contradiction]).
  pose proof (RCX_trans _ _ _ _ _ _ _ _ RC1 RC2) as RC02.
  assert (R2c : get_region s2 c = mkRegion mu' (rg_alloc_user r0) (rg_free r0) fa' (rg_n_allocated r0) (rg_n_freed r0))
    by (destruct RC2 as (X & _); rewrite X; destruct (Z.eq_dec c c); [reflexivity| contradiction]).
  assert (FAB : fa' <= 4 * (rg_alloc_user r0 / size + new) + kFreeArrayMapSize).
  { destruct FA2 as [->|LTf]; [lia|]. unfold rg_num_freed in LTf. cbn [rg_free rg_setmu] in LTf. change (Z.of_nat (length (rg_free r0))) with (zlen (rg_free r0)) in LTf. nia. }
  destruct ok2; cbn [negb].
  2:{ specialize (FA4 eq_refl). rewrite R1c in FA4. cbn [rg_mapped_fa rg_setmu] in FA4. apply hoareW_ret; intros s ->. split; [| rewrite R2c; exact RC02].
      eapply (BI_local nd F F s0 s2 c); [unfold kLargestClassID; lia| exact ORIG| exact RC02| | auto].
      unfold BIc_raw. cbn -[Z.mul Z.add Z.div Z.modulo class_size b24 kNB kUserMapSize kFreeArrayMapSize kFreeArrayOffset kMaxSize zlen]. fold size. rewrite HF.
      replace (zlen (@nil Z)) with 0 by reflexivity. repeat split; try lia. }
  apply hoareW_get_bind. intros s ->. rewrite R2c. cbn [rg_mapped_user rg_alloc_user rg_free rg_mapped_fa rg_n_allocated rg_n_freed].
  apply hoareW_upd_bind. apply hoareW_ret. intros s (sx & -> & ->).
  set (fresh := rev _).
  assert (LF : zlen fresh = new) by (subst fresh; unfold zlen; rewrite length_rev, length_map, length_ziota; lia).
  set (r3 := mkRegion mu' (rg_alloc_user r0 + new * size) (rg_free r0 ++ fresh) fa' (rg_n_allocated r0) (rg_n_freed r0)).
  assert (RC3 : RCX c r3 [] s0 (set_region c r3 s2)).
  { rcx_region_only. destruct RC02 as (_ & X & _); rewrite X; destruct (Z.eq_dec c c); [reflexivity| contradiction]. }
  split; [| rewrite get_set_region_eq; exact RC3].
  eapply (BI_local nd F F s0 _ c); [unfold kLargestClassID; lia| exact ORIG| exact RC3| | auto].
  unfold BIc_raw. subst r3. cbn -[Z.mul Z.add Z.div Z.modulo class_size b24 kNB kUserMapSize kFreeArrayMapSize kFreeArrayOffset kMaxSize zlen app]. fold size. rewrite HF.
  rewrite zlen_app, LF. replace (zlen (@nil Z)) with 0 by reflexivity.
  replace ((rg_alloc_user r0 + new * size) / size) with (rg_alloc_user r0 / size + new)
    by (rewrite (Z.add_comm (rg_alloc_user r0)), Z.div_add_l by lia; lia).
  assert (AM' : (rg_alloc_user r0 + new * size) mod size = 0) by (rewrite Z_mod_plus_full; exact A3).
  repeat split; try lia.
Qed.

Lemma RCX_region_c : forall c r l s0 s, RCX c r l s0 s -> get_region s c = r.
Proof. intros c r l s0 s (X & _). rewrite X. destruct (Z.eq_dec c c); [reflexivity| contradiction]. Qed.
Lemma RCX_cache_c : forall c r l s0 s, RCX c r l s0 s -> get_cache s c = l.
Proof. intros c r l s0 s (_ & X & _). rewrite X. destruct (Z.eq_dec c c); [reflexivity| contradiction]. Qed.

(* [comment removed for export] *)
Lemma BI_c : forall nd F s c, 1 <= c <= kLargestClassID -> BI nd F s ->
  BIc_raw (get_region s c) (get_cache s c) (nchunks s c) (everc s c) (as_nprim_ever s) (nbatch nd s) (F c) c /\ 0 <= nd.
Proof. intros nd F s c Hc (B1 & _ & _ & _ & _ & ND). split; [exact (B1 c Hc)| exact ND]. Qed.

Lemma gfa_cnt : forall nd F s0 c, 1 <= c <= kLargestClassID -> BI nd F s0 -> F c = 0 -> get_cache s0 c = [] -> nbatch nd s0 <= kNB ->
  hoareW (fun s => s = s0) (get_from_allocator E c (hint c))
    (fun s' r => RCX c (get_region s' c) [] s0 s' /\
                 match r with None => BI nd F s' | Some l => zlen l = hint c /\ BI nd (fadd c (hint c) F) s' end).
Proof.
  intros nd F s0 c Hc HBI HF HC HNB. pose proof Hc as Hc'. unfold kLargestClassID in Hc'. pose proof (hint_range c Hc') as HR.
  unfold get_from_allocator. apply hoareW_get_bind. intros s ->.
  eapply hoareW_bind with (Q := fun s1 _ => BI nd F s1 /\ RCX c (get_region s1 c) [] s0 s1).
  { destruct (rg_num_freed (get_region s0 c) <? hint c) eqn:LT.
    - apply Z.ltb_lt in LT. apply populate_cnt; auto; [lia|]. unfold nfree, rg_num_freed, zlen in *. lia.
    - apply hoareW_ret. intros s ->. split; [exact HBI| rewrite <- HC; apply RCX_refl]. }
  intros ok. apply hoareW_pre. intros s1 [BI1 RC1].
  destruct (negb ok); [apply hoareW_ret; intros s ->; split; [exact RC1| exact BI1]|].
  apply hoareW_get_bind. intros s ->. apply hoareW_checkK. intros LE. apply Z.leb_le in LE.
  apply hoareW_upd_bind. apply hoareW_ret. intros s (sx & -> & ->).
  set (r1 := get_region s1 c) in *. set (keep := (length (rg_free r1) - Z.to_nat (hint c))%nat).
  set (r' := mkRegion _ _ _ _ _ _).
  assert (RC2 : RCX c r' [] s1 (set_region c r' s1)) by (rewrite <- (RCX_cache_c _ _ _ _ _ RC1) at 1; apply RCX_set_region).
  split; [rewrite get_set_region_eq; eapply RCX_trans; [exact RC1| exact RC2]|].
  unfold rg_num_freed in LE.
  split; [unfold zlen; rewrite length_skipn; subst keep; lia|].
  destruct (BI_c nd F s1 c Hc BI1) as [X ND]. rewrite (RCX_cache_c _ _ _ _ _ RC1), HF in X. fold r1 in X. unfold BIc_raw in X.
  eapply (BI_local nd F _ s1 _ c); [exact Hc| exact BI1| exact RC2| | intros; apply fadd_ne; auto].
  rewrite fadd_eq, HF. unfold BIc_raw. subst r'. cbn [rg_alloc_user rg_mapped_user rg_mapped_fa rg_free].
  replace (zlen (firstn keep (rg_free r1))) with (zlen (rg_free r1) - hint c) by (unfold zlen in *; rewrite length_firstn; subst keep; lia).
  change (zlen (@nil Z)) with 0 in *. repeat split; try lia.
Qed.

Lemma refill_cnt : forall nd F s0 c, 1 <= c <= kLargestClassID -> BI nd F s0 -> F c = 0 -> get_cache s0 c = [] -> nbatch nd s0 <= kNB ->
  hoareW (fun s => s = s0) (refill E c)
    (fun s' _ => RCX c (get_region s' c) (get_cache s' c) s0 s' /\ BI nd F s').
Proof.
  intros nd F s0 c Hc HBI HF HC HNB. unfold refill, init_cache.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). set (s0' := upd_cache_inited true s0).
  assert (BI0' : BI nd F s0') by (eapply BI_view; [| exact HBI]; reflexivity).
  eapply hoareW_bind; [apply (gfa_cnt nd F s0' c Hc BI0' HF HC HNB)|].
  intros [l|]; apply hoareW_pre; intros s1 [RC1 X].
  - destruct X as [LEN BI1]. apply hoareW_upd_bind. apply hoareW_ret. intros s (sy & -> & ->).
    set (s2 := upd_cache_stale _ _).
    assert (RC2 : RCX c (get_region s1 c) l s1 s2) by (eapply RCX_view; [reflexivity| apply RCX_set_cache]).
    assert (RC02 : RCX c (get_region s1 c) l s0 s2).
    { eapply RCX_trans; [| exact RC2]. eapply (RCX_trans c _ _ _ _ s0 s0' s1); [| exact RC1]. apply (RCX_view c _ _ s0 s0 s0' eq_refl (RCX_refl c s0)). }
    split; [rewrite (RCX_region_c _ _ _ _ _ RC02), (RCX_cache_c _ _ _ _ _ RC02); exact RC02|].
    destruct (BI_c nd _ s1 c Hc BI1) as [Y ND]. rewrite (RCX_cache_c _ _ _ _ _ RC1), fadd_eq, HF in Y. unfold BIc_raw in Y.
    eapply (BI_local nd _ F s1 s2 c); [exact Hc| exact BI1| exact RC2| | intros; symmetry; apply fadd_ne; auto].
    rewrite HF. unfold BIc_raw. rewrite LEN. change (zlen (@nil Z)) with 0 in *. repeat split; try lia.
  - apply hoareW_ret. intros s ->. split; [| exact X].
    eapply (RCX_trans c _ _ _ _ s0 s0' s1); [apply (RCX_view c _ _ s0 s0 s0' eq_refl (RCX_refl c s0))|].
    rewrite (RCX_cache_c _ _ _ _ _ RC1). exact RC1.
Qed.

Lemma zlen_removelast : forall {A} (l : list A), l <> [] -> zlen (removelast l) = zlen l - 1.
Proof.
  intros A l H. rewrite removelast_eq. unfold zlen. destruct (exists_last H) as (l' & a & ->).
  rewrite removelast_last, length_app. cbn. lia.
Qed.

Lemma cache_pop_cnt : forall nd F s0 c, 1 <= c <= kLargestClassID -> BI nd F s0 -> F c = 0 -> nbatch nd s0 <= kNB ->
  hoareW (fun s => s = s0) (cache_pop E c)
    (fun s' r => RCX c (get_region s' c) (get_cache s' c) s0 s' /\
                 match r with None => BI nd F s' | Some _ => BI nd (fadd c 1 F) s' end).
Proof.
  intros nd F s0 c Hc HBI HF HNB. unfold cache_pop. apply hoareW_get_bind. intros s ->.
  eapply hoareW_bind with (Q := fun s1 _ => RCX c (get_region s1 c) (get_cache s1 c) s0 s1 /\ BI nd F s1).
  { destruct (get_cache s0 c) eqn:GC.
    - apply refill_cnt; auto.
    - apply hoareW_ret. intros s ->. split; [apply RCX_refl| exact HBI]. }
  intros ok. apply hoareW_pre. intros s1 [RC1 BI1].
  destruct (negb ok); [apply hoareW_ret; intros s ->; auto|].
  apply hoareW_get_bind. intros s ->. destruct (get_cache s1 c) as [|x0 l0] eqn:GC1; [apply hoareW_undef|].
  apply hoareW_upd_bind. apply hoareW_ret. intros s (sx & -> & ->).
  set (l := x0 :: l0) in *. set (s2 := upd_cache_allocated _ _).
  assert (RC2 : RCX c (get_region s1 c) (removelast l) s1 s2) by (eapply RCX_view; [reflexivity| apply RCX_set_cache]).
  pose proof (RCX_trans _ _ _ _ _ _ _ _ RC1 RC2) as RC02.
  split; [rewrite (RCX_region_c _ _ _ _ _ RC02), (RCX_cache_c _ _ _ _ _ RC02); exact RC02|].
  destruct (BI_c nd _ s1 c Hc BI1) as [Y ND]. rewrite GC1, HF in Y. unfold BIc_raw in Y.
  eapply (BI_local nd _ _ s1 s2 c); [exact Hc| exact BI1| exact RC2| | intros; apply fadd_ne; auto].
  rewrite fadd_eq, HF. unfold BIc_raw. rewrite zlen_removelast by (subst l; discriminate). repeat split; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma map_size_pos : forall n, kPageSize <= map_size n.
Proof.
  intros n. unfold map_size.
  assert (needed n >= 1) by (unfold needed, needed1; pose proof (rounded_ge n); pose proof (rz_size_pos n); destruct (from_primary n); lia).
  pose proof (round_up_ge (needed n) kPageSize ltac:(unfold kPageSize; lia)). unfold kPageSize in *. lia.
Qed.

Lemma call_mmap_anon_cnt : forall s0 len,
  hoareW (fun s => s = s0) (call_mmap_anon E len)
    (fun s' r => s' = s0 /\ match r with None => True | Some a => ranges_free (known_ranges E s0) a len = true end).
Proof.
  intros s0 len. unfold call_mmap_anon. apply hoareW_get_bind. intros s ->.
  eapply hoareW_bind; [apply hoareW_call with (Q := fun s _ => s = s0); auto|]. intros [r|e]; apply hoareW_pre; intros s ->.
  - match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:C1 end; [| apply hoareW_undef].
    match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:C2 end; [| apply hoareW_undef].
    apply hoareW_ret. intros s ->. split; [reflexivity|]. apply andb_prop in C1 as [_ C1]. exact C1.
  - destruct (e =? ENOMEM); [apply hoareW_ret; intros s ->; auto| apply hoareW_undef].
Qed.

(* [comment removed for export] *)
Definition SECX (sc : secchunk) (s0 s' : astate) : Prop :=
  as_sec s' = as_sec s0 ++ [sc] /\ as_regions s' = as_regions s0 /\ as_cache s' = as_cache s0 /\ as_chunks s' = as_chunks s0
  /\ as_tq s' = as_tq s0 /\ as_gq s' = as_gq s0 /\ as_nprim_ever s' = as_nprim_ever s0 /\ as_everc s' = as_everc s0
  /\ ~ In (sc_map_beg sc) (map sc_map_beg (as_sec s0)).

Lemma sec_alloc_cnt : forall nd F s0 nd2, BI nd F s0 -> 0 <= nd2 ->
  hoareW (fun s => s = s0) (sec_alloc E nd2)
    (fun s' r => match r with
                 | None => s' = s0
                 | Some ab => SECX (mkSec (ab - kPageSize) (round_up nd2 kPageSize + kPageSize) nd2) s0 s'
                 end).
Proof.
  intros nd F s0 nd2 HBI Hnd2. unfold sec_alloc.
  eapply hoareW_bind; [apply call_mmap_anon_cnt|]. intros [mb|]; apply hoareW_pre; intros s [-> RF]; [| apply hoareW_ret; auto].
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). apply hoareW_get_bind. intros s ->. apply hoareW_checkK. intros _.
  set (s1 := upd_ts _ s0).
  eapply hoareW_bind with (Q := fun s2 _ => bview_of s2 = bview_of s0).
  { match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b end; [| apply hoareW_ret; intros s ->; reflexivity].
    eapply hoareW_bind; [apply call_mmap_fixed_eq|]. intros [|]; [| apply hoareW_spin]. apply hoareW_upd. intros s ->. reflexivity. }
  intros []. apply hoareW_upd_bind. apply hoareW_ret. intros s (s2 & V & ->).
  unfold bview_of in V. injection V as V1 V2 V3 V4 V5 V6 V7 V8. unfold SECX. cbn -[Z.add Z.sub Z.mul round_up kPageSize].
  replace (mb + kPageSize - kPageSize) with mb by lia.
  rewrite V1, V2, V3, V4, V5, V6, V7, V8. repeat split; try reflexivity.
  intros Hin. apply in_map_iff in Hin as (sc & Hb & Hsc).
  destruct HBI as (_ & _ & _ & B8 & _). destruct (B8 sc Hsc) as (cb & cm & _ & _ & _ & MS).
  pose proof (map_size_pos (cm_n cm)) as P1.
  pose proof (round_up_ge nd2 kPageSize ltac:(unfold kPageSize; lia)) as P2.
  pose proof (ranges_free_In _ _ _ (sc_map_beg sc) (sc_map_size sc) RF) as D.
  specialize (D ltac:(unfold known_ranges; apply in_app_iff; right; apply in_app_iff; left; apply in_map_iff; exists sc; auto)).
  unfold kPageSize in *. lia.
Qed.


Lemma everc_upd_nprimc : forall prim c s c',
  everc (upd_nprimc prim c s) c' = if prim then (if Z.eq_dec c' c then everc s c + 1 else everc s c') else everc s c'.
Proof.
  intros prim c s c'. unfold everc at 1. cbn [as_everc upd_nprimc]. destruct prim; [| reflexivity].
  destruct (Z.eq_dec c' c) as [->|NE]; [rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by auto; reflexivity].
Qed.

Lemma BI_nprimc : forall nd F s prim c, BI nd F s -> (prim = true -> 1 <= c <= kLargestClassID) ->
  BI nd F (upd_nprimc prim c s) /\ (prim = true -> nchunks (upd_nprimc prim c s) c < everc (upd_nprimc prim c s) c).
Proof.
  intros nd F s prim c (B1 & B6 & B7 & B8 & B9 & ND) Hc. split.
  - split; [| split; [exact B6| split; [exact B7| split; [exact B8| split; [exact B9| exact ND]]]]].
    intros c' Hc'. pose proof (B1 c' Hc') as X. unfold BIc in *. rewrite everc_upd_nprimc.
    change (get_region (upd_nprimc prim c s) c') with (get_region s c'). change (get_cache (upd_nprimc prim c s) c') with (get_cache s c').
    change (nchunks (upd_nprimc prim c s) c') with (nchunks s c'). change (nbatch nd (upd_nprimc prim c s)) with (nbatch nd s).
    cbn [as_nprim_ever upd_nprimc]. unfold BIc_raw in *. pose proof (b24_range c') as R24. pose proof (class_size_mod c' ltac:(unfold kLargestClassID in Hc'; lia)) as [_ SZ].
    destruct prim; [| exact X]. destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
    assert (MONO : forall e e', e <= e' -> class_size c' * (e + 8 + b24 c' * kNB) <= class_size c' * (e' + 8 + b24 c' * kNB))
      by (intros; apply Z.mul_le_mono_nonneg_l; lia).
    destruct (Z.eq_dec c' c) as [->|NE]; [pose proof (MONO (everc s c) (everc s c + 1) ltac:(lia))|]; repeat split; try lia.
  - intros ->. rewrite everc_upd_nprimc. destruct (Z.eq_dec c c); [| contradiction].
    change (nchunks (upd_nprimc true c s) c) with (nchunks s c). pose proof (B1 c (Hc eq_refl)) as X. unfold BIc, BIc_raw in X. lia.
Qed.

Lemma BI_chunk_insert_prim : forall nd F s cb cm c, BI nd F s -> as_chunks s !! cb = None -> cm_prim cm = Some c ->
  1 <= c <= kLargestClassID -> 1 <= cm_n cm -> 1 <= F c -> nchunks s c < everc s c ->
  BI nd (fadd c (-1) F) (upd_chunks (fun m => <[cb := cm]> m) s).
Proof.
  intros nd F s cb cm c (B1 & B6 & B7 & B8 & B9 & ND) NONE PC Hc Hn HF LT.
  split; [| split; [| split; [exact B7| split; [| split; [exact B9| exact ND]]]]].
  - intros c' Hc'. pose proof (B1 c' Hc') as X. unfold BIc in *. rewrite (nchunks_insert s cb cm c' NONE).
    change (get_region (upd_chunks _ s) c') with (get_region s c'). change (get_cache (upd_chunks _ s) c') with (get_cache s c').
    change (nbatch nd (upd_chunks _ s)) with (nbatch nd s). change (everc (upd_chunks _ s) c') with (everc s c').
    cbn [as_nprim_ever upd_chunks]. unfold is_cls. cbn [snd]. rewrite PC. unfold BIc_raw in *.
    destruct (Z.eq_dec c' c) as [->|NE]; [rewrite Z.eqb_refl, fadd_eq; repeat split; lia|].
    replace (c =? c') with false by (symmetry; apply Z.eqb_neq; auto). rewrite fadd_ne by auto. rewrite Z.add_0_r. exact X.
  - intros cb' cm' H. cbn in H. destruct (decide (cb' = cb)) as [->|NE]; [rewrite lookup_insert_eq in H; injection H as <-; rewrite PC; split; [exact Hn| exact Hc]|].
    rewrite lookup_insert_ne in H by auto. exact (B6 _ _ H).
  - intros sc Hsc. destruct (B8 sc Hsc) as (cb' & cm' & H & X). exists cb', cm'. split; [| exact X]. cbn [as_chunks upd_chunks].
    rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite NONE in H. discriminate.
Qed.

Lemma BI_sec_register : forall nd F s0 s1 s2 sc cb cm, BI nd F s0 -> SECX sc s0 s1 -> bview_of s2 = bview_of s1 ->
  as_chunks s2 !! cb = None -> cm_prim cm = None -> 1 <= cm_n cm -> cm_alloc_beg cm = sc_map_beg sc + kPageSize ->
  sc_map_size sc = map_size (cm_n cm) ->
  BI nd F (upd_chunks (fun m => <[cb := cm]> m) s2).
Proof.
  intros nd F s0 s1 s2 sc cb cm (B1 & B6 & B7 & B8 & B9 & ND) (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & NIN) V NONE PC Hn AB MS.
  unfold bview_of in V. injection V as V1 V2 V3 V4 V5 V6 V7 V8.
  assert (CH : as_chunks s2 = as_chunks s0) by congruence.
  split; [| split; [| split; [| split; [| split; [| exact ND]]]]].
  - intros c' Hc'. pose proof (B1 c' Hc') as X. unfold BIc in *. rewrite (nchunks_insert s2 cb cm c' NONE).
    unfold is_cls; cbn [snd]; rewrite PC, Z.add_0_r.
    unfold get_region, get_cache, nchunks, chunk_list, nbatch, everc in *. cbn [as_regions as_cache as_chunks as_tq as_gq as_nprim_ever as_everc upd_chunks].
    rewrite V1, V2, V3, V4, V5, V7, V8, X2, X3, X4, X5, X6, X7, X8. exact X.
  - intros cb' cm' H. cbn in H. destruct (decide (cb' = cb)) as [->|NE]; [rewrite lookup_insert_eq in H; injection H as <-; rewrite PC; split; [exact Hn| exact I]|].
    rewrite lookup_insert_ne in H by auto. rewrite CH in H. exact (B6 _ _ H).
  - cbn [as_tq as_gq upd_chunks]. rewrite V4, V5, X5, X6. exact B7.
  - cbn [as_sec upd_chunks]. rewrite V6, X1. intros sc' Hin. apply in_app_iff in Hin as [Hin|[<-|[]]].
    + destruct (B8 sc' Hin) as (cb' & cm' & H & Y). exists cb', cm'. split; [| exact Y]. cbn. rewrite lookup_insert_ne; [rewrite CH; exact H|].
      intros ->. rewrite CH in NONE. rewrite NONE in H. discriminate.
    + exists cb, cm. cbn. rewrite lookup_insert_eq. auto.
  - cbn [as_sec upd_chunks]. rewrite V6, X1, map_app. cbn. apply NoDup_app; [exact B9| constructor; [intros []| constructor]|].
    intros x Hx [<-|[]]. exact (NIN Hx).
Qed.

Lemma nbatch_bound : forall s, BI 0 fzero s -> AQbound s -> nbatch 0 s <= kNB.
Proof.
  intros s (_ & _ & B7 & _) [TQ GQ]. unfold nbatch, tq_bytes, gq_bytes in *.
  assert (G : forall l, (forall b, In b l -> kBatchSize <= b_size b) -> kBatchSize * zlen l <= qbytes l).
  { intros l. induction l as [|b l IH]; intros H; [unfold zlen; cbn; lia|]. rewrite zlen_cons. change (qbytes (b :: l)) with (b_size b + qbytes l).
    pose proof (H b ltac:(left; reflexivity)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. }
  pose proof (G (as_tq s) ltac:(intros; apply B7; apply in_app_iff; left; assumption)).
  pose proof (G (as_gq s) ltac:(intros; apply B7; apply in_app_iff; right; assumption)).
  unfold kBatchSize, kThreadQuarantineMax, kQuarantineMax, kNB in *. lia.
Qed.

Lemma class_of_request : forall n, 0 <= n -> from_primary n = true -> 1 <= class_id (needed1 n) <= kLargestClassID.
Proof.
  intros n Hn PR. pose proof (proj1 (from_primary_iff n Hn) PR). pose proof (malloc_class_ok n ltac:(lia)) as [X _].
  unfold malloc_class, kLargestClassID in *. exact X.
Qed.

Lemma amalloc_core_cnt : forall s0 key n, 0 <= n -> BI 0 fzero s0 -> nbatch 0 s0 <= kNB ->
  hoareW (fun s => s = s0) (amalloc_core E key n)
    (fun s' _ => BI 0 fzero s' /\ as_tq s' = as_tq s0 /\ as_gq s' = as_gq s0).
Proof.
  intros s0 key n Hn HBI HNB. unfold amalloc_core. apply hoareW_checkK. intros _.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  set (prim := from_primary n). set (c := class_id (needed1 n)). set (s1 := upd_nprimc prim c s0).
  assert (HcP : prim = true -> 1 <= c <= kLargestClassID) by (intros PR; apply class_of_request; auto).
  destruct (BI_nprimc 0 fzero s0 prim c HBI HcP) as [BI1 LT1]. fold s1 in BI1, LT1.
  assert (HNB1 : nbatch 0 s1 <= kNB) by exact HNB.
  pose proof (req_geom n) as (G1 & G2 & G3 & G4 & G5).
  eapply hoareW_bind with (Q := fun s2 ab =>
     as_tq s2 = as_tq s0 /\ as_gq s2 = as_gq s0 /\
     match ab with
     | None => BI 0 fzero s2
     | Some a => (prim = true /\ BI 0 (fadd c 1 fzero) s2 /\ nchunks s2 c < everc s2 c)
                 \/ (prim = false /\ SECX (mkSec (a - kPageSize) (round_up (needed n) kPageSize + kPageSize) (needed n)) s1 s2)
     end).
  { destruct prim eqn:PR.
    - specialize (HcP eq_refl). specialize (LT1 eq_refl).
      eapply hoareW_conseq; [apply (cache_pop_cnt 0 fzero s1 c HcP BI1 eq_refl HNB1)| auto|]. cbn beta.
      intros s r [RC X]. destruct RC as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6)).
      split; [exact F2|]. split; [exact F3|]. destruct r as [a|]; [| exact X]. left. split; [reflexivity|]. split; [exact X|].
      unfold nchunks, chunk_list, everc in *. rewrite F1, F6. exact LT1.
    - assert (NN : 0 <= needed n) by (unfold needed, needed1; pose proof (rounded_ge n); pose proof (rz_size_pos n); destruct (from_primary n); lia).
      eapply hoareW_conseq; [apply (sec_alloc_cnt 0 fzero s1 (needed n) BI1 NN)| auto|]. cbn beta.
      intros s [a|] X; [| subst s; split; [reflexivity| split; [reflexivity| exact BI1]]].
      destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). split; [exact X5|]. split; [exact X6|]. right. split; [reflexivity|]. repeat split; assumption. }
  intros [ab|]; apply hoareW_pre; intros s2 (T2 & G2' & CASE).
  2:{ apply hoareW_upd_bind. apply hoareW_ret. intros s (sy & -> & ->). split; [eapply BI_view; [| exact CASE]; reflexivity| cbn; auto]. }
  eapply hoareW_bind; [apply depot_put_view|]. intros id. apply hoareW_pre. intros s3 V3.
  apply hoareW_get_bind. intros s ->. 
  set (cb := ab + rz_size n - kChunkHeaderSize). destruct (as_chunks s3 !! cb) eqn:NONE; [unfold acheck; eapply hoareW_bind with (Q := fun _ _ => False); [apply hoareW_undef| intros [] s []]|].
  apply hoareW_checkK. intros _. apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->).
  set (cm := mkCM _ _ _ _ _). set (s4 := upd_dead _ (upd_chunks _ s3)).
  assert (V3' : as_tq s3 = as_tq s0 /\ as_gq s3 = as_gq s0).
  { unfold bview_of in V3. injection V3 as _ _ _ V4 V5 _ _ _. split; congruence. }
  assert (BI4 : BI 0 fzero s4).
  { assert (E4 : bview_of s4 = bview_of (upd_chunks (fun m => <[cb := cm]> m) s3)) by reflexivity.
    eapply BI_view; [exact E4|].
    destruct CASE as [(PR & BI2 & LT2)|(PR & SX)].
    - apply BI_Fext with (F := fadd c (-1) (fadd c 1 fzero)).
      { intros c'. unfold fadd, fzero. destruct (c' =? c); lia. }
      assert (BI3 : BI 0 (fadd c 1 fzero) s3) by (eapply BI_view; [exact V3| exact BI2]).
      apply (BI_chunk_insert_prim 0 _ s3 cb cm c BI3 NONE); [subst cm; cbn; rewrite PR; reflexivity| exact (HcP PR)| subst cm; cbn; exact G5| rewrite fadd_eq; unfold fzero; lia|].
      unfold bview_of in V3. injection V3 as _ _ V3c _ _ _ _ V3e. unfold nchunks, chunk_list, everc in *. rewrite V3c, V3e. exact LT2.
    - eapply (BI_sec_register 0 fzero s1 s2 s3 _ cb cm BI1 SX V3 NONE); subst cm; cbn; [rewrite PR; reflexivity| exact G5| lia|].
      unfold map_size. rewrite G4. reflexivity. }
  eapply hoareW_bind; [apply poison_zero_view|]. intros []. apply hoareW_pre. intros s ->.
  apply hoareW_upd_bind. apply hoareW_ret. intros s (sz & -> & ->). split; [eapply BI_view; [| exact BI4]; reflexivity| cbn; exact V3'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma return_cnt : forall nd F s0 c chunks, 1 <= c <= kLargestClassID -> BI nd F s0 -> zlen chunks <= F c ->
  hoareW (fun s => s = s0) (return_to_allocator E c chunks)
    (fun s' _ => BI nd (fadd c (- zlen chunks) F) s' /\ RCX c (get_region s' c) (get_cache s0 c) s0 s').
Proof.
  intros nd F s0 c chunks Hc HBI HF. pose proof (zlen_nonneg chunks) as Z0.
  destruct (BI_c nd F s0 c Hc HBI) as [X ND]. unfold BIc_raw in X. destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; lia)) as [_ SZ]. pose proof (b24_range c) as R24. pose proof (nbatch_nonneg nd s0 ND) as NBp.
  pose proof (zlen_nonneg (get_cache s0 c)) as ZC.
  unfold return_to_allocator. apply hoareW_get_bind. intros s ->.
  eapply hoareW_bind; [apply ensure_cnt|]. intros ok. apply hoareW_pre. intros s1 (fa' & RC1 & FA1 & FA2 & FA3 & FA4).
  destruct ok; cbn [negb]; [| apply hoareW_spin]. specialize (FA3 eq_refl).
  apply hoareW_get_bind. intros s ->. rewrite (RCX_region_c _ _ _ _ _ RC1). cbn [rg_mapped_user rg_alloc_user rg_free rg_mapped_fa rg_n_allocated rg_n_freed rg_setfa].
  apply hoareW_upd. intros s ->. set (r' := mkRegion _ _ _ _ _ _).
  assert (RC2 : RCX c r' (get_cache s0 c) s0 (set_region c r' s1)) by (rcx_region_only; exact (RCX_cache_c _ _ _ _ _ RC1)).
  split; [| rewrite get_set_region_eq; exact RC2].
  eapply (BI_local nd F _ s0 _ c); [exact Hc| exact HBI| exact RC2| | intros; apply fadd_ne; auto].
  rewrite fadd_eq. unfold BIc_raw. subst r'. cbn [rg_alloc_user rg_mapped_user rg_mapped_fa rg_free]. rewrite zlen_app.
  unfold rg_num_freed in FA2. change (Z.of_nat (length (rg_free (get_region s0 c)))) with (zlen (rg_free (get_region s0 c))) in FA2.
  repeat split; try lia.
Qed.

Lemma local_dealloc_cnt : forall nd F s0 c p, 1 <= c <= kLargestClassID -> BI nd F s0 -> 1 <= F c ->
  hoareW (fun s => s = s0) (local_dealloc E c p)
    (fun s' _ => BI nd (fadd c (-1) F) s' /\ RCX c (get_region s' c) (get_cache s' c) s0 s').
Proof.
  intros nd F s0 c p Hc HBI HF. unfold local_dealloc, init_cache. apply hoareW_checkK. intros _.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). set (s0' := upd_cache_inited true s0).
  assert (BI0' : BI nd F s0') by (eapply BI_view; [| exact HBI]; reflexivity).
  assert (RC00 : RCX c (get_region s0' c) (get_cache s0' c) s0 s0') by (apply (RCX_view c _ _ s0 s0 s0' eq_refl (RCX_refl c s0))).
  apply hoareW_get_bind. intros s ->.
  eapply hoareW_bind with (Q := fun s1 _ => BI nd F s1 /\ RCX c (get_region s1 c) (get_cache s1 c) s0 s1).
  { destruct (zlen (get_cache s0' c) =? max_count c) eqn:FULL; [| apply hoareW_ret; intros s ->; auto].
    set (l := get_cache s0' c) in *. set (keep := (length l - Z.to_nat (hint c))%nat).
    apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->). set (s1 := set_cache c (firstn keep l) s0').
    pose proof (hint_range c ltac:(unfold kLargestClassID in Hc; lia)) as HR. apply Z.eqb_eq in FULL. unfold max_count in FULL.
    assert (LK : zlen (skipn keep l) = hint c) by (unfold zlen in *; rewrite length_skipn; subst keep; lia).
    assert (LF : zlen (firstn keep l) = zlen l - hint c) by (unfold zlen in *; rewrite length_firstn; subst keep; lia).
    assert (RC1 : RCX c (get_region s0' c) (firstn keep l) s0' s1) by apply RCX_set_cache.
    assert (BI1 : BI nd (fadd c (hint c) F) s1).
    { destruct (BI_c nd F s0' c Hc BI0') as [X ND]. unfold BIc_raw in X. fold l in X.
      eapply (BI_local nd F _ s0' s1 c); [exact Hc| exact BI0'| exact RC1| | intros; apply fadd_ne; auto].
      rewrite fadd_eq. unfold BIc_raw. rewrite LF. repeat split; try lia. }
    eapply hoareW_conseq; [apply (return_cnt nd _ s1 c (skipn keep l) Hc BI1 ltac:(rewrite fadd_eq, LK; lia))| auto|]. cbn beta.
    intros s [] [BI2 RC2]. split.
    - eapply BI_Fext; [| exact BI2]. intros c'. rewrite LK. unfold fadd. destruct (c' =? c); lia.
    - pose proof (RCX_trans _ _ _ _ _ _ _ _ RC00 (RCX_trans _ _ _ _ _ _ _ _ RC1 RC2)) as R.
      replace (get_cache s1 c) with (firstn keep l) in R by (subst s1; rewrite get_set_cache_eq; reflexivity).
      rewrite (RCX_cache_c _ _ _ _ _ R). exact R. }
  intros []. apply hoareW_pre. intros s1 [BI1 RC1]. apply hoareW_get_bind. intros s ->.
  apply hoareW_upd. intros s ->. set (s2 := upd_cache_allocated _ _). set (l1 := get_cache s1 c) in *.
  assert (RC2 : RCX c (get_region s1 c) (l1 ++ [compact_of_chunk SB c p]) s1 s2) by (eapply RCX_view; [reflexivity| apply RCX_set_cache]).
  pose proof (RCX_trans _ _ _ _ _ _ _ _ RC1 RC2) as RC02.
  split; [| rewrite (RCX_region_c _ _ _ _ _ RC02), (RCX_cache_c _ _ _ _ _ RC02); exact RC02].
  destruct (BI_c nd F s1 c Hc BI1) as [X ND]. unfold BIc_raw in X. fold l1 in X.
  eapply (BI_local nd F _ s1 s2 c); [exact Hc| exact BI1| exact RC2| | intros; apply fadd_ne; auto].
  rewrite fadd_eq. unfold BIc_raw. rewrite zlen_app. change (zlen [_]) with 1. repeat split; try lia.
Qed.

Lemma BI_chunk_flip : forall nd F s cb cm cm', BI nd F s -> as_chunks s !! cb = Some cm ->
  cm_prim cm' = cm_prim cm -> cm_alloc_beg cm' = cm_alloc_beg cm -> cm_n cm' = cm_n cm ->
  BI nd F (upd_chunks (fun m => <[cb := cm']> m) s).
Proof.
  intros nd F s cb cm cm' (B1 & B6 & B7 & B8 & B9 & ND) H HP HA HN.
  split; [| split; [| split; [exact B7| split; [| split; [exact B9| exact ND]]]]].
  - intros c' Hc'. pose proof (B1 c' Hc') as X. unfold BIc in *. rewrite (nchunks_flip s cb cm cm' c' H HP). exact X.
  - intros cb' cm'' H'. cbn in H'. destruct (decide (cb' = cb)) as [->|NE]; [rewrite lookup_insert_eq in H'; injection H' as <-; rewrite HP, HN; exact (B6 _ _ H)|].
    rewrite lookup_insert_ne in H' by auto. exact (B6 _ _ H').
  - intros sc Hsc. destruct (B8 sc Hsc) as (cb' & cm'' & H' & X). unfold seccov. cbn [as_chunks upd_chunks].
    destruct (decide (cb' = cb)) as [->|NE].
    + exists cb, cm'. rewrite lookup_insert_eq. rewrite H in H'. injection H' as ->. rewrite HP, HA, HN. auto.
    + exists cb', cm''. rewrite lookup_insert_ne by auto. auto.
Qed.

Lemma BI_chunk_delete_prim : forall nd F s cb cm c, BI nd F s -> as_chunks s !! cb = Some cm -> cm_prim cm = Some c ->
  BI nd (fadd c 1 F) (upd_chunks (delete cb) s).
Proof.
  intros nd F s cb cm c (B1 & B6 & B7 & B8 & B9 & ND) H PC.
  pose proof (B6 _ _ H) as [_ Hc]. rewrite PC in Hc.
  split; [| split; [| split; [exact B7| split; [| split; [exact B9| exact ND]]]]].
  - intros c' Hc'. pose proof (B1 c' Hc') as X. unfold BIc in *. rewrite (nchunks_delete s cb cm c' H).
    change (get_region (upd_chunks _ s) c') with (get_region s c'). change (get_cache (upd_chunks _ s) c') with (get_cache s c').
    change (nbatch nd (upd_chunks _ s)) with (nbatch nd s). change (everc (upd_chunks _ s) c') with (everc s c').
    cbn [as_nprim_ever upd_chunks]. unfold is_cls. cbn [snd]. rewrite PC. unfold BIc_raw in *.
    destruct (Z.eq_dec c' c) as [->|NE]; [rewrite Z.eqb_refl, fadd_eq|].
    + assert (1 <= nchunks s c).
      { unfold nchunks, chunk_list. rewrite <- (countZ_perm _ _ _ (map_to_list_delete (as_chunks s) cb cm H)). cbn [countZ]. unfold is_cls at 1. cbn [snd]. rewrite PC, Z.eqb_refl.
        pose proof (countZ_nonneg (is_cls c) (map_to_list (delete cb (as_chunks s)))). lia. }
      repeat split; lia.
    + replace (c =? c') with false by (symmetry; apply Z.eqb_neq; auto). rewrite fadd_ne by auto. rewrite Z.sub_0_r. exact X.
  - intros cb' cm' H'. cbn in H'. destruct (decide (cb' = cb)) as [->|NE]; [rewrite lookup_delete_eq in H'; discriminate|].
    rewrite lookup_delete_ne in H' by auto. exact (B6 _ _ H').
  - intros sc Hsc. destruct (B8 sc Hsc) as (cb' & cm' & H' & X). exists cb', cm'. cbn [as_chunks upd_chunks]. rewrite lookup_delete_ne; [auto|].
    intros ->. rewrite H in H'. injection H' as ->. destruct X as [X _]. rewrite PC in X. discriminate.
Qed.

(* [comment removed for export] *)
Lemma delete_large_cnt : forall nd F s0 m cm, BI nd F s0 -> as_chunks s0 !! m = Some cm -> cm_prim cm = None ->
  hoareW (fun s => s = s0) (aupd (upd_chunks (delete m)) ;;; large_dealloc (cm_alloc_beg cm))
    (fun s' _ => BI nd F s').
Proof.
  intros nd F s0 m cm HBI Hm PC. pose proof HBI as (B1 & B6 & B7 & B8 & B9 & ND).
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). set (s1 := upd_chunks (delete m) s0).
  unfold large_dealloc. apply hoareW_get_bind. intros s ->. change (as_sec s1) with (as_sec s0).
  set (mb := cm_alloc_beg cm - kPageSize).
  destruct (list_find_index _ (as_sec s0) 0) as [i|] eqn:FI; [| apply hoareW_undef].
  destruct (list_find_index_spec _ _ _ _ FI) as (h & _ & NTH & FH). rewrite Nat.sub_0_r in NTH. rewrite NTH. apply Z.eqb_eq in FH.
  pose proof (swap_remove_perm (as_sec s0) i h NTH) as PERM.
  set (sec' := removelast _) in *.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->). set (s2 := upd_glob _ _ _).
  assert (ND2 : List.NoDup (map sc_map_beg (h :: sec'))).
  { eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PERM| exact B9]. }
  assert (BI2 : BI nd F s2).
  { split; [| split; [| split; [exact B7| split; [| split; [| exact ND]]]]].
    - intros c' Hc'. pose proof (B1 c' Hc') as X. unfold BIc in *.
      change (nchunks s2 c') with (nchunks (upd_chunks (delete m) s0) c'). rewrite (nchunks_delete s0 m cm c' Hm).
      unfold is_cls; cbn [snd]; rewrite PC, Z.sub_0_r. exact X.
    - intros cb' cm' H'. cbn in H'. destruct (decide (cb' = m)) as [->|NE]; [rewrite lookup_delete_eq in H'; discriminate|].
      rewrite lookup_delete_ne in H' by auto. exact (B6 _ _ H').
    - cbn [as_sec upd_glob upd_sec_stats upd_sec_stale upd_sec s2]. intros sc Hsc.
      assert (Hin : In sc (as_sec s0)) by (eapply Permutation_in; [exact PERM| right; exact Hsc]).
      assert (NE : sc_map_beg sc <> sc_map_beg h).
      { inversion ND2; subst. intros EQ. apply H1. rewrite <- EQ. apply in_map_iff. exists sc; auto. }
      destruct (B8 sc Hin) as (cb' & cm' & H' & P' & A' & S'). exists cb', cm'. split; [| auto].
      cbn [as_chunks upd_glob upd_sec_stats upd_sec_stale upd_sec upd_chunks s2 s1]. rewrite lookup_delete_ne; [exact H'|].
      intros ->. rewrite Hm in H'. injection H' as ->. apply NE. rewrite FH. subst mb. rewrite A'. unfold kPageSize. lia.
    - cbn [as_sec upd_glob upd_sec_stats upd_sec_stale upd_sec s2]. inversion ND2; assumption. }
  eapply hoareW_bind; [apply poison_zero_view|]. intros []. apply hoareW_pre. intros s ->.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sz & -> & ->).
  eapply hoareW_conseq; [apply call_munmap_eq| intros ? ->; reflexivity|]. cbn beta. intros s [] ->.
  eapply BI_view; [| exact BI2]. reflexivity.
Qed.

Definition caddr (p : Z) : Z := ((p - SB) / kRegionSize) mod kNumClasses.

Lemma qcb_recycle_cnt : forall nd F s0 m, BI nd F s0 ->
  hoareW (fun s => s = s0) (qcb_recycle E m) (fun s' _ => BI nd F s').
Proof.
  intros nd F s0 m HBI. pose proof HBI as (B1 & B6 & B7 & B8 & B9 & ND).
  unfold qcb_recycle. apply hoareW_get_bind. intros s ->.
  destruct (as_chunks s0 !! m) as [meta|] eqn:Hm; [| apply hoareW_undef].
  destruct (cm_state meta) eqn:ST; [apply hoareW_undef|].
  eapply hoareW_bind with (Q := fun s _ => s = s0).
  { destruct (in_primary SB m); [| apply hoareW_ret; auto]. apply hoareW_checkK. intros _. apply hoareW_ret. auto. }
  intros p. apply hoareW_pre. intros s ->.
  eapply hoareW_bind with (Q := fun s _ => s = s0 /\ (in_primary SB p = true ->
                             p = cm_alloc_beg meta /\ match cm_prim meta with Some c0 => c0 = caddr p | None => False end)).
  { destruct (in_primary SB p) eqn:IP.
    - apply hoareW_checkK. intros P1. apply Z.eqb_eq in P1. unfold acheck.
      destruct (cm_prim meta) as [c0|] eqn:PC; [| apply hoareW_undef].
      destruct (c0 =? _) eqn:CC; [| apply hoareW_undef]. apply Z.eqb_eq in CC. apply hoareW_ret. intros s ->. auto.
    - apply hoareW_ret. intros s ->. split; [reflexivity| discriminate]. }
  intros []. apply hoareW_pre. intros s [-> FACTS].
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). set (s1 := upd_ts _ s0).
  assert (BI1 : BI nd F s1) by (eapply BI_view; [| exact HBI]; reflexivity).
  assert (Hm1 : as_chunks s1 !! m = Some meta) by exact Hm.
  destruct (p =? 0); [apply hoareW_undef|].
  destruct (in_primary SB p) eqn:IP.
  - destruct (FACTS eq_refl) as [P1 PCX]. destruct (cm_prim meta) as [c0|] eqn:PC; [| destruct PCX]. fold (caddr p). rewrite <- PCX.
    pose proof (B6 _ _ Hm) as [Hn Hc0]. rewrite PC in Hc0.
    apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->). set (s2 := upd_dead _ _).
    assert (BI2 : BI nd (fadd c0 1 F) s2).
    { eapply (BI_view nd _ (upd_chunks (delete m) s1) s2); [reflexivity|]. apply (BI_chunk_delete_prim nd F s1 m meta c0 BI1 Hm1 PC). }
    assert (F1 : 1 <= fadd c0 1 F c0).
    { rewrite fadd_eq. pose proof (proj1 (BI_c nd F s0 c0 Hc0 HBI)) as X. unfold BIc_raw in X. lia. }
    eapply hoareW_conseq; [apply (local_dealloc_cnt nd _ s2 c0 p Hc0 BI2 F1)| auto|].
    cbn beta. intros s [] [BI3 _]. eapply BI_Fext; [| exact BI3]. intros c'. unfold fadd. destruct (c' =? c0); lia.
  - apply hoareW_checkK. intros P1. apply Z.eqb_eq in P1.
    unfold acheck at 1. destruct (cm_prim meta) as [c0|] eqn:PC; [eapply hoareW_bind with (Q := fun _ _ => False); [apply hoareW_undef| intros [] s []]|].
    eapply hoareW_bind; [apply hoareW_ret with (Q := fun s _ => s = s1); auto|]. intros []. apply hoareW_pre. intros s ->.
    rewrite P1. apply (delete_large_cnt nd F s1 m meta BI1 Hm1 PC).
Qed.

Lemma recycle_items_cnt : forall nd F items s0, BI nd F s0 ->
  hoareW (fun s => s = s0) (recycle_items E items) (fun s' _ => BI nd F s').
Proof.
  intros nd F items. induction items as [|m rest IH]; intros s0 HBI; cbn [recycle_items].
  - apply hoareW_ret. intros s ->. exact HBI.
  - eapply hoareW_bind; [apply qcb_recycle_cnt; exact HBI|]. intros []. apply hoareW_pre. intros s1 BI1. apply IH. exact BI1.
Qed.

(* [comment removed for export] *)
Lemma BI_detach : forall nd F s, 1 <= nd -> BI nd F s -> BI (nd - 1) (fadd kBatchClass 1 F) s.
Proof.
  intros nd F s Hnd (B1 & B6 & B7 & B8 & B9 & ND). split; [| split; [exact B6| split; [exact B7| split; [exact B8| split; [exact B9| lia]]]]].
  intros c Hc. pose proof (B1 c Hc) as X. unfold BIc, BIc_raw, nbatch, b24 in *.
  destruct (Z.eq_dec c kBatchClass) as [->|NE].
  - rewrite Z.eqb_refl, fadd_eq in *. repeat split; try lia.
  - replace (c =? kBatchClass) with false in * by (symmetry; apply Z.eqb_neq; exact NE). rewrite fadd_ne by exact NE. repeat split; try lia.
Qed.

Lemma do_recycle_cnt : forall bs nd F s0, 0 <= nd -> BI (nd + zlen bs) F s0 ->
  hoareW (fun s => s = s0) (do_recycle E bs) (fun s' _ => BI nd F s').
Proof.
  intros bs. induction bs as [|b rest IH]; intros nd F s0 Hnd HBI; cbn [do_recycle].
  - apply hoareW_ret. intros s ->. rewrite zlen_nil, Z.add_0_r in HBI. exact HBI.
  - rewrite zlen_cons in HBI. pose proof (zlen_nonneg rest) as ZR.
    eapply hoareW_bind; [apply recycle_items_cnt; exact HBI|]. intros []. apply hoareW_pre. intros s1 BI1.
    eapply hoareW_bind with (Q := fun s _ => BI (nd + zlen rest) F s).
    { destruct (in_primary SB (b_addr b)); [| apply hoareW_undef]. apply hoareW_checkK. intros C24. apply Z.eqb_eq in C24. rewrite C24.
      pose proof (BI_detach (nd + (1 + zlen rest)) F s1 ltac:(lia) BI1) as BI2. replace (nd + (1 + zlen rest) - 1) with (nd + zlen rest) in BI2 by lia.
      assert (H24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
      assert (F1 : 1 <= fadd kBatchClass 1 F kBatchClass).
      { rewrite fadd_eq. pose proof (proj1 (BI_c _ F s1 kBatchClass H24 BI1)) as X. unfold BIc_raw in X. lia. }
      eapply hoareW_conseq; [apply (local_dealloc_cnt _ _ s1 kBatchClass (b_addr b) H24 BI2 F1)| auto|].
      cbn beta. intros s [] [BI3 _]. eapply BI_Fext; [| exact BI3]. intros c'. unfold fadd. destruct (c' =? kBatchClass); lia. }
    intros []. apply hoareW_pre. intros s2 BI2. apply IH; [exact Hnd| exact BI2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BI_requeue : forall nd nd' F F' s tq' gq', BI nd F s -> 0 <= nd' ->
  (forall c, 1 <= c <= kLargestClassID -> b24 c * (zlen tq' + zlen gq' + nd') + F' c = b24 c * nbatch nd s + F c /\ 0 <= F' c) ->
  (forall b, In b (tq' ++ gq') -> kBatchSize <= b_size b) ->
  BI nd' F' (upd_tq (fun _ => tq') (upd_gq (fun _ => gq') s)).
Proof.
  intros nd nd' F F' s tq' gq' (B1 & B6 & B7 & B8 & B9 & ND) Hnd HF HB.
  split; [| split; [exact B6| split; [exact HB| split; [exact B8| split; [exact B9| exact Hnd]]]]].
  intros c Hc. pose proof (B1 c Hc) as X. destruct (HF c Hc) as [E1 E2]. unfold BIc in *.
  change (get_region _ c) with (get_region s c). change (get_cache _ c) with (get_cache s c). change (nchunks _ c) with (nchunks s c).
  change (everc _ c) with (everc s c). cbn [as_nprim_ever upd_tq upd_gq]. unfold nbatch in *. cbn [as_tq as_gq upd_tq upd_gq].
  unfold BIc_raw in *. repeat split; try lia.
Qed.

Lemma merge_aux_cnt : forall rest cur acc,
  let '(l, o) := merge_batches_aux cur rest acc in
  zlen l + zlen o = 1 + zlen rest + zlen acc
  /\ ((forall b, In b (cur :: rest) -> kBatchSize <= b_size b) -> forall b, In b l -> kBatchSize <= b_size b).
Proof.
  intros rest. induction rest as [|nx rest IH]; intros cur acc; cbn [merge_batches_aux].
  - rewrite zlen_cons, !(@zlen_nil batch). split; [lia|]. intros H b [<-|[]]. apply H. left; reflexivity.
  - destruct (zlen (b_items cur) + zlen (b_items nx) <=? kBatchCap).
    + set (cur' := mkBatch _ _ _). specialize (IH cur' (acc ++ [mkBatch (b_addr nx) [] kBatchSize])).
      destruct (merge_batches_aux cur' rest _) as [l o]. destruct IH as [IH1 IH2]. rewrite zlen_app, zlen_cons, (@zlen_nil batch) in IH1. rewrite zlen_cons.
      split; [lia|]. intros H. apply IH2. intros b [<-|Hb]; [| apply H; right; right; exact Hb].
      subst cur'. cbn [b_size]. pose proof (H cur ltac:(left; reflexivity)). pose proof (H nx ltac:(right; left; reflexivity)). lia.
    + specialize (IH nx acc). destruct (merge_batches_aux nx rest acc) as [l' o']. destruct IH as [IH1 IH2]. rewrite !zlen_cons.
      split; [lia|]. intros H b [<-|Hb]; [apply H; left; reflexivity|]. apply IH2; [| exact Hb]. intros b' Hb'. apply H. right. exact Hb'.
Qed.

Lemma merge_cnt : forall gq l o, merge_batches gq = (l, o) ->
  zlen l + zlen o = zlen gq /\ ((forall b, In b gq -> kBatchSize <= b_size b) -> forall b, In b l -> kBatchSize <= b_size b).
Proof.
  intros gq l o H. unfold merge_batches in H. destruct gq as [|b rest].
  - injection H as <- <-. rewrite !(@zlen_nil batch). split; [lia| intros _ b []].
  - pose proof (merge_aux_cnt rest b []) as M. rewrite H in M. rewrite (@zlen_nil batch), zlen_cons in *. destruct M as [M1 M2]. split; [lia| exact M2].
Qed.

Lemma recycle_cnt : forall F s0, BI 0 F s0 ->
  hoareW (fun s => s = s0) (recycle E) (fun s' _ => BI 0 F s').
Proof.
  intros F s0 HBI. pose proof HBI as (B1 & B6 & B7 & B8 & B9 & ND). unfold recycle. apply hoareW_get_bind. intros s ->.
  apply hoareW_checkK. intros _.
  match goal with |- hoareW _ (let '(_, _) := ?x in _) _ => destruct x as [gq1 empties] eqn:MG end.
  assert (MF : zlen gq1 + zlen empties = zlen (as_gq s0) /\ forall b, In b gq1 -> kBatchSize <= b_size b).
  { match type of MG with (if ?b then _ else _) = _ => destruct b end.
    - destruct (merge_cnt _ _ _ MG) as [M1 M2]. split; [exact M1|]. apply M2. intros b Hb. apply B7. apply in_app_iff. right; exact Hb.
    - injection MG as <- <-. rewrite (@zlen_nil batch). split; [lia|]. intros b Hb. apply B7. apply in_app_iff. right; exact Hb. }
  destruct MF as [MF1 MF2].
  destruct (pop_prefix gq1 (qbytes gq1) kQuarantineMin) as [popped kept] eqn:PP.
  pose proof (pop_prefix_app gq1 (qbytes gq1) kQuarantineMin) as PA. rewrite PP in PA. cbn [fst snd] in PA.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  apply do_recycle_cnt; [lia|].
  eapply (BI_view _ _ (upd_tq (fun _ => as_tq s0) (upd_gq (fun _ => kept) s0))); [reflexivity|].
  apply (BI_requeue 0 _ F F s0); [exact HBI| pose proof (zlen_nonneg (empties ++ popped)); lia| |].
  - intros c Hc. pose proof (proj1 (BI_c 0 F s0 c Hc HBI)) as X. unfold BIc_raw in X. unfold nbatch.
    rewrite zlen_app. rewrite <- PA in MF1. rewrite zlen_app in MF1. split; [nia| lia].
  - intros b Hb. apply in_app_iff in Hb as [Hb|Hb]; [apply B7; apply in_app_iff; left; exact Hb|]. apply MF2. rewrite <- PA. apply in_app_iff. right; exact Hb.
Qed.

Lemma drain_cnt : forall F s0, BI 0 F s0 ->
  hoareW (fun s => s = s0) (drain_if_needed E) (fun s' _ => BI 0 F s').
Proof.
  intros F s0 HBI. pose proof HBI as (B1 & B6 & B7 & B8 & B9 & ND). unfold drain_if_needed. apply hoareW_get_bind. intros s ->.
  destruct (kThreadQuarantineMax <? tq_bytes s0); [| apply hoareW_ret; intros s ->; exact HBI].
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). set (s1 := upd_tq _ _).
  assert (BI1 : BI 0 F s1).
  { subst s1. apply (BI_requeue 0 0 F F s0); [exact HBI| lia| |].
    - intros c Hc. pose proof (proj1 (BI_c 0 F s0 c Hc HBI)) as X. unfold BIc_raw in X. unfold nbatch. cbn [as_tq]. rewrite zlen_app, (@zlen_nil batch). split; [nia| lia].
    - cbn [as_tq app]. intros b Hb. apply B7. apply in_app_iff in Hb. apply in_app_iff. tauto. }
  apply hoareW_get_bind. intros s ->. destruct (kQuarantineMax <? gq_bytes s1); [apply recycle_cnt; exact BI1| apply hoareW_ret; intros s ->; exact BI1].
Qed.

Lemma enqueue_cnt : forall s0 cb n, BI 0 fzero s0 -> 0 <= n -> nbatch 0 s0 <= kNB ->
  hoareW (fun s => s = s0) (enqueue E cb n) (fun s' _ => BI 0 fzero s').
Proof.
  intros s0 cb n HBI Hn HNB. pose proof HBI as (B1 & B6 & B7 & B8 & B9 & ND). unfold enqueue, batch_alloc. apply hoareW_get_bind. intros s ->.
  assert (H24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:NEED end.
  - eapply hoareW_bind with (Q := fun s1 _ => BI 0 (fadd kBatchClass 1 fzero) s1 /\ as_tq s1 = as_tq s0 /\ as_gq s1 = as_gq s0).
    { eapply hoareW_bind; [apply (cache_pop_cnt 0 fzero s0 kBatchClass H24 HBI eq_refl HNB)|].
      intros [b|]; apply hoareW_pre; intros s1 [RC X]; [| apply hoareW_spin].
      destruct (b =? 0); [apply hoareW_spin|]. apply hoareW_ret. intros s ->. destruct RC as (_ & _ & (_ & T & G & _)). auto. }
    intros b. apply hoareW_upd. intros s1 (BI1 & T1 & G1). cbn beta.
    eapply (BI_view 0 fzero (upd_tq (fun _ => as_tq s1 ++ [mkBatch b [cb] (kBatchSize + n)]) (upd_gq (fun _ => as_gq s1) s1))); [reflexivity|].
    apply (BI_requeue 0 0 (fadd kBatchClass 1 fzero) fzero s1); [exact BI1| lia| |].
    + intros c Hc. unfold nbatch, fzero, fadd, b24. rewrite zlen_app, zlen_cons, (@zlen_nil batch). destruct (c =? kBatchClass); lia.
    + intros b' Hb. rewrite <- app_assoc in Hb. apply in_app_iff in Hb as [Hb|Hb].
      * apply (proj1 (proj2 (proj2 BI1))). apply in_app_iff. left; exact Hb.
      * apply in_app_iff in Hb as [[<-|[]]|Hb]; [cbn; lia|]. apply (proj1 (proj2 (proj2 BI1))). apply in_app_iff. right; exact Hb.
  - apply hoareW_upd. intros s ->. cbn beta. destruct (as_tq s0) as [|b0 l0] eqn:TQ; [discriminate|].
    set (l := b0 :: l0) in *. set (lb := List.last l (mkBatch 0 [] 0)).
    assert (IN : In lb l).
    { subst lb l. destruct (exists_last (l := b0 :: l0) ltac:(discriminate)) as (l' & z & EQ). rewrite EQ, last_last. apply in_app_iff. right; left; reflexivity. }
    eapply (BI_view 0 fzero (upd_tq (fun _ => removelast l ++ [mkBatch (b_addr lb) (b_items lb ++ [cb]) (b_size lb + n)]) (upd_gq (fun _ => as_gq s0) s0)));
      [unfold bview_of; cbn [as_regions as_cache as_chunks as_tq as_gq as_sec as_nprim_ever as_everc upd_tq upd_gq]; rewrite TQ; reflexivity|].
    apply (BI_requeue 0 0 fzero fzero s0); [exact HBI| lia| |].
    + intros c Hc. unfold nbatch. rewrite TQ, zlen_app, zlen_removelast by (subst l; discriminate). rewrite zlen_cons, (@zlen_nil batch). split; [lia| unfold fzero; lia].
    + intros b' Hb. rewrite <- app_assoc in Hb. apply in_app_iff in Hb as [Hb|Hb].
      * apply B7. apply in_app_iff. left. rewrite removelast_eq in Hb. subst lb. subst l.
        destruct (exists_last (l := b0 :: l0) ltac:(discriminate)) as (l' & z & EQ). rewrite EQ in Hb |- *. rewrite removelast_last in Hb. apply in_app_iff. left; exact Hb.
      * apply in_app_iff in Hb as [[<-|[]]|Hb]; [| apply B7; apply in_app_iff; right; exact Hb]. cbn [b_size].
        pose proof (B7 lb ltac:(apply in_app_iff; left; exact IN)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AQbound_tg : forall s s', as_tq s' = as_tq s -> as_gq s' = as_gq s -> AQbound s -> AQbound s'.
Proof. intros s s' T G H. unfold AQbound, tq_bytes, gq_bytes in *. rewrite T, G. exact H. Qed.

Lemma afree_core_cnt : forall s0 key p, BI 0 fzero s0 -> AQbound s0 ->
  hoareW (fun s => s = s0) (afree_core E key p) (fun s' _ => BI 0 fzero s').
Proof.
  intros s0 key p HBI QB. pose proof HBI as (B1 & B6 & B7 & B8 & B9 & ND). unfold afree_core. apply hoareW_get_bind. intros s ->.
  destruct (as_chunks s0 !! (p - kChunkHeaderSize)) as [meta|] eqn:Hm; [| apply hoareW_undef].
  destruct (cm_state meta) as [aid|] eqn:ST; [| apply hoareW_undef].
  destruct (negb (cm_user_beg meta =? p)); [apply hoareW_undef|].
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->). set (s1 := upd_ts _ s0).
  eapply hoareW_bind; [apply depot_put_view|]. intros fid. apply hoareW_pre. intros s2 V2.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->). set (cm' := mkCM _ _ _ _ _). set (s3 := upd_chunks _ s2).
  pose proof V2 as V2'. unfold bview_of in V2'. injection V2' as Vr Vc Vk Vt Vg Vs Vn Ve.
  assert (BI2 : BI 0 fzero s2) by (eapply BI_view; [exact V2| eapply BI_view; [| exact HBI]; reflexivity]).
  assert (Hm2 : as_chunks s2 !! (p - kChunkHeaderSize) = Some meta) by (rewrite Vk; exact Hm).
  assert (BI3 : BI 0 fzero s3) by (apply (BI_chunk_flip 0 fzero s2 _ meta cm' BI2 Hm2); reflexivity).
  assert (QB3 : AQbound s3) by (apply (AQbound_tg s0 s3); [cbn; exact Vt| cbn; exact Vg| exact QB]).
  pose proof (B6 _ _ Hm) as [Hn _].
  eapply hoareW_bind; [apply (enqueue_cnt s3 _ (cm_n meta) BI3 ltac:(lia) (nbatch_bound s3 BI3 QB3))|].
  intros []. apply hoareW_pre. intros s4 BI4. apply drain_cnt. exact BI4.
Qed.

Theorem binv_init : binv (astate0 E).
Proof.
  unfold binv, BI. split; [| split; [intros cb cm H; cbn in H; rewrite lookup_empty in H; discriminate| split; [intros b []| split; [intros sc []| split; [constructor| lia]]]]].
  intros c Hc. unfold BIc, BIc_raw, get_region, get_cache, nchunks, chunk_list, everc, nbatch. cbn -[Z.mul Z.add Z.div Z.modulo class_size b24 kNB kUserMapSize kFreeArrayMapSize kFreeArrayOffset kMaxSize].
  rewrite !lookup_empty. cbn -[Z.mul Z.add Z.div Z.modulo class_size b24 kNB kUserMapSize kFreeArrayMapSize kFreeArrayOffset kMaxSize].
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; lia)) as [_ SZ]. pose proof (b24_range c).
  rewrite Z.div_0_l by lia. rewrite Z.mod_0_l by lia. unfold fzero, kFreeArrayOffset, kFreeArrayMapSize, kUserMapSize, kMaxSize, kNB.
  rewrite map_to_list_empty. cbn [countZ]. rewrite !(@zlen_nil Z), !(@zlen_nil batch).
  repeat split; try lia; try nia.
Qed.

Theorem binv_amalloc : forall s0 key n, 0 <= n -> binv s0 -> AQbound s0 ->
  hoareW (fun s => s = s0) (amalloc E key n) (fun s' _ => binv s').
Proof.
  intros s0 key n Hn HBI QB. unfold amalloc, binv in *.
  eapply hoareW_conseq; [apply (amalloc_core_cnt s0 key n Hn HBI (nbatch_bound s0 HBI QB))| auto|]. cbn beta. intros s r [X _]. exact X.
Qed.

Theorem binv_afree : forall s0 key p, binv s0 -> AQbound s0 ->
  hoareW (fun s => s = s0) (afree E key p) (fun s' _ => binv s').
Proof.
  intros s0 key p HBI QB. unfold afree, ia_init, binv in *. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  set (s1 := upd_ia_inited true s0). assert (BI1 : BI 0 fzero s1) by (eapply BI_view; [| exact HBI]; reflexivity).
  destruct (p =? 0); [apply hoareW_ret; intros s ->; exact BI1|].
  apply afree_core_cnt; [exact BI1| exact QB].
Qed.

Theorem binv_arealloc : forall s0 key p n, 0 <= n -> binv s0 -> AQbound s0 ->
  hoareW (fun s => s = s0) (arealloc E key p n) (fun s' _ => binv s').
Proof.
  intros s0 key p n Hn HBI QB. unfold arealloc, ia_init, binv in *. apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  set (s1 := upd_ia_inited true s0). assert (BI1 : BI 0 fzero s1) by (eapply BI_view; [| exact HBI]; reflexivity).
  assert (QB1 : AQbound s1) by exact QB.
  destruct (p =? 0).
  { eapply hoareW_conseq; [apply (amalloc_core_cnt s1 key n Hn BI1 (nbatch_bound s1 BI1 QB1))| auto|]. cbn beta. intros s r [X _]. exact X. }
  destruct (n =? 0).
  { eapply hoareW_bind; [apply afree_core_cnt; [exact BI1| exact QB1]|]. intros []. apply hoareW_ret. auto. }
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sy & -> & ->). set (s2 := upd_ts _ s1).
  assert (BI2 : BI 0 fzero s2) by (eapply BI_view; [| exact BI1]; reflexivity).
  eapply hoareW_bind; [apply (amalloc_core_cnt s2 key n Hn BI2 (nbatch_bound s2 BI2 QB1))|].
  intros [q|]; apply hoareW_pre; intros s3 (BI3 & T3 & G3); [| apply hoareW_ret; intros s ->; exact BI3].
  apply hoareW_get_bind. intros s ->.
  destruct (as_chunks s3 !! (p - kChunkHeaderSize)) as [meta|]; [| apply hoareW_undef].
  destruct (cm_state meta); [| apply hoareW_undef]. destruct (cm_user_beg meta =? p); [| apply hoareW_undef].
  eapply hoareW_bind; [apply afree_core_cnt; [exact BI3| apply (AQbound_tg s0 s3); [exact T3| exact G3| exact QB]]|].
  intros []. apply hoareW_ret. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sumZ_scale : forall {A} (k : Z) (f : A -> Z) l, sumZ (fun x => k * f x) l = k * sumZ f l.
Proof. induction l; cbn; [lia|]. rewrite IHl. lia. Qed.
Lemma sumZ_add : forall {A} (f g : A -> Z) l, sumZ (fun x => f x + g x) l = sumZ f l + sumZ g l.
Proof. induction l; cbn; [lia|]. rewrite IHl. lia. Qed.
Lemma sumZ_const : forall {A} (k : Z) (l : list A), sumZ (fun _ => k) l = k * zlen l.
Proof. induction l; cbn; [rewrite (@zlen_nil A); lia|]. rewrite IHl, zlen_cons. lia. Qed.

Lemma sum_class_size : sumZ class_size classes30 = 231936.
Proof. vm_compute. reflexivity. Qed.
Lemma sum_b24_class_size : sumZ (fun c => b24 c * class_size c) classes30 = 8192.
Proof. vm_compute. reflexivity. Qed.
Lemma zlen_classes30 : zlen classes30 = 30.
Proof. reflexivity. Qed.
Lemma In_classes30 : forall c, In c classes30 -> 1 <= c <= kLargestClassID.
Proof. intros c H. unfold classes30 in H. apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. unfold kLargestClassID. lia. Qed.

Lemma regions_bytes_sumZ : forall a,
  regions_bytes a = sumZ (fun c => rg_mapped_user (get_region a c) + rg_mapped_fa (get_region a c)) classes30.
Proof. intros a. unfold regions_bytes. rewrite <- fold_right_sumZ. reflexivity. Qed.

(* [comment removed for export] *)
Lemma class_maps_bound : forall a c, binv a -> 1 <= c <= kLargestClassID ->
  8 * (rg_mapped_user (get_region a c) + rg_mapped_fa (get_region a c))
  <= 9 * (class_size c * (as_nprim_ever a + 8 + b24 c * kNB) + kUserMapSize) + 8 * kFreeArrayMapSize.
Proof.
  intros a c HBI Hc. destruct (BI_c 0 fzero a c Hc HBI) as [X _]. unfold BIc_raw in X.
  destruct X as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  pose proof (class_size_mod c ltac:(unfold kLargestClassID in Hc; lia)) as [_ SZ]. pose proof (b24_range c) as R24.
  set (size := class_size c) in *. set (r := get_region a c) in *.
  assert (D : 32 * (rg_alloc_user r / size) <= rg_alloc_user r).
  { transitivity (size * (rg_alloc_user r / size)); [apply Z.mul_le_mono_nonneg_r; [apply Z.div_pos; lia| lia]| apply Z.mul_div_le; lia]. }
  assert (M : size * (everc a c + 8 + b24 c * kNB) <= size * (as_nprim_ever a + 8 + b24 c * kNB)) by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold kNB in *. lia.
Qed.

Theorem M2 : forall a, AWf E [] [] a -> AQbound a -> binv a ->
  regions_bytes a <= 4096 * (160 * as_nprim_ever a + 100000).
Proof.
  intros a _ _ HBI. rewrite regions_bytes_sumZ.
  set (f := fun c => rg_mapped_user (get_region a c) + rg_mapped_fa (get_region a c)).
  set (g := fun c => (9 * (as_nprim_ever a + 8)) * class_size c + (9 * kNB) * (b24 c * class_size c) + (9 * kUserMapSize + 8 * kFreeArrayMapSize)).
  assert (LE : sumZ (fun c => 8 * f c) classes30 <= sumZ g classes30).
  { apply sumZ_le. intros c Hc. subst f g. cbn beta. pose proof (class_maps_bound a c HBI (In_classes30 c Hc)). lia. }
  rewrite sumZ_scale in LE. subst g. rewrite !sumZ_add, !sumZ_scale, sumZ_const, sum_class_size, sum_b24_class_size, zlen_classes30 in LE.
  assert (NP : 0 <= as_nprim_ever a).
  { destruct (BI_c 0 fzero a 1 ltac:(unfold kLargestClassID; lia) HBI) as [X _]. unfold BIc_raw in X. lia. }
  unfold kNB, kUserMapSize, kFreeArrayMapSize in LE. rewrite ?sumZ_const, ?zlen_classes30 in LE. lia.
Qed.

(* [comment removed for export] *)
Theorem binv_mapped_user : forall a c, binv a -> 1 <= c <= kLargestClassID ->
  rg_mapped_user (get_region a c) <= class_size c * (everc a c + 8 + b24 c * kNB) + kUserMapSize
  /\ 0 <= everc a c <= as_nprim_ever a.
Proof.
  intros a c HBI Hc. destruct (BI_c 0 fzero a c Hc HBI) as [X _]. unfold BIc_raw in X. lia.
Qed.

(* [comment removed for export] *)
Theorem binv_user_gap : forall a c, binv a -> 1 <= c <= kLargestClassID ->
  rg_mapped_user (get_region a c) <= rg_alloc_user (get_region a c) + kUserMapSize + kMaxSize.
Proof.
  intros a c HBI Hc. destruct (BI_c 0 fzero a c Hc HBI) as [X _]. unfold BIc_raw in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_cost (sc : secchunk) : Z :=
  sc_map_size sc + 4096 * (if kBigMapSize <=? sc_map_size sc then sc_map_size sc / 32768 else 0).
Definition qc (n : Z) : Z := map_size n + 4096 * (if kBigMapSize <=? map_size n then map_size n / 32768 else 0).
(* [comment removed for export] *)
Definition dep_live (a : astate) : Z := fold_right (fun b acc => arefund (snd b) + acc) 0 (live_blocks a).
Definition interiors_a (a : astate) : Z :=
  fold_right (fun sc acc => (if kBigMapSize <=? sc_map_size sc then sc_map_size sc / 32768 else 0) + acc) 0 (as_sec a).

Lemma sumZ_filter : forall {A} (P : A -> bool) (f : A -> Z) l, sumZ f (List.filter P l) = sumZ (fun x => if P x then f x else 0) l.
Proof. induction l; cbn; [reflexivity|]. destruct (P a); cbn; rewrite IHl; lia. Qed.
Lemma sumZ_concat : forall {A} (f : A -> Z) (ls : list (list A)), sumZ f (concat ls) = sumZ (fun l => sumZ f l) ls.
Proof. induction ls; cbn; [reflexivity|]. rewrite sumZ_app, IHls. reflexivity. Qed.
Lemma qbytes_sumZ : forall l, qbytes l = sumZ b_size l.
Proof. induction l; [reflexivity|]. change (qbytes (a :: l)) with (b_size a + qbytes l). cbn [sumZ]. rewrite IHl. reflexivity. Qed.
Lemma NoDup_map_fst_filter : forall {A B} (P : A * B -> bool) (l : list (A * B)),
  List.NoDup (map fst l) -> List.NoDup (map fst (List.filter P l)).
Proof.
  induction l as [|x l IH]; cbn; intros ND; [constructor|]. inversion ND; subst. destruct (P x); cbn; [| apply IH; assumption].
  constructor; [| apply IH; assumption]. intros Hin. apply in_map_iff in Hin as (y & EQ & Hy). apply filter_In in Hy as [Hy _].
  apply H1. rewrite <- EQ. apply in_map_iff. exists y; auto.
Qed.

(* [comment removed for export] *)
Lemma cover_sum : forall secs (M : gmap Z chunkmeta), List.NoDup (map sc_map_beg secs) ->
  (forall sc, In sc secs -> exists cb cm, M !! cb = Some cm /\ cm_prim cm = None /\ cm_alloc_beg cm = sc_map_beg sc + kPageSize
                                         /\ sc_map_size sc = map_size (cm_n cm)) ->
  sumZ sec_cost secs <= sumZ (fun p => match cm_prim (snd p) with None => qc (cm_n (snd p)) | Some _ => 0 end) (map_to_list M).
Proof.
  intros secs. induction secs as [|sc rest IH]; intros M ND COV; cbn [sumZ].
  - apply sumZ_nonneg. intros [cb cm] _. cbn [snd]. destruct (cm_prim cm); [lia|]. unfold qc. pose proof (map_size_pos (cm_n cm)).
    destruct (kBigMapSize <=? _); [| unfold kPageSize in *; lia]. assert (0 <= map_size (cm_n cm) / 32768) by (apply Z.div_pos; unfold kPageSize in *; lia). unfold kPageSize in *; lia.
  - destruct (COV sc ltac:(left; reflexivity)) as (cb & cm & H & PC & AB & MS).
    rewrite <- (sumZ_perm _ _ _ (map_to_list_delete M cb cm H)). cbn [sumZ snd]. rewrite PC.
    assert (E1 : sec_cost sc = qc (cm_n cm)) by (unfold sec_cost, qc; rewrite MS; reflexivity).
    inversion ND as [|x0 l0 NIN NDr X0]; subst.
    specialize (IH (delete cb M) NDr).
    assert (COV' : forall sc', In sc' rest -> exists cb' cm', delete cb M !! cb' = Some cm' /\ cm_prim cm' = None
                      /\ cm_alloc_beg cm' = sc_map_beg sc' + kPageSize /\ sc_map_size sc' = map_size (cm_n cm')).
    { intros sc' Hin. destruct (COV sc' ltac:(right; exact Hin)) as (cb' & cm' & H' & PC' & AB' & MS'). exists cb', cm'.
      split; [| auto]. rewrite lookup_delete_ne; [exact H'|]. intros ->. rewrite H in H'. injection H' as ->.
      apply NIN. apply in_map_iff. exists sc'. split; [unfold kPageSize in *; lia| exact Hin]. }
    specialize (IH COV'). lia.
Qed.

(* [comment removed for export] *)
Lemma map_size_mod : forall n, map_size n mod 4096 = 0.
Proof. intros n. unfold map_size, kPageSize. rewrite Z.add_mod, round_up_mod, Z.mod_same by lia. reflexivity. Qed.
Lemma qc_arefund : forall n, from_primary n = false -> 4096 * arefund n = qc n.
Proof.
  intros n PR. unfold arefund, qc. rewrite PR. pose proof (map_size_mod n) as M. pose proof (Z.div_mod (map_size n) 4096 ltac:(lia)) as D.
  destruct (map_size n <? kBigMapSize) eqn:B; [apply Z.ltb_lt in B| apply Z.ltb_ge in B].
  - replace (kBigMapSize <=? map_size n) with false by (symmetry; apply Z.leb_gt; lia). lia.
  - replace (kBigMapSize <=? map_size n) with true by (symmetry; apply Z.leb_le; lia). lia.
Qed.
Lemma map_size_le : forall n, 0 <= n -> map_size n <= n + 12296.
Proof.
  intros n Hn. unfold map_size, needed, needed1. pose proof (rounded_ge n) as (R1 & R2 & R3). pose proof (rz_size_pos n) as RZ.
  pose proof (round_up_lt (if from_primary n then rounded n + rz_size n else rounded n + rz_size n + rz_size n) kPageSize ltac:(unfold kPageSize; lia)).
  destruct (from_primary n); unfold kPageSize in *; lia.
Qed.
Lemma qc_quar_bound : forall n, 0 <= n -> from_primary n = false -> 20 * qc n <= 27 * n.
Proof.
  intros n Hn PR. pose proof (map_size_le n Hn) as ML. pose proof (map_size_pos n) as MP.
  assert (BIG : 64512 < n).
  { destruct (Z.le_gt_cases n 64512) as [LE|GT]; [| exact GT]. pose proof (proj2 (from_primary_iff n Hn) LE). congruence. }
  unfold qc. assert (8 * (4096 * (if kBigMapSize <=? map_size n then map_size n / 32768 else 0)) <= map_size n).
  { destruct (kBigMapSize <=? map_size n); [| unfold kPageSize in *; lia]. pose proof (Z.mul_div_le (map_size n) 32768 ltac:(lia)). lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma quarantine_sum0 : forall a, AWf E [] [] a ->
  sumZ (fun p => match cm_state (snd p) with CQuarantined _ _ => cm_n (snd p) | CAllocated _ => 0 end) (chunk_list a)
  <= tq_bytes a + gq_bytes a.
Proof.
  intros a WF. destruct WF as (_ & _ & _ & [K1 _] & (Q1 & _) & _).
  set (isq := fun p : Z * chunkmeta => match cm_state (snd p) with CQuarantined _ _ => true | CAllocated _ => false end).
  rewrite (sumZ_ext _ (fun p => if isq p then cm_n (snd p) else 0)) by (intros [cb cm] _; subst isq; cbn; destruct (cm_state cm); reflexivity).
  rewrite <- sumZ_filter. set (Q := List.filter isq (chunk_list a)).
  (* [comment removed for export] *)
  rewrite (sumZ_ext _ (fun p => chunk_used_size a (fst p)) Q).
  2:{ intros [cb cm] Hin. cbn [fst snd]. unfold chunk_used_size. apply filter_In in Hin as [Hin _].
      apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. rewrite Hin. reflexivity. }
  rewrite <- (sumZ_map (chunk_used_size a) fst).
  set (B := as_tq a ++ as_gq a).
  transitivity (sumZ (chunk_used_size a) (concat (map b_items B))).
  - apply sumZ_incl_nodup.
    + apply NoDup_map_fst_filter. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list.
    + intros cb Hin. apply in_map_iff in Hin as ([cb' cm] & EQ & Hin). cbn in EQ. subst cb'. apply filter_In in Hin as [Hin QQ].
      apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. pose proof (K1 _ _ Hin) as (_ & _ & _ & _ & ST).
      subst isq. cbn in QQ. destruct (cm_state cm); [discriminate|]. destruct ST as (_ & _ & [[]|(b & Hb & Hcb)]).
      unfold all_batches in Hb. rewrite app_nil_r in Hb. apply in_concat. exists (b_items b). split; [apply in_map_iff; exists b; auto| exact Hcb].
    + intros cb Hin. unfold chunk_used_size. destruct (as_chunks a !! cb) as [cm|] eqn:H; [| lia]. pose proof (K1 _ _ H) as (_ & X & _). lia.
  - rewrite sumZ_concat, sumZ_map.
    transitivity (sumZ b_size B).
    + apply sumZ_le. intros b Hb. destruct (Q1 b Hb) as [(_ & _ & _ & _ & _ & SZ & _) _]. rewrite SZ, fold_right_sumZ. unfold kBatchSize. lia.
    + subst B. rewrite sumZ_app, <- !qbytes_sumZ. unfold tq_bytes, gq_bytes in *. lia.
Qed.
Lemma quarantine_sum : forall a, AWf E [] [] a -> AQbound a ->
  sumZ (fun p => match cm_state (snd p) with CQuarantined _ _ => cm_n (snd p) | CAllocated _ => 0 end) (chunk_list a)
  <= kThreadQuarantineMax + kQuarantineMax.
Proof. intros a WF [TQ GQ]. pose proof (quarantine_sum0 a WF). lia. Qed.

Theorem M1 : forall a, AWf E [] [] a -> AQbound a -> binv a ->
  sec_bytes a + 4096 * interiors_a a <= 4096 * (dep_live a + 100000).
Proof.
  intros a WF QB HBI. pose proof WF as (_ & _ & _ & [K1 _] & _ & _ & _). destruct HBI as (_ & _ & _ & B8 & B9 & _).
  assert (LHS : sec_bytes a + 4096 * interiors_a a = sumZ sec_cost (as_sec a)).
  { unfold sec_bytes, interiors_a, sec_cost. rewrite !fold_right_sumZ, sumZ_add, sumZ_scale. reflexivity. }
  rewrite LHS. pose proof (cover_sum (as_sec a) (as_chunks a) B9 B8) as C1. fold (chunk_list a) in C1.
  set (gA := fun p : Z * chunkmeta => match cm_state (snd p) with CAllocated _ => 4096 * arefund (cm_n (snd p)) | _ => 0 end).
  set (gQ := fun p : Z * chunkmeta => match cm_prim (snd p), cm_state (snd p) with None, CQuarantined _ _ => qc (cm_n (snd p)) | _, _ => 0 end).
  assert (SPLIT : sumZ (fun p => match cm_prim (snd p) with None => qc (cm_n (snd p)) | Some _ => 0 end) (chunk_list a) = sumZ gA (chunk_list a) + sumZ gQ (chunk_list a)).
  { rewrite <- sumZ_add. apply sumZ_ext. intros [cb cm] Hin. subst gA gQ. cbn [snd].
    apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. pose proof (K1 _ _ Hin) as (_ & _ & _ & PRM & _).
    destruct (cm_prim cm) as [c|]; destruct (cm_state cm); try lia.
    - destruct PRM as [PR _]. unfold arefund. rewrite PR. lia.
    - destruct PRM as [PR _]. rewrite (qc_arefund _ PR). lia. }
  assert (DEP : sumZ gA (chunk_list a) = 4096 * dep_live a).
  { unfold dep_live, live_blocks. rewrite fold_right_sumZ, sumZ_map, sumZ_filter, <- sumZ_scale. apply sumZ_ext. intros [cb cm] _. subst gA. cbn [snd]. destruct (cm_state cm); lia. }
  assert (QQ : 20 * sumZ gQ (chunk_list a) <= 27 * (kThreadQuarantineMax + kQuarantineMax)).
  { pose proof (quarantine_sum a WF QB) as QS.
    assert (P : sumZ (fun p => 20 * gQ p) (chunk_list a)
                <= sumZ (fun p => 27 * match cm_state (snd p) with CQuarantined _ _ => cm_n (snd p) | CAllocated _ => 0 end) (chunk_list a)).
    { apply sumZ_le. intros [cb cm] Hin. subst gQ. cbn [snd].
      apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. pose proof (K1 _ _ Hin) as (_ & N1 & _ & PRM & _).
      destruct (cm_prim cm) as [c|]; destruct (cm_state cm); try lia. destruct PRM as [PR _]. apply qc_quar_bound; [lia| exact PR]. }
    rewrite !sumZ_scale in P. lia. }
  unfold kThreadQuarantineMax, kQuarantineMax in QQ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nbig_live (s : astate) : Z := zlen (List.filter (fun b => 64512 <? snd b) (live_blocks s)).

Lemma cover_count : forall secs (M : gmap Z chunkmeta), List.NoDup (map sc_map_beg secs) ->
  (forall sc, In sc secs -> exists cb cm, M !! cb = Some cm /\ cm_prim cm = None /\ cm_alloc_beg cm = sc_map_beg sc + kPageSize
                                         /\ sc_map_size sc = map_size (cm_n cm)) ->
  zlen secs <= countZ (fun p => match cm_prim (snd p) with None => true | Some _ => false end) (map_to_list M).
Proof.
  intros secs. induction secs as [|sc rest IH]; intros M ND COV.
  - rewrite (@zlen_nil secchunk). apply countZ_nonneg.
  - destruct (COV sc ltac:(left; reflexivity)) as (cb & cm & H & PC & AB & MS).
    rewrite <- (countZ_perm _ _ _ (map_to_list_delete M cb cm H)). cbn [countZ snd]. rewrite PC. rewrite zlen_cons.
    inversion ND as [|x0 l0 NIN NDr X0]; subst.
    specialize (IH (delete cb M) NDr).
    assert (COV' : forall sc', In sc' rest -> exists cb' cm', delete cb M !! cb' = Some cm' /\ cm_prim cm' = None
                      /\ cm_alloc_beg cm' = sc_map_beg sc' + kPageSize /\ sc_map_size sc' = map_size (cm_n cm')).
    { intros sc' Hin. destruct (COV sc' ltac:(right; exact Hin)) as (cb' & cm' & H' & PC' & AB' & MS'). exists cb', cm'.
      split; [| auto]. rewrite lookup_delete_ne; [exact H'|]. intros ->. rewrite H in H'. injection H' as ->.
      apply NIN. apply in_map_iff. exists sc'. split; [unfold kPageSize in *; lia| exact Hin]. }
    specialize (IH COV'). lia.
Qed.

Lemma countZ_filter_len : forall {A} (P : A -> bool) l, zlen (List.filter P l) = countZ P l.
Proof. induction l; cbn; [reflexivity|]. destruct (P a); cbn; rewrite ?zlen_cons, IHl; lia. Qed.
Lemma countZ_map : forall {A B} (P : B -> bool) (g : A -> B) l, countZ P (map g l) = countZ (fun x => P (g x)) l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.
Lemma countZ_filter : forall {A} (P Q : A -> bool) l, countZ Q (List.filter P l) = countZ (fun x => P x && Q x) l.
Proof. induction l; cbn; [reflexivity|]. destruct (P a); cbn; rewrite IHl; reflexivity. Qed.
Lemma countZ_mono : forall {A} (P Q : A -> bool) l, (forall x, In x l -> P x = true -> Q x = true) -> countZ P l <= countZ Q l.
Proof.
  induction l; cbn; intros H; [lia|]. specialize (IHl ltac:(intros; apply H; auto)).
  destruct (P a) eqn:EP; [rewrite (H a ltac:(left; reflexivity) EP)| destruct (Q a)]; lia.
Qed.
Lemma countZ_split : forall {A} (P Q : A -> bool) l,
  countZ P l = countZ (fun x => P x && Q x) l + countZ (fun x => P x && negb (Q x)) l.
Proof. induction l; cbn; [lia|]. destruct (P a), (Q a); cbn; lia. Qed.
Lemma countZ_sumZ : forall {A} (P : A -> bool) l, countZ P l = sumZ (fun x => if P x then 1 else 0) l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.

Theorem sec_count : forall a, AWf E [] [] a -> binv a ->
  64513 * zlen (as_sec a) <= 64513 * nbig_live a + tq_bytes a + gq_bytes a.
Proof.
  intros a WF HBI. pose proof WF as (_ & _ & _ & [K1 _] & _ & _ & _). destruct HBI as (_ & _ & _ & B8 & B9 & _).
  pose proof (cover_count (as_sec a) (as_chunks a) B9 B8) as C1. fold (chunk_list a) in C1.
  set (isN := fun p : Z * chunkmeta => match cm_prim (snd p) with None => true | Some _ => false end) in *.
  set (isA := fun p : Z * chunkmeta => match cm_state (snd p) with CAllocated _ => true | _ => false end).
  rewrite (countZ_split isN isA) in C1.
  assert (FACT : forall cb cm, In (cb, cm) (chunk_list a) -> cm_prim cm = None -> 64512 < cm_n cm).
  { intros cb cm Hin PN. apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. pose proof (K1 _ _ Hin) as (_ & N1 & _ & PRM & _).
    rewrite PN in PRM. destruct PRM as [PR _].
    destruct (Z.le_gt_cases (cm_n cm) 64512) as [LE|GT]; [| exact GT]. pose proof (proj2 (from_primary_iff (cm_n cm) ltac:(lia)) LE). congruence. }
  (* [comment removed for export] *)
  assert (L1 : countZ (fun x => isN x && isA x) (chunk_list a) <= nbig_live a).
  { unfold nbig_live, live_blocks. rewrite countZ_filter_len, countZ_map, countZ_filter.
    apply countZ_mono. intros [cb cm] Hin H. subst isN isA. cbn [snd] in *. apply andb_prop in H as [H1 H2].
    destruct (cm_prim cm) eqn:PN; [discriminate|]. destruct (cm_state cm); [| discriminate]. cbn. apply Z.ltb_lt. exact (FACT cb cm Hin PN). }
  (* [comment removed for export] *)
  assert (L2 : 64513 * countZ (fun x => isN x && negb (isA x)) (chunk_list a) <= tq_bytes a + gq_bytes a).
  { pose proof (quarantine_sum0 a WF) as QS. rewrite countZ_sumZ, <- sumZ_scale.
    etransitivity; [| exact QS]. apply sumZ_le. intros [cb cm] Hin. subst isN isA. cbn [snd].
    pose proof Hin as Hin'. apply list_elem_of_In in Hin'. apply elem_of_map_to_list in Hin'. pose proof (K1 _ _ Hin') as (_ & N1 & _).
    destruct (cm_prim cm) eqn:PN; destruct (cm_state cm); cbn; try lia.
    pose proof (FACT cb cm Hin PN). lia. }
  lia.
Qed.

End B2.
End RC__1.
