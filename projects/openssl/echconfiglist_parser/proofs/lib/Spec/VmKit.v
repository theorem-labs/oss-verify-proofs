(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma u64_range : forall (x : word), 0 <= bv_unsigned x < 2^64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.
Lemma u64_lit : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.
Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma bv_eqb_refl : forall {n : N} (a : bv n), bv_eqb a a = true.
Proof. intros n a. apply bv_eqb_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, Bool.andb_assoc. reflexivity.
Qed.

Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
  induction l as [|[b0 s0] l IH]; intros lo n b s H Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)]. inversion E; subst.
  unfold iv_overlap in H1.
  destruct (Z.ltb_spec0 (bv_unsigned lo) (bv_unsigned b + bv_unsigned s));
  destruct (Z.ltb_spec0 (bv_unsigned b) (bv_unsigned lo + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
  induction l as [|[b0 s0] l IH]; intros lo n H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros; apply H; right; assumption).
  specialize (H b0 s0 (or_introl eq_refl)). unfold iv_overlap.
  destruct (Z.ltb_spec0 (bv_unsigned lo) (bv_unsigned b0 + bv_unsigned s0));
  destruct (Z.ltb_spec0 (bv_unsigned b0) (bv_unsigned lo + bv_unsigned n)); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_head : forall (a n : word) l, map_has ((a, n) :: l) a n = true.
Proof. intros. unfold map_has. cbn. rewrite !bv_eqb_refl. reflexivity. Qed.
Lemma map_has_cons : forall p (a n : word) l, map_has l a n = true -> map_has (p :: l) a n = true.
Proof. intros [b s] a n l H. unfold map_has in *. cbn. rewrite H. apply Bool.orb_true_r. Qed.
Lemma map_remove_nil : forall (a : word), map_remove [] a = [].
Proof. reflexivity. Qed.
Lemma map_remove_head : forall (a n : word) l, map_remove ((a, n) :: l) a = map_remove l a.
Proof. intros. unfold map_remove. cbn. rewrite bv_eqb_refl. reflexivity. Qed.
Lemma map_remove_skip : forall (b s a : word) l,
  b <> a -> map_remove ((b, s) :: l) a = (b, s) :: map_remove l a.
Proof.
  intros b s a l NE. unfold map_remove. cbn. destruct (bv_eqb b a) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. contradiction.
Qed.
Lemma map_remove_notin : forall l (a : word),
  (forall s, ~ In (a, s) l) -> map_remove l a = l.
Proof.
  induction l as [|[b s] l IH]; intros a H; [reflexivity|].
  destruct (bv_eq_dec _ b a) as [->|NE].
  - exfalso. apply (H s). left. reflexivity.
  - rewrite map_remove_skip by exact NE. rewrite IH; [reflexivity|]. intros s' Hin. apply (H s'). right. exact Hin.
Qed.
(* [comment removed for export] *)
Lemma disjoint_base_ne : forall (lo n b s : word),
  0 < bv_unsigned n -> 0 < bv_unsigned s ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  b <> lo.
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.

Lemma live_bytes_map_remove_le : forall l (a : word), live_bytes (map_remove l a) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
    fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_self : forall (a sz : word),
  iv_subtract a sz (bv_unsigned a) (bv_unsigned a + bv_unsigned sz) = [].
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_suffix : forall (a sz : word) (lo hi : Z),
  bv_unsigned a < lo -> lo <= bv_unsigned a + bv_unsigned sz ->
  bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [(a, Z_to_bv 64 (lo - bv_unsigned a))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
  rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sizes : forall (a sz : word) (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  bv_unsigned sz <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract. apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64_lit by lia. lia.
Qed.

Lemma maps_subtract_sizes : forall l (lo hi : Z) N,
  0 <= lo -> hi < 2 ^ 64 ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
  inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
  - apply iv_subtract_sizes; assumption.
  - apply IH; assumption.
Qed.

Lemma map_remove_sizes : forall l (a : word) N,
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  Forall (fun p => bv_unsigned (snd p) <= N) (map_remove l a).
Proof.
  intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
  apply List.incl_filter.
Qed.

Lemma maps_subtract_length : forall l (lo hi : Z),
  (length (maps_subtract l lo hi) <= 2 * length l)%nat.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
  cbn [maps_subtract]. rewrite length_app. cbn [length].
  assert (length (iv_subtract a sz lo hi) <= 2)%nat.
  { unfold iv_subtract. rewrite length_app.
    destruct (_ <? _); destruct (_ <? _); cbn; lia. }
  specialize (IH lo hi). lia.
Qed.

Lemma map_remove_length : forall l (a : word), (length (map_remove l a) <= length l)%nat.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
    fold (map_remove l a); specialize (IH a); lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma maps_subtract_all_nil : forall maps, maps_subtract_all maps [] = maps.
Proof. reflexivity. Qed.

Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

Lemma vm_backing_used_simple : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.

Lemma vm_backed_bytes_no_noaccess : forall h,
  vm_noaccess h = [] -> vm_backed_bytes h = vm_live_bytes h.
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.

Lemma grant_budget_intro : forall m n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  vm_backing_used m + n <= vm_limit (m_vmmaps m).
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.

(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [exact Hl | exact Hm]|].
  unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.

