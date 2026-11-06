(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require FastWord.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition bas (p : word * word) : Z := bv_unsigned (fst p).
Definition bsz (p : word * word) : Z := bv_unsigned (snd p).

Definition iv_disj (lo hi : Z) (q : word * word) : Prop := hi <= bas q \/ bas q + bsz q <= lo.

Definition inl (l : list (word * word)) (x : Z) : Prop := exists p, In p l /\ bas p <= x < bas p + bsz p.

Definition iv_sub (p q : word * word) : Prop := bas q <= bas p /\ bas p + bsz p <= bas q + bsz q.

Notation two64 := FastWord.two64.

Lemma bas_range (p : word * word) : 0 <= bas p < two64.
Proof. unfold bas. pose proof (bv_unsigned_in_range 64 (fst p)) as H. change (bv_modulus 64) with two64 in H. exact H. Qed.

Lemma bsz_range (p : word * word) : 0 <= bsz p < two64.
Proof. unfold bsz. pose proof (bv_unsigned_in_range 64 (snd p)) as H. change (bv_modulus 64) with two64 in H. exact H. Qed.

Lemma u_Z_to_bv (z : Z) : 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with two64. exact H. Qed.

Lemma inl_nil (x : Z) : ~ inl [] x.
Proof. intros [p [[] _]]. Qed.

Lemma inl_cons (q : word * word) (l : list (word * word)) (x : Z) :
  inl (q :: l) x <-> (bas q <= x < bas q + bsz q) \/ inl l x.
Proof.
  split.
  - intros [p [[<-|Hin] Hp]]; [left; exact Hp | right; exists p; split; assumption].
  - intros [Hq|[p [Hin Hp]]]; [exists q; split; [left; reflexivity | exact Hq] | exists p; split; [right; exact Hin | exact Hp]].
Qed.

Lemma inl_app (l1 l2 : list (word * word)) (x : Z) : inl (l1 ++ l2) x <-> inl l1 x \/ inl l2 x.
Proof.
  split.
  - intros [p [Hin Hp]]. apply in_app_or in Hin as [H|H]; [left | right]; exists p; split; assumption.
  - intros [[p [Hin Hp]]|[p [Hin Hp]]]; exists p; (split; [apply in_or_app; auto | exact Hp]).
Qed.

Lemma iv_overlap_false (lo n a sz : word) :
  iv_overlap lo n a sz = false <-> iv_disj (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) (a, sz).
Proof.
  unfold iv_overlap, iv_disj, bas, bsz. cbn [fst snd]. rewrite andb_false_iff, !Z.ltb_ge. tauto.
Qed.

Lemma region_free_disj (l : list (word * word)) (lo n : word) :
  region_free l lo n = true <-> forall q, In q l -> iv_disj (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n) q.
Proof.
  split.
  - intros H [a sz] Hin. apply iv_overlap_false. exact (region_free_In l lo n a sz H Hin).
  - intros H. apply region_free_intro. intros a sz Hin. apply iv_overlap_false. exact (H (a, sz) Hin).
Qed.

Lemma region_free_app (l1 l2 : list (word * word)) (lo n : word) :
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[a sz] r IH]; [reflexivity|]. cbn [app region_free]. rewrite IH, andb_assoc. reflexivity.
Qed.

Lemma region_free_not_inl (l : list (word * word)) (lo n : word) (x : Z) :
  region_free l lo n = true -> bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n -> ~ inl l x.
Proof.
  intros H Hx [p [Hin Hp]]. pose proof (proj1 (region_free_disj l lo n) H p Hin) as D. unfold iv_disj in D. lia.
Qed.

Lemma live_bytes_app (l1 l2 : list (word * word)) : live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a sz] r IH]; [reflexivity|]. cbn [app live_bytes]. rewrite IH. lia. Qed.

Lemma live_bytes_nonneg (l : list (word * word)) : 0 <= live_bytes l.
Proof.
  induction l as [|[a sz] r IH]; [cbn; lia|]. cbn [live_bytes].
  pose proof (bsz_range (a, sz)) as H. unfold bsz in H. cbn [snd] in H. lia.
Qed.

Lemma live_bytes_cons (p : word * word) (l : list (word * word)) : live_bytes (p :: l) = bsz p + live_bytes l.
Proof. destruct p as [a sz]. reflexivity. Qed.

Lemma iv_subtract_pieces (a sz : word) (lo hi : Z) (p : word * word) :
  In p (iv_subtract a sz lo hi) -> bas (a, sz) + bsz (a, sz) <= two64 ->
  iv_sub p (a, sz) /\ (bas p + bsz p <= lo \/ hi <= bas p) /\ (0 < bsz (a, sz) -> 0 < bsz p).
Proof.
  unfold iv_subtract, iv_sub. intros Hin Hnw.
  pose proof (bas_range (a, sz)) as Ha. pose proof (bsz_range (a, sz)) as Hs.
  unfold bas, bsz in *. cbn [fst snd] in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u_Z_to_bv by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u_Z_to_bv by lia. lia.
Qed.

Lemma iv_subtract_live (a sz : word) (lo hi : Z) : lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros Hlh. unfold iv_subtract.
  pose proof (bas_range (a, sz)) as Ha. pose proof (bsz_range (a, sz)) as Hs. unfold bas, bsz in *. cbn [fst snd] in *.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes]; try apply Z.ltb_lt in E1; try apply Z.ltb_lt in E2; try apply Z.ltb_ge in E1; try apply Z.ltb_ge in E2;
    rewrite ?u_Z_to_bv by lia; lia.
Qed.

Lemma iv_subtract_inside (a sz : word) (lo hi : Z) :
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi -> iv_subtract a sz lo hi = [].
Proof.
  intros H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma iv_subtract_disj (a sz : word) (lo hi : Z) :
  0 < bv_unsigned sz -> lo <= hi -> iv_disj lo hi (a, sz) -> iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros Hp Hlh D. unfold iv_disj, bas, bsz in D. cbn [fst snd] in D. unfold iv_subtract.
  pose proof (bas_range (a, sz)) as Ha. unfold bas in Ha. cbn [fst] in Ha.
  destruct D as [D|D].
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_app (l1 l2 : list (word * word)) (lo hi : Z) :
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof. induction l1 as [|[a sz] r IH]; [reflexivity|]. cbn [app maps_subtract]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma maps_subtract_live (l : list (word * word)) (lo hi : Z) : lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  intros Hlh. induction l as [|[a sz] r IH]; [cbn; lia|]. cbn [maps_subtract live_bytes].
  rewrite live_bytes_app. pose proof (iv_subtract_live a sz lo hi Hlh). lia.
Qed.

Lemma maps_subtract_sub (l : list (word * word)) (lo hi : Z) (p : word * word) :
  (forall q, In q l -> bas q + bsz q <= two64) -> In p (maps_subtract l lo hi) ->
  exists q, In q l /\ iv_sub p q /\ (bas p + bsz p <= lo \/ hi <= bas p) /\ (0 < bsz q -> 0 < bsz p).
Proof.
  intros Hnw. induction l as [|[a sz] r IH]; [intros []|]. cbn [maps_subtract]. intros Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. exact (iv_subtract_pieces a sz lo hi p Hin (Hnw _ (or_introl eq_refl))).
  - destruct (IH (fun q Hq => Hnw q (or_intror Hq)) Hin) as [q [Hq X]]. exists q. split; [right; exact Hq | exact X].
Qed.

Lemma maps_subtract_inside (l : list (word * word)) (lo hi : Z) :
  (forall q, In q l -> lo <= bas q /\ bas q + bsz q <= hi) -> maps_subtract l lo hi = [].
Proof.
  induction l as [|[a sz] r IH]; [reflexivity|]. intros H. cbn [maps_subtract].
  destruct (H (a, sz) (or_introl eq_refl)) as [H1 H2]. unfold bas, bsz in H1, H2. cbn [fst snd] in H1, H2.
  rewrite (iv_subtract_inside a sz lo hi H1 H2). cbn [app]. apply IH. intros q Hq. apply H. right. exact Hq.
Qed.

Lemma subtract_disj_id (l : list (word * word)) (lo hi : Z) :
  lo <= hi -> (forall q, In q l -> 0 < bsz q /\ iv_disj lo hi q) -> maps_subtract l lo hi = l.
Proof.
  intros Hlh. induction l as [|[a sz] r IH]; [reflexivity|]. intros H. cbn [maps_subtract].
  destruct (H (a, sz) (or_introl eq_refl)) as [H1 H2]. unfold bsz in H1. cbn [snd] in H1.
  rewrite (iv_subtract_disj a sz lo hi H1 Hlh H2). cbn [app]. f_equal. apply IH. intros q Hq. apply H. right. exact Hq.
Qed.

Lemma inl_subtract1 (l : list (word * word)) (lo hi x : Z) :
  (forall q, In q l -> bas q + bsz q <= two64) ->
  (inl (maps_subtract l lo hi) x <-> inl l x /\ ~ (lo <= x < hi)).
Proof.
  intros Hnw. split.
  - intros [p [Hin Hp]]. destruct (maps_subtract_sub l lo hi p Hnw Hin) as [q [Hq [[S1 S2] [Ho _]]]].
    split; [exists q; split; [exact Hq | lia] | lia].
  - intros [[q [Hq Hx]] Hout]. induction l as [|[a sz] r IH]; [destruct Hq|]. cbn [maps_subtract]. apply inl_app.
    destruct Hq as [<-|Hq]; [left | right; exact (IH (fun q' H' => Hnw q' (or_intror H')) Hq)].
    pose proof (Hnw (a, sz) (or_introl eq_refl)) as Hw. pose proof (bas_range (a, sz)) as Ha. pose proof (bsz_range (a, sz)) as Hs.
    unfold bas, bsz in Hx, Hw, Ha, Hs. cbn [fst snd] in Hx, Hw, Ha, Hs. unfold iv_subtract.
    destruct (Z_lt_le_dec x lo) as [L|L].
    + rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia. apply inl_app. left. eexists. split; [left; reflexivity|].
      unfold bas, bsz. cbn [fst snd]. rewrite u_Z_to_bv by lia. lia.
    + assert (Hh : hi <= x) by lia. rewrite (proj2 (Z.ltb_lt hi (bv_unsigned a + bv_unsigned sz))) by lia.
      apply inl_app. right. eexists. split; [left; reflexivity|].
      unfold bas, bsz. cbn [fst snd]. rewrite !u_Z_to_bv by lia. lia.
Qed.

Lemma subtract_all_app (l1 l2 cuts : list (word * word)) :
  maps_subtract_all (l1 ++ l2) cuts = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts.
Proof.
  revert l1 l2. induction cuts as [|[a n] r IH]; intros l1 l2; [reflexivity|].
  cbn [maps_subtract_all]. rewrite maps_subtract_app. apply IH.
Qed.

Lemma subtract_all_live (l cuts : list (word * word)) : live_bytes (maps_subtract_all l cuts) <= live_bytes l.
Proof.
  revert l. induction cuts as [|[a n] r IH]; intros l; [cbn; lia|]. cbn [maps_subtract_all].
  pose proof (IH (maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n))) as H1.
  pose proof (bsz_range (a, n)) as Hn. unfold bsz in Hn. cbn [snd] in Hn.
  pose proof (maps_subtract_live l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ltac:(lia)). lia.
Qed.

Lemma subtract_all_sub (l cuts : list (word * word)) (p : word * word) :
  (forall q, In q l -> bas q + bsz q <= two64) -> In p (maps_subtract_all l cuts) ->
  exists q, In q l /\ iv_sub p q /\ (0 < bsz q -> 0 < bsz p).
Proof.
  revert l. induction cuts as [|[a n] r IH]; intros l Hnw Hin.
  - exists p. split; [exact Hin|]. unfold iv_sub. split; [lia | tauto].
  - cbn [maps_subtract_all] in Hin.
    assert (Hnw' : forall q, In q (maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) -> bas q + bsz q <= two64).
    { intros q Hq. destruct (maps_subtract_sub l _ _ q Hnw Hq) as [q0 [Hq0 [[S1 S2] _]]]. pose proof (Hnw q0 Hq0). lia. }
    destruct (IH _ Hnw' Hin) as [q [Hq [[S1 S2] Hpos]]].
    destruct (maps_subtract_sub l _ _ q Hnw Hq) as [q0 [Hq0 [[T1 T2] [_ Hpos0]]]].
    exists q0. split; [exact Hq0|]. split; [unfold iv_sub; lia | tauto].
Qed.

Section Grant.
Variable m : Model.
Variables a n : word.

Local Notation h := (m_vmmaps m).

Definition grant_maps (na' : list (word * word)) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) na' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Lemma used_with_vmmaps (H : VmMaps) :
  vm_backing_used (with_vmmaps H m) = live_bytes (maps_subtract_all (maps_subtract_all (vm_maps H) (vm_noaccess H)) (m_vm_lazy m))
                       + Z.of_nat (length (m_vm_materialized m)) * page_size.
Proof. reflexivity. Qed.

Lemma used_add_lazy (H : VmMaps) (a0 n0 : word) :
  vm_backing_used (vm_add_lazy a0 n0 (with_vmmaps H m)) =
  live_bytes (maps_subtract_all (maps_subtract_all (vm_maps H) (vm_noaccess H)) (lazy_interior a0 n0 ++ m_vm_lazy m))
  + Z.of_nat (length (m_vm_materialized m)) * page_size.
Proof. reflexivity. Qed.

Lemma used_self :
  vm_backing_used m = live_bytes (maps_subtract_all (maps_subtract_all (vm_maps h) (vm_noaccess h)) (m_vm_lazy m))
                       + Z.of_nat (length (m_vm_materialized m)) * page_size.
Proof. reflexivity. Qed.

Lemma used_grant_eager : vm_backing_used (with_vmmaps (grant_maps (vm_noaccess h)) m) <= vm_backing_used m + bv_unsigned n.
Proof.
  rewrite used_with_vmmaps, used_self. unfold grant_maps. cbn [vm_maps vm_noaccess].
  change ((a, n) :: vm_maps h) with ([(a, n)] ++ vm_maps h). rewrite !subtract_all_app, live_bytes_app.
  pose proof (subtract_all_live (maps_subtract_all [(a, n)] (vm_noaccess h)) (m_vm_lazy m)) as H1.
  pose proof (subtract_all_live [(a, n)] (vm_noaccess h)) as H2. cbn [live_bytes] in H2. lia.
Qed.

Lemma used_cons_eager (H : VmMaps) :
  vm_maps H = (a, n) :: vm_maps h -> vm_noaccess H = vm_noaccess h ->
  vm_backing_used (with_vmmaps H m) <= vm_backing_used m + bv_unsigned n.
Proof.
  intros E1 E2. rewrite used_with_vmmaps, used_self, E1, E2.
  change ((a, n) :: vm_maps h) with ([(a, n)] ++ vm_maps h). rewrite !subtract_all_app, live_bytes_app.
  pose proof (subtract_all_live (maps_subtract_all [(a, n)] (vm_noaccess h)) (m_vm_lazy m)) as H1.
  pose proof (subtract_all_live [(a, n)] (vm_noaccess h)) as H2. cbn [live_bytes] in H2. lia.
Qed.

Hypothesis Hnw : bv_unsigned a + bv_unsigned n <= two64.
Hypothesis Hpos : 0 < bv_unsigned n.
Hypothesis Hfree : region_free (vm_maps h) a n = true.
Hypothesis Hmaps_nw : forall q, In q (vm_maps h) -> bas q + bsz q <= two64.
Hypothesis Hmaps_pos : forall q, In q (vm_maps h) -> 0 < bsz q.

Lemma backed_disj : forall q, In q (maps_subtract_all (vm_maps h) (vm_noaccess h)) ->
  0 < bsz q /\ iv_disj (bv_unsigned a) (bv_unsigned a + bv_unsigned n) q.
Proof.
  intros q Hq. destruct (subtract_all_sub _ _ q Hmaps_nw Hq) as [q0 [Hq0 [[S1 S2] Hp]]].
  split; [exact (Hp (Hmaps_pos q0 Hq0))|].
  pose proof (proj1 (region_free_disj _ _ _) Hfree q0 Hq0) as D. pose proof (Hp (Hmaps_pos q0 Hq0)). unfold iv_disj in *. lia.
Qed.

Lemma maps_disj : forall q, In q (vm_maps h) -> 0 < bsz q /\ iv_disj (bv_unsigned a) (bv_unsigned a + bv_unsigned n) q.
Proof. intros q Hq. split; [exact (Hmaps_pos q Hq) | exact (proj1 (region_free_disj _ _ _) Hfree q Hq)]. Qed.

Lemma used_grant_noaccess : vm_backing_used (with_vmmaps (grant_maps ((a, n) :: vm_noaccess h)) m) = vm_backing_used m.
Proof.
  rewrite used_with_vmmaps, used_self. unfold grant_maps. cbn [vm_maps vm_noaccess maps_subtract_all maps_subtract].
  rewrite (iv_subtract_inside a n) by lia. cbn [app].
  rewrite (subtract_disj_id (vm_maps h)); [reflexivity | lia | exact maps_disj].
Qed.

Hypothesis Hal_a : bv_unsigned a mod page_size = 0.
Hypothesis Hal_n : bv_unsigned n mod page_size = 0.

Lemma lazy_interior_aligned : lazy_interior a n = [(a, n)].
Proof.
  unfold lazy_interior. cbv zeta. unfold page_size in *.
  assert (E1 : (bv_unsigned a + 4096 - 1) / 4096 * 4096 = bv_unsigned a).
  { pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)) as D. rewrite Hal_a in D.
    replace (bv_unsigned a + 4096 - 1) with (4095 + bv_unsigned a / 4096 * 4096) by lia.
    rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (E2 : (bv_unsigned a + bv_unsigned n) / 4096 * 4096 = bv_unsigned a + bv_unsigned n).
  { pose proof (Z.div_mod (bv_unsigned a + bv_unsigned n) 4096 ltac:(lia)) as D.
    rewrite Z.add_mod, Hal_a, Hal_n in D by lia. change ((0 + 0) mod 4096) with 0 in D. lia. }
  rewrite E1, E2. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  replace (bv_unsigned a + bv_unsigned n - bv_unsigned a) with (bv_unsigned n) by lia.
  rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma used_grant_lazy : vm_backing_used (vm_add_lazy a n (with_vmmaps (grant_maps (vm_noaccess h)) m)) = vm_backing_used m.
Proof.
  rewrite used_add_lazy, used_self, lazy_interior_aligned. unfold grant_maps. cbn [vm_maps vm_noaccess app maps_subtract_all].
  change ((a, n) :: vm_maps h) with ([(a, n)] ++ vm_maps h). rewrite subtract_all_app, maps_subtract_app.
  rewrite (maps_subtract_inside (maps_subtract_all [(a, n)] (vm_noaccess h))).
  - cbn [app]. rewrite (subtract_disj_id (maps_subtract_all (vm_maps h) (vm_noaccess h))); [reflexivity | lia | exact backed_disj].
  - intros q Hq. destruct (subtract_all_sub [(a, n)] (vm_noaccess h) q) as [q0 [Hq0 [[S1 S2] _]]]; [|exact Hq|].
    + intros q0 [<-|[]]. unfold bas, bsz. cbn [fst snd]. exact Hnw.
    + destruct Hq0 as [<-|[]]. unfold bas, bsz in *. cbn [fst snd] in *. lia.
Qed.

Lemma used_grant_noaccess_lazy :
  vm_backing_used (vm_add_lazy a n (with_vmmaps (grant_maps ((a, n) :: vm_noaccess h)) m)) = vm_backing_used m.
Proof.
  rewrite used_add_lazy, used_self, lazy_interior_aligned. unfold grant_maps. cbn [vm_maps vm_noaccess app maps_subtract_all maps_subtract].
  rewrite (iv_subtract_inside a n) by lia. cbn [app].
  rewrite (subtract_disj_id (vm_maps h)); [| lia | exact maps_disj].
  rewrite (subtract_disj_id (maps_subtract_all (vm_maps h) (vm_noaccess h))); [reflexivity | lia | exact backed_disj].
Qed.

End Grant.
