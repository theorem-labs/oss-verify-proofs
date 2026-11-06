(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mremap.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimInv.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma Z_to_bv_id : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros w. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma msa_cuts_app : forall P Q X, maps_subtract_all X (P ++ Q) = maps_subtract_all (maps_subtract_all X P) Q.
Proof. intros P. induction P as [| [a n] P IH]; intros Q X; [reflexivity |]. cbn [app maps_subtract_all]. apply IH. Qed.
Lemma msa_cons : forall e X P, maps_subtract_all (e :: X) P = maps_subtract_all [e] P ++ maps_subtract_all X P.
Proof. intros e X P. change (e :: X) with ([e] ++ X). apply maps_subtract_all_app. Qed.
Lemma ms_single : forall (a sz : word) lo hi, maps_subtract [(a, sz)] lo hi = iv_subtract a sz lo hi.
Proof. intros. cbn [maps_subtract]. apply app_nil_r. Qed.

Section Cut.
Variables lo hi : Z.
Hypothesis Hlo : (0 <= lo)%Z.
Hypothesis Hle : (lo <= hi)%Z.
Hypothesis Hhi : (hi < two_pow_64)%Z.

(* [comment removed for export] *)
Definition good (e : word * word) : Prop :=
  in_space e /\ (bv_unsigned (fst e) + bv_unsigned (snd e) <= lo \/ hi <= bv_unsigned (fst e))%Z.

Lemma good_iv_subtract : forall (a sz : word) l h, good (a, sz) -> Forall good (iv_subtract a sz l h).
Proof.
  intros a sz l h [Hs Hm]. pose proof (mis_iv_subtract a sz l h Hs) as HF.
  apply Forall_forall. intros [b s] Hin. split; [exact (proj1 (Forall_forall _ _) HF _ Hin) |].
  destruct Hs as [_ Hs]. cbn [fst snd] in *.
  destruct (iv_subtract_within a sz l h b s Hs Hin) as [H1 H2]. lia.
Qed.
Lemma good_maps_subtract : forall X l h, Forall good X -> Forall good (maps_subtract X l h).
Proof.
  intros X l h H. induction H as [| [a sz] X He HX IH]; cbn [maps_subtract]; [constructor |].
  apply Forall_app. split; [apply good_iv_subtract; exact He | exact IH].
Qed.

(* [comment removed for export] *)
Lemma ms_disjoint : forall X l h, (l <= h)%Z ->
  (forall (p q : word), In (p, q) X -> (0 < bv_unsigned q /\ (bv_unsigned p + bv_unsigned q <= l \/ h <= bv_unsigned p))%Z) ->
  maps_subtract X l h = X.
Proof.
  intros X l h Hlh. induction X as [| [p q] X IH]; intros H; [reflexivity |].
  cbn [maps_subtract]. destruct (H p q (or_introl eq_refl)) as [Hq Hm].
  rewrite (iv_subtract_disjoint p q l h Hq Hlh Hm). cbn [app]. f_equal. apply IH. intros p' q' Hin. apply H. right. exact Hin.
Qed.
(* [comment removed for export] *)
Lemma iv_subtract_hi_irrel : forall (b s : word) l h1 h2,
  (bv_unsigned b + bv_unsigned s <= h1)%Z -> (bv_unsigned b + bv_unsigned s <= h2)%Z -> iv_subtract b s l h1 = iv_subtract b s l h2.
Proof.
  intros b s l h1 h2 H1 H2. unfold iv_subtract. cbv zeta.
  destruct (h1 <? bv_unsigned b + bv_unsigned s)%Z eqn:E1; [apply Z.ltb_lt in E1; lia |].
  destruct (h2 <? bv_unsigned b + bv_unsigned s)%Z eqn:E2; [apply Z.ltb_lt in E2; lia |]. reflexivity.
Qed.
Lemma iv_subtract_lo_max : forall (b s : word) c k h, (k <= bv_unsigned b)%Z -> iv_subtract b s (Z.max c k) h = iv_subtract b s c h.
Proof.
  intros b s c k h Hk. unfold iv_subtract. cbv zeta.
  destruct (bv_unsigned b <? Z.max c k)%Z eqn:E1; destruct (bv_unsigned b <? c)%Z eqn:E2;
    try apply Z.ltb_lt in E1; try apply Z.ltb_ge in E1; try apply Z.ltb_lt in E2; try apply Z.ltb_ge in E2; try lia; [| reflexivity].
  replace (Z.max c k) with c by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cut_piece : forall (b s c n : word), good (b, s) ->
  maps_subtract_all [(b, s)] (iv_subtract c n lo hi) = iv_subtract b s (bv_unsigned c) (bv_unsigned c + bv_unsigned n).
Proof.
  intros b s c n HG. pose proof HG as [[Hp Hs] Hm]. cbn [fst snd] in *.
  pose proof (mremap_word_range b) as Hb. pose proof (mremap_word_range s) as Hsr.
  pose proof (mremap_word_range c) as Hc. pose proof (mremap_word_range n) as Hn. unfold two_pow_64 in *.
  set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *. set (C := bv_unsigned c) in *. set (N := bv_unsigned n) in *.
  (* [comment removed for export] *)
  assert (HLcut : forall X, (C < lo)%Z ->
            maps_subtract_all X [(c, Z_to_bv 64 (Z.min N (lo - C)))] = maps_subtract X C (C + Z.min N (lo - C))).
  { intros X Hc1. cbn [maps_subtract_all]. fold C. rewrite mremap_u64 by (unfold two_pow_64; lia). reflexivity. }
  assert (HRcut : forall X, (hi < C + N)%Z ->
            maps_subtract_all X [(Z_to_bv 64 (Z.max C hi), Z_to_bv 64 (C + N - Z.max C hi))] = maps_subtract X (Z.max C hi) (C + N)).
  { intros X Hc2. cbn [maps_subtract_all]. rewrite !mremap_u64 by (unfold two_pow_64; lia). f_equal. lia. }
  unfold iv_subtract at 1. cbv zeta. fold C N.
  destruct (C <? lo)%Z eqn:E1; destruct (hi <? C + N)%Z eqn:E2;
    try apply Z.ltb_lt in E1; try apply Z.ltb_ge in E1; try apply Z.ltb_lt in E2; try apply Z.ltb_ge in E2.
  - (* [comment removed for export] *)
    rewrite msa_cuts_app, (HLcut _ E1), (HRcut _ E2), ms_single.
    destruct Hm as [Hm | Hm].
    + (* [comment removed for export] *)
      assert (HE : iv_subtract b s C (C + Z.min N (lo - C)) = iv_subtract b s C (C + N)).
      { destruct (Z.le_gt_cases N (lo - C)) as [Hn1 | Hn1]; [replace (Z.min N (lo - C)) with N by lia; reflexivity |].
        apply iv_subtract_hi_irrel; fold B S; lia. }
      rewrite HE. apply ms_disjoint; [lia |]. intros p q Hin.
      pose proof (good_iv_subtract b s C (C + N) HG) as HF. destruct (proj1 (Forall_forall _ _) HF _ Hin) as [[Hq _] _]. cbn [fst snd] in Hq.
      destruct (iv_subtract_within b s C (C + N) p q ltac:(unfold two_pow_64; fold B S; lia) Hin) as [_ Hw]. fold B S in Hw. split; [exact Hq | left; lia].
    + (* [comment removed for export] *)
      rewrite (iv_subtract_disjoint b s C (C + Z.min N (lo - C))) by (fold B S; lia). rewrite ms_single.
      apply iv_subtract_lo_max. fold B. exact Hm.
  - (* [comment removed for export] *)
    rewrite (HLcut _ E1), ms_single.
    destruct Hm as [Hm | Hm].
    + destruct (Z.le_gt_cases N (lo - C)) as [Hn1 | Hn1]; [replace (Z.min N (lo - C)) with N by lia; reflexivity |].
      apply iv_subtract_hi_irrel; fold B S; lia.
    + rewrite (iv_subtract_disjoint b s C (C + Z.min N (lo - C))) by (fold B S; lia).
      rewrite (iv_subtract_disjoint b s C (C + N)) by (fold B S; lia). reflexivity.
  - (* [comment removed for export] *)
    rewrite (HRcut _ E2), ms_single.
    destruct Hm as [Hm | Hm].
    + rewrite (iv_subtract_disjoint b s (Z.max C hi) (C + N)) by (fold B S; lia).
      rewrite (iv_subtract_disjoint b s C (C + N)) by (fold B S; lia). reflexivity.
    + apply iv_subtract_lo_max. fold B. exact Hm.
  - (* [comment removed for export] *)
    cbn [app maps_subtract_all]. rewrite (iv_subtract_disjoint b s C (C + N)) by (fold B S; lia). reflexivity.
Qed.

Lemma cut_list : forall X (c n : word), Forall good X ->
  maps_subtract_all X (iv_subtract c n lo hi) = maps_subtract X (bv_unsigned c) (bv_unsigned c + bv_unsigned n).
Proof.
  intros X c n H. induction H as [| [b s] X He HX IH]; [apply maps_subtract_all_nil |].
  rewrite msa_cons, IH, (cut_piece b s c n He). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cut_free : forall KL X, Forall good X ->
  maps_subtract_all X (maps_subtract KL lo hi) = maps_subtract_all X KL.
Proof.
  intros KL. induction KL as [| [c n] KL IH]; intros X HX; [reflexivity |].
  cbn [maps_subtract]. rewrite msa_cuts_app, (cut_list X c n HX). cbn [maps_subtract_all].
  apply IH. apply good_maps_subtract. exact HX.
Qed.

(* [comment removed for export] *)
Lemma ms_inside : forall D, (forall (b s : word), In (b, s) D -> (lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi)%Z) ->
  maps_subtract D lo hi = [].
Proof.
  intros D. induction D as [| [b s] D IH]; intros H; [reflexivity |].
  cbn [maps_subtract]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin). rewrite app_nil_r.
  destruct (H b s (or_introl eq_refl)) as [H1 H2]. unfold iv_subtract. cbv zeta.
  destruct (bv_unsigned b <? lo)%Z eqn:E1; [apply Z.ltb_lt in E1; lia |].
  destruct (hi <? bv_unsigned b + bv_unsigned s)%Z eqn:E2; [apply Z.ltb_lt in E2; lia |]. reflexivity.
Qed.
End Cut.

Lemma good_msa : forall lo hi cuts X, Forall (good lo hi) X -> Forall (good lo hi) (maps_subtract_all X cuts).
Proof.
  intros lo hi cuts. induction cuts as [| [a n] cuts IH]; intros X H; [exact H |].
  cbn [maps_subtract_all]. apply IH. apply good_maps_subtract. exact H.
Qed.
Lemma filter_length_le' : forall {A} (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros A f l. induction l as [| x l IH]; cbn [List.filter length]; [lia |]. destruct (f x); cbn [length]; lia. Qed.

(* [comment removed for export] *)
Theorem mremap_star : forall m old old_n dst new_n,
  Inv m ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n < two_pow_64)%Z ->
  region_free (vm_maps (m_vmmaps m)) dst new_n = true ->
  (vm_backing_used (mremap_model_next m old old_n dst new_n) <= mremap_move_charge m old old_n new_n)%Z.
Proof.
  intros m old old_n dst new_n HI Halign Hnalign Hpos Hend Hmaps.
  assert (P1 : forall L P m', m_vmmaps (with_vm_backing L P m') = m_vmmaps m') by reflexivity.
  assert (P2 : forall L P m', m_vm_lazy (with_vm_backing L P m') = L) by reflexivity.
  assert (P3 : forall L P m', m_vm_materialized (with_vm_backing L P m') = P) by reflexivity.
  assert (P4 : forall h m', m_vmmaps (with_vmmaps h m') = h) by reflexivity.
  assert (P5 : forall h m', m_vm_lazy (with_vmmaps h m') = m_vm_lazy m') by reflexivity.
  assert (P6 : forall h m', m_vm_materialized (with_vmmaps h m') = m_vm_materialized m') by reflexivity.
  unfold vm_backing_used, mremap_move_charge, mremap_model_next, vm_resize_backing, mremap_maps_next.
  cbv zeta.
  rewrite !P1, !P2, !P3, !P4, !P5, !P6.
  unfold vm_backed_maps. cbn [vm_maps vm_noaccess vm_limit].
  set (KL := maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) in *.
  set (KP := List.filter (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) (m_vm_materialized m)) in *.
  set (R0 := map_remove (vm_maps (m_vmmaps m)) old) in *.
  set (NA := vm_noaccess (m_vmmaps m)) in *.
  set (lo := bv_unsigned dst) in *. set (hi := (lo + bv_unsigned new_n)%Z) in *.
  pose proof (mremap_word_range dst) as Hd. fold lo in Hd.
  assert (Hlo : (0 <= lo)%Z) by lia. assert (Hle : (lo <= hi)%Z) by (unfold hi; lia).
  (* [comment removed for export] *)
  assert (HX : Forall (good lo hi) (maps_subtract_all R0 NA)).
  { apply good_msa. apply Forall_forall. intros [a sz] Hin. unfold R0, map_remove in Hin. apply List.filter_In in Hin. destruct Hin as [Hin _].
    split; [exact (proj1 (Forall_forall _ _) HI _ Hin) |]. cbn [fst snd].
    pose proof (region_free_In _ _ _ a sz Hmaps Hin) as Hov. unfold iv_overlap in Hov. apply andb_false_iff in Hov.
    fold lo in Hov. destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; unfold hi; lia. }
  (* [comment removed for export] *)
  assert (HD : forall (b s : word), In (b, s) (maps_subtract_all [(dst, new_n)] NA) -> (lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi)%Z).
  { intros b s Hin.
    destruct (maps_subtract_all_within NA [(dst, new_n)] b s) as [a [sz [Hin0 Hw]]]; [| exact Hin |].
    - intros a sz [E | []]. injection E as <- <-. fold lo. lia.
    - destruct Hin0 as [E | []]. injection E as <- <-. fold lo in Hw. unfold hi. lia. }
  change ((dst, new_n) :: R0) with ([(dst, new_n)] ++ R0).
  rewrite maps_subtract_all_app.
  rewrite length_app.
  pose proof (filter_length_le' (page_outside_range lo hi) KP) as HKP.
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  destruct (mremap_source_lazy_b m old old_n) eqn:Hsrc.
  - (* [comment removed for export] *)
    rewrite (lazy_interior_aligned dst new_n Halign Hnalign Hpos).
    rewrite length_map.
    rewrite maps_subtract_all_app, live_bytes_app.
    rewrite !(msa_cuts_app [(dst, new_n)]).
    cbn [maps_subtract_all]. fold lo hi.
    rewrite (ms_inside lo hi _ HD), maps_subtract_all_nil. cbn [live_bytes].
    rewrite (ms_disjoint (maps_subtract_all R0 NA) lo hi Hle).
    2:{ intros p q Hin. destruct (proj1 (Forall_forall _ _) HX _ Hin) as [[Hq _] Hm]. cbn [fst snd] in *. split; [exact Hq | exact Hm]. }
    rewrite (cut_free lo hi Hlo Hle Hend KL _ HX).
    nia.
  - (* [comment removed for export] *)
    rewrite maps_subtract_all_app, live_bytes_app.
    rewrite (cut_free lo hi Hlo Hle Hend KL _ HX).
    pose proof (live_bytes_maps_subtract_all_le (maps_subtract KL lo hi) (maps_subtract_all [(dst, new_n)] NA)) as H1.
    pose proof (live_bytes_maps_subtract_all_le NA [(dst, new_n)]) as H2. cbn [live_bytes] in H2.
    cbn [length] in *. nia.
Qed.
