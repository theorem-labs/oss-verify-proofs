(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl.
From Stdlib Require Wf_nat.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MI_Fuel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Section WithCeil.
Context {CE : CEIL}.
Inductive tle {R : Type} : M R -> M R -> Prop :=
| tle_ret : forall r, tle (SRet r) (SRet r)
| tle_fuel : forall k t, tle (SVis (EUndef UFuel) k) t
| tle_vis : forall e k1 k2, (forall a, tle (k1 a) (k2 a)) -> tle (SVis e k1) (SVis e k2).

#[using="Type"] Lemma tle_refl {R} (t : M R) : tle t t.
Proof. induction t; constructor; auto. Qed.

#[using="Type"] Lemma tle_trans {R} (t1 t2 t3 : M R) : tle t1 t2 -> tle t2 t3 -> tle t1 t3.
Proof.
  intros H1. revert t3. induction H1 as [r|k t|e k1 k2 Hk IH]; intros t3 H2.
  - exact H2.
  - constructor.
  - inversion H2; subst.
    + constructor.
    + constructor. intros a. apply IH. auto.
Qed.

#[using="Type"] Lemma follow_tle {R} (t1 t2 : M R) : tle t1 t2 -> forall ans r, follow t1 ans = Some r -> follow t2 ans = Some r.
Proof.
  induction 1 as [r0|k t|e k1 k2 Hk IH]; intros ans r H.
  - exact H.
  - cbn [follow] in H. destruct ans; discriminate H.
  - cbn [follow] in H |- *. destruct e; try exact H; destruct ans as [|a ans']; try discriminate H; apply IH; exact H.
Qed.

(* [comment removed for export] *)
Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).

#[using="Type"] Lemma prun_tle {R} (t1 t2 : M R) : tle t1 t2 -> forall o, tle (prun pans pupd o t1) (prun pans pupd o t2).
Proof.
  unfold prun. induction 1 as [r0|k t|e k1 k2 Hk IH]; intros o; cbn [eruns psel].
  - constructor.
  - constructor.
  - destruct e; cbn [psel]; try (constructor; intros a; apply IH). apply IH.
Qed.
End PRUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kle {X Y R} (k k' : X -> Y -> M R) : Prop := forall x y, tle (k x y) (k' x y).
Definition kle1 {X R} (k k' : X -> M R) : Prop := forall x, tle (k x) (k' x).
End WithCeil.


Ltac mono_case :=
  lazymatch goal with
  | |- tle (match ?c with _ => _ end) _ => destruct c
  end.

Ltac mono_auto cal :=
  first [ apply tle_refl
        | cal
        | (apply tle_vis; intros ?); mono_auto cal
        | mono_case; mono_auto cal
        | progress (cbv zeta); mono_auto cal ].

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma guard_mono {R} tag c (k k' bail bail' : M R) :
  tle k k' -> tle bail bail' -> tle (guard tag c k bail) (guard tag c k' bail').
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. constructor. intros _. exact HB. Qed.

#[using="Type"] Lemma bad_answer_mono {R} (b b' : M R) : tle b b' -> tle (bad_answer b) (bad_answer b').
Proof. intros HB. unfold bad_answer. constructor. intros _. exact HB. Qed.

#[using="Type"] Lemma queue_mono {R} h m st (k k' : mstate -> M R) bail bail' :
  kle1 k k' -> tle bail bail' -> tle (queue h m st k bail) (queue h m st k' bail').
Proof.
  intros HK HB. unfold queue. apply guard_mono; [| exact HB]. apply guard_mono; [| exact HB].
  mono_auto ltac:(first [apply HK | exact HB]).
Qed.

#[using="Type"] Lemma free_meta_mono {R} m st (k k' : mstate -> M R) bail bail' :
  kle1 k k' -> tle bail bail' -> tle (free_meta m st k bail) (free_meta m st k' bail').
Proof. intros HK HB. unfold free_meta. apply queue_mono; assumption. Qed.

#[using="Type"] Lemma activate_group_mono {R} m st (k k' : mstate -> Z -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (activate_group m st k bail) (activate_group m st k' bail').
Proof. intros HK HB. unfold activate_group. apply guard_mono; [| exact HB]. cbv zeta. apply HK. Qed.

#[using="Type"] Lemma am_take_mono {R} st (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_take st k bail) (am_take st k' bail').
Proof. intros HK HB. unfold am_take. mono_auto ltac:(first [apply HK | exact HB]). Qed.

#[using="Type"] Lemma am_carve_mono {R} st p (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_carve st p k bail) (am_carve st p k' bail').
Proof. intros HK HB. unfold am_carve. cbv zeta. apply am_take_mono; assumption. Qed.

#[using="Type"] Lemma am_finish_mono {R} st nu (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_finish st nu k bail) (am_finish st nu k' bail').
Proof.
  intros HK HB. unfold am_finish.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_carve_mono; assumption]).
Qed.

#[using="Type"] Lemma am_after_brk_mono {R} st nu (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_after_brk st nu k bail) (am_after_brk st nu k' bail').
Proof.
  intros HK HB. unfold am_after_brk.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_finish_mono; assumption]).
Qed.

#[using="Type"] Lemma alloc_meta_mono {R} st (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (alloc_meta st k bail) (alloc_meta st k' bail').
Proof.
  intros HK HB. unfold alloc_meta.
  (* [comment removed for export] *)
  cbv zeta. match goal with |- context [c_free_meta_head (ctx ?s)] => generalize s as st0; intros st0 end.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_take_mono; assumption | apply am_after_brk_mono; assumption]).
Qed.

#[using="Type"] Lemma ta_fin_mono {R} st m mask (k k' : mstate -> Z -> M R) :
  kle k k' -> tle (ta_fin st m mask k) (ta_fin st m mask k').
Proof. intros HK. unfold ta_fin. cbv zeta. apply HK. Qed.

#[using="Type"] Lemma try_avail_mono {R} sc st (k k' : mstate -> Z -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (try_avail sc st k bail) (try_avail sc st k' bail').
Proof.
  intros HK HB. unfold try_avail.
  destruct (active st sc) as [m|]; [| apply HK]. cbv zeta.
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply ta_fin_mono; exact HK|].
  mono_case.
  - destruct p as [st1 m1]. mono_case. destruct p as [st2 m2]. mono_case.
    apply activate_group_mono; [| exact HB]. intros st4 mask. apply guard_mono; [| exact HB]. apply ta_fin_mono. exact HK.
  - mono_case; [apply HK|]. constructor. intros _. exact HB.
Qed.

#[using="Type"] Lemma ag_tail_mono {R} lay st sc m p cnt ai (k k' : mstate -> optr -> M R) :
  kle k k' -> tle (ag_tail lay st sc m p cnt ai k) (ag_tail lay st sc m p cnt ai k').
Proof. intros HK. unfold ag_tail. cbv zeta. apply HK. Qed.

Section AG.
Variable R : Type.
Variable lay : layout_hook.
Variables rec rec' : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Hypothesis rec_mono : forall st sc req (k k' : mstate -> Z -> M R) bail bail',
  kle k k' -> tle bail bail' -> tle (rec st sc req k bail) (rec' st sc req k' bail').

#[using="rec_mono"] Lemma alloc_group_mono st sc req (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' ->
  tle (alloc_group R lay rec st sc req k bail) (alloc_group R lay rec' st sc req k' bail').
Proof.
  intros HK HB. unfold alloc_group. cbv zeta. apply alloc_meta_mono; [| exact HB].
  intros st' mo. destruct mo as [m|]; [| apply HK].
  mono_case.
  - (* [comment removed for export] *)
    match goal with |- tle (let '(_, _) := ?p in _) _ => destruct p as [cnt' needed] end.
    constructor. intros r. mono_case; [apply bad_answer_mono; exact HB|].
    mono_case; [apply free_meta_mono; [intros ?; apply HK| exact HB]|].
    mono_case. cbv zeta. apply ag_tail_mono. exact HK.
  - (* [comment removed for export] *)
    apply rec_mono; [| exact HB]. intros st1 idx.
    mono_case; [apply free_meta_mono; [intros ?; apply HK| exact HB]|].
    mono_case; [| constructor; intros _; exact HB]. cbv zeta. apply ag_tail_mono. exact HK.
Qed.
End AG.

#[using="Type"] Lemma alloc_slot_mono lay f : forall R st sc req (k k' : mstate -> Z -> M R) bail bail',
  kle k k' -> tle bail bail' ->
  tle (alloc_slot lay f st sc req k bail) (alloc_slot lay (S f) st sc req k' bail').
Proof.
  induction f as [|f IH]; intros R st sc req k k' bail bail' HK HB.
  - cbn [alloc_slot]. apply tle_fuel.
  - change (alloc_slot lay (S (S f)) st sc req k' bail') with
      (try_avail sc st (fun st1 first =>
         if negb (first =? 0) then k' st1 (ctz32 first)
         else alloc_group R lay (alloc_slot lay (S f)) st1 sc req (fun st2 go =>
                match go with
                | None => k' st2 (-1)
                | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                            queue (LActive sc) g st3 (fun st4 => k' st4 0) bail'
                end) bail') bail').
    change (alloc_slot lay (S f) st sc req k bail) with
      (try_avail sc st (fun st1 first =>
         if negb (first =? 0) then k st1 (ctz32 first)
         else alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
                match go with
                | None => k st2 (-1)
                | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                            queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                end) bail) bail).
    apply try_avail_mono; [| exact HB]. intros st1 first.
    destruct (negb (first =? 0)); [apply HK|].
    apply (alloc_group_mono lay (alloc_slot lay f) (alloc_slot lay (S f))); [intros; apply IH; assumption| | exact HB].
    intros st2 go. destruct go as [g|]; [| apply HK]. cbv zeta. apply queue_mono; [intros ?; apply HK| exact HB].
Qed.

#[using="Type"] Lemma alloc_slot_mono_le lay f f' : (f <= f')%nat -> forall R st sc req (k : mstate -> Z -> M R) bail,
  tle (alloc_slot lay f st sc req k bail) (alloc_slot lay f' st sc req k bail).
Proof.
  induction 1 as [|f' H IH]; intros R st sc req k bail.
  - apply tle_refl.
  - eapply tle_trans; [apply IH|]. apply alloc_slot_mono; [intros ? ?; apply tle_refl| apply tle_refl].
Qed.

(* [comment removed for export] *)
Section LEAF.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
#[using="Type"] Lemma alloc_slot_follow_mono lay f f' R st sc req (k : mstate -> Z -> M R) bail o ans r :
  (f <= f')%nat ->
  follow (prun pans pupd o (alloc_slot lay f st sc req k bail)) ans = Some r ->
  follow (prun pans pupd o (alloc_slot lay f' st sc req k bail)) ans = Some r.
Proof. intros Hf H. eapply follow_tle; [apply prun_tle; apply alloc_slot_mono_le; exact Hf| exact H]. Qed.
End LEAF.

End WithCeil.
End MI_Fuel.

(* [comment removed for export] *)
Module MI_Kit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma aptr_eqb_refl (a : aptr) : aptr_eqb a a = true.
Proof. unfold aptr_eqb. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma aptr_eqb_eq (a b : aptr) : aptr_eqb a b = true <-> a = b.
Proof.
  unfold aptr_eqb. destruct a as [r o], b as [r' o']; cbn. rewrite Bool.andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

#[using="Type"] Lemma aptr_eqb_spec (a b : aptr) : reflect (a = b) (aptr_eqb a b).
Proof.
  destruct (aptr_eqb a b) eqn:E; constructor.
  - apply aptr_eqb_eq. exact E.
  - intros ->. rewrite aptr_eqb_refl in E. discriminate.
Qed.

#[using="Type"] Lemma aptr_eqb_neq (a b : aptr) : a <> b -> aptr_eqb a b = false.
Proof. intros H. destruct (aptr_eqb_spec a b); [contradiction| reflexivity]. Qed.

#[using="Type"] Lemma optr_eqb_spec (a b : optr) : reflect (a = b) (optr_eqb a b).
Proof.
  destruct a as [a|], b as [b|]; cbn; try (constructor; congruence).
  destruct (aptr_eqb_spec a b); constructor; congruence.
Qed.

#[using="Type"] Lemma optr_eqb_refl (a : optr) : optr_eqb a a = true.
Proof. destruct (optr_eqb_spec a a); [reflexivity| contradiction]. Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac case_ptr x y := destruct (aptr_eqb_spec x y) as [?EQp|?NEp]; [first [subst x | subst y | idtac]|].

#[export] Instance aptr_eq_dec : EqDecision aptr := _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma get_meta_rec_put st m r x :
  get_meta_rec (put_meta m r st) x = if aptr_eqb x m then r else get_meta_rec st x.
Proof.
  unfold get_meta_rec, put_meta; cbn. destruct (aptr_eqb_spec x m) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma get_meta_rec_upd st m f x :
  get_meta_rec (upd_meta m f st) x = if aptr_eqb x m then f (get_meta_rec st m) else get_meta_rec st x.
Proof. unfold upd_meta. apply get_meta_rec_put. Qed.

#[using="Type"] Lemma get_meta_rec_put_same st m r : get_meta_rec (put_meta m r st) m = r.
Proof. rewrite get_meta_rec_put, aptr_eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_put_other st m r x : x <> m -> get_meta_rec (put_meta m r st) x = get_meta_rec st x.
Proof. intros H. rewrite get_meta_rec_put, aptr_eqb_neq by exact H. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_upd_same st m f : get_meta_rec (upd_meta m f st) m = f (get_meta_rec st m).
Proof. rewrite get_meta_rec_upd, aptr_eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_upd_other st m f x : x <> m -> get_meta_rec (upd_meta m f st) x = get_meta_rec st x.
Proof. intros H. rewrite get_meta_rec_upd, aptr_eqb_neq by exact H. reflexivity. Qed.

#[using="Type"] Lemma s_metas_put_meta m r st : s_metas (put_meta m r st) = <[m := r]> (s_metas st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_upd_meta m f st : s_metas (upd_meta m f st) = <[m := f (get_meta_rec st m)]> (s_metas st).
Proof. reflexivity. Qed.

#[using="Type"] Lemma lookup_metas_put st m r x :
  s_metas (put_meta m r st) !! x = if aptr_eqb x m then Some r else s_metas st !! x.
Proof.
  cbn. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma lookup_metas_upd st m f x :
  s_metas (upd_meta m f st) !! x = if aptr_eqb x m then Some (f (get_meta_rec st m)) else s_metas st !! x.
Proof. unfold upd_meta. apply lookup_metas_put. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma get_meta_rec_ext st st' x : s_metas st' = s_metas st -> get_meta_rec st' x = get_meta_rec st x.
Proof. intros H. unfold get_meta_rec. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac msimp := cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
                   m_set_prev m_set_next m_set_mem m_set_avail m_set_freed m_set_last_idx m_set_freeable m_set_sizeclass m_set_maplen
                   meta0] in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma s_ctx_upd_ctx f st : s_ctx (upd_ctx f st) = f (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_upd_ctx f st : s_regions (upd_ctx f st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_upd_ctx f st : s_shadow (upd_ctx f st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_upd_ctx f st : s_next_rid (upd_ctx f st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_upd_ctx f st : s_metas (upd_ctx f st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_upd_ctx f st : s_areas (upd_ctx f st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_upd_ctx f st : s_groups (upd_ctx f st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_upd_ctx f st : s_slots (upd_ctx f st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_upd_ctx f st : s_tick (upd_ctx f st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_upd_ctx f st : s_secret (upd_ctx f st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_upd_ctx f st : s_reserved (upd_ctx f st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_regions v st : s_ctx (set_regions v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_regions v st : s_regions (set_regions v st) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_regions v st : s_shadow (set_regions v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_regions v st : s_next_rid (set_regions v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_regions v st : s_metas (set_regions v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_regions v st : s_areas (set_regions v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_regions v st : s_groups (set_regions v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_regions v st : s_slots (set_regions v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_regions v st : s_tick (set_regions v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_regions v st : s_secret (set_regions v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_regions v st : s_reserved (set_regions v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_shadow v st : s_ctx (set_shadow v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_shadow v st : s_regions (set_shadow v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_shadow v st : s_shadow (set_shadow v st) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_shadow v st : s_next_rid (set_shadow v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_shadow v st : s_metas (set_shadow v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_shadow v st : s_areas (set_shadow v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_shadow v st : s_groups (set_shadow v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_shadow v st : s_slots (set_shadow v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_shadow v st : s_tick (set_shadow v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_shadow v st : s_secret (set_shadow v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_shadow v st : s_reserved (set_shadow v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_next_rid v st : s_ctx (set_next_rid v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_next_rid v st : s_regions (set_next_rid v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_next_rid v st : s_shadow (set_next_rid v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_next_rid v st : s_next_rid (set_next_rid v st) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_next_rid v st : s_metas (set_next_rid v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_next_rid v st : s_areas (set_next_rid v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_next_rid v st : s_groups (set_next_rid v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_next_rid v st : s_slots (set_next_rid v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_next_rid v st : s_tick (set_next_rid v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_next_rid v st : s_secret (set_next_rid v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_next_rid v st : s_reserved (set_next_rid v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_metas v st : s_ctx (set_metas v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_metas v st : s_regions (set_metas v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_metas v st : s_shadow (set_metas v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_metas v st : s_next_rid (set_metas v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_metas v st : s_metas (set_metas v st) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_metas v st : s_areas (set_metas v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_metas v st : s_groups (set_metas v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_metas v st : s_slots (set_metas v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_metas v st : s_tick (set_metas v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_metas v st : s_secret (set_metas v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_metas v st : s_reserved (set_metas v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_areas v st : s_ctx (set_areas v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_areas v st : s_regions (set_areas v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_areas v st : s_shadow (set_areas v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_areas v st : s_next_rid (set_areas v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_areas v st : s_metas (set_areas v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_areas v st : s_areas (set_areas v st) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_areas v st : s_groups (set_areas v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_areas v st : s_slots (set_areas v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_areas v st : s_tick (set_areas v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_areas v st : s_secret (set_areas v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_areas v st : s_reserved (set_areas v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_groups v st : s_ctx (set_groups v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_groups v st : s_regions (set_groups v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_groups v st : s_shadow (set_groups v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_groups v st : s_next_rid (set_groups v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_groups v st : s_metas (set_groups v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_groups v st : s_areas (set_groups v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_groups v st : s_groups (set_groups v st) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_groups v st : s_slots (set_groups v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_groups v st : s_tick (set_groups v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_groups v st : s_secret (set_groups v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_groups v st : s_reserved (set_groups v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_slots v st : s_ctx (set_slots v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_slots v st : s_regions (set_slots v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_slots v st : s_shadow (set_slots v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_slots v st : s_next_rid (set_slots v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_slots v st : s_metas (set_slots v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_slots v st : s_areas (set_slots v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_slots v st : s_groups (set_slots v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_slots v st : s_slots (set_slots v st) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_slots v st : s_tick (set_slots v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_slots v st : s_secret (set_slots v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_slots v st : s_reserved (set_slots v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_tick v st : s_ctx (set_tick v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_tick v st : s_regions (set_tick v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_tick v st : s_shadow (set_tick v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_tick v st : s_next_rid (set_tick v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_tick v st : s_metas (set_tick v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_tick v st : s_areas (set_tick v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_tick v st : s_groups (set_tick v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_tick v st : s_slots (set_tick v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_tick v st : s_tick (set_tick v st) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_tick v st : s_secret (set_tick v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_tick v st : s_reserved (set_tick v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_secret v c : c_secret (set_secret v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_secret v c : c_init_done (set_secret v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_secret v c : c_mmap_counter (set_secret v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_secret v c : c_free_meta_head (set_secret v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_secret v c : c_avail_meta (set_secret v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_secret v c : c_avail_meta_count (set_secret v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_secret v c : c_avail_meta_area_count (set_secret v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_secret v c : c_meta_alloc_shift (set_secret v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_secret v c : c_meta_area_head (set_secret v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_secret v c : c_meta_area_tail (set_secret v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_secret v c : c_avail_meta_areas (set_secret v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_secret v c : c_active (set_secret v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_secret v c : c_usage (set_secret v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_secret v c : c_unmap_seq (set_secret v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_secret v c : c_bounces (set_secret v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_secret v c : c_seq (set_secret v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_secret v c : c_brk (set_secret v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_init_done v c : c_secret (set_init_done v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_init_done v c : c_init_done (set_init_done v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_init_done v c : c_mmap_counter (set_init_done v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_init_done v c : c_free_meta_head (set_init_done v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_init_done v c : c_avail_meta (set_init_done v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_init_done v c : c_avail_meta_count (set_init_done v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_init_done v c : c_avail_meta_area_count (set_init_done v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_init_done v c : c_meta_alloc_shift (set_init_done v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_init_done v c : c_meta_area_head (set_init_done v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_init_done v c : c_meta_area_tail (set_init_done v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_init_done v c : c_avail_meta_areas (set_init_done v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_init_done v c : c_active (set_init_done v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_init_done v c : c_usage (set_init_done v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_init_done v c : c_unmap_seq (set_init_done v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_init_done v c : c_bounces (set_init_done v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_init_done v c : c_seq (set_init_done v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_init_done v c : c_brk (set_init_done v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_mmap_counter v c : c_secret (set_mmap_counter v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_mmap_counter v c : c_init_done (set_mmap_counter v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_mmap_counter v c : c_mmap_counter (set_mmap_counter v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_mmap_counter v c : c_free_meta_head (set_mmap_counter v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_mmap_counter v c : c_avail_meta (set_mmap_counter v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_mmap_counter v c : c_avail_meta_count (set_mmap_counter v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_mmap_counter v c : c_avail_meta_area_count (set_mmap_counter v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_mmap_counter v c : c_meta_alloc_shift (set_mmap_counter v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_mmap_counter v c : c_meta_area_head (set_mmap_counter v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_mmap_counter v c : c_meta_area_tail (set_mmap_counter v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_mmap_counter v c : c_avail_meta_areas (set_mmap_counter v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_mmap_counter v c : c_active (set_mmap_counter v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_mmap_counter v c : c_usage (set_mmap_counter v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_mmap_counter v c : c_unmap_seq (set_mmap_counter v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_mmap_counter v c : c_bounces (set_mmap_counter v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_mmap_counter v c : c_seq (set_mmap_counter v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_mmap_counter v c : c_brk (set_mmap_counter v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_free_meta_head v c : c_secret (set_free_meta_head v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_free_meta_head v c : c_init_done (set_free_meta_head v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_free_meta_head v c : c_mmap_counter (set_free_meta_head v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_free_meta_head v c : c_free_meta_head (set_free_meta_head v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_free_meta_head v c : c_avail_meta (set_free_meta_head v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_free_meta_head v c : c_avail_meta_count (set_free_meta_head v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_free_meta_head v c : c_avail_meta_area_count (set_free_meta_head v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_free_meta_head v c : c_meta_alloc_shift (set_free_meta_head v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_free_meta_head v c : c_meta_area_head (set_free_meta_head v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_free_meta_head v c : c_meta_area_tail (set_free_meta_head v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_free_meta_head v c : c_avail_meta_areas (set_free_meta_head v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_free_meta_head v c : c_active (set_free_meta_head v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_free_meta_head v c : c_usage (set_free_meta_head v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_free_meta_head v c : c_unmap_seq (set_free_meta_head v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_free_meta_head v c : c_bounces (set_free_meta_head v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_free_meta_head v c : c_seq (set_free_meta_head v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_free_meta_head v c : c_brk (set_free_meta_head v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_avail_meta v c : c_secret (set_avail_meta v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_avail_meta v c : c_init_done (set_avail_meta v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_avail_meta v c : c_mmap_counter (set_avail_meta v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_avail_meta v c : c_free_meta_head (set_avail_meta v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_avail_meta v c : c_avail_meta (set_avail_meta v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_avail_meta v c : c_avail_meta_count (set_avail_meta v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_avail_meta v c : c_avail_meta_area_count (set_avail_meta v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_avail_meta v c : c_meta_alloc_shift (set_avail_meta v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_avail_meta v c : c_meta_area_head (set_avail_meta v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_avail_meta v c : c_meta_area_tail (set_avail_meta v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_avail_meta v c : c_avail_meta_areas (set_avail_meta v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_avail_meta v c : c_active (set_avail_meta v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_avail_meta v c : c_usage (set_avail_meta v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_avail_meta v c : c_unmap_seq (set_avail_meta v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_avail_meta v c : c_bounces (set_avail_meta v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_avail_meta v c : c_seq (set_avail_meta v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_avail_meta v c : c_brk (set_avail_meta v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_avail_meta_count v c : c_secret (set_avail_meta_count v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_avail_meta_count v c : c_init_done (set_avail_meta_count v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_avail_meta_count v c : c_mmap_counter (set_avail_meta_count v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_avail_meta_count v c : c_free_meta_head (set_avail_meta_count v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_avail_meta_count v c : c_avail_meta (set_avail_meta_count v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_avail_meta_count v c : c_avail_meta_count (set_avail_meta_count v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_avail_meta_count v c : c_avail_meta_area_count (set_avail_meta_count v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_avail_meta_count v c : c_meta_alloc_shift (set_avail_meta_count v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_avail_meta_count v c : c_meta_area_head (set_avail_meta_count v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_avail_meta_count v c : c_meta_area_tail (set_avail_meta_count v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_avail_meta_count v c : c_avail_meta_areas (set_avail_meta_count v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_avail_meta_count v c : c_active (set_avail_meta_count v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_avail_meta_count v c : c_usage (set_avail_meta_count v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_avail_meta_count v c : c_unmap_seq (set_avail_meta_count v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_avail_meta_count v c : c_bounces (set_avail_meta_count v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_avail_meta_count v c : c_seq (set_avail_meta_count v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_avail_meta_count v c : c_brk (set_avail_meta_count v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_avail_meta_area_count v c : c_secret (set_avail_meta_area_count v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_avail_meta_area_count v c : c_init_done (set_avail_meta_area_count v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_avail_meta_area_count v c : c_mmap_counter (set_avail_meta_area_count v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_avail_meta_area_count v c : c_free_meta_head (set_avail_meta_area_count v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_avail_meta_area_count v c : c_avail_meta (set_avail_meta_area_count v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_avail_meta_area_count v c : c_avail_meta_count (set_avail_meta_area_count v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_avail_meta_area_count v c : c_avail_meta_area_count (set_avail_meta_area_count v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_avail_meta_area_count v c : c_meta_alloc_shift (set_avail_meta_area_count v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_avail_meta_area_count v c : c_meta_area_head (set_avail_meta_area_count v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_avail_meta_area_count v c : c_meta_area_tail (set_avail_meta_area_count v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_avail_meta_area_count v c : c_avail_meta_areas (set_avail_meta_area_count v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_avail_meta_area_count v c : c_active (set_avail_meta_area_count v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_avail_meta_area_count v c : c_usage (set_avail_meta_area_count v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_avail_meta_area_count v c : c_unmap_seq (set_avail_meta_area_count v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_avail_meta_area_count v c : c_bounces (set_avail_meta_area_count v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_avail_meta_area_count v c : c_seq (set_avail_meta_area_count v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_avail_meta_area_count v c : c_brk (set_avail_meta_area_count v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_meta_alloc_shift v c : c_secret (set_meta_alloc_shift v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_meta_alloc_shift v c : c_init_done (set_meta_alloc_shift v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_meta_alloc_shift v c : c_mmap_counter (set_meta_alloc_shift v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_meta_alloc_shift v c : c_free_meta_head (set_meta_alloc_shift v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_meta_alloc_shift v c : c_avail_meta (set_meta_alloc_shift v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_meta_alloc_shift v c : c_avail_meta_count (set_meta_alloc_shift v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_meta_alloc_shift v c : c_avail_meta_area_count (set_meta_alloc_shift v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_meta_alloc_shift v c : c_meta_alloc_shift (set_meta_alloc_shift v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_meta_alloc_shift v c : c_meta_area_head (set_meta_alloc_shift v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_meta_alloc_shift v c : c_meta_area_tail (set_meta_alloc_shift v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_meta_alloc_shift v c : c_avail_meta_areas (set_meta_alloc_shift v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_meta_alloc_shift v c : c_active (set_meta_alloc_shift v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_meta_alloc_shift v c : c_usage (set_meta_alloc_shift v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_meta_alloc_shift v c : c_unmap_seq (set_meta_alloc_shift v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_meta_alloc_shift v c : c_bounces (set_meta_alloc_shift v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_meta_alloc_shift v c : c_seq (set_meta_alloc_shift v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_meta_alloc_shift v c : c_brk (set_meta_alloc_shift v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_meta_area_head v c : c_secret (set_meta_area_head v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_meta_area_head v c : c_init_done (set_meta_area_head v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_meta_area_head v c : c_mmap_counter (set_meta_area_head v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_meta_area_head v c : c_free_meta_head (set_meta_area_head v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_meta_area_head v c : c_avail_meta (set_meta_area_head v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_meta_area_head v c : c_avail_meta_count (set_meta_area_head v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_meta_area_head v c : c_avail_meta_area_count (set_meta_area_head v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_meta_area_head v c : c_meta_alloc_shift (set_meta_area_head v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_meta_area_head v c : c_meta_area_head (set_meta_area_head v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_meta_area_head v c : c_meta_area_tail (set_meta_area_head v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_meta_area_head v c : c_avail_meta_areas (set_meta_area_head v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_meta_area_head v c : c_active (set_meta_area_head v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_meta_area_head v c : c_usage (set_meta_area_head v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_meta_area_head v c : c_unmap_seq (set_meta_area_head v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_meta_area_head v c : c_bounces (set_meta_area_head v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_meta_area_head v c : c_seq (set_meta_area_head v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_meta_area_head v c : c_brk (set_meta_area_head v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_meta_area_tail v c : c_secret (set_meta_area_tail v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_meta_area_tail v c : c_init_done (set_meta_area_tail v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_meta_area_tail v c : c_mmap_counter (set_meta_area_tail v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_meta_area_tail v c : c_free_meta_head (set_meta_area_tail v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_meta_area_tail v c : c_avail_meta (set_meta_area_tail v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_meta_area_tail v c : c_avail_meta_count (set_meta_area_tail v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_meta_area_tail v c : c_avail_meta_area_count (set_meta_area_tail v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_meta_area_tail v c : c_meta_alloc_shift (set_meta_area_tail v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_meta_area_tail v c : c_meta_area_head (set_meta_area_tail v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_meta_area_tail v c : c_meta_area_tail (set_meta_area_tail v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_meta_area_tail v c : c_avail_meta_areas (set_meta_area_tail v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_meta_area_tail v c : c_active (set_meta_area_tail v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_meta_area_tail v c : c_usage (set_meta_area_tail v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_meta_area_tail v c : c_unmap_seq (set_meta_area_tail v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_meta_area_tail v c : c_bounces (set_meta_area_tail v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_meta_area_tail v c : c_seq (set_meta_area_tail v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_meta_area_tail v c : c_brk (set_meta_area_tail v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_avail_meta_areas v c : c_secret (set_avail_meta_areas v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_avail_meta_areas v c : c_init_done (set_avail_meta_areas v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_avail_meta_areas v c : c_mmap_counter (set_avail_meta_areas v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_avail_meta_areas v c : c_free_meta_head (set_avail_meta_areas v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_avail_meta_areas v c : c_avail_meta (set_avail_meta_areas v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_avail_meta_areas v c : c_avail_meta_count (set_avail_meta_areas v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_avail_meta_areas v c : c_avail_meta_area_count (set_avail_meta_areas v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_avail_meta_areas v c : c_meta_alloc_shift (set_avail_meta_areas v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_avail_meta_areas v c : c_meta_area_head (set_avail_meta_areas v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_avail_meta_areas v c : c_meta_area_tail (set_avail_meta_areas v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_avail_meta_areas v c : c_avail_meta_areas (set_avail_meta_areas v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_avail_meta_areas v c : c_active (set_avail_meta_areas v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_avail_meta_areas v c : c_usage (set_avail_meta_areas v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_avail_meta_areas v c : c_unmap_seq (set_avail_meta_areas v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_avail_meta_areas v c : c_bounces (set_avail_meta_areas v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_avail_meta_areas v c : c_seq (set_avail_meta_areas v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_avail_meta_areas v c : c_brk (set_avail_meta_areas v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_active_map v c : c_secret (set_active_map v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_active_map v c : c_init_done (set_active_map v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_active_map v c : c_mmap_counter (set_active_map v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_active_map v c : c_free_meta_head (set_active_map v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_active_map v c : c_avail_meta (set_active_map v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_active_map v c : c_avail_meta_count (set_active_map v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_active_map v c : c_avail_meta_area_count (set_active_map v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_active_map v c : c_meta_alloc_shift (set_active_map v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_active_map v c : c_meta_area_head (set_active_map v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_active_map v c : c_meta_area_tail (set_active_map v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_active_map v c : c_avail_meta_areas (set_active_map v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_active_map v c : c_active (set_active_map v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_active_map v c : c_usage (set_active_map v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_active_map v c : c_unmap_seq (set_active_map v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_active_map v c : c_bounces (set_active_map v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_active_map v c : c_seq (set_active_map v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_active_map v c : c_brk (set_active_map v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_usage_map v c : c_secret (set_usage_map v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_usage_map v c : c_init_done (set_usage_map v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_usage_map v c : c_mmap_counter (set_usage_map v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_usage_map v c : c_free_meta_head (set_usage_map v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_usage_map v c : c_avail_meta (set_usage_map v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_usage_map v c : c_avail_meta_count (set_usage_map v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_usage_map v c : c_avail_meta_area_count (set_usage_map v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_usage_map v c : c_meta_alloc_shift (set_usage_map v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_usage_map v c : c_meta_area_head (set_usage_map v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_usage_map v c : c_meta_area_tail (set_usage_map v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_usage_map v c : c_avail_meta_areas (set_usage_map v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_usage_map v c : c_active (set_usage_map v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_usage_map v c : c_usage (set_usage_map v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_usage_map v c : c_unmap_seq (set_usage_map v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_usage_map v c : c_bounces (set_usage_map v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_usage_map v c : c_seq (set_usage_map v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_usage_map v c : c_brk (set_usage_map v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_unmap_seq_map v c : c_secret (set_unmap_seq_map v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_unmap_seq_map v c : c_init_done (set_unmap_seq_map v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_unmap_seq_map v c : c_mmap_counter (set_unmap_seq_map v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_unmap_seq_map v c : c_free_meta_head (set_unmap_seq_map v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_unmap_seq_map v c : c_avail_meta (set_unmap_seq_map v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_unmap_seq_map v c : c_avail_meta_count (set_unmap_seq_map v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_unmap_seq_map v c : c_avail_meta_area_count (set_unmap_seq_map v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_unmap_seq_map v c : c_meta_alloc_shift (set_unmap_seq_map v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_unmap_seq_map v c : c_meta_area_head (set_unmap_seq_map v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_unmap_seq_map v c : c_meta_area_tail (set_unmap_seq_map v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_unmap_seq_map v c : c_avail_meta_areas (set_unmap_seq_map v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_unmap_seq_map v c : c_active (set_unmap_seq_map v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_unmap_seq_map v c : c_usage (set_unmap_seq_map v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_unmap_seq_map v c : c_unmap_seq (set_unmap_seq_map v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_unmap_seq_map v c : c_bounces (set_unmap_seq_map v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_unmap_seq_map v c : c_seq (set_unmap_seq_map v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_unmap_seq_map v c : c_brk (set_unmap_seq_map v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_bounces_map v c : c_secret (set_bounces_map v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_bounces_map v c : c_init_done (set_bounces_map v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_bounces_map v c : c_mmap_counter (set_bounces_map v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_bounces_map v c : c_free_meta_head (set_bounces_map v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_bounces_map v c : c_avail_meta (set_bounces_map v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_bounces_map v c : c_avail_meta_count (set_bounces_map v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_bounces_map v c : c_avail_meta_area_count (set_bounces_map v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_bounces_map v c : c_meta_alloc_shift (set_bounces_map v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_bounces_map v c : c_meta_area_head (set_bounces_map v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_bounces_map v c : c_meta_area_tail (set_bounces_map v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_bounces_map v c : c_avail_meta_areas (set_bounces_map v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_bounces_map v c : c_active (set_bounces_map v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_bounces_map v c : c_usage (set_bounces_map v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_bounces_map v c : c_unmap_seq (set_bounces_map v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_bounces_map v c : c_bounces (set_bounces_map v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_bounces_map v c : c_seq (set_bounces_map v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_bounces_map v c : c_brk (set_bounces_map v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_seq v c : c_secret (set_seq v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_seq v c : c_init_done (set_seq v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_seq v c : c_mmap_counter (set_seq v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_seq v c : c_free_meta_head (set_seq v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_seq v c : c_avail_meta (set_seq v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_seq v c : c_avail_meta_count (set_seq v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_seq v c : c_avail_meta_area_count (set_seq v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_seq v c : c_meta_alloc_shift (set_seq v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_seq v c : c_meta_area_head (set_seq v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_seq v c : c_meta_area_tail (set_seq v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_seq v c : c_avail_meta_areas (set_seq v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_seq v c : c_active (set_seq v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_seq v c : c_usage (set_seq v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_seq v c : c_unmap_seq (set_seq v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_seq v c : c_bounces (set_seq v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_seq v c : c_seq (set_seq v c) = v. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_seq v c : c_brk (set_seq v c) = c_brk c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_brk v c : c_secret (set_brk v c) = c_secret c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_brk v c : c_init_done (set_brk v c) = c_init_done c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_brk v c : c_mmap_counter (set_brk v c) = c_mmap_counter c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_brk v c : c_free_meta_head (set_brk v c) = c_free_meta_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_brk v c : c_avail_meta (set_brk v c) = c_avail_meta c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_brk v c : c_avail_meta_count (set_brk v c) = c_avail_meta_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_brk v c : c_avail_meta_area_count (set_brk v c) = c_avail_meta_area_count c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_brk v c : c_meta_alloc_shift (set_brk v c) = c_meta_alloc_shift c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_brk v c : c_meta_area_head (set_brk v c) = c_meta_area_head c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_brk v c : c_meta_area_tail (set_brk v c) = c_meta_area_tail c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_brk v c : c_avail_meta_areas (set_brk v c) = c_avail_meta_areas c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_brk v c : c_active (set_brk v c) = c_active c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_brk v c : c_usage (set_brk v c) = c_usage c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_brk v c : c_unmap_seq (set_brk v c) = c_unmap_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_brk v c : c_bounces (set_brk v c) = c_bounces c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_brk v c : c_seq (set_brk v c) = c_seq c. Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_brk v c : c_brk (set_brk v c) = v. Proof. reflexivity. Qed.
End WithCeil.

#[export] Hint Rewrite @s_ctx_upd_ctx @s_regions_upd_ctx @s_shadow_upd_ctx @s_next_rid_upd_ctx @s_metas_upd_ctx @s_areas_upd_ctx @s_groups_upd_ctx @s_slots_upd_ctx @s_tick_upd_ctx @s_secret_upd_ctx @s_reserved_upd_ctx @s_ctx_set_regions @s_regions_set_regions @s_shadow_set_regions @s_next_rid_set_regions @s_metas_set_regions @s_areas_set_regions @s_groups_set_regions @s_slots_set_regions @s_tick_set_regions @s_secret_set_regions @s_reserved_set_regions @s_ctx_set_shadow @s_regions_set_shadow @s_shadow_set_shadow @s_next_rid_set_shadow @s_metas_set_shadow @s_areas_set_shadow @s_groups_set_shadow @s_slots_set_shadow @s_tick_set_shadow @s_secret_set_shadow @s_reserved_set_shadow @s_ctx_set_next_rid @s_regions_set_next_rid @s_shadow_set_next_rid @s_next_rid_set_next_rid @s_metas_set_next_rid @s_areas_set_next_rid @s_groups_set_next_rid @s_slots_set_next_rid @s_tick_set_next_rid @s_secret_set_next_rid @s_reserved_set_next_rid @s_ctx_set_metas @s_regions_set_metas @s_shadow_set_metas @s_next_rid_set_metas @s_metas_set_metas @s_areas_set_metas @s_groups_set_metas @s_slots_set_metas @s_tick_set_metas @s_secret_set_metas @s_reserved_set_metas @s_ctx_set_areas @s_regions_set_areas @s_shadow_set_areas @s_next_rid_set_areas @s_metas_set_areas @s_areas_set_areas @s_groups_set_areas @s_slots_set_areas @s_tick_set_areas @s_secret_set_areas @s_reserved_set_areas @s_ctx_set_groups @s_regions_set_groups @s_shadow_set_groups @s_next_rid_set_groups @s_metas_set_groups @s_areas_set_groups @s_groups_set_groups @s_slots_set_groups @s_tick_set_groups @s_secret_set_groups @s_reserved_set_groups @s_ctx_set_slots @s_regions_set_slots @s_shadow_set_slots @s_next_rid_set_slots @s_metas_set_slots @s_areas_set_slots @s_groups_set_slots @s_slots_set_slots @s_tick_set_slots @s_secret_set_slots @s_reserved_set_slots @s_ctx_set_tick @s_regions_set_tick @s_shadow_set_tick @s_next_rid_set_tick @s_metas_set_tick @s_areas_set_tick @s_groups_set_tick @s_slots_set_tick @s_tick_set_tick @s_secret_set_tick @s_reserved_set_tick @c_secret_set_secret @c_init_done_set_secret @c_mmap_counter_set_secret @c_free_meta_head_set_secret @c_avail_meta_set_secret @c_avail_meta_count_set_secret @c_avail_meta_area_count_set_secret @c_meta_alloc_shift_set_secret @c_meta_area_head_set_secret @c_meta_area_tail_set_secret @c_avail_meta_areas_set_secret @c_active_set_secret @c_usage_set_secret @c_unmap_seq_set_secret @c_bounces_set_secret @c_seq_set_secret @c_brk_set_secret @c_secret_set_init_done @c_init_done_set_init_done @c_mmap_counter_set_init_done @c_free_meta_head_set_init_done @c_avail_meta_set_init_done @c_avail_meta_count_set_init_done @c_avail_meta_area_count_set_init_done @c_meta_alloc_shift_set_init_done @c_meta_area_head_set_init_done @c_meta_area_tail_set_init_done @c_avail_meta_areas_set_init_done @c_active_set_init_done @c_usage_set_init_done @c_unmap_seq_set_init_done @c_bounces_set_init_done @c_seq_set_init_done @c_brk_set_init_done @c_secret_set_mmap_counter @c_init_done_set_mmap_counter @c_mmap_counter_set_mmap_counter @c_free_meta_head_set_mmap_counter @c_avail_meta_set_mmap_counter @c_avail_meta_count_set_mmap_counter @c_avail_meta_area_count_set_mmap_counter @c_meta_alloc_shift_set_mmap_counter @c_meta_area_head_set_mmap_counter @c_meta_area_tail_set_mmap_counter @c_avail_meta_areas_set_mmap_counter @c_active_set_mmap_counter @c_usage_set_mmap_counter @c_unmap_seq_set_mmap_counter @c_bounces_set_mmap_counter @c_seq_set_mmap_counter @c_brk_set_mmap_counter @c_secret_set_free_meta_head @c_init_done_set_free_meta_head @c_mmap_counter_set_free_meta_head @c_free_meta_head_set_free_meta_head @c_avail_meta_set_free_meta_head @c_avail_meta_count_set_free_meta_head @c_avail_meta_area_count_set_free_meta_head @c_meta_alloc_shift_set_free_meta_head @c_meta_area_head_set_free_meta_head @c_meta_area_tail_set_free_meta_head @c_avail_meta_areas_set_free_meta_head @c_active_set_free_meta_head @c_usage_set_free_meta_head @c_unmap_seq_set_free_meta_head @c_bounces_set_free_meta_head @c_seq_set_free_meta_head @c_brk_set_free_meta_head @c_secret_set_avail_meta @c_init_done_set_avail_meta @c_mmap_counter_set_avail_meta @c_free_meta_head_set_avail_meta @c_avail_meta_set_avail_meta @c_avail_meta_count_set_avail_meta @c_avail_meta_area_count_set_avail_meta @c_meta_alloc_shift_set_avail_meta @c_meta_area_head_set_avail_meta @c_meta_area_tail_set_avail_meta @c_avail_meta_areas_set_avail_meta @c_active_set_avail_meta @c_usage_set_avail_meta @c_unmap_seq_set_avail_meta @c_bounces_set_avail_meta @c_seq_set_avail_meta @c_brk_set_avail_meta @c_secret_set_avail_meta_count @c_init_done_set_avail_meta_count @c_mmap_counter_set_avail_meta_count @c_free_meta_head_set_avail_meta_count @c_avail_meta_set_avail_meta_count @c_avail_meta_count_set_avail_meta_count @c_avail_meta_area_count_set_avail_meta_count @c_meta_alloc_shift_set_avail_meta_count @c_meta_area_head_set_avail_meta_count @c_meta_area_tail_set_avail_meta_count @c_avail_meta_areas_set_avail_meta_count @c_active_set_avail_meta_count @c_usage_set_avail_meta_count @c_unmap_seq_set_avail_meta_count @c_bounces_set_avail_meta_count @c_seq_set_avail_meta_count @c_brk_set_avail_meta_count @c_secret_set_avail_meta_area_count @c_init_done_set_avail_meta_area_count @c_mmap_counter_set_avail_meta_area_count @c_free_meta_head_set_avail_meta_area_count @c_avail_meta_set_avail_meta_area_count @c_avail_meta_count_set_avail_meta_area_count @c_avail_meta_area_count_set_avail_meta_area_count @c_meta_alloc_shift_set_avail_meta_area_count @c_meta_area_head_set_avail_meta_area_count @c_meta_area_tail_set_avail_meta_area_count @c_avail_meta_areas_set_avail_meta_area_count @c_active_set_avail_meta_area_count @c_usage_set_avail_meta_area_count @c_unmap_seq_set_avail_meta_area_count @c_bounces_set_avail_meta_area_count @c_seq_set_avail_meta_area_count @c_brk_set_avail_meta_area_count @c_secret_set_meta_alloc_shift @c_init_done_set_meta_alloc_shift @c_mmap_counter_set_meta_alloc_shift @c_free_meta_head_set_meta_alloc_shift @c_avail_meta_set_meta_alloc_shift @c_avail_meta_count_set_meta_alloc_shift @c_avail_meta_area_count_set_meta_alloc_shift @c_meta_alloc_shift_set_meta_alloc_shift @c_meta_area_head_set_meta_alloc_shift @c_meta_area_tail_set_meta_alloc_shift @c_avail_meta_areas_set_meta_alloc_shift @c_active_set_meta_alloc_shift @c_usage_set_meta_alloc_shift @c_unmap_seq_set_meta_alloc_shift @c_bounces_set_meta_alloc_shift @c_seq_set_meta_alloc_shift @c_brk_set_meta_alloc_shift @c_secret_set_meta_area_head @c_init_done_set_meta_area_head @c_mmap_counter_set_meta_area_head @c_free_meta_head_set_meta_area_head @c_avail_meta_set_meta_area_head @c_avail_meta_count_set_meta_area_head @c_avail_meta_area_count_set_meta_area_head @c_meta_alloc_shift_set_meta_area_head @c_meta_area_head_set_meta_area_head @c_meta_area_tail_set_meta_area_head @c_avail_meta_areas_set_meta_area_head @c_active_set_meta_area_head @c_usage_set_meta_area_head @c_unmap_seq_set_meta_area_head @c_bounces_set_meta_area_head @c_seq_set_meta_area_head @c_brk_set_meta_area_head @c_secret_set_meta_area_tail @c_init_done_set_meta_area_tail @c_mmap_counter_set_meta_area_tail @c_free_meta_head_set_meta_area_tail @c_avail_meta_set_meta_area_tail @c_avail_meta_count_set_meta_area_tail @c_avail_meta_area_count_set_meta_area_tail @c_meta_alloc_shift_set_meta_area_tail @c_meta_area_head_set_meta_area_tail @c_meta_area_tail_set_meta_area_tail @c_avail_meta_areas_set_meta_area_tail @c_active_set_meta_area_tail @c_usage_set_meta_area_tail @c_unmap_seq_set_meta_area_tail @c_bounces_set_meta_area_tail @c_seq_set_meta_area_tail @c_brk_set_meta_area_tail @c_secret_set_avail_meta_areas @c_init_done_set_avail_meta_areas @c_mmap_counter_set_avail_meta_areas @c_free_meta_head_set_avail_meta_areas @c_avail_meta_set_avail_meta_areas @c_avail_meta_count_set_avail_meta_areas @c_avail_meta_area_count_set_avail_meta_areas @c_meta_alloc_shift_set_avail_meta_areas @c_meta_area_head_set_avail_meta_areas @c_meta_area_tail_set_avail_meta_areas @c_avail_meta_areas_set_avail_meta_areas @c_active_set_avail_meta_areas @c_usage_set_avail_meta_areas @c_unmap_seq_set_avail_meta_areas @c_bounces_set_avail_meta_areas @c_seq_set_avail_meta_areas @c_brk_set_avail_meta_areas @c_secret_set_active_map @c_init_done_set_active_map @c_mmap_counter_set_active_map @c_free_meta_head_set_active_map @c_avail_meta_set_active_map @c_avail_meta_count_set_active_map @c_avail_meta_area_count_set_active_map @c_meta_alloc_shift_set_active_map @c_meta_area_head_set_active_map @c_meta_area_tail_set_active_map @c_avail_meta_areas_set_active_map @c_active_set_active_map @c_usage_set_active_map @c_unmap_seq_set_active_map @c_bounces_set_active_map @c_seq_set_active_map @c_brk_set_active_map @c_secret_set_usage_map @c_init_done_set_usage_map @c_mmap_counter_set_usage_map @c_free_meta_head_set_usage_map @c_avail_meta_set_usage_map @c_avail_meta_count_set_usage_map @c_avail_meta_area_count_set_usage_map @c_meta_alloc_shift_set_usage_map @c_meta_area_head_set_usage_map @c_meta_area_tail_set_usage_map @c_avail_meta_areas_set_usage_map @c_active_set_usage_map @c_usage_set_usage_map @c_unmap_seq_set_usage_map @c_bounces_set_usage_map @c_seq_set_usage_map @c_brk_set_usage_map @c_secret_set_unmap_seq_map @c_init_done_set_unmap_seq_map @c_mmap_counter_set_unmap_seq_map @c_free_meta_head_set_unmap_seq_map @c_avail_meta_set_unmap_seq_map @c_avail_meta_count_set_unmap_seq_map @c_avail_meta_area_count_set_unmap_seq_map @c_meta_alloc_shift_set_unmap_seq_map @c_meta_area_head_set_unmap_seq_map @c_meta_area_tail_set_unmap_seq_map @c_avail_meta_areas_set_unmap_seq_map @c_active_set_unmap_seq_map @c_usage_set_unmap_seq_map @c_unmap_seq_set_unmap_seq_map @c_bounces_set_unmap_seq_map @c_seq_set_unmap_seq_map @c_brk_set_unmap_seq_map @c_secret_set_bounces_map @c_init_done_set_bounces_map @c_mmap_counter_set_bounces_map @c_free_meta_head_set_bounces_map @c_avail_meta_set_bounces_map @c_avail_meta_count_set_bounces_map @c_avail_meta_area_count_set_bounces_map @c_meta_alloc_shift_set_bounces_map @c_meta_area_head_set_bounces_map @c_meta_area_tail_set_bounces_map @c_avail_meta_areas_set_bounces_map @c_active_set_bounces_map @c_usage_set_bounces_map @c_unmap_seq_set_bounces_map @c_bounces_set_bounces_map @c_seq_set_bounces_map @c_brk_set_bounces_map @c_secret_set_seq @c_init_done_set_seq @c_mmap_counter_set_seq @c_free_meta_head_set_seq @c_avail_meta_set_seq @c_avail_meta_count_set_seq @c_avail_meta_area_count_set_seq @c_meta_alloc_shift_set_seq @c_meta_area_head_set_seq @c_meta_area_tail_set_seq @c_avail_meta_areas_set_seq @c_active_set_seq @c_usage_set_seq @c_unmap_seq_set_seq @c_bounces_set_seq @c_seq_set_seq @c_brk_set_seq @c_secret_set_brk @c_init_done_set_brk @c_mmap_counter_set_brk @c_free_meta_head_set_brk @c_avail_meta_set_brk @c_avail_meta_count_set_brk @c_avail_meta_area_count_set_brk @c_meta_alloc_shift_set_brk @c_meta_area_head_set_brk @c_meta_area_tail_set_brk @c_avail_meta_areas_set_brk @c_active_set_brk @c_usage_set_brk @c_unmap_seq_set_brk @c_bounces_set_brk @c_seq_set_brk @c_brk_set_brk : mst.
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma s_regions_set_active sc v st : s_regions (set_active sc v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_active sc v st : s_shadow (set_active sc v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_active sc v st : s_next_rid (set_active sc v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_active sc v st : s_metas (set_active sc v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_active sc v st : s_areas (set_active sc v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_active sc v st : s_groups (set_active sc v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_active sc v st : s_slots (set_active sc v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_active sc v st : s_tick (set_active sc v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_active sc v st : s_secret (set_active sc v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_active sc v st : s_reserved (set_active sc v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_usage sc v st : s_regions (set_usage sc v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_usage sc v st : s_shadow (set_usage sc v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_usage sc v st : s_next_rid (set_usage sc v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_usage sc v st : s_metas (set_usage sc v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_usage sc v st : s_areas (set_usage sc v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_usage sc v st : s_groups (set_usage sc v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_usage sc v st : s_slots (set_usage sc v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_usage sc v st : s_tick (set_usage sc v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_usage sc v st : s_secret (set_usage sc v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_usage sc v st : s_reserved (set_usage sc v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_bounce i v st : s_regions (set_bounce i v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_bounce i v st : s_shadow (set_bounce i v st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_bounce i v st : s_next_rid (set_bounce i v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_bounce i v st : s_metas (set_bounce i v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_bounce i v st : s_areas (set_bounce i v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_bounce i v st : s_groups (set_bounce i v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_bounce i v st : s_slots (set_bounce i v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_bounce i v st : s_tick (set_bounce i v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_bounce i v st : s_secret (set_bounce i v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_bounce i v st : s_reserved (set_bounce i v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_put_meta m r st : s_ctx (put_meta m r st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_put_meta m r st : s_regions (put_meta m r st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_put_meta m r st : s_shadow (put_meta m r st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_put_meta m r st : s_next_rid (put_meta m r st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_put_meta m r st : s_areas (put_meta m r st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_put_meta m r st : s_groups (put_meta m r st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_put_meta m r st : s_slots (put_meta m r st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_put_meta m r st : s_tick (put_meta m r st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_put_meta m r st : s_secret (put_meta m r st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_put_meta m r st : s_reserved (put_meta m r st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_upd_meta m f st : s_ctx (upd_meta m f st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_upd_meta m f st : s_regions (upd_meta m f st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_upd_meta m f st : s_shadow (upd_meta m f st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_upd_meta m f st : s_next_rid (upd_meta m f st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_upd_meta m f st : s_areas (upd_meta m f st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_upd_meta m f st : s_groups (upd_meta m f st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_upd_meta m f st : s_slots (upd_meta m f st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_upd_meta m f st : s_tick (upd_meta m f st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_upd_meta m f st : s_secret (upd_meta m f st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_upd_meta m f st : s_reserved (upd_meta m f st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_put_group g mo ai st : s_ctx (put_group g mo ai st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_put_group g mo ai st : s_regions (put_group g mo ai st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_put_group g mo ai st : s_shadow (put_group g mo ai st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_put_group g mo ai st : s_next_rid (put_group g mo ai st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_put_group g mo ai st : s_metas (put_group g mo ai st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_put_group g mo ai st : s_areas (put_group g mo ai st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_put_group g mo ai st : s_slots (put_group g mo ai st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_put_group g mo ai st : s_tick (put_group g mo ai st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_put_group g mo ai st : s_secret (put_group g mo ai st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_put_group g mo ai st : s_reserved (put_group g mo ai st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_del_group g st : s_ctx (del_group g st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_del_group g st : s_regions (del_group g st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_del_group g st : s_shadow (del_group g st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_del_group g st : s_next_rid (del_group g st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_del_group g st : s_metas (del_group g st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_del_group g st : s_areas (del_group g st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_del_group g st : s_slots (del_group g st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_del_group g st : s_tick (del_group g st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_del_group g st : s_secret (del_group g st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_del_group g st : s_reserved (del_group g st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_group_active_idx g ai st : s_ctx (set_group_active_idx g ai st) = s_ctx st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_group_active_idx g ai st : s_regions (set_group_active_idx g ai st) = s_regions st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_group_active_idx g ai st : s_shadow (set_group_active_idx g ai st) = s_shadow st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_group_active_idx g ai st : s_next_rid (set_group_active_idx g ai st) = s_next_rid st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_group_active_idx g ai st : s_metas (set_group_active_idx g ai st) = s_metas st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_group_active_idx g ai st : s_areas (set_group_active_idx g ai st) = s_areas st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_group_active_idx g ai st : s_slots (set_group_active_idx g ai st) = s_slots st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_group_active_idx g ai st : s_tick (set_group_active_idx g ai st) = s_tick st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_group_active_idx g ai st : s_secret (set_group_active_idx g ai st) = s_secret st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_group_active_idx g ai st : s_reserved (set_group_active_idx g ai st) = s_reserved st. Proof. unfold set_group_active_idx; destruct (get_group st g); reflexivity. Qed.
#[using="Type"] Lemma s_ctx_drop_region rid st : s_ctx (drop_region rid st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_drop_region rid st : s_next_rid (drop_region rid st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_drop_region rid st : s_metas (drop_region rid st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_drop_region rid st : s_areas (drop_region rid st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_drop_region rid st : s_groups (drop_region rid st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_drop_region rid st : s_slots (drop_region rid st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_drop_region rid st : s_tick (drop_region rid st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_drop_region rid st : s_secret (drop_region rid st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_drop_region rid st : s_reserved (drop_region rid st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_upd_region rid f st : s_ctx (upd_region rid f st) = s_ctx st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_shadow_upd_region rid f st : s_shadow (upd_region rid f st) = s_shadow st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_upd_region rid f st : s_next_rid (upd_region rid f st) = s_next_rid st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_metas_upd_region rid f st : s_metas (upd_region rid f st) = s_metas st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_areas_upd_region rid f st : s_areas (upd_region rid f st) = s_areas st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_groups_upd_region rid f st : s_groups (upd_region rid f st) = s_groups st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_slots_upd_region rid f st : s_slots (upd_region rid f st) = s_slots st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_tick_upd_region rid f st : s_tick (upd_region rid f st) = s_tick st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_secret_upd_region rid f st : s_secret (upd_region rid f st) = s_secret st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_reserved_upd_region rid f st : s_reserved (upd_region rid f st) = s_reserved st. Proof. unfold upd_region; destruct (get_region st rid); reflexivity. Qed.
#[using="Type"] Lemma s_ctx_add_slots m p stride cnt st : s_ctx (add_slots m p stride cnt st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_add_slots m p stride cnt st : s_regions (add_slots m p stride cnt st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_add_slots m p stride cnt st : s_shadow (add_slots m p stride cnt st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_add_slots m p stride cnt st : s_next_rid (add_slots m p stride cnt st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_add_slots m p stride cnt st : s_metas (add_slots m p stride cnt st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_add_slots m p stride cnt st : s_areas (add_slots m p stride cnt st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_add_slots m p stride cnt st : s_groups (add_slots m p stride cnt st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_add_slots m p stride cnt st : s_tick (add_slots m p stride cnt st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_add_slots m p stride cnt st : s_secret (add_slots m p stride cnt st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_add_slots m p stride cnt st : s_reserved (add_slots m p stride cnt st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_del_slots p stride cnt st : s_ctx (del_slots p stride cnt st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_del_slots p stride cnt st : s_regions (del_slots p stride cnt st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_del_slots p stride cnt st : s_shadow (del_slots p stride cnt st) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_del_slots p stride cnt st : s_next_rid (del_slots p stride cnt st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_del_slots p stride cnt st : s_metas (del_slots p stride cnt st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_del_slots p stride cnt st : s_areas (del_slots p stride cnt st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_del_slots p stride cnt st : s_groups (del_slots p stride cnt st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_del_slots p stride cnt st : s_tick (del_slots p stride cnt st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_del_slots p stride cnt st : s_secret (del_slots p stride cnt st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_del_slots p stride cnt st : s_reserved (del_slots p stride cnt st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_upd_shadow rid f st : s_ctx (upd_shadow rid f st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_upd_shadow rid f st : s_regions (upd_shadow rid f st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_upd_shadow rid f st : s_next_rid (upd_shadow rid f st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_upd_shadow rid f st : s_metas (upd_shadow rid f st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_upd_shadow rid f st : s_areas (upd_shadow rid f st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_upd_shadow rid f st : s_groups (upd_shadow rid f st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_upd_shadow rid f st : s_slots (upd_shadow rid f st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_upd_shadow rid f st : s_tick (upd_shadow rid f st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_upd_shadow rid f st : s_secret (upd_shadow rid f st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_upd_shadow rid f st : s_reserved (upd_shadow rid f st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_wr8 p v st : s_ctx (wr8 p v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_wr8 p v st : s_regions (wr8 p v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_wr8 p v st : s_next_rid (wr8 p v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_wr8 p v st : s_metas (wr8 p v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_wr8 p v st : s_areas (wr8 p v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_wr8 p v st : s_groups (wr8 p v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_wr8 p v st : s_slots (wr8 p v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_wr8 p v st : s_tick (wr8 p v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_wr8 p v st : s_secret (wr8 p v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_wr8 p v st : s_reserved (wr8 p v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_wr16 p v st : s_ctx (wr16 p v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_wr16 p v st : s_regions (wr16 p v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_wr16 p v st : s_next_rid (wr16 p v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_wr16 p v st : s_metas (wr16 p v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_wr16 p v st : s_areas (wr16 p v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_wr16 p v st : s_groups (wr16 p v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_wr16 p v st : s_slots (wr16 p v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_wr16 p v st : s_tick (wr16 p v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_wr16 p v st : s_secret (wr16 p v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_wr16 p v st : s_reserved (wr16 p v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_wr32 p v st : s_ctx (wr32 p v st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_wr32 p v st : s_regions (wr32 p v st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_wr32 p v st : s_next_rid (wr32 p v st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_wr32 p v st : s_metas (wr32 p v st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_wr32 p v st : s_areas (wr32 p v st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_wr32 p v st : s_groups (wr32 p v st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_wr32 p v st : s_slots (wr32 p v st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_wr32 p v st : s_tick (wr32 p v st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_wr32 p v st : s_secret (wr32 p v st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_wr32 p v st : s_reserved (wr32 p v st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_ctx_havoc p n st : s_ctx (havoc p n st) = s_ctx st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_regions_havoc p n st : s_regions (havoc p n st) = s_regions st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_havoc p n st : s_next_rid (havoc p n st) = s_next_rid st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_metas_havoc p n st : s_metas (havoc p n st) = s_metas st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_areas_havoc p n st : s_areas (havoc p n st) = s_areas st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_groups_havoc p n st : s_groups (havoc p n st) = s_groups st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_slots_havoc p n st : s_slots (havoc p n st) = s_slots st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_tick_havoc p n st : s_tick (havoc p n st) = s_tick st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_secret_havoc p n st : s_secret (havoc p n st) = s_secret st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_reserved_havoc p n st : s_reserved (havoc p n st) = s_reserved st. Proof. unfold havoc; destruct (n <=? 0); reflexivity. Qed.
#[using="Type"] Lemma s_ctx_hdr_havoc b st : s_ctx (hdr_havoc b st) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_hdr_havoc b st : s_regions (hdr_havoc b st) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_hdr_havoc b st : s_next_rid (hdr_havoc b st) = s_next_rid st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_metas_hdr_havoc b st : s_metas (hdr_havoc b st) = s_metas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_areas_hdr_havoc b st : s_areas (hdr_havoc b st) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_hdr_havoc b st : s_groups (hdr_havoc b st) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_slots_hdr_havoc b st : s_slots (hdr_havoc b st) = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_tick_hdr_havoc b st : s_tick (hdr_havoc b st) = s_tick st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_secret_hdr_havoc b st : s_secret (hdr_havoc b st) = s_secret st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_reserved_hdr_havoc b st : s_reserved (hdr_havoc b st) = s_reserved st. Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_step_seq  st : s_regions (step_seq st) = s_regions st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_shadow_step_seq  st : s_shadow (step_seq st) = s_shadow st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_step_seq  st : s_next_rid (step_seq st) = s_next_rid st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_metas_step_seq  st : s_metas (step_seq st) = s_metas st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_areas_step_seq  st : s_areas (step_seq st) = s_areas st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_groups_step_seq  st : s_groups (step_seq st) = s_groups st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_slots_step_seq  st : s_slots (step_seq st) = s_slots st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_tick_step_seq  st : s_tick (step_seq st) = s_tick st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_secret_step_seq  st : s_secret (step_seq st) = s_secret st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_reserved_step_seq  st : s_reserved (step_seq st) = s_reserved st. Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma s_regions_record_seq sc st : s_regions (record_seq sc st) = s_regions st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_shadow_record_seq sc st : s_shadow (record_seq sc st) = s_shadow st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_record_seq sc st : s_next_rid (record_seq sc st) = s_next_rid st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_metas_record_seq sc st : s_metas (record_seq sc st) = s_metas st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_areas_record_seq sc st : s_areas (record_seq sc st) = s_areas st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_groups_record_seq sc st : s_groups (record_seq sc st) = s_groups st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_slots_record_seq sc st : s_slots (record_seq sc st) = s_slots st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_tick_record_seq sc st : s_tick (record_seq sc st) = s_tick st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_secret_record_seq sc st : s_secret (record_seq sc st) = s_secret st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_reserved_record_seq sc st : s_reserved (record_seq sc st) = s_reserved st. Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma s_regions_account_bounce sc st : s_regions (account_bounce sc st) = s_regions st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_shadow_account_bounce sc st : s_shadow (account_bounce sc st) = s_shadow st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_account_bounce sc st : s_next_rid (account_bounce sc st) = s_next_rid st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_metas_account_bounce sc st : s_metas (account_bounce sc st) = s_metas st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_areas_account_bounce sc st : s_areas (account_bounce sc st) = s_areas st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_groups_account_bounce sc st : s_groups (account_bounce sc st) = s_groups st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_slots_account_bounce sc st : s_slots (account_bounce sc st) = s_slots st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_tick_account_bounce sc st : s_tick (account_bounce sc st) = s_tick st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_secret_account_bounce sc st : s_secret (account_bounce sc st) = s_secret st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_reserved_account_bounce sc st : s_reserved (account_bounce sc st) = s_reserved st. Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma s_regions_decay_bounces sc st : s_regions (decay_bounces sc st) = s_regions st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_shadow_decay_bounces sc st : s_shadow (decay_bounces sc st) = s_shadow st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_decay_bounces sc st : s_next_rid (decay_bounces sc st) = s_next_rid st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_metas_decay_bounces sc st : s_metas (decay_bounces sc st) = s_metas st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_areas_decay_bounces sc st : s_areas (decay_bounces sc st) = s_areas st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_groups_decay_bounces sc st : s_groups (decay_bounces sc st) = s_groups st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_slots_decay_bounces sc st : s_slots (decay_bounces sc st) = s_slots st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_tick_decay_bounces sc st : s_tick (decay_bounces sc st) = s_tick st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_secret_decay_bounces sc st : s_secret (decay_bounces sc st) = s_secret st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_reserved_decay_bounces sc st : s_reserved (decay_bounces sc st) = s_reserved st. Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_head h v st : s_regions (set_head h v st) = s_regions st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_shadow_set_head h v st : s_shadow (set_head h v st) = s_shadow st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_head h v st : s_next_rid (set_head h v st) = s_next_rid st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_head h v st : s_metas (set_head h v st) = s_metas st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_head h v st : s_areas (set_head h v st) = s_areas st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_head h v st : s_groups (set_head h v st) = s_groups st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_head h v st : s_slots (set_head h v st) = s_slots st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_head h v st : s_tick (set_head h v st) = s_tick st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_head h v st : s_secret (set_head h v st) = s_secret st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_head h v st : s_reserved (set_head h v st) = s_reserved st. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma s_regions_dequeue h m st : s_regions (dequeue h m st) = s_regions st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_shadow_dequeue h m st : s_shadow (dequeue h m st) = s_shadow st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_dequeue h m st : s_next_rid (dequeue h m st) = s_next_rid st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_areas_dequeue h m st : s_areas (dequeue h m st) = s_areas st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_groups_dequeue h m st : s_groups (dequeue h m st) = s_groups st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_slots_dequeue h m st : s_slots (dequeue h m st) = s_slots st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_tick_dequeue h m st : s_tick (dequeue h m st) = s_tick st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_secret_dequeue h m st : s_secret (dequeue h m st) = s_secret st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_reserved_dequeue h m st : s_reserved (dequeue h m st) = s_reserved st. Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma s_ctx_set_size p e n b3 st : s_ctx (set_size p e n b3 st) = s_ctx st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_regions_set_size p e n b3 st : s_regions (set_size p e n b3 st) = s_regions st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_set_size p e n b3 st : s_next_rid (set_size p e n b3 st) = s_next_rid st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_metas_set_size p e n b3 st : s_metas (set_size p e n b3 st) = s_metas st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_areas_set_size p e n b3 st : s_areas (set_size p e n b3 st) = s_areas st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_groups_set_size p e n b3 st : s_groups (set_size p e n b3 st) = s_groups st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_slots_set_size p e n b3 st : s_slots (set_size p e n b3 st) = s_slots st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_tick_set_size p e n b3 st : s_tick (set_size p e n b3 st) = s_tick st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_secret_set_size p e n b3 st : s_secret (set_size p e n b3 st) = s_secret st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma s_reserved_set_size p e n b3 st : s_reserved (set_size p e n b3 st) = s_reserved st. Proof. unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_active sc v st : c_secret (s_ctx (set_active sc v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_active sc v st : c_init_done (s_ctx (set_active sc v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_active sc v st : c_mmap_counter (s_ctx (set_active sc v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_active sc v st : c_free_meta_head (s_ctx (set_active sc v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_active sc v st : c_avail_meta (s_ctx (set_active sc v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_active sc v st : c_avail_meta_count (s_ctx (set_active sc v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_active sc v st : c_avail_meta_area_count (s_ctx (set_active sc v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_active sc v st : c_meta_alloc_shift (s_ctx (set_active sc v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_active sc v st : c_meta_area_head (s_ctx (set_active sc v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_active sc v st : c_meta_area_tail (s_ctx (set_active sc v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_active sc v st : c_avail_meta_areas (s_ctx (set_active sc v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_active sc v st : c_usage (s_ctx (set_active sc v st)) = c_usage (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_active sc v st : c_unmap_seq (s_ctx (set_active sc v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_active sc v st : c_bounces (s_ctx (set_active sc v st)) = c_bounces (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_active sc v st : c_seq (s_ctx (set_active sc v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_active sc v st : c_brk (s_ctx (set_active sc v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_usage sc v st : c_secret (s_ctx (set_usage sc v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_usage sc v st : c_init_done (s_ctx (set_usage sc v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_usage sc v st : c_mmap_counter (s_ctx (set_usage sc v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_usage sc v st : c_free_meta_head (s_ctx (set_usage sc v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_usage sc v st : c_avail_meta (s_ctx (set_usage sc v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_usage sc v st : c_avail_meta_count (s_ctx (set_usage sc v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_usage sc v st : c_avail_meta_area_count (s_ctx (set_usage sc v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_usage sc v st : c_meta_alloc_shift (s_ctx (set_usage sc v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_usage sc v st : c_meta_area_head (s_ctx (set_usage sc v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_usage sc v st : c_meta_area_tail (s_ctx (set_usage sc v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_usage sc v st : c_avail_meta_areas (s_ctx (set_usage sc v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_usage sc v st : c_active (s_ctx (set_usage sc v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_usage sc v st : c_unmap_seq (s_ctx (set_usage sc v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_bounces_set_usage sc v st : c_bounces (s_ctx (set_usage sc v st)) = c_bounces (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_usage sc v st : c_seq (s_ctx (set_usage sc v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_usage sc v st : c_brk (s_ctx (set_usage sc v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_set_bounce i v st : c_secret (s_ctx (set_bounce i v st)) = c_secret (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_init_done_set_bounce i v st : c_init_done (s_ctx (set_bounce i v st)) = c_init_done (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_set_bounce i v st : c_mmap_counter (s_ctx (set_bounce i v st)) = c_mmap_counter (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_set_bounce i v st : c_free_meta_head (s_ctx (set_bounce i v st)) = c_free_meta_head (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_set_bounce i v st : c_avail_meta (s_ctx (set_bounce i v st)) = c_avail_meta (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_set_bounce i v st : c_avail_meta_count (s_ctx (set_bounce i v st)) = c_avail_meta_count (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_set_bounce i v st : c_avail_meta_area_count (s_ctx (set_bounce i v st)) = c_avail_meta_area_count (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_set_bounce i v st : c_meta_alloc_shift (s_ctx (set_bounce i v st)) = c_meta_alloc_shift (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_set_bounce i v st : c_meta_area_head (s_ctx (set_bounce i v st)) = c_meta_area_head (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_set_bounce i v st : c_meta_area_tail (s_ctx (set_bounce i v st)) = c_meta_area_tail (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_set_bounce i v st : c_avail_meta_areas (s_ctx (set_bounce i v st)) = c_avail_meta_areas (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_active_set_bounce i v st : c_active (s_ctx (set_bounce i v st)) = c_active (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_usage_set_bounce i v st : c_usage (s_ctx (set_bounce i v st)) = c_usage (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_set_bounce i v st : c_unmap_seq (s_ctx (set_bounce i v st)) = c_unmap_seq (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_seq_set_bounce i v st : c_seq (s_ctx (set_bounce i v st)) = c_seq (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_brk_set_bounce i v st : c_brk (s_ctx (set_bounce i v st)) = c_brk (s_ctx st). Proof. reflexivity. Qed.
#[using="Type"] Lemma c_secret_step_seq  st : c_secret (s_ctx (step_seq st)) = c_secret (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_init_done_step_seq  st : c_init_done (s_ctx (step_seq st)) = c_init_done (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_step_seq  st : c_mmap_counter (s_ctx (step_seq st)) = c_mmap_counter (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_step_seq  st : c_free_meta_head (s_ctx (step_seq st)) = c_free_meta_head (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_step_seq  st : c_avail_meta (s_ctx (step_seq st)) = c_avail_meta (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_step_seq  st : c_avail_meta_count (s_ctx (step_seq st)) = c_avail_meta_count (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_step_seq  st : c_avail_meta_area_count (s_ctx (step_seq st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_step_seq  st : c_meta_alloc_shift (s_ctx (step_seq st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_step_seq  st : c_meta_area_head (s_ctx (step_seq st)) = c_meta_area_head (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_step_seq  st : c_meta_area_tail (s_ctx (step_seq st)) = c_meta_area_tail (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_step_seq  st : c_avail_meta_areas (s_ctx (step_seq st)) = c_avail_meta_areas (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_active_step_seq  st : c_active (s_ctx (step_seq st)) = c_active (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_usage_step_seq  st : c_usage (s_ctx (step_seq st)) = c_usage (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_bounces_step_seq  st : c_bounces (s_ctx (step_seq st)) = c_bounces (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_brk_step_seq  st : c_brk (s_ctx (step_seq st)) = c_brk (s_ctx st). Proof. unfold step_seq; destruct (_ =? _); reflexivity. Qed.
#[using="Type"] Lemma c_secret_record_seq sc st : c_secret (s_ctx (record_seq sc st)) = c_secret (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_init_done_record_seq sc st : c_init_done (s_ctx (record_seq sc st)) = c_init_done (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_record_seq sc st : c_mmap_counter (s_ctx (record_seq sc st)) = c_mmap_counter (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_record_seq sc st : c_free_meta_head (s_ctx (record_seq sc st)) = c_free_meta_head (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_record_seq sc st : c_avail_meta (s_ctx (record_seq sc st)) = c_avail_meta (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_record_seq sc st : c_avail_meta_count (s_ctx (record_seq sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_record_seq sc st : c_avail_meta_area_count (s_ctx (record_seq sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_record_seq sc st : c_meta_alloc_shift (s_ctx (record_seq sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_record_seq sc st : c_meta_area_head (s_ctx (record_seq sc st)) = c_meta_area_head (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_record_seq sc st : c_meta_area_tail (s_ctx (record_seq sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_record_seq sc st : c_avail_meta_areas (s_ctx (record_seq sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_active_record_seq sc st : c_active (s_ctx (record_seq sc st)) = c_active (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_usage_record_seq sc st : c_usage (s_ctx (record_seq sc st)) = c_usage (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_bounces_record_seq sc st : c_bounces (s_ctx (record_seq sc st)) = c_bounces (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_seq_record_seq sc st : c_seq (s_ctx (record_seq sc st)) = c_seq (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_brk_record_seq sc st : c_brk (s_ctx (record_seq sc st)) = c_brk (s_ctx st). Proof. unfold record_seq; destruct (sc_in_seq_range sc); reflexivity. Qed.
#[using="Type"] Lemma c_secret_account_bounce sc st : c_secret (s_ctx (account_bounce sc st)) = c_secret (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_init_done_account_bounce sc st : c_init_done (s_ctx (account_bounce sc st)) = c_init_done (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_account_bounce sc st : c_mmap_counter (s_ctx (account_bounce sc st)) = c_mmap_counter (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_account_bounce sc st : c_free_meta_head (s_ctx (account_bounce sc st)) = c_free_meta_head (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_account_bounce sc st : c_avail_meta (s_ctx (account_bounce sc st)) = c_avail_meta (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_account_bounce sc st : c_avail_meta_count (s_ctx (account_bounce sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_account_bounce sc st : c_avail_meta_area_count (s_ctx (account_bounce sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_account_bounce sc st : c_meta_alloc_shift (s_ctx (account_bounce sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_account_bounce sc st : c_meta_area_head (s_ctx (account_bounce sc st)) = c_meta_area_head (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_account_bounce sc st : c_meta_area_tail (s_ctx (account_bounce sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_account_bounce sc st : c_avail_meta_areas (s_ctx (account_bounce sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_active_account_bounce sc st : c_active (s_ctx (account_bounce sc st)) = c_active (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_usage_account_bounce sc st : c_usage (s_ctx (account_bounce sc st)) = c_usage (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_account_bounce sc st : c_unmap_seq (s_ctx (account_bounce sc st)) = c_unmap_seq (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_seq_account_bounce sc st : c_seq (s_ctx (account_bounce sc st)) = c_seq (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_brk_account_bounce sc st : c_brk (s_ctx (account_bounce sc st)) = c_brk (s_ctx st). Proof. unfold account_bounce, set_bounce; destruct (sc_in_seq_range sc); [destruct (_ && _); [destruct (_ <? _)|]|]; reflexivity. Qed.
#[using="Type"] Lemma c_secret_decay_bounces sc st : c_secret (s_ctx (decay_bounces sc st)) = c_secret (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_init_done_decay_bounces sc st : c_init_done (s_ctx (decay_bounces sc st)) = c_init_done (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_decay_bounces sc st : c_mmap_counter (s_ctx (decay_bounces sc st)) = c_mmap_counter (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_free_meta_head_decay_bounces sc st : c_free_meta_head (s_ctx (decay_bounces sc st)) = c_free_meta_head (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_decay_bounces sc st : c_avail_meta (s_ctx (decay_bounces sc st)) = c_avail_meta (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_decay_bounces sc st : c_avail_meta_count (s_ctx (decay_bounces sc st)) = c_avail_meta_count (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_decay_bounces sc st : c_avail_meta_area_count (s_ctx (decay_bounces sc st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_decay_bounces sc st : c_meta_alloc_shift (s_ctx (decay_bounces sc st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_decay_bounces sc st : c_meta_area_head (s_ctx (decay_bounces sc st)) = c_meta_area_head (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_decay_bounces sc st : c_meta_area_tail (s_ctx (decay_bounces sc st)) = c_meta_area_tail (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_decay_bounces sc st : c_avail_meta_areas (s_ctx (decay_bounces sc st)) = c_avail_meta_areas (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_active_decay_bounces sc st : c_active (s_ctx (decay_bounces sc st)) = c_active (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_usage_decay_bounces sc st : c_usage (s_ctx (decay_bounces sc st)) = c_usage (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_decay_bounces sc st : c_unmap_seq (s_ctx (decay_bounces sc st)) = c_unmap_seq (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_seq_decay_bounces sc st : c_seq (s_ctx (decay_bounces sc st)) = c_seq (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_brk_decay_bounces sc st : c_brk (s_ctx (decay_bounces sc st)) = c_brk (s_ctx st). Proof. unfold decay_bounces, set_bounce; destruct (_ && _); reflexivity. Qed.
#[using="Type"] Lemma c_secret_dequeue h m st : c_secret (s_ctx (dequeue h m st)) = c_secret (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_init_done_dequeue h m st : c_init_done (s_ctx (dequeue h m st)) = c_init_done (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_mmap_counter_dequeue h m st : c_mmap_counter (s_ctx (dequeue h m st)) = c_mmap_counter (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_dequeue h m st : c_avail_meta (s_ctx (dequeue h m st)) = c_avail_meta (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_count_dequeue h m st : c_avail_meta_count (s_ctx (dequeue h m st)) = c_avail_meta_count (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_area_count_dequeue h m st : c_avail_meta_area_count (s_ctx (dequeue h m st)) = c_avail_meta_area_count (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_meta_alloc_shift_dequeue h m st : c_meta_alloc_shift (s_ctx (dequeue h m st)) = c_meta_alloc_shift (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_head_dequeue h m st : c_meta_area_head (s_ctx (dequeue h m st)) = c_meta_area_head (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_meta_area_tail_dequeue h m st : c_meta_area_tail (s_ctx (dequeue h m st)) = c_meta_area_tail (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_avail_meta_areas_dequeue h m st : c_avail_meta_areas (s_ctx (dequeue h m st)) = c_avail_meta_areas (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_usage_dequeue h m st : c_usage (s_ctx (dequeue h m st)) = c_usage (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_unmap_seq_dequeue h m st : c_unmap_seq (s_ctx (dequeue h m st)) = c_unmap_seq (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_bounces_dequeue h m st : c_bounces (s_ctx (dequeue h m st)) = c_bounces (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_seq_dequeue h m st : c_seq (s_ctx (dequeue h m st)) = c_seq (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
#[using="Type"] Lemma c_brk_dequeue h m st : c_brk (s_ctx (dequeue h m st)) = c_brk (s_ctx st). Proof. unfold dequeue; destruct (negb _); [destruct (m_prev _); destruct (m_next _); destruct (optr_eqb _ _); try destruct h|destruct h]; reflexivity. Qed.
End WithCeil.

#[export] Hint Rewrite @s_regions_set_active @s_shadow_set_active @s_next_rid_set_active @s_metas_set_active @s_areas_set_active @s_groups_set_active @s_slots_set_active @s_tick_set_active @s_secret_set_active @s_reserved_set_active @s_regions_set_usage @s_shadow_set_usage @s_next_rid_set_usage @s_metas_set_usage @s_areas_set_usage @s_groups_set_usage @s_slots_set_usage @s_tick_set_usage @s_secret_set_usage @s_reserved_set_usage @s_regions_set_bounce @s_shadow_set_bounce @s_next_rid_set_bounce @s_metas_set_bounce @s_areas_set_bounce @s_groups_set_bounce @s_slots_set_bounce @s_tick_set_bounce @s_secret_set_bounce @s_reserved_set_bounce @s_ctx_put_meta @s_regions_put_meta @s_shadow_put_meta @s_next_rid_put_meta @s_areas_put_meta @s_groups_put_meta @s_slots_put_meta @s_tick_put_meta @s_secret_put_meta @s_reserved_put_meta @s_ctx_upd_meta @s_regions_upd_meta @s_shadow_upd_meta @s_next_rid_upd_meta @s_areas_upd_meta @s_groups_upd_meta @s_slots_upd_meta @s_tick_upd_meta @s_secret_upd_meta @s_reserved_upd_meta @s_ctx_put_group @s_regions_put_group @s_shadow_put_group @s_next_rid_put_group @s_metas_put_group @s_areas_put_group @s_slots_put_group @s_tick_put_group @s_secret_put_group @s_reserved_put_group @s_ctx_del_group @s_regions_del_group @s_shadow_del_group @s_next_rid_del_group @s_metas_del_group @s_areas_del_group @s_slots_del_group @s_tick_del_group @s_secret_del_group @s_reserved_del_group @s_ctx_set_group_active_idx @s_regions_set_group_active_idx @s_shadow_set_group_active_idx @s_next_rid_set_group_active_idx @s_metas_set_group_active_idx @s_areas_set_group_active_idx @s_slots_set_group_active_idx @s_tick_set_group_active_idx @s_secret_set_group_active_idx @s_reserved_set_group_active_idx @s_ctx_drop_region @s_next_rid_drop_region @s_metas_drop_region @s_areas_drop_region @s_groups_drop_region @s_slots_drop_region @s_tick_drop_region @s_secret_drop_region @s_reserved_drop_region @s_ctx_upd_region @s_shadow_upd_region @s_next_rid_upd_region @s_metas_upd_region @s_areas_upd_region @s_groups_upd_region @s_slots_upd_region @s_tick_upd_region @s_secret_upd_region @s_reserved_upd_region @s_ctx_add_slots @s_regions_add_slots @s_shadow_add_slots @s_next_rid_add_slots @s_metas_add_slots @s_areas_add_slots @s_groups_add_slots @s_tick_add_slots @s_secret_add_slots @s_reserved_add_slots @s_ctx_del_slots @s_regions_del_slots @s_shadow_del_slots @s_next_rid_del_slots @s_metas_del_slots @s_areas_del_slots @s_groups_del_slots @s_tick_del_slots @s_secret_del_slots @s_reserved_del_slots @s_ctx_upd_shadow @s_regions_upd_shadow @s_next_rid_upd_shadow @s_metas_upd_shadow @s_areas_upd_shadow @s_groups_upd_shadow @s_slots_upd_shadow @s_tick_upd_shadow @s_secret_upd_shadow @s_reserved_upd_shadow @s_ctx_wr8 @s_regions_wr8 @s_next_rid_wr8 @s_metas_wr8 @s_areas_wr8 @s_groups_wr8 @s_slots_wr8 @s_tick_wr8 @s_secret_wr8 @s_reserved_wr8 @s_ctx_wr16 @s_regions_wr16 @s_next_rid_wr16 @s_metas_wr16 @s_areas_wr16 @s_groups_wr16 @s_slots_wr16 @s_tick_wr16 @s_secret_wr16 @s_reserved_wr16 @s_ctx_wr32 @s_regions_wr32 @s_next_rid_wr32 @s_metas_wr32 @s_areas_wr32 @s_groups_wr32 @s_slots_wr32 @s_tick_wr32 @s_secret_wr32 @s_reserved_wr32 @s_ctx_havoc @s_regions_havoc @s_next_rid_havoc @s_metas_havoc @s_areas_havoc @s_groups_havoc @s_slots_havoc @s_tick_havoc @s_secret_havoc @s_reserved_havoc @s_ctx_hdr_havoc @s_regions_hdr_havoc @s_next_rid_hdr_havoc @s_metas_hdr_havoc @s_areas_hdr_havoc @s_groups_hdr_havoc @s_slots_hdr_havoc @s_tick_hdr_havoc @s_secret_hdr_havoc @s_reserved_hdr_havoc @s_regions_step_seq @s_shadow_step_seq @s_next_rid_step_seq @s_metas_step_seq @s_areas_step_seq @s_groups_step_seq @s_slots_step_seq @s_tick_step_seq @s_secret_step_seq @s_reserved_step_seq @s_regions_record_seq @s_shadow_record_seq @s_next_rid_record_seq @s_metas_record_seq @s_areas_record_seq @s_groups_record_seq @s_slots_record_seq @s_tick_record_seq @s_secret_record_seq @s_reserved_record_seq @s_regions_account_bounce @s_shadow_account_bounce @s_next_rid_account_bounce @s_metas_account_bounce @s_areas_account_bounce @s_groups_account_bounce @s_slots_account_bounce @s_tick_account_bounce @s_secret_account_bounce @s_reserved_account_bounce @s_regions_decay_bounces @s_shadow_decay_bounces @s_next_rid_decay_bounces @s_metas_decay_bounces @s_areas_decay_bounces @s_groups_decay_bounces @s_slots_decay_bounces @s_tick_decay_bounces @s_secret_decay_bounces @s_reserved_decay_bounces @s_regions_set_head @s_shadow_set_head @s_next_rid_set_head @s_metas_set_head @s_areas_set_head @s_groups_set_head @s_slots_set_head @s_tick_set_head @s_secret_set_head @s_reserved_set_head @s_regions_dequeue @s_shadow_dequeue @s_next_rid_dequeue @s_areas_dequeue @s_groups_dequeue @s_slots_dequeue @s_tick_dequeue @s_secret_dequeue @s_reserved_dequeue @s_ctx_set_size @s_regions_set_size @s_next_rid_set_size @s_metas_set_size @s_areas_set_size @s_groups_set_size @s_slots_set_size @s_tick_set_size @s_secret_set_size @s_reserved_set_size @c_secret_set_active @c_init_done_set_active @c_mmap_counter_set_active @c_free_meta_head_set_active @c_avail_meta_set_active @c_avail_meta_count_set_active @c_avail_meta_area_count_set_active @c_meta_alloc_shift_set_active @c_meta_area_head_set_active @c_meta_area_tail_set_active @c_avail_meta_areas_set_active @c_usage_set_active @c_unmap_seq_set_active @c_bounces_set_active @c_seq_set_active @c_brk_set_active @c_secret_set_usage @c_init_done_set_usage @c_mmap_counter_set_usage @c_free_meta_head_set_usage @c_avail_meta_set_usage @c_avail_meta_count_set_usage @c_avail_meta_area_count_set_usage @c_meta_alloc_shift_set_usage @c_meta_area_head_set_usage @c_meta_area_tail_set_usage @c_avail_meta_areas_set_usage @c_active_set_usage @c_unmap_seq_set_usage @c_bounces_set_usage @c_seq_set_usage @c_brk_set_usage @c_secret_set_bounce @c_init_done_set_bounce @c_mmap_counter_set_bounce @c_free_meta_head_set_bounce @c_avail_meta_set_bounce @c_avail_meta_count_set_bounce @c_avail_meta_area_count_set_bounce @c_meta_alloc_shift_set_bounce @c_meta_area_head_set_bounce @c_meta_area_tail_set_bounce @c_avail_meta_areas_set_bounce @c_active_set_bounce @c_usage_set_bounce @c_unmap_seq_set_bounce @c_seq_set_bounce @c_brk_set_bounce @c_secret_step_seq @c_init_done_step_seq @c_mmap_counter_step_seq @c_free_meta_head_step_seq @c_avail_meta_step_seq @c_avail_meta_count_step_seq @c_avail_meta_area_count_step_seq @c_meta_alloc_shift_step_seq @c_meta_area_head_step_seq @c_meta_area_tail_step_seq @c_avail_meta_areas_step_seq @c_active_step_seq @c_usage_step_seq @c_bounces_step_seq @c_brk_step_seq @c_secret_record_seq @c_init_done_record_seq @c_mmap_counter_record_seq @c_free_meta_head_record_seq @c_avail_meta_record_seq @c_avail_meta_count_record_seq @c_avail_meta_area_count_record_seq @c_meta_alloc_shift_record_seq @c_meta_area_head_record_seq @c_meta_area_tail_record_seq @c_avail_meta_areas_record_seq @c_active_record_seq @c_usage_record_seq @c_bounces_record_seq @c_seq_record_seq @c_brk_record_seq @c_secret_account_bounce @c_init_done_account_bounce @c_mmap_counter_account_bounce @c_free_meta_head_account_bounce @c_avail_meta_account_bounce @c_avail_meta_count_account_bounce @c_avail_meta_area_count_account_bounce @c_meta_alloc_shift_account_bounce @c_meta_area_head_account_bounce @c_meta_area_tail_account_bounce @c_avail_meta_areas_account_bounce @c_active_account_bounce @c_usage_account_bounce @c_unmap_seq_account_bounce @c_seq_account_bounce @c_brk_account_bounce @c_secret_decay_bounces @c_init_done_decay_bounces @c_mmap_counter_decay_bounces @c_free_meta_head_decay_bounces @c_avail_meta_decay_bounces @c_avail_meta_count_decay_bounces @c_avail_meta_area_count_decay_bounces @c_meta_alloc_shift_decay_bounces @c_meta_area_head_decay_bounces @c_meta_area_tail_decay_bounces @c_avail_meta_areas_decay_bounces @c_active_decay_bounces @c_usage_decay_bounces @c_unmap_seq_decay_bounces @c_seq_decay_bounces @c_brk_decay_bounces @c_secret_dequeue @c_init_done_dequeue @c_mmap_counter_dequeue @c_avail_meta_dequeue @c_avail_meta_count_dequeue @c_avail_meta_area_count_dequeue @c_meta_alloc_shift_dequeue @c_meta_area_head_dequeue @c_meta_area_tail_dequeue @c_avail_meta_areas_dequeue @c_usage_dequeue @c_unmap_seq_dequeue @c_bounces_dequeue @c_seq_dequeue @c_brk_dequeue : mst.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma strip_fields st :
  s_ctx (strip st) = s_ctx st /\ s_regions (strip st) = s_regions st /\ s_next_rid (strip st) = s_next_rid st
  /\ s_metas (strip st) = s_metas st /\ s_areas (strip st) = s_areas st /\ s_groups (strip st) = s_groups st
  /\ s_slots (strip st) = s_slots st /\ s_secret (strip st) = s_secret st /\ s_reserved (strip st) = s_reserved st.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac by_strip H :=
  first [ apply (f_equal s_ctx) in H | apply (f_equal s_regions) in H | apply (f_equal s_next_rid) in H
        | apply (f_equal s_metas) in H | apply (f_equal s_areas) in H | apply (f_equal s_groups) in H
        | apply (f_equal s_slots) in H | apply (f_equal s_secret) in H | apply (f_equal s_reserved) in H ]; exact H.

Section WithCeil.
Context {CE : CEIL}.
Section LAYOUT_FIELDS.
  Ltac lay lem := intros; pose proof lem as H; cbn [strip] in H;
    match goal with |- ?F _ = _ => apply (f_equal F) in H; cbn in H; exact H end.
  #[using="Type"] Lemma s_ctx_zero_hdrs p size i cnt st : s_ctx (zero_hdrs p size i cnt st) = s_ctx st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_regions_zero_hdrs p size i cnt st : s_regions (zero_hdrs p size i cnt st) = s_regions st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_next_rid_zero_hdrs p size i cnt st : s_next_rid (zero_hdrs p size i cnt st) = s_next_rid st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_metas_zero_hdrs p size i cnt st : s_metas (zero_hdrs p size i cnt st) = s_metas st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_areas_zero_hdrs p size i cnt st : s_areas (zero_hdrs p size i cnt st) = s_areas st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_groups_zero_hdrs p size i cnt st : s_groups (zero_hdrs p size i cnt st) = s_groups st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_slots_zero_hdrs p size i cnt st : s_slots (zero_hdrs p size i cnt st) = s_slots st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_secret_zero_hdrs p size i cnt st : s_secret (zero_hdrs p size i cnt st) = s_secret st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_reserved_zero_hdrs p size i cnt st : s_reserved (zero_hdrs p size i cnt st) = s_reserved st. Proof. lay (strip_zero_hdrs p size i cnt st). Qed.
  #[using="Type"] Lemma s_tick_zero_hdrs p size i cnt st : s_tick (zero_hdrs p size i cnt st) = s_tick st.
  Proof. revert i st; induction cnt; intros; cbn [zero_hdrs]; [reflexivity|]. rewrite IHcnt. reflexivity. Qed.

  #[using="Type"] Lemma s_ctx_enframe_at st g idx n off : s_ctx (fst (enframe_at st g idx n off)) = s_ctx st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_regions_enframe_at st g idx n off : s_regions (fst (enframe_at st g idx n off)) = s_regions st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_next_rid_enframe_at st g idx n off : s_next_rid (fst (enframe_at st g idx n off)) = s_next_rid st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_metas_enframe_at st g idx n off : s_metas (fst (enframe_at st g idx n off)) = s_metas st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_areas_enframe_at st g idx n off : s_areas (fst (enframe_at st g idx n off)) = s_areas st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_groups_enframe_at st g idx n off : s_groups (fst (enframe_at st g idx n off)) = s_groups st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_slots_enframe_at st g idx n off : s_slots (fst (enframe_at st g idx n off)) = s_slots st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_secret_enframe_at st g idx n off : s_secret (fst (enframe_at st g idx n off)) = s_secret st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_reserved_enframe_at st g idx n off : s_reserved (fst (enframe_at st g idx n off)) = s_reserved st. Proof. lay (strip_enframe_at st g idx n off). Qed.
  #[using="Type"] Lemma s_tick_enframe_at st g idx n off : s_tick (fst (enframe_at st g idx n off)) = s_tick st.
  Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn -[set_size wr8 wr16 Z.add Z.sub Z.mul Z.div get_stride];
    unfold set_size; destruct (5 <=? _); destruct (negb _); reflexivity. Qed.

  #[using="Type"] Lemma s_ctx_nest_layout st g idx j size cnt : s_ctx (nest_layout st g idx j size cnt) = s_ctx st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_regions_nest_layout st g idx j size cnt : s_regions (nest_layout st g idx j size cnt) = s_regions st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_next_rid_nest_layout st g idx j size cnt : s_next_rid (nest_layout st g idx j size cnt) = s_next_rid st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_metas_nest_layout st g idx j size cnt : s_metas (nest_layout st g idx j size cnt) = s_metas st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_areas_nest_layout st g idx j size cnt : s_areas (nest_layout st g idx j size cnt) = s_areas st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_groups_nest_layout st g idx j size cnt : s_groups (nest_layout st g idx j size cnt) = s_groups st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_slots_nest_layout st g idx j size cnt : s_slots (nest_layout st g idx j size cnt) = s_slots st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_secret_nest_layout st g idx j size cnt : s_secret (nest_layout st g idx j size cnt) = s_secret st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_reserved_nest_layout st g idx j size cnt : s_reserved (nest_layout st g idx j size cnt) = s_reserved st. Proof. lay (strip_nest_layout st g idx j size cnt). Qed.
  #[using="Type"] Lemma s_tick_nest_layout st g idx j size cnt : s_tick (nest_layout st g idx j size cnt) = s_tick st.
  Proof. unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
    rewrite s_tick_zero_hdrs. cbn. pose proof (s_tick_enframe_at st g idx (UNIT * size_class j - IB) 0) as H. rewrite E in H. exact H. Qed.
End LAYOUT_FIELDS.
End WithCeil.

#[export] Hint Rewrite @s_ctx_zero_hdrs @s_regions_zero_hdrs @s_next_rid_zero_hdrs @s_metas_zero_hdrs @s_areas_zero_hdrs @s_groups_zero_hdrs @s_slots_zero_hdrs @s_secret_zero_hdrs @s_reserved_zero_hdrs @s_tick_zero_hdrs
  @s_ctx_enframe_at @s_regions_enframe_at @s_next_rid_enframe_at @s_metas_enframe_at @s_areas_enframe_at @s_groups_enframe_at @s_slots_enframe_at @s_secret_enframe_at @s_reserved_enframe_at @s_tick_enframe_at
  @s_ctx_nest_layout @s_regions_nest_layout @s_next_rid_nest_layout @s_metas_nest_layout @s_areas_nest_layout @s_groups_nest_layout @s_slots_nest_layout @s_secret_nest_layout @s_reserved_nest_layout @s_tick_nest_layout : mst.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma s_regions_new_region k b l st : s_regions (fst (new_region k b l st)) = <[s_next_rid st := mkRegion k b l]> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_next_rid_new_region k b l st : s_next_rid (fst (new_region k b l st)) = N.succ (s_next_rid st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma snd_new_region k b l st : snd (new_region k b l st) = s_next_rid st.
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_regions_drop_region rid st : s_regions (drop_region rid st) = delete rid (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_drop_region rid st : s_shadow (drop_region rid st) = delete rid (s_shadow st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_put_group g mo ai st : s_groups (put_group g mo ai st) = <[g := mkGhdr mo (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_groups_del_group g st : s_groups (del_group g st) = delete g (s_groups st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma s_shadow_upd_shadow rid f st : s_shadow (upd_shadow rid f st) = <[rid := f (get_shadow st rid)]> (s_shadow st).
Proof. reflexivity. Qed.
End WithCeil.

#[export] Hint Rewrite @s_regions_new_region @s_next_rid_new_region @snd_new_region @s_regions_drop_region @s_shadow_drop_region
  @s_groups_put_group @s_groups_del_group @s_shadow_upd_shadow : mst.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma active_set_active st sc v sc' : active (set_active sc v st) sc' = if sc' =? sc then v else active st sc'.
Proof.
  unfold active, set_active, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE].
  - destruct v; [rewrite lookup_insert_eq| rewrite lookup_delete_eq]; reflexivity.
  - destruct v; [rewrite lookup_insert_ne by congruence| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma usage_set_usage st sc v sc' : usage (set_usage sc v st) sc' = if sc' =? sc then v else usage st sc'.
Proof.
  unfold usage, set_usage, ctx; cbn. destruct (Z.eqb_spec sc' sc) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma bounces_set_bounce st i v i' : bounces (set_bounce i v st) i' = if i' =? i then v else bounces st i'.
Proof.
  unfold bounces, set_bounce, ctx; cbn. destruct (Z.eqb_spec i' i) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma get_head_set_head st h v : get_head (set_head h v st) h = v.
Proof. destruct h; cbn; [rewrite active_set_active, Z.eqb_refl|]; reflexivity. Qed.
#[using="Type"] Lemma get_head_set_head_other st h h' v : h' <> h -> get_head (set_head h v st) h' = get_head st h'.
Proof.
  intros NE. destruct h as [sc|], h' as [sc'|]; cbn; try reflexivity; try congruence.
  rewrite active_set_active. destruct (Z.eqb_spec sc' sc); [congruence| reflexivity].
Qed.
#[using="Type"] Lemma active_upd_meta st m f sc : active (upd_meta m f st) sc = active st sc. Proof. reflexivity. Qed.
#[using="Type"] Lemma active_put_meta st m r sc : active (put_meta m r st) sc = active st sc. Proof. reflexivity. Qed.
#[using="Type"] Lemma usage_upd_meta st m f sc : usage (upd_meta m f st) sc = usage st sc. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_head_upd_meta st m f h : get_head (upd_meta m f st) h = get_head st h. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma get_head_put_meta st m r h : get_head (put_meta m r st) h = get_head st h. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_set_head st h v x : get_meta_rec (set_head h v st) x = get_meta_rec st x. Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma get_meta_rec_upd_ctx st f x : get_meta_rec (upd_ctx f st) x = get_meta_rec st x. Proof. reflexivity. Qed.
End WithCeil.

#[export] Hint Rewrite @active_set_active @usage_set_usage @bounces_set_bounce @get_head_set_head
  @active_upd_meta @active_put_meta @usage_upd_meta @get_head_upd_meta @get_head_put_meta @get_meta_rec_set_head @get_meta_rec_upd_ctx : mst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma lookup_new_region k b l st rid :
  s_regions (fst (new_region k b l st)) !! rid = if (rid =? s_next_rid st)%N then Some (mkRegion k b l) else s_regions st !! rid.
Proof.
  rewrite s_regions_new_region. destruct (N.eqb_spec rid (s_next_rid st)) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma lookup_drop_region rid st rid' :
  s_regions (drop_region rid st) !! rid' = if (rid' =? rid)%N then None else s_regions st !! rid'.
Proof.
  rewrite s_regions_drop_region. destruct (N.eqb_spec rid' rid) as [->|NE];
  [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma lookup_upd_region rid f st rid' :
  s_regions (upd_region rid f st) !! rid' =
  if (rid' =? rid)%N then option_map f (s_regions st !! rid) else s_regions st !! rid'.
Proof.
  unfold upd_region, get_region. destruct (s_regions st !! rid) as [r|] eqn:E; cbn.
  - destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; [reflexivity|reflexivity].
  - destruct (N.eqb_spec rid' rid) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
#[using="Type"] Lemma conc_eq st p r : s_regions st !! (fst p) = Some r -> conc st p = r_base r + snd p.
Proof. intros H. unfold conc, get_region. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma lookup_put_group g mo ai st b :
  s_groups (put_group g mo ai st) !! b = if aptr_eqb b g then Some (mkGhdr mo (Z.land ai 31)) else s_groups st !! b.
Proof.
  rewrite s_groups_put_group. destruct (aptr_eqb_spec b g) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma lookup_del_group g st b :
  s_groups (del_group g st) !! b = if aptr_eqb b g then None else s_groups st !! b.
Proof.
  rewrite s_groups_del_group. destruct (aptr_eqb_spec b g) as [->|NE];
  [rewrite lookup_delete_eq| rewrite lookup_delete_ne by congruence]; reflexivity.
Qed.
#[using="Type"] Lemma lookup_set_group_active_idx g ai st b :
  s_groups (set_group_active_idx g ai st) !! b =
  if aptr_eqb b g then option_map (fun h => mkGhdr (g_meta h) (Z.land ai 31)) (s_groups st !! g) else s_groups st !! b.
Proof.
  unfold set_group_active_idx, get_group. destruct (s_groups st !! g) as [h|] eqn:E; cbn.
  - destruct (aptr_eqb_spec b g) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
  - destruct (aptr_eqb_spec b g) as [->|NE]; [rewrite E|]; reflexivity.
Qed.
#[using="Type"] Lemma group_active_idx_eq st g m ai : s_groups st !! g = Some (mkGhdr m ai) -> group_active_idx st g = Z.land ai 31.
Proof. intros H. unfold group_active_idx, get_group. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
  P 0 x -> (forall n a, 0 <= n -> P n a -> P (n + 1) (f a)) -> forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
  intros H0 HS n Hn. rewrite iter_nat_of_Z by exact Hn.
  rewrite <- (Z2Nat.id n) at 1 by exact Hn. rewrite <- Zabs2Nat.abs_nat_nonneg by exact Hn.
  induction (Z.abs_nat n) as [|k IH]; [exact H0|].
  cbn [nat_rect]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply HS; [lia| exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lookup_add_slots m p stride cnt st s : 0 <= cnt -> 0 < stride ->
  s_slots (add_slots m p stride cnt st) !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
  then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s.
Proof.
  intros Hc Hs. unfold add_slots. cbn -[Z.iter Z.add Z.mul Z.sub Z.div Z.modulo Z.leb Z.ltb Z.eqb lookup insert].
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> tb)).
  assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (0, s_slots st) in fst r = n /\
            snd r !! s = if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n)
                         then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s).
  { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = n /\ snd r !! s = (if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n) then Some (m, (snd s - snd p - UNIT) / stride) else s_slots st !! s))); [| |exact Hn].
    - cbn. split; [reflexivity|]. destruct ((fst s =? fst p)%N && _ && _) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) 0); [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Bool.andb_true_iff in E as [E _]. apply Bool.andb_true_iff in E as [_ E]. apply Z.leb_le in E.
      pose proof (Z.div_pos (snd s - snd p - UNIT) stride E Hs). lia.
    - intros k [i tb] Hk [Hi IH]. cbn in Hi; subst i. unfold F. cbn [fst snd]. split; [reflexivity|].
      destruct (aptr_eqb_spec s (aadd p (UNIT + stride * k))) as [->|NE].
      + rewrite lookup_insert_eq. unfold aadd; cbn [fst snd]. rewrite N.eqb_refl.
        replace (snd p + (UNIT + stride * k) - snd p - UNIT) with (k * stride) by lia.
        rewrite Z_mod_mult, Z.div_mul, Z.eqb_refl by lia. cbn.
        destruct (Z.leb_spec 0 (k * stride)); [|nia]. destruct (Z.ltb_spec k (k + 1)); [|lia]. reflexivity.
      + rewrite lookup_insert_ne by congruence. rewrite IH.
        destruct ((fst s =? fst p)%N) eqn:E1; cbn; [|reflexivity].
        destruct (Z.leb_spec 0 (snd s - snd p - UNIT)); cbn; [|reflexivity].
        destruct (Z.eqb_spec ((snd s - snd p - UNIT) mod stride) 0); cbn; [|reflexivity].
        destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) k), (Z.ltb_spec ((snd s - snd p - UNIT) / stride) (k + 1)); try reflexivity; try lia.
        exfalso. apply NE. apply N.eqb_eq in E1. unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
        assert ((so - po - UNIT) / stride = k) by lia.
        pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia. }
  destruct (GEN cnt Hc) as [_ G]. exact G.
Qed.

#[using="Type"] Lemma lookup_del_slots p stride cnt st s : 0 <= cnt -> 0 < stride ->
  s_slots (del_slots p stride cnt st) !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)
  then None else s_slots st !! s.
Proof.
  intros Hc Hs. unfold del_slots. cbn -[Z.iter Z.add Z.mul Z.sub Z.div Z.modulo Z.leb Z.ltb Z.eqb lookup delete].
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, delete (aadd p (UNIT + stride * i)) tb)).
  assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (0, s_slots st) in fst r = n /\
            snd r !! s = if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n)
                         then None else s_slots st !! s).
  { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = n /\ snd r !! s = (if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? n) then None else s_slots st !! s))); [| |exact Hn].
    - cbn. split; [reflexivity|]. destruct ((fst s =? fst p)%N && _ && _) eqn:E; [|reflexivity].
      destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) 0); [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Bool.andb_true_iff in E as [E _]. apply Bool.andb_true_iff in E as [_ E]. apply Z.leb_le in E.
      pose proof (Z.div_pos (snd s - snd p - UNIT) stride E Hs). lia.
    - intros k [i tb] Hk [Hi IH]. cbn in Hi; subst i. unfold F. cbn [fst snd]. split; [reflexivity|].
      destruct (aptr_eqb_spec s (aadd p (UNIT + stride * k))) as [->|NE].
      + rewrite lookup_delete_eq. unfold aadd; cbn [fst snd]. rewrite N.eqb_refl.
        replace (snd p + (UNIT + stride * k) - snd p - UNIT) with (k * stride) by lia.
        rewrite Z_mod_mult, Z.div_mul, Z.eqb_refl by lia. cbn.
        destruct (Z.leb_spec 0 (k * stride)); [|nia]. destruct (Z.ltb_spec k (k + 1)); [|lia]. reflexivity.
      + rewrite lookup_delete_ne by congruence. rewrite IH.
        destruct ((fst s =? fst p)%N) eqn:E1; cbn; [|reflexivity].
        destruct (Z.leb_spec 0 (snd s - snd p - UNIT)); cbn; [|reflexivity].
        destruct (Z.eqb_spec ((snd s - snd p - UNIT) mod stride) 0); cbn; [|reflexivity].
        destruct (Z.ltb_spec ((snd s - snd p - UNIT) / stride) k), (Z.ltb_spec ((snd s - snd p - UNIT) / stride) (k + 1)); try reflexivity; try lia.
        exfalso. apply NE. apply N.eqb_eq in E1. unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
        assert ((so - po - UNIT) / stride = k) by lia.
        pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia. }
  destruct (GEN cnt Hc) as [_ G]. exact G.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_key_test p stride cnt s : 0 < stride ->
  ((fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod stride =? 0) && ((snd s - snd p - UNIT) / stride <? cnt)) = true
  <-> exists i, 0 <= i < cnt /\ s = aadd p (UNIT + stride * i).
Proof.
  intros Hs. rewrite !Bool.andb_true_iff, N.eqb_eq, Z.leb_le, Z.eqb_eq, Z.ltb_lt. split.
  - intros [[[E1 E2] E3] E4]. exists ((snd s - snd p - UNIT) / stride). split.
    + split; [apply Z.div_pos; lia| exact E4].
    + unfold aadd. destruct s as [sr so], p as [pr po]; cbn in *. subst sr. f_equal.
      pose proof (Z.div_mod (so - po - UNIT) stride ltac:(lia)). lia.
  - intros (i & Hi & ->). unfold aadd; cbn. replace (snd p + (UNIT + stride * i) - snd p - UNIT) with (i * stride) by lia.
    rewrite Z_mod_mult, Z.div_mul by lia. repeat split; auto; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma get_shadow_eq st rid : get_shadow st rid = default shadow0 (s_shadow st !! rid).
Proof. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_ext st st' rid : s_shadow st' = s_shadow st -> get_shadow st' rid = get_shadow st rid.
Proof. intros H. unfold get_shadow. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_upd_shadow rid f st rid' :
  get_shadow (upd_shadow rid f st) rid' = if (rid' =? rid)%N then f (get_shadow st rid) else get_shadow st rid'.
Proof.
  unfold get_shadow, upd_shadow; cbn. destruct (N.eqb_spec rid' rid) as [->|NE];
  [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cell_read_wr8 p v st q :
  cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) =
  if aptr_eqb q p then
    (let r := get_shadow st (fst p) in
     let hl := default [] (r_hav r !! (snd p / 16)) in
     let hp := r_havp r !! (snd p / 4096) in
     if stale_pg hp (Some (s_tick st)) || stale hl (snd p mod 16) (Some (s_tick st)) then Unknown (Z.land v 255) else Known (Z.land v 255))
  else cell_read (get_shadow st (fst q)) (snd q).
Proof.
  unfold wr8. rewrite get_shadow_upd_shadow. destruct (aptr_eqb_spec q p) as [->|NE].
  - rewrite N.eqb_refl. unfold cell_read; cbn. rewrite lookup_insert_eq. reflexivity.
  - destruct (N.eqb_spec (fst q) (fst p)) as [E|NE2]; [|reflexivity].
    unfold cell_read; cbn. rewrite E. rewrite lookup_insert_ne; [reflexivity|].
    intros E2. apply NE. destruct q, p; cbn in *; congruence.
Qed.

(* [comment removed for export] *)
Definition sh_ticks (r : shadow) (t : N) : Prop :=
  (forall u hl ch, r_hav r !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
  /\ (forall pg t', r_havp r !! pg = Some t' -> (t' <= t)%N).

#[using="Type"] Lemma not_stale_cur r t b : sh_ticks r t ->
  forall u pg, stale_pg (r_havp r !! pg) (Some t) || stale (default [] (r_hav r !! u)) b (Some t) = false.
Proof.
  intros [Hh Hp] u pg. apply Bool.orb_false_iff. split.
  - destruct (r_havp r !! pg) as [t'|] eqn:E; cbn; [|reflexivity]. apply N.ltb_ge. eapply Hp; eauto.
  - unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([c h] & Hin & Hb). cbn in Hb.
    apply Bool.andb_true_iff in Hb as [_ Hb]. apply N.ltb_lt in Hb.
    destruct (r_hav r !! u) as [hl|] eqn:E; cbn in Hin; [|contradiction].
    pose proof (Hh u hl (c, h) E Hin). cbn in H. lia.
Qed.

#[using="Type"] Lemma cell_read_wr8_same p v st : sh_ticks (get_shadow st (fst p)) (s_tick st) ->
  cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known (Z.land v 255).
Proof.
  intros HT. rewrite (cell_read_wr8 p v st p), aptr_eqb_refl. cbn zeta. rewrite (not_stale_cur _ _ _ HT). reflexivity.
Qed.
#[using="Type"] Lemma cell_read_wr8_other p v st q : q <> p ->
  cell_read (get_shadow (wr8 p v st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. intros NE. rewrite cell_read_wr8, aptr_eqb_neq by exact NE. reflexivity. Qed.

#[using="Type"] Lemma sh_ticks_wr8 p v st rid : sh_ticks (get_shadow st rid) (s_tick st) -> sh_ticks (get_shadow (wr8 p v st) rid) (s_tick st).
Proof.
  intros H. unfold wr8. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst p)) as [->|NE]; [|exact H].
  destruct H as [Hh Hp]. split; cbn; eauto.
Qed.

End WithCeil.
End MI_Kit.

(* [comment removed for export] *)
Module MI_Geom.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Wf_nat.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
Section GEOM.
Variable X : extras.
Variable st : mstate.
Variable L : mled.
Variable BL : list blk.
Variable LS : lhead -> list aptr.
Hypothesis IM : inv_M X st LS.
Hypothesis IG : inv_G X st LS.
Hypothesis IS : inv_S X st BL.
Local Notation R := (MR st).

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="X LS IM"] Lemma hosts_gbase b m : hosts st b m -> gbase (R m) = b.
Proof.
  intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst.
  unfold gbase, MR. rewrite Hmem. reflexivity.
Qed.

#[using="X LS IM"] Lemma hosts_mem b m : hosts st b m -> m_mem (R m) = Some b.
Proof.
  intros [ai H]. destruct (im_hdr _ _ _ IM _ _ H) as (m' & Hm & Hmem & _). cbn in Hm. inversion Hm; subst. exact Hmem.
Qed.

#[using="X LS IM"] Lemma hosts_inj b1 b2 m : hosts st b1 m -> hosts st b2 m -> b1 = b2.
Proof. intros H1 H2. pose proof (hosts_mem _ _ H1). pose proof (hosts_mem _ _ H2). congruence. Qed.

#[using="Type"] Lemma hosts_fun b m1 m2 : hosts st b m1 -> hosts st b m2 -> m1 = m2.
Proof. intros [a1 H1] [a2 H2]. rewrite H1 in H2. inversion H2. reflexivity. Qed.

#[using="IG"] Lemma hosts_ok b m : hosts st b m -> exists ai, s_groups st !! b = Some (mkGhdr (Some m) ai) /\ group_ok X st LS m b ai.
Proof. intros [ai H]. exists ai. split; [exact H|]. exact (ig_ok _ _ _ IG _ _ _ H). Qed.

#[using="Type"] Lemma live_hosts m : live_group st m -> exists b, hosts st b m.
Proof. intros H. exact H. Qed.

#[using="X LS IM"] Lemma slot_start'_eq m b i : hosts st b m -> slot_start' (R m) i = (fst b, sstart (R m) i).
Proof. intros H. rewrite slot_start'_sstart. rewrite (hosts_gbase _ _ H). reflexivity. Qed.

#[using="X LS IG"] Lemma stride_cases b m : hosts st b m ->
  get_stride (R m) = UNIT * size_class (m_sizeclass (R m)) /\ 0 <= m_sizeclass (R m) < 48
  \/ get_stride (R m) = m_maplen (R m) * 4096 - UNIT /\ m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0.
Proof.
  intros H. destruct (hosts_ok _ _ H) as (ai & Hg & GO). unfold get_stride.
  destruct (Z.eqb_spec (m_last_idx (R m)) 0) as [E|NE]; cbn.
  - destruct (Z.eqb_spec (m_maplen (R m)) 0) as [E2|NE2]; cbn.
    + left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
    + right. auto.
  - left. split; [reflexivity|]. destruct (g_sc _ _ _ _ _ _ GO) as [[? _]|(? & ? & ? & _)]; [assumption| congruence].
Qed.

#[using="X LS IG"] Lemma stride_ge b m : hosts st b m -> UNIT <= get_stride (R m) /\ get_stride (R m) mod UNIT = 0.
Proof.
  intros H. destruct (stride_cases _ _ H) as [[E Hsc]|(E & _ & NZ)]; rewrite E.
  - pose proof (size_class_bound _ Hsc). unfold UNIT. split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT. split; [lia|].
    replace (m_maplen (R m) * 4096 - 16) with ((m_maplen (R m) * 256 - 1) * 16) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="X LS IG"] Lemma sstart_mono b m i j : hosts st b m -> i <= j -> sstart (R m) i <= sstart (R m) j.
Proof. intros H Hij. unfold sstart. destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. Qed.

#[using="Type"] Lemma sstart_succ m i : sstart (R m) (i + 1) = sstart (R m) i + get_stride (R m).
Proof. unfold sstart. lia. Qed.

#[using="X LS IG"] Lemma sstart_lt b m i j : hosts st b m -> i < j -> sstart (R m) i + get_stride (R m) <= sstart (R m) j.
Proof. intros H Hij. rewrite <- sstart_succ. apply (sstart_mono _ _ _ _ H). lia. Qed.

#[using="X LS IM"] Lemma sstart0 b m : hosts st b m -> sstart (R m) 0 = snd b + UNIT.
Proof. intros H. unfold sstart. rewrite (hosts_gbase _ _ H). lia. Qed.

#[using="Type"] Lemma gend_eq m : gend (R m) = sstart (R m) (m_last_idx (R m) + 1).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition child (c p : aptr) (i : Z) : Prop :=
  exists b, hosts st b c /\ m_maplen (R c) = 0 /\ s_slots st !! b = Some (p, i).

Inductive anc : aptr -> aptr -> Z -> aptr -> Prop :=
| anc_child c p i : child c p i -> anc c p i c
| anc_step m c j c' p i : anc m c j c' -> child c p i -> anc m p i c.

#[using="X BL LS IM IG IS"] Lemma child_facts c p i : child c p i ->
  exists bc bp, hosts st bc c /\ hosts st bp p /\ fst bc = fst bp /\ 0 <= i <= m_last_idx (R p)
    /\ bc = (fst bp, sstart (R p) i)
    /\ sstart (R p) i = snd bc /\ gend (R c) <= sstart (R p) (i + 1)
    /\ m_sizeclass (R c) < m_sizeclass (R p) < 48.
Proof.
  intros (bc & Hc & Hml & Hsl).
  destruct (is_valid _ _ _ IS _ _ _ Hsl) as (Hlive & Hi & Hs).
  destruct Hlive as [bp Hp].
  destruct (hosts_ok _ _ Hc) as (ai & Hg & GO).
  destruct (g_nest _ _ _ _ _ _ GO Hml) as (p' & i' & Hsl' & Hfst & Hend & Hsc & Hstr).
  rewrite Hsl in Hsl'. inversion Hsl'; subst p' i'.
  exists bc, bp. rewrite (slot_start'_eq _ _ _ Hp) in Hs.
  repeat split; auto; try lia.
  - rewrite Hs. reflexivity.
  - rewrite Hs. reflexivity.
  - rewrite sstart_succ. exact Hend.
Qed.

#[using="X BL LS IM IG IS"] Lemma anc_facts m p i c : anc m p i c ->
  exists bm bp, hosts st bm m /\ hosts st bp p /\ fst bm = fst bp /\ 0 <= i <= m_last_idx (R p)
    /\ child c p i /\ (m = c \/ exists j c', anc m c j c')
    /\ sstart (R p) i <= snd bm /\ gend (R m) <= sstart (R p) (i + 1)
    /\ m_sizeclass (R m) < m_sizeclass (R p) < 48.
Proof.
  induction 1 as [c p i Hch|m c j c' p i Ha IH Hch].
  - destruct (child_facts _ _ _ Hch) as (bc & bp & Hc & Hp & Hfst & Hi & Hbc & Hs & Hend & Hsc).
    exists bc, bp. repeat split; auto; lia.
  - destruct IH as (bm & bc & Hm & Hc & Hfst & Hj & Hch' & _ & Hs & Hend & Hsc).
    destruct (child_facts _ _ _ Hch) as (bc' & bp & Hc' & Hp & Hfst' & Hi & Hbc & Hs' & Hend' & Hsc').
    pose proof (hosts_inj _ _ _ Hc Hc') as E.
    pose proof (sstart0 _ _ Hc). pose proof (sstart_mono _ _ 0 j Hc ltac:(lia)).
    pose proof (sstart_mono _ _ (j + 1) (m_last_idx (R c) + 1) Hc ltac:(lia)). rewrite <- gend_eq in *.
    subst bc bc'. cbn [fst snd] in *.
    exists bm, bp. split; [exact Hm|]. split; [exact Hp|]. split; [congruence|]. split; [exact Hi|].
    split; [exact Hch|]. split; [right; eauto|].
    unfold UNIT in *. repeat split; lia.
Qed.

#[using="X BL LS IM IG IS"] Lemma anc_irrefl m i c : anc m m i c -> False.
Proof. intros H. destruct (anc_facts _ _ _ _ H) as (? & ? & _ & _ & _ & _ & _ & _ & _ & _ & Hsc). lia. Qed.

#[using="Type"] Lemma anc_trans m q j c' p i c : anc m q j c' -> anc q p i c -> anc m p i c.
Proof.
  intros H1 H2. revert m j c' H1. induction H2 as [q p i Hch|q c j2 c2 p i Ha IH Hch]; intros m j' c' H1.
  - eapply anc_step; eauto.
  - eapply anc_step; [| exact Hch]. eapply IH. exact H1.
Qed.

(* [comment removed for export] *)
#[using="X BL LS IM IG IS"] Lemma child_unique c1 c2 p i : child c1 p i -> child c2 p i -> c1 = c2.
Proof.
  intros H1 H2.
  destruct (child_facts _ _ _ H1) as (b1 & bp & Hc1 & Hp & _ & _ & Hb1 & _).
  destruct (child_facts _ _ _ H2) as (b2 & bp' & Hc2 & Hp' & _ & _ & Hb2 & _).
  pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. subst b1 b2. exact (hosts_fun _ _ _ Hc1 Hc2).
Qed.

(* [comment removed for export] *)
#[using="X BL LS IM IG IS"] Lemma top_chain m bm : hosts st bm m -> m_maplen (R m) = 0 ->
  exists t i c bt, anc m t i c /\ hosts st bt t /\ m_maplen (R t) <> 0 /\ fst bt = fst bm.
Proof.
  intros Hm Hml.
  remember (Z.to_nat (48 - m_sizeclass (R m))) as n eqn:En.
  revert m bm Hm Hml En. induction n as [n IH] using lt_wf_ind; intros m bm Hm Hml En.
  assert (Hch : exists p i, child m p i).
  { destruct (hosts_ok _ _ Hm) as (ai & Hg & GO). destruct (g_nest _ _ _ _ _ _ GO Hml) as (p & i & Hsl & _). exists p, i. exists bm. auto. }
  destruct Hch as (p & i & Hch).
  destruct (child_facts _ _ _ Hch) as (bc & bp & Hc & Hp & Hfst & Hi & Hbc & _ & _ & Hsc).
  pose proof (hosts_inj _ _ _ Hm Hc). subst bc bm. cbn [fst snd] in *.
  destruct (Z.eq_dec (m_maplen (R p)) 0) as [Hml'|Hml'].
  - destruct (IH (Z.to_nat (48 - m_sizeclass (R p))) ltac:(lia) p bp Hp Hml' eq_refl) as (t & j & c & bt & Ha & Ht & Htop & Hfst').
    exists t, j, c, bt. split; [| repeat split; auto; congruence]. eapply anc_trans; [apply anc_child; exact Hch| exact Ha].
  - exists p, i, m, bp. repeat split; auto. apply anc_child. exact Hch.
Qed.

(* [comment removed for export] *)
#[using="X LS IG"] Lemma top_at0 t bt : hosts st bt t -> m_maplen (R t) <> 0 -> snd bt = 0.
Proof. intros Ht Hml. destruct (hosts_ok _ _ Ht) as (ai & _ & GO). destruct (g_top _ _ _ _ _ _ GO Hml) as [H0 _]. exact H0. Qed.

#[using="X LS IG"] Lemma top_unique t1 t2 b1 b2 : hosts st b1 t1 -> hosts st b2 t2 -> m_maplen (R t1) <> 0 -> m_maplen (R t2) <> 0 ->
  fst b1 = fst b2 -> t1 = t2.
Proof.
  intros H1 H2 M1 M2 Hf. pose proof (top_at0 _ _ H1 M1). pose proof (top_at0 _ _ H2 M2).
  assert (b1 = b2) by (destruct b1, b2; cbn in *; congruence). subst b2. exact (hosts_fun _ _ _ H1 H2).
Qed.

(* [comment removed for export] *)
#[using="X BL LS IM IG IS"] Lemma anc_not_top m p i c bm : anc m p i c -> hosts st bm m -> 0 < snd bm.
Proof.
  intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & Hi & _ & _ & Hs & _).
  pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
  destruct (hosts_ok _ _ Hp) as (ai & _ & GO). pose proof (g_align _ _ _ _ _ _ GO) as [H0 _].
  pose proof (sstart0 _ _ Hp). pose proof (sstart_mono _ _ 0 i Hp ltac:(lia)). unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
#[using="X BL LS IM IG IS"] Lemma dichotomy m1 m2 b1 b2 : hosts st b1 m1 -> hosts st b2 m2 -> fst b1 = fst b2 -> m1 <> m2 ->
  (exists i c, anc m1 m2 i c) \/ (exists i c, anc m2 m1 i c)
  \/ (exists p i1 i2 c1 c2, i1 <> i2 /\ anc m1 p i1 c1 /\ anc m2 p i2 c2).
Proof.
  remember (Z.to_nat (48 - m_sizeclass (R m1)) + Z.to_nat (48 - m_sizeclass (R m2)))%nat as n eqn:En.
  revert m1 m2 b1 b2 En. induction n as [n IH] using lt_wf_ind; intros m1 m2 b1 b2 En H1 H2 Hf NE.
  destruct (Z.eq_dec (m_maplen (R m1)) 0) as [M1|M1]; destruct (Z.eq_dec (m_maplen (R m2)) 0) as [M2|M2].
  - (* [comment removed for export] *)
    destruct (hosts_ok _ _ H1) as (a1 & _ & G1). destruct (g_nest _ _ _ _ _ _ G1 M1) as (p1 & i1 & S1 & _).
    destruct (hosts_ok _ _ H2) as (a2 & _ & G2). destruct (g_nest _ _ _ _ _ _ G2 M2) as (p2 & i2 & S2 & _).
    assert (C1 : child m1 p1 i1) by (exists b1; auto). assert (C2 : child m2 p2 i2) by (exists b2; auto).
    destruct (child_facts _ _ _ C1) as (bc1 & bp1 & Hc1 & Hp1 & Hf1 & Hi1 & Hb1 & _ & _ & Hsc1).
    destruct (child_facts _ _ _ C2) as (bc2 & bp2 & Hc2 & Hp2 & Hf2 & Hi2 & Hb2 & _ & _ & Hsc2).
    pose proof (hosts_inj _ _ _ H1 Hc1); subst bc1. pose proof (hosts_inj _ _ _ H2 Hc2); subst bc2.
    destruct (aptr_eq_dec p1 m2) as [->|N1]; [left; exists i1, m1; apply anc_child; exact C1|].
    destruct (aptr_eq_dec p2 m1) as [->|N2]; [right; left; exists i2, m2; apply anc_child; exact C2|].
    destruct (aptr_eq_dec p1 p2) as [->|N3].
    + pose proof (hosts_inj _ _ _ Hp1 Hp2); subst bp2.
      destruct (Z.eq_dec i1 i2) as [->|Ni].
      * exfalso. apply NE. exact (child_unique _ _ _ _ C1 C2).
      * right; right. exists p2, i1, i2, m1, m2. split; [exact Ni|]. split; apply anc_child; assumption.
    + assert (Hf' : fst bp1 = fst bp2) by congruence.
      destruct (IH (Z.to_nat (48 - m_sizeclass (R p1)) + Z.to_nat (48 - m_sizeclass (R p2)))%nat ltac:(lia) p1 p2 bp1 bp2 eq_refl Hp1 Hp2 Hf' N3)
        as [(j & c & Ha)|[(j & c & Ha)|(p & j1 & j2 & c1 & c2 & Nj & Ha1 & Ha2)]].
      * (* [comment removed for export] *)
        destruct (Z.eq_dec j i2) as [->|Nj].
        -- destruct (anc_facts _ _ _ _ Ha) as (_ & _ & _ & _ & _ & _ & Cc & Hor & _).
           pose proof (child_unique _ _ _ _ Cc C2); subst c.
           destruct Hor as [->|(j' & c' & Ha')]; [contradiction|].
           left. exists j', c'. eapply anc_trans; [apply anc_child; exact C1| exact Ha'].
        -- right; right. exists p2, j, i2, c, m2. split; [exact Nj|]. split; [| apply anc_child; exact C2].
           eapply anc_trans; [apply anc_child; exact C1| exact Ha].
      * destruct (Z.eq_dec j i1) as [->|Nj].
        -- destruct (anc_facts _ _ _ _ Ha) as (_ & _ & _ & _ & _ & _ & Cc & Hor & _).
           pose proof (child_unique _ _ _ _ Cc C1); subst c.
           destruct Hor as [->|(j' & c' & Ha')]; [congruence|].
           right; left. exists j', c'. eapply anc_trans; [apply anc_child; exact C2| exact Ha'].
        -- right; right. exists p1, i1, j, m1, c. split; [congruence|]. split; [apply anc_child; exact C1|].
           eapply anc_trans; [apply anc_child; exact C2| exact Ha].
      * right; right. exists p, j1, j2, c1, c2. split; [exact Nj|]. split.
        -- eapply anc_trans; [apply anc_child; exact C1| exact Ha1].
        -- eapply anc_trans; [apply anc_child; exact C2| exact Ha2].
  - (* [comment removed for export] *)
    destruct (top_chain _ _ H1 M1) as (t & i & c & bt & Ha & Ht & Mt & Hft).
    assert (t = m2) by (eapply top_unique; eauto; congruence). subst t. left. exists i, c. exact Ha.
  - destruct (top_chain _ _ H2 M2) as (t & i & c & bt & Ha & Ht & Mt & Hft).
    assert (t = m1) by (eapply top_unique; eauto; congruence). subst t. right; left. exists i, c. exact Ha.
  - exfalso. apply NE. eapply top_unique; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="X LS IG"] Lemma last_idx_nonneg b m : hosts st b m -> 0 <= m_last_idx (R m).
Proof. intros H. destruct (hosts_ok _ _ H) as (ai & _ & GO). pose proof (g_li _ _ _ _ _ _ GO). lia. Qed.

(* [comment removed for export] *)
#[using="X BL LS IM IG IS"] Lemma anc_box m p j c bm : anc m p j c -> hosts st bm m ->
  sstart (R p) j <= snd bm /\ gend (R m) <= sstart (R p) (j + 1)
  /\ sstart (R p) j + 16 <= sstart (R m) 0.
Proof.
  intros Ha Hm. destruct (anc_facts _ _ _ _ Ha) as (bm' & bp & Hm' & Hp & _ & _ & _ & _ & Hs & He & _).
  pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (sstart0 _ _ Hm). unfold UNIT in *. lia.
Qed.

(* [comment removed for export] *)
#[using="X BL LS IM IG IS"] Lemma anc_hostslot m p j c : anc m p j c -> exists bp, hosts st bp p /\ s_groups st !! (fst bp, sstart (R p) j) <> None.
Proof.
  intros Ha. destruct (anc_facts _ _ _ _ Ha) as (bm & bp & Hm & Hp & _ & _ & Hch & _).
  destruct (child_facts _ _ _ Hch) as (bc & bp' & Hc & Hp' & _ & _ & Hbc & _).
  pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'. exists bp. split; [exact Hp|].
  rewrite <- Hbc. destruct Hc as [ai Hc]. rewrite Hc. discriminate.
Qed.

#[using="X LS IG"] Lemma sst_lt b m i j : hosts st b m -> i < j -> sstart (R m) i + 16 <= sstart (R m) j.
Proof. intros H Hij. pose proof (sstart_lt _ _ i j H Hij). destruct (stride_ge _ _ H) as [Hs _]. unfold UNIT in Hs. lia. Qed.

#[using="X LS IM IG"] Lemma gend_ge b m : hosts st b m -> snd b + 32 <= gend (R m).
Proof.
  intros H. rewrite gend_eq. pose proof (sstart0 _ _ H). pose proof (sst_lt _ _ 0 (m_last_idx (R m) + 1) H ltac:(pose proof (last_idx_nonneg _ _ H); lia)).
  unfold UNIT in *. lia.
Qed.

Section SEP.
  Variables (m : aptr) (bm : aptr) (i : Z).
  Hypothesis Hm : hosts st bm m.
  Hypothesis Hi : 0 <= i <= m_last_idx (R m).
  Hypothesis NH : s_groups st !! (fst bm, sstart (R m) i) = None.

  (* [comment removed for export] *)
  #[using="X BL LS IM IG IS bm Hm NH"] Lemma sep_no_anc m2 c : anc m2 m i c -> False.
  Proof. intros Ha. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ Hm Hp); subst bp. exact (Hne NH). Qed.

  (* [comment removed for export] *)
  Let S0m := sstart0 _ _ Hm.
  Let Lm := sst_lt _ _ i (i + 1) Hm ltac:(lia).

  (* [comment removed for export] *)
  #[using="X BL LS IM IG IS Hm Hi NH S0m Lm"] Lemma sep_hdr0 m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) + 1 ->
    (m2 <> m \/ i2 <> i) ->
    sstart (R m2) i2 <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sstart_mono _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ i2 j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="X BL LS IM IG IS Hm Hi NH S0m Lm"] Lemma sep_h3 m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) ->
    (m2 <> m \/ i2 <> i) ->
    sstart (R m2) i2 + 16 <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sst_lt _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sst_lt _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ i2 j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sst_lt _ _ i2 (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="X BL LS IM IG IS Hm Hi NH S0m Lm"] Lemma sep_ghdr m2 b2 : hosts st b2 m2 -> fst b2 = fst bm ->
    snd b2 + 16 <= sstart (R m) i \/ sstart (R m) (i + 1) <= snd b2 + 4.
  Proof.
    intros H2 Hf. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - left. pose proof (hosts_inj _ _ _ Hm H2); subst b2. pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2. pose proof (gend_ge _ _ H2) as G2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + left. destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3).
        pose proof (sstart_mono _ _ 0 j H2 ltac:(lia)). pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="X BL LS IM IG IS Hm Hi NH S0m Lm"] Lemma sep_ext m2 b2 i2 : hosts st b2 m2 -> fst b2 = fst bm -> 0 <= i2 <= m_last_idx (R m2) ->
    (m2 <> m \/ i2 <> i) -> s_groups st !! (fst b2, sstart (R m2) i2) = None ->
    sstart (R m2) (i2 + 1) <= sstart (R m) i \/ sstart (R m) (i + 1) <= sstart (R m2) i2.
  Proof.
    intros H2 Hf Hi2 NE NH2. pose proof S0m as S0. pose proof Lm as L1. unfold UNIT in S0.
    destruct (aptr_eq_dec m2 m) as [->|NEm].
    - destruct NE as [|NEi]; [congruence|].
      destruct (Z.lt_ge_cases i2 i).
      + left. apply (sstart_mono _ _ _ _ Hm). lia.
      + right. apply (sstart_mono _ _ _ _ Hm). lia.
    - pose proof (sstart0 _ _ H2) as S2. unfold UNIT in S2.
      destruct (dichotomy _ _ _ _ H2 Hm Hf NEm) as [(j & c & Ha)|[(j & c & Ha)|(p & j2 & j1 & c2 & c1 & Nj & Ha2 & Ha1)]].
      + destruct (Z.eq_dec j i) as [->|Nj]; [exfalso; exact (sep_no_anc _ _ Ha)|].
        destruct (anc_box _ _ _ _ _ Ha H2) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ (i2 + 1) (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j i).
        * left. pose proof (sstart_mono _ _ (j + 1) i Hm ltac:(lia)). lia.
        * right. pose proof (sstart_mono _ _ (i + 1) j Hm ltac:(lia)). lia.
      + destruct (Z.eq_dec j i2) as [->|Nj].
        { exfalso. destruct (anc_hostslot _ _ _ _ Ha) as (bp & Hp & Hne). pose proof (hosts_inj _ _ _ H2 Hp); subst bp. exact (Hne NH2). }
        destruct (anc_facts _ _ _ _ Ha) as (bm' & b2' & Hm' & H2' & _ & Hj & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'. pose proof (hosts_inj _ _ _ H2 H2'); subst b2'.
        destruct (anc_box _ _ _ _ _ Ha Hm) as (A1 & A2 & A3). rewrite gend_eq in A2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        destruct (Z.lt_ge_cases j i2).
        * right. pose proof (sstart_mono _ _ (j + 1) i2 H2 ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (i2 + 1) j H2 ltac:(lia)). lia.
      + destruct (anc_facts _ _ _ _ Ha1) as (bm' & bp & Hm' & Hp & _ & Hj1 & _).
        pose proof (hosts_inj _ _ _ Hm Hm'); subst bm'.
        destruct (anc_facts _ _ _ _ Ha2) as (b2' & bp' & H2' & Hp' & _ & Hj2 & _).
        pose proof (hosts_inj _ _ _ H2 H2'); subst b2'. pose proof (hosts_inj _ _ _ Hp Hp'); subst bp'.
        destruct (anc_box _ _ _ _ _ Ha1 Hm) as (A1 & A2 & A3).
        destruct (anc_box _ _ _ _ _ Ha2 H2) as (B1 & B2 & B3). rewrite gend_eq in A2, B2.
        pose proof (sstart_mono _ _ 0 i Hm ltac:(lia)). pose proof (sstart_mono _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)).
        pose proof (sstart_mono _ _ 0 i2 H2 ltac:(lia)). pose proof (sstart_mono _ _ (i2 + 1) (m_last_idx (R m2) + 1) H2 ltac:(lia)).
        destruct (Z.lt_ge_cases j1 j2).
        * right. pose proof (sstart_mono _ _ (j1 + 1) j2 Hp ltac:(lia)). lia.
        * left. pose proof (sstart_mono _ _ (j2 + 1) j1 Hp ltac:(lia)). lia.
  Qed.
End SEP.

End GEOM.

End WithCeil.
End MI_Geom.

(* [comment removed for export] *)
Module MI_Addr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
Section ADDR.
Variable X : extras.
Variable st : mstate.
Variable L : mled.
Variable BL : list blk.
Variable LS : lhead -> list aptr.
Hypothesis INV : INVL X st L BL LS.
Local Notation R := (MR st).

Let IR : inv_R X st L := proj1 INV.
Let IM : inv_M X st LS := proj1 (proj2 (proj2 INV)).
Let IG : inv_G X st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S X st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
#[using="CEc X L BL LS INV IM IG IS"] Lemma group_in_region m bm :
  hosts st bm m -> exists r, s_regions st !! (fst bm) = Some r /\ r_kind r = RKGroup /\ 0 <= snd bm /\ gend (R m) <= round_up_pg (r_len r).
Proof.
  intros Hm. destruct (hosts_ok X st LS IG _ _ Hm) as (ai & Hg & GO).
  destruct (ig_region _ _ _ IG _ _ Hg) as (r & Hr & Hk). exists r. split; [exact Hr|]. split; [exact Hk|].
  split; [exact (proj1 (g_align _ _ _ _ _ _ GO))|].
  destruct (Z.eq_dec (m_maplen (R m)) 0) as [ML|ML].
  - destruct (top_chain X st BL LS IM IG IS m bm Hm ML) as (t & i & c & bt & Ha & Ht & Htop & Hfst).
    destruct (anc_box X st BL LS IM IG IS _ _ _ _ _ Ha Hm) as (_ & He & _).
    destruct (anc_facts X st BL LS IM IG IS _ _ _ _ Ha) as (bm' & bt' & _ & Ht' & _ & Hi & _).
    pose proof (hosts_inj X st LS IM _ _ _ Ht Ht'); subst bt'.
    destruct (hosts_ok X st LS IG _ _ Ht) as (ait & Hgt & GOt). destruct (g_top _ _ _ _ _ _ GOt Htop) as (_ & rt & Hrt & _ & Hml & Hend).
    rewrite Hfst in Hrt. rewrite Hr in Hrt. injection Hrt as <-.
    pose proof (sstart_mono X st LS IG _ _ (i + 1) (m_last_idx (R t) + 1) Ht ltac:(lia)) as Hmono.
    rewrite <- gend_eq in Hmono. lia.
  - destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r' & Hr' & _ & Hml & Hend). rewrite Hr in Hr'. injection Hr' as <-. lia.
Qed.

(* [comment removed for export] *)
#[using="X L LS INV IR IM IG IS"] Theorem blk_addr_range k :
  In k BL -> 0 < conc st (bptr_of k) /\ conc st (bptr_of k) + bsize k <= alloc_ceiling /\ 0 <= bsize k.
Proof.
  intros Hk. destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & Hoff & Hsz & Hfit).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bm Hm] & Hi & Es).
  rewrite (slot_start'_eq X st LS IM _ _ _ Hm) in Es.
  destruct (group_in_region m bm Hm) as (r & Hr & _ & Hb0 & Hend).
  pose proof (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & L0 & _ & CE & _).
  pose proof (sstart0 X st LS IM _ _ Hm) as S0.
  pose proof (sstart_mono X st LS IG _ _ 0 i Hm ltac:(lia)) as M0.
  pose proof (sstart_mono X st LS IG _ _ (i + 1) (m_last_idx (R m) + 1) Hm ltac:(lia)) as M1. rewrite <- gend_eq in M1.
  rewrite sstart_succ in M1.
  unfold conc, bptr_of, aadd, get_region. rewrite Es. cbn [fst snd]. rewrite Hr.
  unfold UNIT, IB in *. lia.
Qed.

End ADDR.

End WithCeil.
End MI_Addr.

(* [comment removed for export] *)
Module MI_Shadow.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition hl_ticks (hl : list (Z * N)) (t : N) : Prop := forall ch, In ch hl -> (snd ch <= t)%N.

#[using="Type"] Lemma stale_hav_add_some cov t hl b tk :
  hl_ticks hl t ->
  stale (hav_add cov t hl) b (Some tk) = ((b <? cov) && (tk <? t)%N) || stale hl b (Some tk).
Proof.
  intros Ht. unfold hav_add, stale. cbn [existsb fst snd].
  destruct ((b <? cov) && (tk <? t)%N) eqn:E; cbn [orb]; [reflexivity|].
  induction hl as [|[c h] hl IH]; [reflexivity|].
  assert (Hh : (h <= t)%N) by (apply (Ht (c, h)); left; reflexivity).
  assert (IH' : existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) (filter (fun ch : Z * N => cov <? fst ch) hl)
                = existsb (fun ch : Z * N => (b <? fst ch) && (tk <? snd ch)%N) hl).
  { apply IH. intros ch Hin. apply Ht. right. exact Hin. }
  rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd].
  - rewrite IH'. reflexivity.
  - rewrite IH'. destruct ((b <? c) && (tk <? h)%N) eqn:E2; cbn; [|reflexivity].
    exfalso. apply Bool.andb_true_iff in E2 as [E2 E3]. apply Z.ltb_lt in E2. apply N.ltb_lt in E3.
    assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
    apply Bool.andb_false_iff in E as [E|E]; [apply Z.ltb_ge in E; lia| apply N.ltb_ge in E; lia].
Qed.

#[using="Type"] Lemma stale_hav_add_none cov t hl b :
  stale (hav_add cov t hl) b None = (b <? cov) || stale hl b None.
Proof.
  unfold hav_add, stale. cbn [existsb fst snd]. rewrite Bool.andb_true_r.
  destruct (b <? cov) eqn:E; cbn [orb]; [reflexivity|].
  induction hl as [|[c h] hl IH]; [reflexivity|].
  rewrite filter_cons. cbn [existsb fst snd]. destruct (decide _) as [D|D]; cbn [existsb fst snd]; rewrite ?Bool.andb_true_r.
  - rewrite IH. reflexivity.
  - rewrite IH. destruct (Z.ltb_spec b c); cbn; [|reflexivity]. exfalso.
    assert (Hc : ~ cov < c) by (intros X; apply D; apply Is_true_true_2; apply Z.ltb_lt; exact X).
    apply Z.ltb_ge in E. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma havoc_units_lookup x y t h u :
  let u0 := x / 16 in let u1 := (y - 1) / 16 in
  let lastcov := (if y mod 16 =? 0 then 16 else y mod 16) in
  (havoc_units x y t h) !! u =
    if (u0 <=? u) && (u <=? u1) then Some (hav_add (if u =? u1 then lastcov else 16) t (default [] (h !! u))) else h !! u.
Proof.
  cbn zeta. unfold havoc_units.
  set (u0 := x / 16). set (u1 := (y - 1) / 16). set (lastcov := if y mod 16 =? 0 then 16 else y mod 16).
  set (F := fun acc : Z * gmap Z (list (Z * N)) => let (u2, h0) := acc in (u2 + 1, <[u2 := hav_add (if u2 =? u1 then lastcov else 16) t (default [] (h0 !! u2))]> h0)).
  destruct (Z.lt_ge_cases (u1 - u0 + 1) 0) as [Hneg|Hnn].
  - (* [comment removed for export] *)
    destruct (u1 - u0 + 1) eqn:E; try lia. cbn.
    destruct (Z.leb_spec u0 u), (Z.leb_spec u u1); cbn; try reflexivity. lia.
  - assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (u0, h) in fst r = u0 + n /\
              forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v).
    { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = u0 + n /\ forall v, snd r !! v = if (u0 <=? v) && (v <? u0 + n) then Some (hav_add (if v =? u1 then lastcov else 16) t (default [] (h !! v))) else h !! v)); [| | exact Hn].
      - cbn. split; [lia|]. intros v. destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + 0)); cbn; try reflexivity. lia.
      - intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
        destruct (Z.eq_dec v (u0 + k)) as [->|NE].
        + rewrite lookup_insert_eq. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + (k + 1))); cbn; try lia.
          f_equal. f_equal. rewrite IH. destruct (Z.leb_spec u0 (u0 + k)), (Z.ltb_spec (u0 + k) (u0 + k)); cbn; try lia. reflexivity.
        + rewrite lookup_insert_ne by congruence. rewrite IH.
          destruct (Z.leb_spec u0 v), (Z.ltb_spec v (u0 + k)), (Z.ltb_spec v (u0 + (k + 1))); cbn; try reflexivity; lia. }
    destruct (GEN (u1 - u0 + 1) Hnn) as [_ G]. rewrite G.
    destruct (Z.leb_spec u0 u), (Z.ltb_spec u (u0 + (u1 - u0 + 1))), (Z.leb_spec u u1); cbn; try reflexivity; lia.
Qed.

#[using="Type"] Lemma havoc_pages_lookup p0 p1 t h pg :
  (havoc_pages p0 p1 t h) !! pg = if (p0 <=? pg) && (pg <? p1) then Some t else h !! pg.
Proof.
  unfold havoc_pages.
  set (F := fun acc : Z * gmap Z N => let (pg0, h0) := acc in (pg0 + 1, <[pg0 := t]> h0)).
  destruct (Z.lt_ge_cases (p1 - p0) 0) as [Hneg|Hnn].
  - destruct (p1 - p0) eqn:E; try lia. cbn. destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg p1); cbn; try reflexivity. lia.
  - assert (GEN : forall n, 0 <= n -> let r := Z.iter n F (p0, h) in fst r = p0 + n /\
              forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v).
    { intros n Hn. apply (Z_iter_ind F (fun n r => fst r = p0 + n /\ forall v, snd r !! v = if (p0 <=? v) && (v <? p0 + n) then Some t else h !! v)); [| | exact Hn].
      - cbn. split; [lia|]. intros v. destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + 0)); cbn; try reflexivity. lia.
      - intros k [i tb] Hk [Hi IH]. cbn in Hi. subst i. unfold F. cbn [fst snd]. split; [lia|]. intros v.
        destruct (Z.eq_dec v (p0 + k)) as [->|NE].
        + rewrite lookup_insert_eq. destruct (Z.leb_spec p0 (p0 + k)), (Z.ltb_spec (p0 + k) (p0 + (k + 1))); cbn; try lia. reflexivity.
        + rewrite lookup_insert_ne by congruence. rewrite IH.
          destruct (Z.leb_spec p0 v), (Z.ltb_spec v (p0 + k)), (Z.ltb_spec v (p0 + (k + 1))); cbn; try reflexivity; lia. }
    destruct (GEN (p1 - p0) Hnn) as [_ G]. rewrite G.
    destruct (Z.leb_spec p0 pg), (Z.ltb_spec pg (p0 + (p1 - p0))), (Z.ltb_spec pg p1); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma div16_mono a b : a <= b -> a / 16 <= b / 16.
Proof. intros. apply Z.div_le_mono; lia. Qed.

#[using="Type"] Lemma havoc_units_in x y t h o tko :
  x mod 16 = 0 -> x <= o < y ->
  match tko with Some tk => (tk < t)%N | None => True end ->
  stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = true.
Proof.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  assert (U0 : x / 16 <= o / 16) by (apply div16_mono; lia).
  assert (U1 : o / 16 <= (y - 1) / 16) by (apply div16_mono; lia).
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); try lia. cbn [andb default].
  cbn [default id]. unfold hav_add, stale. cbn [existsb fst snd].
  match goal with |- (?a && ?b) || _ = true => enough (E : a && b = true) by (rewrite E; reflexivity) end.
  apply Bool.andb_true_iff. split.
  - apply Z.ltb_lt. destruct (Z.eqb_spec (o / 16) ((y - 1) / 16)) as [E|NE].
    + destruct (Z.eqb_spec (y mod 16) 0) as [Ey|Ny].
      * pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
      * (* [comment removed for export] *)
        pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)).
        pose proof (Z.div_mod y 16 ltac:(lia)).
        pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
        assert (y / 16 = (y - 1) / 16 \/ y / 16 = (y - 1) / 16 + 1) by (pose proof (div16_mono (y - 1) y ltac:(lia)); pose proof (div16_mono y (y - 1 + 16) ltac:(lia)); rewrite <- Z.div_add in * by lia; nia).
        lia.
    + pose proof (Z.mod_pos_bound o 16 ltac:(lia)). lia.
  - destruct tko as [tk|]; [apply N.ltb_lt; exact Htk| reflexivity].
Qed.

#[using="Type"] Lemma havoc_units_out x y t h o tko :
  x mod 16 = 0 -> ~ (x <= o < y) ->
  match tko with Some tk => hl_ticks (default [] (h !! (o / 16))) t | None => True end ->
  stale (default [] (havoc_units x y t h !! (o / 16))) (o mod 16) tko = stale (default [] (h !! (o / 16))) (o mod 16) tko.
Proof.
  intros Hx Ho Htk. rewrite havoc_units_lookup.
  destruct (Z.leb_spec (x / 16) (o / 16)), (Z.leb_spec (o / 16) ((y - 1) / 16)); cbn [andb]; try reflexivity.
  cbn [default id].
  (* [comment removed for export] *)
  assert (Hoy : y <= o).
  { destruct (Z.lt_ge_cases o x); [|lia]. exfalso.
    pose proof (Z.div_mod x 16 ltac:(lia)). pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.mod_pos_bound o 16 ltac:(lia)). nia. }
  assert (E : o / 16 = (y - 1) / 16) by (pose proof (div16_mono (y - 1) o ltac:(lia)); lia).
  rewrite E, Z.eqb_refl.
  pose proof (Z.div_mod o 16 ltac:(lia)). pose proof (Z.div_mod (y - 1) 16 ltac:(lia)). pose proof (Z.div_mod y 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound o 16 ltac:(lia)). pose proof (Z.mod_pos_bound (y - 1) 16 ltac:(lia)). pose proof (Z.mod_pos_bound y 16 ltac:(lia)).
  assert (Ny : y mod 16 <> 0 /\ y mod 16 <= o mod 16) by nia.
  destruct (Z.eqb_spec (y mod 16) 0) as [|_]; [lia|].
  destruct tko as [tk|].
  - rewrite stale_hav_add_some by (rewrite <- E; exact Htk). destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
  - rewrite stale_hav_add_none. destruct (Z.ltb_spec (o mod 16) (y mod 16)); [lia|]. reflexivity.
Qed.

#[using="Type"] Lemma hav_add_ticks cov t hl : hl_ticks hl t -> hl_ticks (hav_add cov t hl) t.
Proof.
  intros H ch Hin. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
  apply H. apply list_elem_of_In. apply list_elem_of_In in Hin. apply list_elem_of_filter in Hin. tauto.
Qed.

#[using="Type"] Lemma havoc_units_ticks x y t h :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) ->
  forall u hl, havoc_units x y t h !! u = Some hl -> hl_ticks hl t.
Proof.
  intros Hh u hl. rewrite havoc_units_lookup. destruct (_ && _).
  - intros E. inversion E. subst. apply hav_add_ticks. destruct (h !! u) as [hl0|] eqn:E0; cbn; [eapply Hh; exact E0| intros ? []].
  - apply Hh.
Qed.

#[using="Type"] Lemma havoc_units_default_ticks x y t h o :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (havoc_units x y t h !! o)) t.
Proof.
  intros Hh. destruct (havoc_units x y t h !! o) as [hl|] eqn:E; cbn; [eapply havoc_units_ticks; eauto| intros ? []].
Qed.

#[using="Type"] Lemma default_ticks (h : gmap Z (list (Z * N))) t o :
  (forall u hl, h !! u = Some hl -> hl_ticks hl t) -> hl_ticks (default [] (h !! o)) t.
Proof. intros Hh. destruct (h !! o) as [hl|] eqn:E; cbn; [eapply Hh; eauto| intros ? []]. Qed.

Section HAVOC.
Variables (p : aptr) (n : Z) (st : mstate).
Hypothesis Al : snd p mod 16 = 0.
Hypothesis Hn : 0 < n.
Let sh := get_shadow st (fst p).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).
Let a := snd p.
Let b := snd p + n.
Let t := s_tick st.
Let fp := (a + 4095) / 4096.
Let lp := b / 4096.

#[using="Hn"] Lemma havoc_shadow :
  get_shadow (havoc p n st) (fst p) =
    mkShadow (r_cells sh)
      (if fp <? lp then
         (if lp * 4096 <? b then havoc_units (lp * 4096) b t (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh)
          else (if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav sh) else r_hav sh))
       else havoc_units a b t (r_hav sh))
      (if fp <? lp then havoc_pages fp lp t (r_havp sh) else r_havp sh).
Proof.
  unfold havoc. destruct (Z.leb_spec n 0); [lia|]. rewrite get_shadow_upd_shadow, N.eqb_refl.
  subst sh a b t fp lp. destruct (_ <? _); [|reflexivity]. destruct (_ <? _); destruct (_ <? _); reflexivity.
Qed.

#[using="Type"] Lemma havoc_other_region rid : rid <> fst p -> get_shadow (havoc p n st) rid = get_shadow st rid.
Proof.
  intros NE. unfold havoc. destruct (n <=? 0); [reflexivity|]. rewrite get_shadow_upd_shadow.
  destruct (N.eqb_spec rid (fst p)); [congruence| reflexivity].
Qed.

#[using="n st b t lp"] Lemma fp_ge : a <= fp * 4096.
Proof. subst fp. pose proof (Z.div_mod (a + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (a + 4095) 4096 ltac:(lia)). lia. Qed.
#[using="st a t fp"] Lemma lp_le : lp * 4096 <= b.
Proof. subst lp. pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). lia. Qed.
#[using="Type"] Lemma fp_al : (fp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.
#[using="Type"] Lemma lp_al : (lp * 4096) mod 16 = 0.
Proof. rewrite Z.mul_comm. replace 4096 with (16 * 256) by reflexivity. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
#[using="Al Hn TK t fp lp"] Lemma havoc_stale_out o tko :
  ~ (a <= o < b) ->
  match tko with Some tk => True | None => True end ->
  let sh' := get_shadow (havoc p n st) (fst p) in
  stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko
  = stale_pg (r_havp sh !! (o / 4096)) tko || stale (default [] (r_hav sh !! (o / 16))) (o mod 16) tko.
Proof.
  intros Ho _. rewrite havoc_shadow. cbn [r_hav r_havp].
  pose proof fp_ge. pose proof lp_le.
  assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
            match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
  { intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
  destruct (Z.ltb_spec fp lp).
  - f_equal.
    + rewrite havoc_pages_lookup. destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); cbn [andb]; try reflexivity.
      exfalso. apply Ho. pose proof (Z.div_mod o 4096 ltac:(lia)). pose proof (Z.mod_pos_bound o 4096 ltac:(lia)). nia.
    + destruct (Z.ltb_spec (lp * 4096) b); destruct (Z.ltb_spec a (fp * 4096)).
      * rewrite havoc_units_out; [| apply lp_al| lia| apply TKo; apply havoc_units_ticks; exact TK].
        rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
      * rewrite havoc_units_out; [reflexivity| apply lp_al| lia| apply TKo; exact TK].
      * rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
      * reflexivity.
  - f_equal. rewrite havoc_units_out; [reflexivity| exact Al| lia| apply TKo; exact TK].
Qed.

(* [comment removed for export] *)
#[using="Al Hn sh TK fp lp"] Lemma havoc_stale_in o tko :
  a <= o < b ->
  match tko with Some tk => (tk < t)%N | None => True end ->
  let sh' := get_shadow (havoc p n st) (fst p) in
  stale_pg (r_havp sh' !! (o / 4096)) tko || stale (default [] (r_hav sh' !! (o / 16))) (o mod 16) tko = true.
Proof.
  intros Ho Htk. rewrite havoc_shadow. cbn [r_hav r_havp].
  pose proof fp_ge. pose proof lp_le.
  assert (TKo : forall hh : gmap Z (list (Z * N)), (forall u hl, hh !! u = Some hl -> hl_ticks hl t) ->
            match tko with Some _ => hl_ticks (default [] (hh !! (o / 16))) t | None => True end).
  { intros hh Hh. destruct tko; [apply default_ticks; exact Hh| exact I]. }
  apply Bool.orb_true_iff.
  destruct (Z.ltb_spec fp lp).
  - destruct (Z.lt_ge_cases o (fp * 4096)) as [Hhead|Hnh].
    + right. destruct (Z.ltb_spec a (fp * 4096)); [|lia].
      destruct (Z.ltb_spec (lp * 4096) b).
      * rewrite havoc_units_out; [| apply lp_al| nia| apply TKo; apply havoc_units_ticks; exact TK].
        apply havoc_units_in; [exact Al| lia| exact Htk].
      * apply havoc_units_in; [exact Al| lia| exact Htk].
    + destruct (Z.lt_ge_cases o (lp * 4096)) as [Hmid|Htail].
      * left. rewrite havoc_pages_lookup.
        assert (fp <= o / 4096 < lp).
        { split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. }
        destruct (Z.leb_spec fp (o / 4096)), (Z.ltb_spec (o / 4096) lp); try lia. cbn [andb].
        destruct tko as [tk|]; cbn; [apply N.ltb_lt; exact Htk| reflexivity].
      * right. destruct (Z.ltb_spec (lp * 4096) b); [|lia].
        apply havoc_units_in; [apply lp_al| lia| exact Htk].
  - right. apply havoc_units_in; [exact Al| lia| exact Htk].
Qed.

(* [comment removed for export] *)
#[using="Al Hn sh TK t fp lp"] Lemma cell_read_havoc_out q :
  ~ (fst q = fst p /\ a <= snd q < b) ->
  cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst p)) as [E|NE].
  - rewrite E. assert (Ho : ~ (a <= snd q < b)) by tauto.
    unfold cell_read. pose proof (havoc_stale_out (snd q)) as SO. cbn zeta in SO.
    replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
    subst sh. destruct (r_cells (get_shadow st (fst p)) !! snd q) as [[v tk]|].
    + rewrite (SO (Some tk) Ho I). reflexivity.
    + rewrite (SO None Ho I). reflexivity.
  - rewrite havoc_other_region by exact NE. reflexivity.
Qed.

#[using="Al Hn TK fp lp"] Lemma cell_read_havoc_in q :
  fst q = fst p -> a <= snd q < b ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < t)%N) ->
  exists h, cell_read (get_shadow (havoc p n st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E. unfold cell_read.
  replace (r_cells (get_shadow (havoc p n st) (fst p))) with (r_cells sh) by (rewrite havoc_shadow; reflexivity).
  pose proof (havoc_stale_in (snd q)) as SI. cbn zeta in SI.
  destruct (r_cells sh !! snd q) as [[v tk]|] eqn:Ec.
  - rewrite (SI (Some tk) Ho (Htk v tk eq_refl)). eauto.
  - rewrite (SI None Ho I). eauto.
Qed.

#[using="Hn sh a b t fp lp"] Lemma havoc_cells rid : r_cells (get_shadow (havoc p n st) rid) = r_cells (get_shadow st rid).
Proof.
  destruct (N.eq_dec rid (fst p)) as [->|NE]; [rewrite havoc_shadow; reflexivity| rewrite havoc_other_region by exact NE; reflexivity].
Qed.

#[using="Hn sh TK a b fp lp"] Lemma havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl t) ->
  (forall pg tk, r_havp (get_shadow st rid) !! pg = Some tk -> (tk <= t)%N) ->
  (forall u hl, r_hav (get_shadow (havoc p n st) rid) !! u = Some hl -> hl_ticks hl t)
  /\ (forall pg tk, r_havp (get_shadow (havoc p n st) rid) !! pg = Some tk -> (tk <= t)%N).
Proof.
  intros H1 H2. destruct (N.eq_dec rid (fst p)) as [->|NE]; [| rewrite havoc_other_region by exact NE; auto].
  rewrite havoc_shadow. cbn [r_hav r_havp]. split.
  - destruct (fp <? lp); [| apply havoc_units_ticks; exact TK].
    destruct (lp * 4096 <? b); destruct (a <? fp * 4096); repeat apply havoc_units_ticks; exact TK.
  - destruct (fp <? lp); [| exact H2]. intros pg tk. rewrite havoc_pages_lookup. destruct (_ && _); [| apply H2].
    intros X. inversion X. lia.
Qed.
End HAVOC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HDR.
Variables (bp : aptr) (st : mstate).
Hypothesis Al : snd bp mod 16 = 0.
Let sh := get_shadow st (fst bp).
Hypothesis TK : forall u hl, r_hav sh !! u = Some hl -> hl_ticks hl (s_tick st).

#[using="Type"] Lemma hdr_havoc_shadow :
  get_shadow (hdr_havoc bp st) (fst bp) =
  mkShadow (r_cells sh) (<[snd bp / 16 := hav_add 12 (s_tick st) (default [] (r_hav sh !! (snd bp / 16)))]> (r_hav sh)) (r_havp sh).
Proof. unfold hdr_havoc. rewrite get_shadow_upd_shadow, N.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma hdr_havoc_other_region rid : rid <> fst bp -> get_shadow (hdr_havoc bp st) rid = get_shadow st rid.
Proof. intros NE. unfold hdr_havoc. rewrite get_shadow_upd_shadow. destruct (N.eqb_spec rid (fst bp)); [congruence| reflexivity]. Qed.

#[using="Al sh TK"] Lemma cell_read_hdr_havoc_out q :
  ~ (fst q = fst bp /\ snd bp <= snd q < snd bp + 12) ->
  cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. destruct (N.eq_dec (fst q) (fst bp)) as [E|NE]; [| rewrite hdr_havoc_other_region by exact NE; reflexivity].
  rewrite E. rewrite hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
  destruct (Z.eq_dec (snd q / 16) (snd bp / 16)) as [Eu|Nu].
  - rewrite Eu, lookup_insert_eq. cbn [default id].
    assert (Hb : 12 <= snd q mod 16).
    { pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (snd q) 16 ltac:(lia)).
      assert (~ (snd bp <= snd q < snd bp + 12)) by tauto. nia. }
    destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|].
    + rewrite stale_hav_add_some by (apply default_ticks; exact TK). destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [andb orb]. rewrite <- Eu. reflexivity.
    + rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [lia|]. cbn [orb]. rewrite <- Eu. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Al"] Lemma cell_read_hdr_havoc_in q :
  fst q = fst bp -> snd bp <= snd q < snd bp + 12 ->
  (forall v tk, r_cells sh !! snd q = Some (v, tk) -> (tk < s_tick st)%N) ->
  exists h, cell_read (get_shadow (hdr_havoc bp st) (fst q)) (snd q) = Unknown h.
Proof.
  intros E Ho Htk. rewrite E, hdr_havoc_shadow. unfold cell_read. cbn [r_cells r_hav r_havp]. subst sh.
  assert (Eu : snd q / 16 = snd bp / 16).
  { pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). symmetry. apply Z.div_unique with (r := snd q - snd bp); lia. }
  rewrite Eu, lookup_insert_eq. cbn [default id].
  assert (Hb : snd q mod 16 < 12).
  { pose proof (Z.div_mod (snd q) 16 ltac:(lia)). pose proof (Z.div_mod (snd bp) 16 ltac:(lia)). nia. }
  destruct (r_cells (get_shadow st (fst bp)) !! snd q) as [[v tk]|] eqn:Ec.
  - unfold hav_add, stale. cbn [existsb fst snd].
    destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. rewrite (proj2 (N.ltb_lt _ _)) by (eapply Htk; reflexivity).
    cbn [andb orb]. rewrite Bool.orb_true_r. eauto.
  - rewrite stale_hav_add_none. destruct (Z.ltb_spec (snd q mod 16) 12); [|lia]. cbn [orb]. rewrite Bool.orb_true_r. eauto.
Qed.

#[using="sh"] Lemma hdr_havoc_cells rid : r_cells (get_shadow (hdr_havoc bp st) rid) = r_cells (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [rewrite hdr_havoc_shadow; reflexivity| rewrite hdr_havoc_other_region by exact NE; reflexivity]. Qed.

#[using="sh TK"] Lemma hdr_havoc_ticks rid :
  (forall u hl, r_hav (get_shadow st rid) !! u = Some hl -> hl_ticks hl (s_tick st)) ->
  (forall u hl, r_hav (get_shadow (hdr_havoc bp st) rid) !! u = Some hl -> hl_ticks hl (s_tick st))
  /\ r_havp (get_shadow (hdr_havoc bp st) rid) = r_havp (get_shadow st rid).
Proof.
  intros H1. destruct (N.eq_dec rid (fst bp)) as [->|NE]; [| rewrite hdr_havoc_other_region by exact NE; auto].
  rewrite hdr_havoc_shadow. cbn [r_hav r_havp]. split; [| reflexivity].
  intros u hl. destruct (Z.eq_dec u (snd bp / 16)) as [->|Nu].
  - rewrite lookup_insert_eq. intros X. inversion X. subst. apply hav_add_ticks. apply default_ticks. exact TK.
  - rewrite lookup_insert_ne by congruence. apply H1.
Qed.
End HDR.

End WithCeil.
End MI_Shadow.

(* [comment removed for export] *)
Module MI_Tree.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition rejects {R} (t : M R) : Prop :=
  match t with SVis (EUndef _) _ => True | _ => False end.

Definition is_peek (e : ev) : bool := match e with EPeek _ _ _ => true | _ => false end.
Definition is_undef (e : ev) : bool := match e with EUndef _ => true | _ => false end.

#[using="Type"] Lemma rejects_inv {R} (t : M R) : rejects t -> exists w k, t = SVis (EUndef w) k.
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; try tauto. intros _. eauto. Qed.

#[using="Type"] Lemma rejects_bind {R S} (t : M R) (f : R -> M S) : rejects t -> rejects (sbind t f).
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; tauto. Qed.

Fixpoint ftree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> ftree L (k v) Post
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a)
  end.

(* [comment removed for export] *)
Fixpoint ptree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => False
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ptree (event_post L e a) (k a) Post else rejects (k a)
  end.
End WithCeil.


Ltac case_ans :=
  match goal with
  | |- context [if answer_ok ?L ?e ?a then _ else _] => destruct (answer_ok L e a) eqn:?
  | H : context [if answer_ok ?L ?e ?a then _ else _] |- _ => destruct (answer_ok L e a) eqn:?
  end.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma ftree_ret {R} L (r : R) Post : Post L r -> ftree L (SRet r) Post.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma ftree_vis {R} L e (k : Z -> M R) Post :
  is_peek e = false -> is_undef e = false ->
  event_pre L e ->
  (forall a, answer_ok L e a = true -> ftree (event_post L e a) (k a) Post) ->
  (forall a, answer_ok L e a = false -> rejects (k a)) ->
  ftree L (SVis e k) Post.
Proof.
  intros Hp Hu He Hk Hr. destruct e; cbn in Hp, Hu; try discriminate; cbn [ftree]; split; auto;
  intros a; case_ans; auto.
Qed.

#[using="Type"] Lemma ftree_peek {R} L p c h (k : Z -> M R) Post :
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) -> ftree L (SVis (EPeek p c h) k) Post.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma ftree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ftree L t Post -> ftree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

#[using="Type"] Lemma ftree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
  ftree L t Post -> (forall L' r, Post L' r -> ftree L' (f r) Q) -> ftree L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk).
    + intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
    + destruct H.
Qed.

#[using="Type"] Lemma rejects_bad_answer {R} (b : M R) : rejects (bad_answer b).
Proof. exact I. Qed.

#[using="Type"] Lemma ftree_guard {R} L tag (c : bool) (k bail : M R) Post :
  c = true -> ftree L k Post -> ftree L (guard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

#[using="Type"] Lemma ftree_guard_inv {R} L tag (c : bool) (k bail : M R) Post :
  ftree L (guard tag c k bail) Post -> c = true /\ ftree L k Post.
Proof. unfold guard. destruct c; cbn; [auto| intros H; destruct H]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ptree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ptree L t Post -> ptree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]); exact H.
Qed.

#[using="Type"] Lemma ptree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
  ptree L t Post -> (forall L' r, Post L' r -> ptree L' (f r) Q) -> ptree L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk); exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ptree_ctree_ok {R} : forall (t : M R) L Post, ptree L t Post -> ctree_ok L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ftree ptree follow sbind] in *; [exact H|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros z Hz; specialize (Hk z); rewrite Hz in Hk; apply IH; exact Hk);
    destruct H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ptree_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L (P1 : mled -> R1 -> Prop) (P2 : mled -> R2 -> Prop),
  (forall L' r1 r2, RR r1 r2 -> P1 L' r1 -> P2 L' r2) ->
  ptree L t1 P1 -> ptree L t2 P2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L P1 P2 HP H; cbn [ftree ptree follow sbind] in *.
  - eapply HP; eauto.
  - destruct e; try exact H. all: destruct H as [He H]; split; [exact He|]; intros a; specialize (H a);
      case_ans; [eapply IH; eauto|].
    all: specialize (Hk a); destruct (rejects_inv _ H) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I.
Qed.

(* [comment removed for export] *)
Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

#[using="Hpans"] Lemma ftree_prun {R} : forall (t : M R) L Post o,
  ftree L t Post -> ptree L (prun pans pupd o t) (fun L' x => Post L' (snd x)).
Proof.
  induction t as [r|e k IH]; intros L Post o H; cbn [ftree ptree follow sbind] in *.
  - exact H.
  - unfold prun. destruct e; cbn [eruns psel];
      try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
           case_ans; [apply IH; exact Hk|];
           destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E; exact I).
    + apply IH. apply H. apply Hpans.
    + destruct H.
Qed.
End PRUN.

(* [comment removed for export] *)
#[using="Type"] Lemma ptree_follow {R} : forall (t : M R) L Post ans r,
  ptree L t Post -> follow t ans = Some r -> exists L', cpath L t L' r /\ Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ftree ptree follow sbind] in *.
  - inversion Hf; subst. exists L. split; [constructor| exact H].
  - destruct e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); case_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as (L' & Hp & HP); exists L'; split; [econstructor; eauto| exact HP]
      | destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

#[using="Type"] Lemma ptree_cpath {R} : forall (t : M R) L Post L' r,
  ptree L t Post -> cpath L t L' r -> Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post L' r H Hp; cbn [ftree ptree follow sbind] in *.
  - inversion Hp; subst. exact H.
  - inversion Hp; subst. destruct e; try contradiction.
    all: destruct H as [He Hk];
      match goal with Ha : answer_ok _ _ ?z = true |- _ => specialize (Hk z); rewrite Ha in Hk; eapply IH; eauto end.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma strel_cpath {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L L' r2, cpath L t2 L' r2 -> exists r1, cpath L t1 L' r1 /\ RR r1 r2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L L' r Hp.
  - inversion Hp; subst. exists r1. split; [constructor| exact Hr].
  - inversion Hp; subst.
    match goal with Hc : cpath _ (k2 ?z) _ _ |- _ =>
      destruct (IH z _ _ _ Hc) as (r1 & Hp1 & Hr1); exists r1; split; [econstructor; eauto| exact Hr1] end.
Qed.

#[using="Type"] Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall ans,
  match follow t1 ans, follow t2 ans with
  | Some r1, Some r2 => RR r1 r2
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans; cbn.
  - exact Hr.
  - destruct e; destruct ans; cbn; auto; apply IH.
Qed.

End WithCeil.
End MI_Tree.

(* [comment removed for export] *)
Module MI_Read.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma known_at st rid o v rid' o' :
  known st (rid, o) v -> o' = o -> rid' = rid -> cell_read (get_shadow st rid') o' = Known v.
Proof. intros H -> ->. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rd8_ftree {R} L st q (k : Z -> M R) Post :
  (forall v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) ->
  ftree L (rd8 st q k) Post.
Proof.
  intros Hk H. unfold rd8. destruct (cell_read _ _) as [v|h] eqn:E.
  - apply H. apply Hk. reflexivity.
  - cbn [ftree]. intros v Hv. unfold peek_answer_ok.
    destruct (Z.leb_spec 0 v), (Z.ltb_spec v 256); cbn [andb]; try lia. apply H. lia.
Qed.

#[using="Type"] Lemma rd16_ftree {R} L st q (k : Z -> M R) Post :
  (forall q' v, cell_read (get_shadow st (fst q')) (snd q') = Known v -> 0 <= v < 256) ->
  (forall v, 0 <= v < 65536 -> ftree L (k v) Post) ->
  ftree L (rd16 st q k) Post.
Proof.
  intros Hk H. unfold rd16. apply rd8_ftree; [apply Hk|]. intros b0 H0. apply rd8_ftree; [apply Hk|]. intros b1 H1. apply H. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma known_byte st rid o v :
  (forall sh o' v' t, s_shadow st !! rid = Some sh -> r_cells sh !! o' = Some (v', t) -> 0 <= v' < 256) ->
  cell_read (get_shadow st rid) o = Known v -> 0 <= v < 256.
Proof.
  intros Hc H. unfold cell_read, get_shadow in H. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn [default id] in H.
  - destruct (r_cells sh !! o) as [[v' t]|] eqn:E2.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. subst. eapply Hc; eauto.
    + match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. lia.
  - rewrite !lookup_empty in H. cbn in H. inversion H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma land_255 x : 0 <= x -> Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

#[using="Type"] Lemma byte_of_0 x : 0 <= x -> byte_of x 0 = x mod 256.
Proof. intros. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r. apply land_255. lia. Qed.
#[using="Type"] Lemma byte_of_1 x : 0 <= x -> byte_of x 1 = (x / 256) mod 256.
Proof. intros. unfold byte_of. replace (8 * 1) with 8 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply land_255. apply Z.div_pos; lia. Qed.
#[using="Type"] Lemma byte_of_2 x : 0 <= x -> byte_of x 2 = (x / 65536) mod 256.
Proof. intros. unfold byte_of. replace (8 * 2) with 16 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. apply land_255. apply Z.div_pos; lia. Qed.
#[using="Type"] Lemma byte_of_3 x : 0 <= x -> byte_of x 3 = (x / 16777216) mod 256.
Proof. intros. unfold byte_of. replace (8 * 3) with 24 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply land_255. apply Z.div_pos; lia. Qed.

#[using="Type"] Lemma byte_of_range x k : 0 <= x -> 0 <= k -> 0 <= byte_of x k < 256.
Proof.
  intros. unfold byte_of. rewrite land_255 by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]).
  apply Z.mod_pos_bound. lia.
Qed.

#[using="Type"] Lemma u16_bytes q : 0 <= q < 2^16 -> byte_of q 0 + 256 * byte_of q 1 = q.
Proof. intros. rewrite byte_of_0, byte_of_1 by lia. rewrite (Z.mod_small (q / 256)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). pose proof (Z.div_mod q 256 ltac:(lia)). lia. Qed.

#[using="Type"] Lemma u32_bytes r : 0 <= r < 2^32 ->
  byte_of r 0 + 256 * byte_of r 1 + 65536 * byte_of r 2 + 16777216 * byte_of r 3 = r.
Proof.
  intros. rewrite byte_of_0, byte_of_1, byte_of_2, byte_of_3 by lia.
  pose proof (Z.div_mod r 256 ltac:(lia)) as E1.
  pose proof (Z.div_mod (r / 256) 256 ltac:(lia)) as E2. rewrite (Z.div_div r 256 256) in E2 by lia. change (256 * 256) with 65536 in E2.
  pose proof (Z.div_mod (r / 65536) 256 ltac:(lia)) as E3. rewrite (Z.div_div r 65536 256) in E3 by lia. change (65536 * 256) with 16777216 in E3.
  rewrite (Z.mod_small (r / 16777216)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land31_idx i r : 0 <= i <= 31 -> 0 <= r -> Z.land (i + 32 * r) 31 = i.
Proof.
  intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (i + r * 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma shiftr5_res i r : 0 <= i <= 31 -> 0 <= r -> Z.shiftr (i + 32 * r) 5 = r.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  replace (i + 32 * r) with (r * 32 + i) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma area_of_mslot a k : snd a mod PGSZ = 0 -> 0 <= k < NSLOTS -> area_of (mslot a k) = a.
Proof.
  intros Ha Hk. unfold area_of, mslot, aadd, AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. destruct a as [r o]; cbn in *. f_equal.
  rewrite <- Zplus_mod_idemp_l, Ha. cbn [Z.add]. rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma mod_pg_mod16 x : x mod PGSZ = 0 -> x mod 16 = 0.
Proof. intros H. unfold PGSZ in H. pose proof (Z.div_mod x 4096 ltac:(lia)). rewrite H in H0.
  rewrite H0. replace (4096 * (x / 4096) + 0) with ((256 * (x / 4096)) * 16) by lia. apply Z_mod_mult. Qed.

#[using="Type"] Lemma mslot_mod8 a k : snd a mod PGSZ = 0 -> snd (mslot a k) mod 8 = 0.
Proof.
  intros Ha. unfold mslot, aadd, AREA_HDR, META_SIZE. cbn [snd].
  pose proof (Z.div_mod (snd a) 4096 ltac:(lia)). unfold PGSZ in Ha. rewrite Ha in H.
  rewrite H. replace (4096 * (snd a / 4096) + 0 + (24 + 40 * k)) with ((512 * (snd a / 4096) + 3 + 5 * k) * 8) by lia. apply Z_mod_mult.
Qed.

End WithCeil.
End MI_Read.

(* [comment removed for export] *)
Module MI_Progress.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.
Set Implicit Arguments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition good (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap _ _ _ flags => Z.land flags MAP_FIXED = 0 -> is_err z = false
  | EMprotect _ _ _ => (z =? 0) || (z =? TWO64 - ENOSYS) = true
  | _ => True
  end.

Fixpoint gleaf {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis (EUndef _) _ => True
  | SVis (EPeek _ _ _) k => forall v, gleaf P (k v)
  | SVis e k => forall z, good e z -> gleaf P (k z)
  end.

#[using="Type"] Lemma gleaf_ret {R} (P : R -> Prop) r : P r -> gleaf P (SRet r).
Proof. exact (fun H => H). Qed.

#[using="Type"] Lemma gleaf_vis {R} (P : R -> Prop) e k : (forall z, good e z -> gleaf P (k z)) -> gleaf P (SVis e k).
Proof. intros H. destruct e; cbn; auto. intros v; apply H; exact I. Qed.

#[using="Type"] Lemma gleaf_undef {R} (P : R -> Prop) w k : gleaf P (SVis (EUndef w) k).
Proof. exact I. Qed.

#[using="Type"] Lemma gleaf_mono {R} (P Q : R -> Prop) : (forall r, P r -> Q r) -> forall t, gleaf P t -> gleaf Q t.
Proof.
  intros HPQ. induction t as [r|e k IH]; cbn; [auto|].
  destruct e; intros H; try (intros z Hz; apply IH; apply H; exact Hz); [intros v; apply IH; apply H| exact I].
Qed.

#[using="Type"] Lemma gleaf_bind {R S} (P : R -> Prop) (Q : S -> Prop) (t : M R) (f : R -> M S) :
  gleaf P t -> (forall r, P r -> gleaf Q (f r)) -> gleaf Q (sbind t f).
Proof.
  revert t. induction t as [r|e k IH]; intros Ht Hf; cbn [sbind]; [apply Hf; exact Ht|].
  destruct e; cbn in Ht |- *; auto.
Qed.

#[using="Type"] Lemma gleaf_guard {R} (P : R -> Prop) tag c (k bail : M R) : gleaf P k -> gleaf P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [exact H| exact I]. Qed.

#[using="Type"] Lemma gleaf_bad {R} (P : R -> Prop) (bail : M R) : gleaf P (bad_answer bail).
Proof. exact I. Qed.

(* [comment removed for export] *)
Inductive gpath {R} : M R -> R -> Prop :=
| gpath_ret r : gpath (SRet r) r
| gpath_vis e k z r : is_peek e = false -> is_undef e = false -> good e z -> gpath (k z) r -> gpath (SVis e k) r
| gpath_peek p c h k v r : gpath (k v) r -> gpath (SVis (EPeek p c h) k) r.

#[using="Type"] Lemma gleaf_gpath {R} (P : R -> Prop) (t : M R) r : gleaf P t -> gpath t r -> P r.
Proof.
  intros Hg Hp. induction Hp as [r|e k z r He Hu Hz Hp IH|p c h k v r Hp IH].
  - exact Hg.
  - apply IH. destruct e; cbn in He, Hu, Hg; try discriminate; auto.
  - apply IH. exact (Hg v).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma gleaf_rd8 {R} (P : R -> Prop) st p (k : Z -> M R) : (forall v, gleaf P (k v)) -> gleaf P (rd8 st p k).
Proof. intros H. unfold rd8. destruct (cell_read _ _); [apply H|]. cbn. intros v. destruct (peek_answer_ok v); [apply H| exact I]. Qed.

#[using="Type"] Lemma gleaf_rd16 {R} (P : R -> Prop) st p (k : Z -> M R) : (forall v, gleaf P (k v)) -> gleaf P (rd16 st p k).
Proof. intros H. unfold rd16. apply gleaf_rd8. intros; apply gleaf_rd8. intros; apply H. Qed.

#[using="Type"] Lemma gleaf_rd32 {R} (P : R -> Prop) st p (k : Z -> M R) : (forall v, gleaf P (k v)) -> gleaf P (rd32 st p k).
Proof. intros H. unfold rd32. repeat (apply gleaf_rd8; intros). apply H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM.
Variable R : Type.
Variable P : R -> Prop.
(* [comment removed for export] *)
Definition KS (k : mstate -> optr -> M R) : Prop := forall st m, gleaf P (k st (Some m)).

#[using="Type"] Lemma queue_gleaf h m st (k : mstate -> M R) bail : (forall st, gleaf P (k st)) -> gleaf P (queue h m st k bail).
Proof. intros Hk. unfold queue. apply gleaf_guard, gleaf_guard. destruct (get_head st h); apply Hk. Qed.

#[using="Type"] Lemma free_meta_gleaf m st (k : mstate -> M R) bail : (forall st, gleaf P (k st)) -> gleaf P (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply queue_gleaf. exact Hk. Qed.

#[using="Type"] Lemma am_take_gleaf st k bail : KS k -> gleaf P (am_take st k bail).
Proof. intros Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk| exact I]. Qed.

#[using="Type"] Lemma am_carve_gleaf st p k bail : KS k -> gleaf P (am_carve st p k bail).
Proof. intros Hk. unfold am_carve. apply am_take_gleaf. exact Hk. Qed.

#[using="Type"] Lemma am_finish_gleaf st nu k bail : KS k -> gleaf P (am_finish st nu k bail).
Proof.
  intros Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - apply gleaf_vis. intros z Hz. cbv beta. destruct (mprotect_answer_ok z); cbn [negb]; [|apply gleaf_bad]. cbn [good] in Hz. rewrite Hz. apply am_carve_gleaf. exact Hk.
  - apply am_carve_gleaf. exact Hk.
Qed.

#[using="Type"] Lemma am_after_brk_gleaf st nu k bail : KS k -> gleaf P (am_after_brk st nu k bail).
Proof.
  intros Hk. unfold am_after_brk. destruct (c_avail_meta_area_count (ctx st) =? 0); [|apply am_finish_gleaf; exact Hk].
  apply gleaf_vis. intros z Hz. cbv beta. destruct (mmap_answer_ok _ _ z); cbn [negb]; [|apply gleaf_bad].
  cbn [good] in Hz. rewrite (Hz eq_refl). destruct (new_region _ _ _ _) as [st1 rid]. apply am_finish_gleaf. exact Hk.
Qed.

#[using="Type"] Lemma alloc_meta_gleaf st k bail : KS k -> gleaf P (alloc_meta st k bail).
Proof.
  intros Hk. unfold alloc_meta.
  set (st0 := if c_init_done (ctx st) =? 0 then _ else st).
  destruct (c_free_meta_head (ctx st0)); [apply Hk|].
  destruct (negb (c_avail_meta_count (ctx st0) =? 0)); [apply am_take_gleaf; exact Hk|].
  destruct ((c_avail_meta_area_count (ctx st0) =? 0) && _); [|apply am_after_brk_gleaf; exact Hk].
  destruct (c_brk (ctx st0)) as [| |rid off].
  - apply gleaf_vis. intros cur _. cbv beta. destruct (brk0_answer_ok cur); cbn [negb]; [|apply gleaf_bad]. apply gleaf_vis. intros r _. cbv beta.
    destruct (brk_answer_ok _ _ r); cbn [negb]; [|apply gleaf_bad].
    destruct (negb (r =? _)); [apply am_after_brk_gleaf; exact Hk|].
    destruct (brk_pages_ok _ _ _); cbn [negb]; [|apply gleaf_bad]. apply gleaf_vis. intros rg _. cbv beta.
    destruct (mmap_fixed_answer_ok _ rg); cbn [negb]; [|apply gleaf_bad].
    destruct (new_region _ _ _ _) as [st1 rid]. apply am_after_brk_gleaf. exact Hk.
  - apply am_after_brk_gleaf. exact Hk.
  - apply gleaf_vis. intros r _. cbv beta. destruct (brk_answer_ok _ _ r); cbn [negb]; [|apply gleaf_bad].
    destruct (negb (r =? _)); [apply am_after_brk_gleaf; exact Hk|].
    destruct (brk_pages_ok _ _ _); cbn [negb]; [|apply gleaf_bad]. apply am_after_brk_gleaf. exact Hk.
Qed.
End AM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AS.
Variable R : Type.
Variable P : R -> Prop.

#[using="Type"] Lemma activate_group_gleaf m st (k : mstate -> Z -> M R) bail :
  (forall st v, gleaf P (k st v)) -> gleaf P (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply gleaf_guard. apply Hk. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma try_avail_gleaf sc st (k : mstate -> Z -> M R) bail :
  (forall st v, gleaf P (k st v)) -> gleaf P (try_avail sc st k bail).
Proof.
  intros Hk. unfold try_avail. destruct (active st sc) as [m|]; [|apply Hk].
  destruct (negb (m_avail (get_meta_rec st m) =? 0)); [apply Hk|].
  lazymatch goal with |- gleaf P (match ?s with _ => _ end) => destruct s as [[st1 m1]|] end.
  2:{ destruct (m_freed _ =? 0); [apply Hk| exact I]. }
  lazymatch goal with |- gleaf P (match ?x with _ => _ end) => destruct x as [[st2 m2] mask] end.
  lazymatch goal with |- gleaf P (match ?x with _ => _ end) => destruct x as [st3 m3] end.
  apply activate_group_gleaf. intros st4 v. apply gleaf_guard. apply Hk.
Qed.

#[using="Type"] Lemma ag_tail_gleaf lay st sc m p cnt ai (k : mstate -> optr -> M R) :
  KS P k -> gleaf P (ag_tail lay st sc m p cnt ai k).
Proof. intros Hk. unfold ag_tail. apply Hk. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma alloc_group_gleaf lay (asr : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R) st sc req k bail :
  (forall st j rq (k' : mstate -> Z -> M R) bail', (forall st idx, 0 <= idx -> gleaf P (k' st idx)) -> gleaf P (asr st j rq k' bail')) ->
  KS P k -> gleaf P (alloc_group R lay asr st sc req k bail).
Proof.
  intros Hasr Hk. unfold alloc_group. apply alloc_meta_gleaf. intros st0 m. cbv beta.
  match goal with |- gleaf P (if ?c then _ else _) => destruct c end.
  - (* [comment removed for export] *)
    match goal with |- gleaf P (let '(cnt, needed) := ?x in _) => destruct x as [cnt needed] end.
    apply gleaf_vis. intros z Hz. cbv beta. destruct (mmap_answer_ok _ _ z); cbn [negb]; [|apply gleaf_bad].
    cbn [good] in Hz. rewrite (Hz eq_refl). destruct (new_region _ _ _ _) as [st2 rid]. apply ag_tail_gleaf. exact Hk.
  - (* [comment removed for export] *)
    apply Hasr. intros st1 idx Hidx.
    replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; exact Hidx).
    destruct (active st1 _); [apply ag_tail_gleaf; exact Hk| exact I].
Qed.

#[using="Type"] Lemma ctz32_nonneg m : 0 <= ctz32 m.
Proof. unfold ctz32. apply Z.log2_nonneg. Qed.

#[using="Type"] Lemma alloc_slot_gleaf lay : forall fuel st sc req (k : mstate -> Z -> M R) bail,
  (forall st idx, 0 <= idx -> gleaf P (k st idx)) -> gleaf P (alloc_slot lay fuel st sc req k bail).
Proof.
  induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [exact I|].
  apply try_avail_gleaf. intros st1 first.
  destruct (negb (first =? 0)); [apply Hk; apply ctz32_nonneg|].
  apply alloc_group_gleaf; [intros; apply IH; assumption|].
  intros st2 g. cbv beta iota. apply queue_gleaf. intros st4. apply Hk. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KC (k : mstate -> option (aptr * Z) -> M R) : Prop := forall st g idx, gleaf P (k st (Some (g, idx))).

#[using="Type"] Lemma malloc_small_ctrl_gleaf lay st n k bail : KC k -> gleaf P (malloc_small_ctrl lay st n k bail).
Proof.
  intros Hk. unfold malloc_small_ctrl.
  assert (AS : forall sc', gleaf P (alloc_slot lay FUEL st sc' n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc' with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail)).
  { intros sc'. apply alloc_slot_gleaf. intros st1 idx Hidx. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; exact Hidx).
    destruct (active st1 _); [apply Hk| exact I]. }
  lazymatch goal with |- gleaf P (match ?g with _ => _ end) => destruct g as [gp|]; [| apply AS] end.
  lazymatch goal with |- gleaf P (match ?b with _ => _ end) => destruct b; [apply Hk| apply AS] end.
Qed.
End AS.

Definition core_ok (r : mstate * option (aptr * Z)) : Prop := snd r <> None.

#[using="Type"] Theorem malloc_core_progress lay st n : size_overflows n = false -> gleaf core_ok (malloc_core lay st n).
Proof.
  intros Hov. unfold malloc_core. rewrite Hov.
  destruct (MMAP_THRESHOLD <=? n).
  - apply gleaf_vis. intros z Hz. cbv beta. destruct (mmap_answer_ok _ _ z); cbn [negb]; [|apply gleaf_bad]. cbn [good] in Hz. rewrite (Hz eq_refl).
    destruct (new_region _ _ _ _) as [st1 rid]. apply alloc_meta_gleaf. intros st3 g. cbn. discriminate.
  - apply malloc_small_ctrl_gleaf. intros st1 g idx. cbn. discriminate.
Qed.

Definition res_ok (r : mstate * optr) : Prop := snd r <> None.

#[using="Type"] Lemma enframe_full_gleaf {R} (P : R -> Prop) st g idx n ctr (k : mstate -> aptr -> M R) :
  (forall st p, gleaf P (k st p)) -> gleaf P (enframe_full st g idx n ctr k).
Proof.
  intros Hk. unfold enframe_full, enframe_read_off. apply gleaf_rd8. intros b3.
  destruct (negb (b3 =? 0)); [apply gleaf_rd16; intros|]; destruct (enframe_at _ _ _ _ _); apply Hk.
Qed.

#[using="Type"] Theorem malloc_progress st n : size_overflows n = false -> gleaf res_ok (malloc st n).
Proof.
  intros Hov. unfold malloc. eapply gleaf_bind; [apply malloc_core_progress; exact Hov|].
  intros [st1 [[g idx]|]] Hr; [| exfalso; exact (Hr eq_refl)].
  apply enframe_full_gleaf. intros st2 p. cbn. discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma get_meta_gleaf {R} (P : R -> Prop) st p (k : aptr -> Z -> Z -> M R) bail :
  (forall m off idx, gleaf P (k m off idx)) -> gleaf P (get_meta st p k bail).
Proof.
  intros Hk. unfold get_meta. apply gleaf_guard. apply gleaf_rd16. intros o16. cbv beta. apply gleaf_rd8. intros b3. cbv beta. apply gleaf_rd8. intros b4. cbv beta.
  destruct (negb (b4 =? 0)).
  - apply gleaf_guard. apply gleaf_rd32. intros o32. cbv beta. apply gleaf_guard.
    destruct (get_group st _) as [gh|]; [| exact I]. destruct (g_meta gh) as [m|]; [| exact I]. repeat apply gleaf_guard. apply Hk.
  - destruct (get_group st _) as [gh|]; [| exact I]. destruct (g_meta gh) as [m|]; [| exact I]. repeat apply gleaf_guard. apply Hk.
Qed.

#[using="Type"] Lemma get_nominal_size_gleaf {R} (P : R -> Prop) st p e (k : Z -> M R) bail :
  (forall v, gleaf P (k v)) -> gleaf P (get_nominal_size st p e k bail).
Proof.
  intros Hk. unfold get_nominal_size. apply gleaf_rd8. intros b3.
  assert (C : forall reserved, gleaf P (guard 22 (reserved <=? snd e - snd p)
     (rd8 st (aadd e (- reserved)) (fun cb => guard 23 (cb =? 0) (rd8 st e (fun eb => guard 24 (eb =? 0) (k (snd e - reserved - snd p)) bail)) bail)) bail)).
  { intros reserved. apply gleaf_guard. apply gleaf_rd8. intros. apply gleaf_guard. apply gleaf_rd8. intros. apply gleaf_guard. apply Hk. }
  destruct (5 <=? Z.shiftr b3 5); [| apply C].
  apply gleaf_guard. apply gleaf_rd32. intros. apply gleaf_guard. apply gleaf_rd8. intros. apply gleaf_guard. apply C.
Qed.

#[using="Type"] Lemma free_hdr_gleaf st p : gleaf (fun _ => True) (free_hdr st p).
Proof.
  unfold free_hdr. apply get_meta_gleaf. intros m off idx. destruct (slot_start _ _); [| exact I].
  apply get_nominal_size_gleaf. intros v. exact I.
Qed.

#[using="Type"] Lemma nontrivial_free_gleaf {R} (P : R -> Prop) dec : forall fuel st g i (k : mstate -> mapinfo -> M R) bail,
  (forall st p (k' : aptr -> Z -> M R) bail', (forall m idx, gleaf P (k' m idx)) -> gleaf P (dec st p k' bail')) ->
  (forall st mi, gleaf P (k st mi)) -> gleaf P (nontrivial_free dec fuel st g i k bail).
Proof.
  induction fuel as [|f IH]; intros st g i k bail Hdec Hk; cbn [nontrivial_free]; [exact I|].
  match goal with |- gleaf P (if ?c then _ else _) => destruct c end.
  - assert (FG : forall st', gleaf P (free_group R dec (nontrivial_free dec f) st' g k bail)).
    { intros st'. unfold free_group. destruct (m_mem _); [| exact I].
      destruct (negb (m_maplen _ =? 0)); [apply free_meta_gleaf; intros; apply Hk|].
      apply Hdec. intros m idx. apply IH; [exact Hdec|]. intros st3 mi. apply free_meta_gleaf. intros; apply Hk. }
    destruct (m_next _); [| apply FG]. apply gleaf_guard.
    destruct (optr_eqb _ _); [| apply FG]. destruct (active _ _); [| apply FG].
    apply activate_group_gleaf. intros; apply FG.
  - destruct (_ =? 0); [| apply Hk]. apply gleaf_guard. destruct (negb _); [apply queue_gleaf; intros; apply Hk| apply Hk].
Qed.

#[using="Type"] Lemma free_tail_gleaf (dec : forall R', decoder R') st g idx :
  (forall R' (P' : R' -> Prop) st p (k' : aptr -> Z -> M R') (bail' : M R'), (forall m idx, gleaf P' (k' m idx)) -> gleaf P' (dec R' st p k' bail')) ->
  gleaf (fun _ => True) (free_tail (dec mstate) st g idx).
Proof.
  intros Hdec. unfold free_tail. apply gleaf_guard. destruct (negb _); [exact I|].
  apply nontrivial_free_gleaf; [apply Hdec|]. intros st2 [[base len]|]; [| exact I].
  destruct (negb (len =? 0)); [| exact I]. apply gleaf_vis. intros z _. cbv beta. destruct (munmap_answer_ok z); exact I.
Qed.

#[using="Type"] Lemma dec_hdr_gleaf R' (P' : R' -> Prop) st p (k' : aptr -> Z -> M R') bail' :
  (forall m idx, gleaf P' (k' m idx)) -> gleaf P' (@dec_hdr R' st p k' bail').
Proof. intros Hk. unfold dec_hdr. apply get_meta_gleaf. intros; apply Hk. Qed.

#[using="Type"] Lemma free_gleaf st p : gleaf (fun _ => True) (free st p).
Proof.
  unfold free. destruct p as [p|]; [| exact I].
  eapply gleaf_bind; [apply free_hdr_gleaf|]. intros [[[st1 g] idx]|] _; [| exact I].
  apply (free_tail_gleaf (fun R' => @dec_hdr R')). intros. apply dec_hdr_gleaf. assumption.
Qed.

#[using="Type"] Theorem realloc_progress st p n : size_overflows n = false -> gleaf res_ok (realloc st p n).
Proof.
  intros Hov. unfold realloc. destruct p as [p|]; [| apply malloc_progress; exact Hov]. rewrite Hov.
  apply get_meta_gleaf. intros g off idx. destruct (slot_start _ _) as [start|]; [| exact I].
  apply get_nominal_size_gleaf. intros old.
  assert (FB : forall st1, gleaf res_ok ('(st2, q) <-- malloc st1 n ;; match q with None => ret (st2, None) | Some q0 => st3 <-- free st2 (Some p);; ret (st3, Some q0) end)).
  { intros st1. eapply gleaf_bind; [apply malloc_progress; exact Hov|]. intros [st2 [q|]] Hq; [| exfalso; exact (Hq eq_refl)].
    eapply gleaf_bind; [apply free_gleaf|]. intros st3 _. cbn. discriminate. }
  destruct (_ && _ && _); [cbn; discriminate|].
  destruct (_ && _); [| apply FB]. apply gleaf_guard.
  destruct (_ =? _); [cbn; discriminate|].
  apply gleaf_vis. intros z _. cbv beta. destruct (mremap_answer_ok _ _ _ _ _ z); cbn [negb]; [| apply gleaf_bad].
  destruct (is_err z); [apply FB| cbn; discriminate].
Qed.

#[using="Type"] Theorem calloc_progress st m n :
  (negb (n =? 0) && (SIZE_MAX / n <? m)) = false -> size_overflows (m * n) = false -> gleaf res_ok (calloc st m n).
Proof.
  intros Hov1 Hov2. unfold calloc. rewrite Hov1.
  eapply gleaf_bind; [apply malloc_progress; exact Hov2|]. intros [st1 [q|]] Hq; [| exfalso; exact (Hq eq_refl)].
  unfold is_allzero. apply get_meta_gleaf. intros. cbn. discriminate.
Qed.

End WithCeil.
End MI_Progress.
