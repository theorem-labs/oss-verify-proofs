(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Inductive tle {R : Type} : M R -> M R -> Prop :=
| tle_ret : forall r, tle (SRet r) (SRet r)
| tle_fuel : forall k t, tle (SVis (EUndef UFuel) k) t
| tle_vis : forall e k1 k2, (forall a, tle (k1 a) (k2 a)) -> tle (SVis e k1) (SVis e k2).

Lemma tle_refl {R} (t : M R) : tle t t.
Proof. induction t; constructor; auto. Qed.

Lemma tle_trans {R} (t1 t2 t3 : M R) : tle t1 t2 -> tle t2 t3 -> tle t1 t3.
Proof.
  intros H1. revert t3. induction H1 as [r|k t|e k1 k2 Hk IH]; intros t3 H2.
  - exact H2.
  - constructor.
  - inversion H2; subst.
    + constructor.
    + constructor. intros a. apply IH. auto.
Qed.

Lemma follow_tle {R} (t1 t2 : M R) : tle t1 t2 -> forall ans r, follow t1 ans = Some r -> follow t2 ans = Some r.
Proof.
  induction 1 as [r0|k t|e k1 k2 Hk IH]; intros ans r H.
  - exact H.
  - cbn [follow] in H. destruct ans; discriminate H.
  - cbn [follow] in H |- *. destruct e; try exact H; destruct ans as [|a ans']; try discriminate H; apply IH; exact H.
Qed.

Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).

Lemma prun_tle {R} (t1 t2 : M R) : tle t1 t2 -> forall o, tle (prun pans pupd o t1) (prun pans pupd o t2).
Proof.
  unfold prun. induction 1 as [r0|k t|e k1 k2 Hk IH]; intros o; cbn [eruns psel].
  - constructor.
  - constructor.
  - destruct e; cbn [psel]; try (constructor; intros a; apply IH). apply IH.
Qed.
End PRUN.

Definition kle {X Y R} (k k' : X -> Y -> M R) : Prop := forall x y, tle (k x y) (k' x y).
Definition kle1 {X R} (k k' : X -> M R) : Prop := forall x, tle (k x) (k' x).

Ltac mono_case :=
  lazymatch goal with
  | |- tle (match ?c with _ => _ end) _ => destruct c
  end.

Ltac mono_auto cal :=

  first [ lazymatch goal with |- tle ?x ?x => apply tle_refl end
        | cal
        | (apply tle_vis; intros ?); mono_auto cal
        | mono_case; mono_auto cal
        | progress (cbv zeta); mono_auto cal ].

Lemma guard_mono {R} tag c (k k' bail bail' : M R) :
  tle k k' -> tle bail bail' -> tle (guard tag c k bail) (guard tag c k' bail').
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. constructor. intros _. exact HB. Qed.

Lemma bad_answer_mono {R} (b b' : M R) : tle b b' -> tle (bad_answer b) (bad_answer b').
Proof. intros HB. unfold bad_answer. constructor. intros _. exact HB. Qed.

Lemma queue_mono {R} h m st (k k' : mstate -> M R) bail bail' :
  kle1 k k' -> tle bail bail' -> tle (queue h m st k bail) (queue h m st k' bail').
Proof.
  intros HK HB. unfold queue. apply guard_mono; [| exact HB]. apply guard_mono; [| exact HB].
  mono_auto ltac:(first [apply HK | exact HB]).
Qed.

Lemma free_meta_mono {R} m st (k k' : mstate -> M R) bail bail' :
  kle1 k k' -> tle bail bail' -> tle (free_meta m st k bail) (free_meta m st k' bail').
Proof. intros HK HB. unfold free_meta. apply queue_mono; assumption. Qed.

Lemma activate_group_mono {R} m st (k k' : mstate -> Z -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (activate_group m st k bail) (activate_group m st k' bail').
Proof. intros HK HB. unfold activate_group. apply guard_mono; [| exact HB]. cbv zeta. apply HK. Qed.

Lemma am_take_mono {R} st (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_take st k bail) (am_take st k' bail').
Proof. intros HK HB. unfold am_take. mono_auto ltac:(first [apply HK | exact HB]). Qed.

Lemma am_carve_mono {R} st p (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_carve st p k bail) (am_carve st p k' bail').
Proof. intros HK HB. unfold am_carve. cbv zeta. apply am_take_mono; assumption. Qed.

Lemma am_finish_mono {R} st nu (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_finish st nu k bail) (am_finish st nu k' bail').
Proof.
  intros HK HB. unfold am_finish.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_carve_mono; assumption]).
Qed.

Lemma am_after_brk_mono {R} st nu (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (am_after_brk st nu k bail) (am_after_brk st nu k' bail').
Proof.
  intros HK HB. unfold am_after_brk.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_finish_mono; assumption]).
Qed.

Lemma alloc_meta_mono {R} st (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' -> tle (alloc_meta st k bail) (alloc_meta st k' bail').
Proof.
  intros HK HB. unfold alloc_meta.

  generalize (if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st) as st'. intros st'.
  cbv zeta.
  mono_auto ltac:(first [apply HK | exact HB | apply bad_answer_mono; exact HB | apply am_take_mono; assumption | apply am_after_brk_mono; assumption]).
Qed.

Lemma ta_fin_mono {R} st m mask (k k' : mstate -> Z -> M R) :
  kle k k' -> tle (ta_fin st m mask k) (ta_fin st m mask k').
Proof. intros HK. unfold ta_fin. cbv zeta. apply HK. Qed.

Lemma try_avail_mono {R} sc st (k k' : mstate -> Z -> M R) bail bail' :
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

Lemma ag_tail_mono {R} lay st sc m p cnt ai (k k' : mstate -> optr -> M R) :
  kle k k' -> tle (ag_tail lay st sc m p cnt ai k) (ag_tail lay st sc m p cnt ai k').
Proof. intros HK. unfold ag_tail. cbv zeta. apply HK. Qed.

Section AG.
Variable R : Type.
Variable lay : layout_hook.
Variables rec rec' : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.
Hypothesis rec_mono : forall st sc req (k k' : mstate -> Z -> M R) bail bail',
  kle k k' -> tle bail bail' -> tle (rec st sc req k bail) (rec' st sc req k' bail').

Lemma alloc_group_mono st sc req (k k' : mstate -> optr -> M R) bail bail' :
  kle k k' -> tle bail bail' ->
  tle (alloc_group R lay rec st sc req k bail) (alloc_group R lay rec' st sc req k' bail').
Proof.
  intros HK HB. unfold alloc_group. cbv zeta. apply alloc_meta_mono; [| exact HB].
  intros st' mo. destruct mo as [m|]; [| apply HK].
  mono_case.
  -
    match goal with |- tle (let '(_, _) := ?p in _) _ => destruct p as [cnt' needed] end.
    constructor. intros r. mono_case; [apply bad_answer_mono; exact HB|].
    mono_case; [apply free_meta_mono; [intros ?; apply HK| exact HB]|].
    mono_case. cbv zeta. apply ag_tail_mono. exact HK.
  -
    apply rec_mono; [| exact HB]. intros st1 idx.
    mono_case; [apply free_meta_mono; [intros ?; apply HK| exact HB]|].
    mono_case; [| constructor; intros _; exact HB]. cbv zeta. apply ag_tail_mono. exact HK.
Qed.
End AG.

Lemma alloc_slot_mono lay f : forall R st sc req (k k' : mstate -> Z -> M R) bail bail',
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
    cbn [alloc_slot]. apply try_avail_mono; [| exact HB]. intros st1 first.
    destruct (negb (first =? 0)); [apply HK|].
    apply (alloc_group_mono lay (alloc_slot lay f) (alloc_slot lay (S f))); [intros; apply IH; assumption| | exact HB].
    intros st2 go. destruct go as [g|]; [| apply HK]. cbv zeta. apply queue_mono; [intros ?; apply HK| exact HB].
Qed.

Lemma alloc_slot_mono_le lay f f' : (f <= f')%nat -> forall R st sc req (k : mstate -> Z -> M R) bail,
  tle (alloc_slot lay f st sc req k bail) (alloc_slot lay f' st sc req k bail).
Proof.
  induction 1 as [|f' H IH]; intros R st sc req k bail.
  - apply tle_refl.
  - eapply tle_trans; [apply IH|]. apply alloc_slot_mono; [intros ? ?; apply tle_refl| apply tle_refl].
Qed.

Section LEAF.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Lemma alloc_slot_follow_mono lay f f' R st sc req (k : mstate -> Z -> M R) bail o ans r :
  (f <= f')%nat ->
  follow (prun pans pupd o (alloc_slot lay f st sc req k bail)) ans = Some r ->
  follow (prun pans pupd o (alloc_slot lay f' st sc req k bail)) ans = Some r.
Proof. intros Hf H. eapply follow_tle; [apply prun_tle; apply alloc_slot_mono_le; exact Hf| exact H]. Qed.
End LEAF.
