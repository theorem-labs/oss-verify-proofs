(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Local Open Scope Z_scope.

Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.

Lemma steq_trans {E A R} (t1 t2 t3 : stree E A R) : steq t1 t2 -> steq t2 t3 -> steq t1 t3.
Proof.
  intros H1 H2. apply strel_eq_steq. apply strel_eq_steq in H1. apply strel_eq_steq in H2.
  eapply strel_trans_eq; [exact H1| exact H2].
Qed.

Lemma steq_sbind {E A R S} (t1 t2 : stree E A R) (f1 f2 : R -> stree E A S) :
  steq t1 t2 -> (forall r, steq (f1 r) (f2 r)) -> steq (sbind t1 f1) (sbind t2 f2).
Proof.
  intros Ht Hf. apply strel_eq_steq. eapply (strel_sbind (RR := eq)); [apply strel_eq_steq; exact Ht|].
  intros r1 r2 ->. apply strel_eq_steq. apply Hf.
Qed.

Lemma eruns_steq {E A O R} (sel : O -> E -> option A) (upd : O -> E -> A -> O) (t1 t2 : stree E A R) :
  steq t1 t2 -> forall o, steq (eruns sel upd o t1) (eruns sel upd o t2).
Proof.
  induction 1 as [r|e k1 k2 Hk IH]; intros o; cbn [eruns].
  - constructor.
  - destruct (sel o e) as [a|]; [apply IH|]. constructor. intros a. apply IH.
Qed.

Definition kS {X Y : Type} : X -> Y -> Malloc.M (option (X * Y)) := fun x y => SRet (Some (x, y)).
Definition bS {T : Type} : Malloc.M (option T) := SRet None.
Definition KF {X Y R : Type} (k : X -> Y -> Malloc.M R) (bail : Malloc.M R) (r : option (X * Y)) : Malloc.M R :=
  match r with Some (x, y) => k x y | None => bail end.

Definition kS1 {X : Type} : X -> Malloc.M (option X) := fun x => SRet (Some x).
Definition KF1 {X R : Type} (k : X -> Malloc.M R) (bail : Malloc.M R) (r : option X) : Malloc.M R :=
  match r with Some x => k x | None => bail end.

Ltac nat_leaf := cbn [sbind KF KF1 kS kS1 bS]; apply steq_refl.
Ltac nat_vis := cbn [sbind]; apply steq_vis; intros ?.
Ltac nat_case :=
  lazymatch goal with
  | |- steq _ (sbind (match ?c with _ => _ end) _) => destruct c
  end.

Ltac nat_call NAT :=
  eapply steq_trans; [apply NAT|];
  eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
  apply steq_sbind; [apply steq_refl|];
  intros [[? ?]|]; cbn [KF sbind].
Ltac nat_call1 NAT :=
  eapply steq_trans; [apply NAT|];
  eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply NAT| intros ?; apply steq_refl]| apply sbind_assoc]];
  apply steq_sbind; [apply steq_refl|];
  intros [?|]; cbn [KF1 sbind].

Lemma guard_nat {X Y R} tag c (K : Malloc.M R) (K' : Malloc.M (option (X * Y))) bail f :
  steq K (sbind K' f) -> steq bail (f None) ->
  steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

Lemma guard_nat1 {X R} tag c (K : Malloc.M R) (K' : Malloc.M (option X)) bail f :
  steq K (sbind K' f) -> steq bail (f None) ->
  steq (guard tag c K bail) (sbind (guard tag c K' bS) f).
Proof. intros HK HB. unfold guard. destruct c; [exact HK|]. nat_vis. cbn [sbind bS]. exact HB. Qed.

Lemma queue_nat {R} h m st (k : mstate -> Malloc.M R) bail :
  steq (queue h m st k bail) (sbind (queue h m st kS1 bS) (KF1 k bail)).
Proof.
  unfold queue. apply guard_nat1; [|nat_leaf]. apply guard_nat1; [|nat_leaf].
  nat_case; cbv zeta; [destruct (m_prev _)|]; nat_leaf.
Qed.

Lemma free_meta_nat {R} m st (k : mstate -> Malloc.M R) bail :
  steq (free_meta m st k bail) (sbind (free_meta m st kS1 bS) (KF1 k bail)).
Proof. unfold free_meta. apply queue_nat. Qed.

Lemma activate_group_nat {R} m st (k : mstate -> Z -> Malloc.M R) bail :
  steq (activate_group m st k bail) (sbind (activate_group m st kS bS) (KF k bail)).
Proof. unfold activate_group. apply guard_nat; [|nat_leaf]. cbv zeta. nat_leaf. Qed.

Ltac nat_auto cal :=
  first [ nat_leaf
        | cal
        | nat_vis; nat_auto cal
        | nat_case; nat_auto cal
        | progress (cbv zeta); nat_auto cal ].

Lemma am_take_nat {R} st (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_take st k bail) (sbind (am_take st kS bS) (KF k bail)).
Proof. unfold am_take. nat_auto fail. Qed.

Lemma am_carve_nat {R} st p (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_carve st p k bail) (sbind (am_carve st p kS bS) (KF k bail)).
Proof. unfold am_carve. cbv zeta. apply am_take_nat. Qed.

Lemma am_finish_nat {R} st nu (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_finish st nu k bail) (sbind (am_finish st nu kS bS) (KF k bail)).
Proof. unfold am_finish, bad_answer. nat_auto ltac:(apply am_carve_nat). Qed.

Lemma am_after_brk_nat {R} st nu (k : mstate -> optr -> Malloc.M R) bail :
  steq (am_after_brk st nu k bail) (sbind (am_after_brk st nu kS bS) (KF k bail)).
Proof. unfold am_after_brk, bad_answer. nat_auto ltac:(apply am_finish_nat). Qed.

Lemma alloc_meta_nat {R} st (k : mstate -> optr -> Malloc.M R) bail :
  steq (alloc_meta st k bail) (sbind (alloc_meta st kS bS) (KF k bail)).
Proof.
  unfold alloc_meta, bad_answer. nat_auto ltac:(first [apply am_take_nat | apply am_after_brk_nat]).
Qed.

Lemma ta_fin_nat {R} st m mask (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) :
  steq (ta_fin st m mask k) (sbind (ta_fin st m mask kS) (KF k bail)).
Proof. unfold ta_fin. cbv zeta. nat_leaf. Qed.

Lemma try_avail_nat {R} sc st (k : mstate -> Z -> Malloc.M R) bail :
  steq (try_avail sc st k bail) (sbind (try_avail sc st kS bS) (KF k bail)).
Proof.
  unfold try_avail. nat_case; [|nat_leaf]. cbv zeta. nat_case; [apply ta_fin_nat|].
  nat_case.
  - destruct p as [st1 m1]. nat_case. destruct p as [st2 m2]. nat_case.
    eapply steq_trans; [apply activate_group_nat|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply activate_group_nat| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[st4 mask]|]; cbn [KF sbind]; [|nat_leaf].
    apply guard_nat; [apply ta_fin_nat| nat_leaf].
  - nat_case; [nat_leaf|]. nat_vis. nat_leaf.
Qed.

Lemma ag_tail_nat {R} lay st sc m p cnt ai (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) :
  steq (ag_tail lay st sc m p cnt ai k) (sbind (ag_tail lay st sc m p cnt ai kS) (KF k bail)).
Proof. unfold ag_tail. cbv zeta. nat_leaf. Qed.

Section AG.
Variable lay : layout_hook.
Variable rec : forall R, mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R.
Hypothesis rec_nat : forall R st sc req (k : mstate -> Z -> Malloc.M R) bail,
  steq (rec R st sc req k bail) (sbind (rec _ st sc req kS bS) (KF k bail)).

#[using="rec_nat"] Lemma alloc_group_nat {R} st sc req (k : mstate -> optr -> Malloc.M R) bail :
  steq (alloc_group R lay (rec R) st sc req k bail)
       (sbind (alloc_group _ lay (rec _) st sc req kS bS) (KF k bail)).
Proof.
  unfold alloc_group, bad_answer. cbv zeta. nat_call (@alloc_meta_nat); [|nat_leaf].
  nat_case; [|nat_leaf]. nat_case.
  -
    match goal with |- steq _ (sbind (let '(_, _) := ?p in _) _) => destruct p as [cnt' needed] end.
    nat_vis. nat_case; [nat_vis; nat_leaf|]. nat_case.
    + nat_call1 (@free_meta_nat); nat_leaf.
    + nat_case. cbv zeta. apply ag_tail_nat.
  -
    nat_call rec_nat; [|nat_leaf]. nat_case.
    + nat_call1 (@free_meta_nat); nat_leaf.
    + nat_case; [|nat_vis; nat_leaf]. cbv zeta. apply ag_tail_nat.
Qed.
End AG.

Lemma alloc_slot_nat lay fuel : forall R st sc req (k : mstate -> Z -> Malloc.M R) bail,
  steq (alloc_slot lay fuel st sc req k bail) (sbind (alloc_slot lay fuel st sc req kS bS) (KF k bail)).
Proof.
  induction fuel as [|f IH]; intros R st sc req k bail.
  - cbn [alloc_slot]. nat_vis. nat_leaf.
  - cbn [alloc_slot]. nat_call (@try_avail_nat); [|nat_leaf]. nat_case; [nat_leaf|].
    eapply steq_trans; [apply (alloc_group_nat lay (fun R => @alloc_slot R lay f) IH)|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply (alloc_group_nat lay (fun R => @alloc_slot R lay f) IH)| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[st2 go]|]; cbn [KF sbind]; [|nat_leaf].
    nat_case; [|nat_leaf]. cbv zeta. nat_call1 (@queue_nat); nat_leaf.
Qed.

Section FG.
Variable dec : forall R, decoder R.
Hypothesis dec_nat : forall R st p (k : aptr -> Z -> Malloc.M R) bail,
  steq (dec R st p k bail) (sbind (dec _ st p (fun m i => SRet (Some (m, i))) bS) (KF k bail)).
Variable rec : forall R, mstate -> aptr -> Z -> (mstate -> mapinfo -> Malloc.M R) -> Malloc.M R -> Malloc.M R.
Hypothesis rec_nat : forall R st g i (k : mstate -> mapinfo -> Malloc.M R) bail,
  steq (rec R st g i k bail) (sbind (rec _ st g i kS bS) (KF k bail)).

#[using="dec_nat rec_nat"] Lemma free_group_nat {R} st g (k : mstate -> mapinfo -> Malloc.M R) bail :
  steq (free_group R (dec R) (rec R) st g k bail) (sbind (free_group _ (dec _) (rec _) st g kS bS) (KF k bail)).
Proof.
  unfold free_group. cbv zeta. nat_case; [| nat_vis; nat_leaf]. nat_case.
  - nat_call1 (@free_meta_nat); nat_leaf.
  - eapply steq_trans; [apply dec_nat|].
    eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply dec_nat| intros ?; apply steq_refl]| apply sbind_assoc]].
    apply steq_sbind; [apply steq_refl|]. intros [[m idx]|]; cbn [KF sbind]; [|nat_leaf].
    nat_call rec_nat; [|nat_leaf]. nat_call1 (@free_meta_nat); nat_leaf.
Qed.
End FG.

Lemma dec_slots_nat R st p (k : aptr -> Z -> Malloc.M R) bail :
  steq (dec_slots st p k bail) (sbind (dec_slots st p (fun m i => SRet (Some (m, i))) bS) (KF k bail)).
Proof. unfold dec_slots. nat_case; [destruct p0; nat_leaf| nat_vis; nat_leaf]. Qed.

Lemma nontrivial_free_nat fuel : forall R st g i (k : mstate -> mapinfo -> Malloc.M R) bail,
  steq (nontrivial_free dec_slots fuel st g i k bail) (sbind (nontrivial_free dec_slots fuel st g i kS bS) (KF k bail)).
Proof.
  induction fuel as [|f IH]; intros R st g i k bail.
  - cbn [nontrivial_free]. nat_vis. nat_leaf.
  - cbn [nontrivial_free]. cbv zeta. nat_case.
    + nat_case.
      * unfold guard. nat_case; [| nat_vis; nat_leaf]. cbv zeta. nat_case; [nat_case|].
        -- eapply steq_trans; [apply activate_group_nat|].
           eapply steq_trans; [| apply steq_sym; eapply steq_trans; [eapply steq_sbind; [apply activate_group_nat| intros ?; apply steq_refl]| apply sbind_assoc]].
           apply steq_sbind; [apply steq_refl|]. intros [[st4 mask]|]; cbn [KF sbind]; [|nat_leaf].
           apply (free_group_nat (fun R => @dec_slots R) dec_slots_nat (fun R => @nontrivial_free R dec_slots f) (IH)).
        -- apply (free_group_nat (fun R => @dec_slots R) dec_slots_nat (fun R => @nontrivial_free R dec_slots f) (IH)).
        -- apply (free_group_nat (fun R => @dec_slots R) dec_slots_nat (fun R => @nontrivial_free R dec_slots f) (IH)).
      * apply (free_group_nat (fun R => @dec_slots R) dec_slots_nat (fun R => @nontrivial_free R dec_slots f) (IH)).
    + nat_case.
      * unfold guard. nat_case; [| nat_vis; nat_leaf]. cbv zeta. nat_case; [| nat_leaf]. nat_call1 (@queue_nat); nat_leaf.
      * nat_leaf.
Qed.
