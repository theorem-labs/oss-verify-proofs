(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1hv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Section NbSame.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types (st : nb_state ptr) (b : bits_st ptr).

Definition nb_same st (st' : nb_state ptr) : Prop :=
nb_blk st' = nb_blk st /\ nb_innov_save st' = nb_innov_save st.

#[using="Type"] Lemma nb_same_refl : forall st, nb_same st st.
Proof. intros; split; reflexivity. Qed.
#[using="Type"] Lemma nb_same_trans : forall x y z, nb_same x y -> nb_same y z -> nb_same x z.
Proof. intros x y z [A1 A2] [B1 B2]. split; congruence. Qed.

#[using="Type"] Lemma subframe_pure_same : forall sm olp sub st b st' b',
subframe_pure sm olp sub st b = Some (st', b') -> nb_same st st'.
Proof.
intros sm olp sub st b st' b' H. unfold subframe_pure in H.
destruct (sm_ltp_unquant sm) as [k|]; [| discriminate]. destruct (sm_innovation_unquant sm) as [ki|]; [| discriminate].
cbv zeta in H.
match type of H with (if ?c then _ else _) = _ => destruct c end.
- destruct (voc_loop _ _ _); [| discriminate]. injection H as <- _. destruct st; split; reflexivity.
- injection H as <- _. apply nb_same_refl.
Qed.
#[using="Type"] Lemma subframes_pure_same : forall n sub sm olp st b st' b',
subframes_pure n sub sm olp st b = Some (st', b') -> nb_same st st'.
Proof.
induction n as [|n IH]; intros sub sm olp st b st' b' H; cbn [subframes_pure] in H.
- injection H as <- _. apply nb_same_refl.
- destruct (subframe_pure sm olp sub st b) as [[st1 b1]|] eqn:E; [| discriminate].
eapply nb_same_trans; [eapply subframe_pure_same; exact E | eapply IH; exact H].
Qed.
#[using="Type"] Lemma segD_st_same : forall st sm b, nb_same st (segD_st st sm b).
Proof.
intros st sm b. unfold segD_st.
destruct (nb_submodeID st =? 1); [destruct st; split; reflexivity|].
destruct (1 <? nb_submodeID st); [destruct st; split; reflexivity| apply nb_same_refl].
Qed.
#[using="Type"] Lemma nb_end_same : forall st, nb_same st (nb_end st).
Proof. intros st. unfold nb_end. destruct st; split; reflexivity. Qed.
#[using="Type"] Lemma nb_rest_pure_same : forall sm st1 b st' b', nb_rest_pure sm st1 b = Some (st', b') -> nb_same st1 st'.
Proof.
intros sm st1 b st' b' H. unfold nb_rest_pure in H. cbv zeta in H.
destruct (subframes_pure 4 0 sm _ _ _) as [[st3 b3]|] eqn:E; [| discriminate]. injection H as <- _.
eapply nb_same_trans; [apply segD_st_same|]. eapply nb_same_trans; [eapply subframes_pure_same; exact E| apply nb_end_same].
Qed.
End NbSame.

Section Leaves.
Context {RCEIL : RunCeiling}.
Context {St ptr : Type}.
Variable spx_notify : list Z -> M St unit.
Local Notation unpackM := (@bits_unpack_unsigned_M St ptr).
Local Notation advanceM := (@bits_advance_M St ptr).
Local Notation remainingM := (@bits_remaining_M St ptr).
Local Notation peekM := (@bits_peek_M St ptr).
Implicit Types (b : bits_st ptr).

#[using="Type"] Theorem nb_decode_leaves2 : forall (st : nb_state ptr) b s,
mleaves (nb_decode spx_notify unpackM advanceM remainingM st b) s
(fun p => let '(r, st', b') := fst p in -2 <= r <= 0 /\ bits_sim b b' /\ nb_same st st').
Proof.
intros st b s. unfold nb_decode.
eapply mleaves_bind_mono with (P := fun p => search_ok b (fst p)).
{ destruct (negb _); [apply search_leaves | apply mleaves_ret; cbn; apply bits_sim_refl]. }
intros [r b'|m b'] s' H; cbn in H.
- apply mleaves_ret. cbn. destruct H as [[-> | ->] S]; (split; [lia|]); (split; [exact S| apply nb_same_refl]).
- cbv beta iota zeta.
destruct (submode_at nb_submodes (nb_submodeID (set_nb_submodeID st m))) as [sm|] eqn:ES.
+ destruct (nb_submodes_unq _ _ ES) as [HK HI].
change (mleaves (nb_rest sm (set_nb_submodeID st m) b') s'
(fun p => let '(r, st', b'0) := fst p in -2 <= r <= 0 /\ bits_sim b b'0 /\ nb_same st st')).
eapply mleaves_eq; [apply nb_rest_run; assumption|].
destruct (nb_rest_pure sm (set_nb_submodeID st m) b') as [[st2 b2]|] eqn:ER; [| exact I].
cbn. split; [lia|]. split; [eapply bits_sim_trans; [exact H| eapply nb_rest_pure_sim; exact ER]|].
eapply nb_same_trans; [| eapply nb_rest_pure_same; exact ER]. destruct st; split; reflexivity.
+ apply mleaves_ret. cbn. split; [lia|]. split; [exact H|]. destruct st; split; reflexivity.
Qed.

Definition sb_same (s s' : sbd_state ptr) : Prop :=
sbd_innov_save s' = sbd_innov_save s /\ sbd_blk s' = sbd_blk s /\ sbd_mode s' = sbd_mode s.
#[using="Type"] Lemma sb_same_refl : forall s, sb_same s s. Proof. intros; repeat split; reflexivity. Qed.

Ltac mret_bind := apply mleaves_bind; apply mleaves_ret; cbv beta iota delta [fst snd].

#[using="Type"] Lemma sb_decode_isave : forall (s0 : sbd_state ptr) (low : dec_state ptr)
(lowdec : dec_state ptr -> bits_st ptr -> Z -> M St (Z * dec_state ptr * bits_st ptr)) b out st
(PL : (Z * dec_state ptr * bits_st ptr) -> Prop),
(forall low1 st1, mleaves (lowdec low1 b out) st1 (fun p => PL (fst p))) ->
mleaves (sb_decode spx_notify unpackM peekM remainingM s0 low lowdec b out) st
(fun p => let '(r, sl, b') := fst p in let '(s', low') := sl in
sb_same s0 s' /\
(exists rl dl bl, PL (rl, dl, bl) /\ (r = rl \/ r = -2 \/ r = 0) /\ bits_sim bl b')).
Proof.
intros s0 low lowdec b out st PL HL. unfold sb_decode.
destruct (speex_decoder_ctl low (CtlSetInnovationSave (out + sbd_frame_size s0))) as [u low1].
eapply mleaves_bind_mono; [apply HL|]. intros [[rl dl] bl] st1 H1; cbn in H1.
destruct (speex_decoder_ctl dl CtlGetDtxStatus) as [dtx low2].
destruct (negb (rl =? 0)).
{ apply mleaves_ret. cbn. split; [apply sb_same_refl|]. first [ unshelve sf_eexists 3%nat; [ exact (rl) | exact (dl) | exact (bl) | ] | sf_fb; exists rl, dl, bl ]. split; [exact H1|]. split; [left; reflexivity| apply bits_sim_refl]. }

eapply mleaves_bind_mono with
(P := fun p => match fst p with
| inl (s1, b1) => sb_same s0 s1 /\ bits_sim bl b1
| inr (s1, b1) => sb_same s0 s1 /\ bits_sim bl b1
end).
{ destruct (negb (sbd_encode_submode s0 =? 0)).
2: { apply mleaves_ret. cbn. split; [apply sb_same_refl| apply bits_sim_refl]. }
apply mleaves_bind. unfold bits_remaining_M at 1. apply mleaves_ret. cbv beta iota delta [fst snd].
eapply mleaves_bind_mono with (P := fun p => bits_sim bl (snd (fst p))).
{ destruct (0 <? _); [| apply mleaves_ret; cbn; apply bits_sim_refl].
unfold bits_peek_M. apply mleaves_ret. cbn. unfold speex_bits_peek. destruct (_ || _); repeat split; reflexivity. }
intros [w b1] st2 HB; cbn in HB.
eapply mleaves_bind_mono with (P := fun p => sb_same s0 (fst (fst p)) /\ bits_sim bl (snd (fst p))).
{ destruct (negb (w =? 0)).
- apply mleaves_bind. unfold bits_unpack_unsigned_M at 1. apply mleaves_ret. rewrite unpack_eta. cbv beta iota delta [fst snd].
apply mleaves_bind. unfold bits_unpack_unsigned_M at 1. apply mleaves_ret. rewrite unpack_eta. cbv beta iota delta [fst snd].
apply mleaves_ret. cbn. split; [destruct s0; repeat split; reflexivity|].
eapply bits_sim_trans; [exact HB|]. eapply bits_sim_trans; apply ub_sim.
- apply mleaves_ret. cbn. split; [destruct s0; repeat split; reflexivity| exact HB]. }
intros [s1 b2] st3 [HS HB2]; cbn in HS, HB2.
destruct (_ && _).
- apply notify_then. intros s'. cbn. split; assumption.
- apply mleaves_ret. cbn. split; assumption. }
intros [[s1 b1]|[s1 b1]] st2 [HS HB1]; cbn in HS, HB1.
2: { apply mleaves_ret. cbn. split; [exact HS|]. first [ unshelve sf_eexists 3%nat; [ exact (rl) | exact (dl) | exact (bl) | ] | sf_fb; exists rl, dl, bl ]. split; [exact H1|]. split; [right; left; reflexivity| exact HB1]. }
destruct (submode_at (sbm_submodes (sbd_mode s1)) (sbd_submodeID s1)) as [sm|].
- destruct (speex_decoder_ctl low2 CtlGetPiGain) as [u1 low3]. destruct (speex_decoder_ctl low3 CtlGetExc) as [u2 low4].
apply mleaves_bind. eapply mleaves_eq; [apply (lsp_unquant_run (St:=St))|]. cbv beta iota delta [fst snd].
eapply mleaves_bind_mono with (P := fun p => bits_sim bl (fst p)).
{
assert (SF : forall n smx bx stx, mleaves (sb_decode_subframes unpackM n smx bx) stx (fun p => bits_sim bx (fst p))).
{ induction n as [|n IH]; intros smx bx stx; cbn [sb_decode_subframes].
- apply mleaves_ret. cbn. apply bits_sim_refl.
- eapply mleaves_bind_mono with (P := fun p => bits_sim bx (fst p)).
+ unfold sb_decode_subframe. destruct (sm_innovation_unquant smx) as [ki|].
* apply mleaves_bind. unfold bits_unpack_unsigned_M at 1. apply mleaves_ret. rewrite unpack_eta. cbv beta iota delta [fst snd].
apply mleaves_bind. eapply mleaves_eq; [apply (innovation_unquant_run (St:=St))|]. cbv beta iota delta [fst snd].
destruct (negb _).
-- eapply mleaves_eq; [apply (innovation_unquant_run (St:=St))|]. cbn.
eapply bits_sim_trans; [apply ub_sim|]. eapply bits_sim_trans; apply innov_bits_sim.
-- apply mleaves_ret. cbn. eapply bits_sim_trans; [apply ub_sim| apply innov_bits_sim].
* apply mleaves_bind. unfold bits_unpack_unsigned_M at 1. apply mleaves_ret. rewrite unpack_eta. cbv beta iota delta [fst snd].
apply mleaves_ret. cbn. apply ub_sim.
+ intros bx1 sty HB; cbn in HB. eapply mleaves_mono; [apply IH|]. intros [by2 stz] HB2; cbn in HB2 |- *.
eapply bits_sim_trans; [exact HB| exact HB2]. }
eapply mleaves_mono; [apply SF|]. intros [bq stq] HB; cbn in HB |- *.
eapply bits_sim_trans; [exact HB1|]. eapply bits_sim_trans; [apply lsp_bits_sim| exact HB]. }
intros b3 st4 HB3; cbn in HB3. apply mleaves_ret. cbn.
split; [destruct HS as (E1 & E2 & E3); destruct s1; cbn in *; subst; repeat split; reflexivity|].
first [ unshelve sf_eexists 3%nat; [ exact (rl) | exact (dl) | exact (bl) | ] | sf_fb; exists rl, dl, bl ]. split; [exact H1|]. split; [right; right; reflexivity| exact HB3].
- apply mleaves_ret. cbn.
split; [destruct HS as (E1 & E2 & E3); destruct s1; cbn in *; subst; repeat split; reflexivity|].
first [ unshelve sf_eexists 3%nat; [ exact (rl) | exact (dl) | exact (bl) | ] | sf_fb; exists rl, dl, bl ]. split; [exact H1|]. split; [right; right; reflexivity| exact HB1].
Qed.

Definition dec_isave (d : dec_state ptr) : option Z :=
match d with DecNB st => nb_innov_save st | DecSB s _ => sbd_innov_save s end.
Definition dec_blkid (d : dec_state ptr) : ptr :=
match d with DecNB st => nb_blk st | DecSB s _ => sbd_blk s end.

#[using="Type"] Theorem speex_decode_n_leaves : forall n (d : dec_state ptr) b out st,
mleaves (speex_decode_n spx_notify unpackM peekM advanceM remainingM n d b out) st
(fun p => let '(r, d', b') := fst p in
-2 <= r <= 0 /\ bits_sim b b' /\ dec_isave d' = dec_isave d /\ dec_blkid d' = dec_blkid d /\ dec_mode d' = dec_mode d).
Proof.
induction n as [|n IH]; intros d b out st; [apply mleaves_unr|].
cbn [speex_decode_n]. destruct d as [st0|s0 low].
- eapply mleaves_bind_mono; [apply nb_decode_leaves2|]. intros [[r st'] b'] st1 (HR & HB & HS); cbn in HR, HB, HS.
apply mleaves_ret. cbn. destruct HS as [E1 E2]. split; [exact HR|]. split; [exact HB|]. split; [exact E2|]. split; [exact E1| reflexivity].
- eapply mleaves_bind_mono.
{ apply (sb_decode_isave s0 low _ b out st
(fun q => let '(r, d', b') := q in -2 <= r <= 0 /\ bits_sim b b')).
intros low1 st1. eapply mleaves_mono; [apply IH|]. intros [[[r d'] b'] st2] (HR & HB & _). cbn. split; assumption. }
intros [[r [s' low']] b'] st1 [HS HX]; cbn in HS, HX.
first [ sf_destruct 6%nat HX as rl dl bl [HR HBL] Hr HB2 | sf_fb; destruct HX as (rl & dl & bl & [HR HBL] & Hr & HB2) ].
apply mleaves_ret. cbn. destruct HS as (E1 & E2 & E3).
split; [lia|]. split; [eapply bits_sim_trans; [exact HBL| exact HB2]|]. split; [exact E1|]. split; [exact E2|]. cbn [dec_mode]. rewrite E3. reflexivity.
Qed.

#[using="Type"] Corollary speex_decode_leaves : forall (d : dec_state ptr) b out st,
mleaves (speex_decode spx_notify unpackM peekM advanceM remainingM d b out) st
(fun p => let '(r, d', b') := fst p in
-2 <= r <= 0 /\ bits_sim b b' /\ dec_isave d' = dec_isave d /\ dec_blkid d' = dec_blkid d /\ dec_mode d' = dec_mode d).
Proof. intros. unfold speex_decode. apply speex_decode_n_leaves. Qed.
End Leaves.
