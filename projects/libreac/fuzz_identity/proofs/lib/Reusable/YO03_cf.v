(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YO03.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: no single donor found by measurement; 33 of its 123 lines of code match lines of projects/cgif/cgif_file_fuzzer/proofs/lib/YO03.v up to module paths. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0g YO0x YO0d YO0e YO05 YO02 YO0p YO0d_cf.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma roomcf_ibind_all {A B} X : forall (t : itree astate A) (f : A -> itree astate B),
roomcf X t -> (forall a, roomcf X (f a)) -> roomcf X (ibind t f).
Proof using.
induction t as [a | q s k IH | e]; intros f Ht Hf; cbn in *.
- apply Hf.
- destruct Ht as [H1 H2]. split; [exact H1|]. intros z Hz. apply IH; [apply H2; exact Hz | exact Hf].
- exact I.
Qed.
Lemma roomcf_ibind_yields {A B} X (P : A -> Prop) : forall (t : itree astate A) (f : A -> itree astate B),
roomcf X t -> leaves P t -> (forall tr a, yields t tr a -> P a -> roomcf X (f a)) -> roomcf X (ibind t f).
Proof using.
induction t as [a | q s k IH | e]; intros f Ht Hl Hf; cbn in *.
- apply (Hf []); [reflexivity | exact Hl].
- destruct Ht as [H1 H2]. split; [exact H1|]. intros z Hz.
assert (Hz' : answer_ok q z) by (apply canswer_answer_ok, canswer04_canswer; exact Hz).
apply IH; [apply H2; exact Hz | apply Hl; exact Hz' |].
intros tr a Hy HP. apply (Hf ((q, z) :: tr)); [cbn; auto | exact HP].
- exact I.
Qed.
Definition presR {A} (m : M A) : Prop := forall X s, roomcf X (m s).
Lemma presR_bind {A B} (m : M A) (k : A -> M B) : presR m -> (forall a, presR (k a)) -> presR (bind m k).
Proof using.
intros Hm Hk X s. unfold bind. apply roomcf_ibind_all; [exact (Hm X s)|]. intros [a s']. exact (Hk a X s').
Qed.
Lemma presR_ret {A} (a : A) : presR (ret a). Proof using. intros X s. exact I. Qed.
Lemma presR_get : presR get. Proof using. intros X s. exact I. Qed.
Lemma presR_put s1 : presR (put s1). Proof using. intros X s. exact I. Qed.
Lemma presR_modify f : presR (modify f). Proof using. intros X s. exact I. Qed.
Lemma presR_fail {A} f : presR (@fail A f). Proof using. intros X s. exact I. Qed.
Lemma presR_massert b x : presR (massert b x). Proof using. intros X s. destruct b; exact I. Qed.
Lemma presR_mcheck b x : presR (mcheck b x). Proof using. intros X s. destruct b; exact I. Qed.
Lemma presR_askz_junk p : presR (askz (KJunk p)).
Proof using. intros X s. cbn. split; [intros E; discriminate E | intros; exact I]. Qed.
Lemma presR_ask q : charged q = false -> presR (ask q).
Proof using. intros Hq X s. cbn. split; [intros E; rewrite Hq in E; discriminate E | intros; exact I]. Qed.
Lemma presR_upd_region r f : presR (upd_region r f). Proof using. intros X s. exact I. Qed.
End e.
Create HintDb presR.
#[export] Hint Resolve presR_ret presR_get presR_put presR_modify presR_fail presR_massert presR_mcheck presR_askz_junk presR_upd_region : presR.
Ltac cfstep :=
lazymatch goal with
| |- presR (bind _ _) => apply presR_bind; [ | intros ? ]
| |- presR (ret _) => apply presR_ret
| |- presR get => apply presR_get
| |- presR (put _) => apply presR_put
| |- presR (modify _) => apply presR_modify
| |- presR (fail _) => apply presR_fail
| |- presR (massert _ _) => apply presR_massert
| |- presR (mcheck _ _) => apply presR_mcheck
| |- presR (askz (KJunk _)) => apply presR_askz_junk
| |- presR (ask _) => apply presR_ask; reflexivity
| |- presR (match ?x with _ => _ end) => destruct x
| |- presR _ => solve [auto with presR]
end.
Ltac cfgo := repeat (cbv beta iota zeta; cfstep).
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_getm p : presR (getm p). Proof using. unfold getm. cfgo. Qed.
Lemma r_setm p am : presR (setm p am). Proof using. unfold setm. cfgo. Qed.
Lemma r_setslot p x : presR (setslot p x). Proof using. unfold setslot. cfgo. Qed.
Lemma r_get_links p : presR (get_links p). Proof using. unfold get_links. cfgo. Qed.
End j.
#[export] Hint Resolve r_getm r_setm r_setslot r_get_links : presR.
Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_set_links p a b : presR (set_links p a b). Proof using. unfold set_links. cfgo. Qed.
Lemma r_get_head h : presR (get_head h). Proof using. unfold get_head. cfgo. Qed.
Lemma r_set_head h v : presR (set_head h v). Proof using. unfold set_head. cfgo. Qed.
End o.
#[export] Hint Resolve r_set_links r_get_head r_set_head : presR.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_set_prev p a : presR (set_prev p a). Proof using. unfold set_prev. cfgo. Qed.
Lemma r_set_next p a : presR (set_next p a). Proof using. unfold set_next. cfgo. Qed.
End w.
#[export] Hint Resolve r_set_prev r_set_next : presR.
Section y. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_queue h m : presR (queue h m). Proof using. unfold queue. cfgo. Qed.
Lemma r_dequeue h m : presR (dequeue h m). Proof using. unfold dequeue. cfgo. Qed.
End y.
#[export] Hint Resolve r_queue r_dequeue : presR.
Section a0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_dequeue_head h : presR (dequeue_head h). Proof using. unfold dequeue_head. cfgo. Qed.
Lemma r_free_meta m : presR (free_meta m). Proof using. unfold free_meta. cfgo. Qed.
Lemma r_set_usage_of sc v : presR (set_usage_of sc v). Proof using. unfold set_usage_of. cfgo. Qed.
Lemma r_step_seq : presR step_seq. Proof using. unfold step_seq. cfgo. Qed.
Lemma r_record_seq sc : presR (record_seq sc). Proof using. unfold record_seq. cfgo. Qed.
Lemma r_account_bounce sc : presR (account_bounce sc). Proof using. unfold account_bounce. cfgo. Qed.
Lemma r_decay_bounces sc : presR (decay_bounces sc). Proof using. unfold decay_bounces. cfgo. Qed.
End a0.
#[export] Hint Resolve r_dequeue_head r_free_meta r_set_usage_of r_step_seq r_record_seq r_account_bounce r_decay_bounces : presR.
Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_activate_group m : presR (activate_group m). Proof using. unfold activate_group. cfgo. Qed.
End b0.
#[export] Hint Resolve r_activate_group : presR.
Section c0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_try_avail sc : presR (try_avail sc). Proof using. unfold try_avail. cfgo. Qed.
Lemma r_enframe g idx n ctr k : presR (enframe g idx n ctr k). Proof using. unfold enframe. cfgo. Qed.
End c0.
#[export] Hint Resolve r_try_avail r_enframe : presR.
Section d0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_install_group m sc cnt aidx maplen mem sl : presR (install_group m sc cnt aidx maplen mem sl).
Proof using. unfold install_group. cfgo. Qed.
Lemma r_find_frame p : presR (find_frame p). Proof using. unfold find_frame. cfgo. Qed.
Lemma r_forget_frame g i : presR (forget_frame g i). Proof using. unfold forget_frame. cfgo. Qed.
Lemma r_release_slot g i : presR (release_slot g i). Proof using. unfold release_slot. cfgo. Qed.
End d0.
#[export] Hint Resolve r_install_group r_find_frame r_forget_frame r_release_slot : presR.
Section e0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_nontrivial_free f : forall g i, presR (nontrivial_free f g i).
Proof using. induction f as [|f IH]; intros g i; cbn [nontrivial_free]; cfgo. Qed.
End e0.
#[export] Hint Resolve r_nontrivial_free : presR.
Section f0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma r_free p : presR (free p). Proof using. unfold free. cfgo. Qed.
End f0.
#[export] Hint Resolve r_free : presR.
