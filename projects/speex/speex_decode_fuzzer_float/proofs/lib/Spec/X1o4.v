(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1qv X1ri X1r3 X1r4
X1ns X1r8 X1nu X1ob X1o3 X1o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition fstable (K : assnE PState) : Prop :=
forall s mo tr s' mo', K s mo tr -> ps_so s' = ps_so s -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> K s' mo' tr.

Definition fstable2 (K : PState -> Model -> Prop) : Prop :=
forall s mo s' mo', K s mo -> ps_so s' = ps_so s -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> K s' mo'.

Lemma TR_fstable : forall (K : PState -> Model -> Prop) tr0 q, fstable2 K -> fstable (TR K tr0 q).
Proof. intros K tr0 q HK s mo tr s' mo' [H ->] Hso Hfd Hfs. split; [eapply HK; eauto| reflexivity]. Qed.

Section Embed.
Variable sel : option bool.
Variable X : list event -> Prop.

Lemma ev_step_E : forall ceil e (K : assnE PState), fstable K ->
mspecE sel X K (ev_step ceil e) (fun z s mo tr => K s mo tr /\ okans e z).
Proof.
intros ceil e K HK.
assert (Hupd : forall v, mspecE sel X K (mupd (set_brk_ps v)) (fun _ => K)).
{ intros v. apply mspecE_upd. intros s mo tr H. eapply HK; [exact H| reflexivity| reflexivity| reflexivity]. }
assert (Hmm : forall n A (dec : resp -> option A), is_mm n -> mspecE sel X K (msys n dec) (fun _ => K)).
{ intros n A dec Hn. apply msysE_mm; [exact Hn|]. intros s mo tr rsp mo' a HKs Hfd Hfs _ _.
eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]. }
destruct e as [req|addr len prot flags|addr len|addr len prot|p c h|w]; cbn [ev_step].
- destruct (req =? 0).
+ eapply mspecE_seq; [apply Hmm; exact I|]. intros r. eapply mspecE_seq; [apply Hupd|]. intros _.
apply mspecE_ret. intros s mo tr H. split; [exact H| exact I].
+ eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0); [apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
eapply mspecE_bind.
{ apply (msysE_mm sel X (NBrk req) _ (fun s mo tr => K s mo tr /\ s = s0) (fun _ s mo tr => K s mo tr /\ s = s0)); [exact I|].
intros s mo tr rsp mo' a [HKs ->] Hfd Hfs _ _. split; [eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]| reflexivity]. }
intros [|].
* eapply mspecE_seq; [eapply mspecE_pre; [apply Hupd| intros s mo tr [H _]; exact H]|]. intros _.
apply mspecE_ret. intros s mo tr H. split; [exact H| exact I].
* apply mspecE_ret. intros s mo tr [H _]. split; [exact H| exact I].
- destruct (negb (Z.land flags MAP_FIXED_Z =? 0)) eqn:Ef.
+ eapply mspecE_seq; [apply Hmm; exact I|]. intros a.
apply mspecE_ret. intros s mo tr H. split; [exact H|]. cbn [okans].
change MAP_FIXED with MAP_FIXED_Z. rewrite <- (negb_involutive (Z.land flags MAP_FIXED_Z =? 0)), Ef. discriminate.
+ apply negb_false_iff in Ef. pose proof Ef as Ef'. apply Z.eqb_eq in Ef'. destruct (prot =? 0).
* eapply mspecE_bind.
{ apply (msysE_mm sel X (NMmap addr len prot flags) _ K (fun a s mo tr => K s mo tr /\ exists x, a = MmOk x /\ is_err x = false)); [exact I|].
intros s mo tr rsp mo' a HKs Hfd Hfs Hok Hd. split; [eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]|].
cbn [ans_ok] in Hok. specialize (Hok Ef').
destruct a as [e|x]; [exfalso; exact (dec_mmap_none_MmErr _ _ _ _ _ Hd Hok)|].
exists x. split; [reflexivity|]. rewrite (dec_mmap_none_MmOk _ _ _ _ _ Hd). apply is_err_errno_none. exact Hok. }
intros a. apply mspecE_ret. intros s mo tr [H (x & -> & Hx)]. split; [exact H|]. intros _. exact Hx.
* eapply mspecE_bind.
{ apply (msysE_mm sel X (NMmap addr len prot flags) _ K (fun a s mo tr => K s mo tr /\ exists x, a = MmOk x /\ is_err x = false)); [exact I|].
intros s mo tr rsp mo' a HKs Hfd Hfs Hok Hd. split; [eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]|].
cbn [ans_ok] in Hok. specialize (Hok Ef').
destruct a as [e|x]; [exfalso; exact (dec_mmap_MmErr _ _ _ _ _ Hd Hok)|].
exists x. split; [reflexivity|]. rewrite (dec_mmap_MmOk _ _ _ _ _ Hd). apply is_err_errno_none. exact Hok. }
intros a. apply mspecE_ret. intros s mo tr [H (x & -> & Hx)]. split; [exact H|]. intros _. exact Hx.
- eapply mspecE_seq; [apply Hmm; exact I|]. intros a.
apply mspecE_ret. intros s mo tr H. split; [exact H| exact I].
- eapply mspecE_bind.
{ apply (msysE_mm sel X (NMprotect addr len prot) _ K (fun a s mo tr => K s mo tr /\ exists b, a = RgDone b)); [exact I|].
intros s mo tr rsp mo' a HKs Hfd Hfs Hok Hd. split; [eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]|].
cbn [ans_ok] in Hok. destruct a as [e|b]; [exfalso; exact (dec_mprotect_rw_RgErr _ _ _ _ Hd Hok)| eauto]. }
intros a. apply mspecE_ret. intros s mo tr [H (b & ->)]. split; [exact H| reflexivity].
- apply mspecE_munr.
- apply mspecE_munr.
Qed.

Lemma membed_E : forall {R} ceil (t : stree ev Z R) (P : R -> Prop) (K : assnE PState),
fstable K -> oktree t P -> mspecE sel X K (membed ceil t) (fun r s mo tr => K s mo tr /\ P r).
Proof.
intros R ceil t. induction t as [r|e k IH]; intros P K HK Ht; cbn [membed].
- apply mspecE_ret. intros s mo tr H. split; [exact H| exact Ht].
- assert (Hpk : match e with EPeek _ _ _ | EUndef _ => True | _ => False end \/ forall z, okans e z -> oktree (k z) P).
{ cbn [oktree] in Ht. destruct e as [a|a len prot flags|a len|a len prot|p c h|w]; cbn [okans]; [right..|left; exact I|left; exact I].
- intros z _. exact (Ht z).
- destruct (Z.land flags MAP_FIXED =? 0) eqn:E; intros z Hz; [exact (Ht z (Hz eq_refl))| exact (Ht z)].
- intros z _. exact (Ht z).
- intros z ->. exact Ht. }
destruct Hpk as [Hpk|Hpk].
+ destruct e; try contradiction; intros s mo tr _; exact I.
+ eapply mspecE_bind; [apply ev_step_E; exact HK|]. intros z. apply mspecE_pure. intros Hz.
apply IH; [exact HK| exact (Hpk z Hz)].
Qed.

Lemma raw_malloc_E : forall n (K : assnE PState), fstable K -> size_overflows n = false ->
mspecE sel X K (raw_malloc n) (fun r s mo tr => K s mo tr /\ r <> None).
Proof.
intros n K HK Hn. unfold raw_malloc.
eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0);
[apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
eapply mspecE_bind.
{ eapply mspecE_pre; [apply membed_E; [exact HK| apply cmalloc_ok; exact Hn]| intros s mo tr [H _]; exact H]. }
intros [st' p]. cbv beta iota. apply mspecE_pure. intros Hp. cbn [snd] in Hp.
destruct p as [slot|]; [|contradiction].
destruct (slot_top st' slot).
- eapply mspecE_seq with (R := K).
{ apply mspecE_upd. intros s mo tr H. eapply HK; [exact H| reflexivity| reflexivity| reflexivity]. }
intros _. apply mspecE_ret. intros s mo tr H. split; [exact H| discriminate].
- eapply mspecE_seq with (R := K).
{ apply mspecE_upd. intros s mo tr H. eapply HK; [exact H| reflexivity| reflexivity| reflexivity]. }
intros _. apply mspecE_ret. intros s mo tr H. split; [exact H| discriminate].
Qed.

Lemma cmalloc_ovf : forall cs n, size_overflows n = true -> cmalloc cs n = SRet (strip cs, None).
Proof. intros cs n Hn. unfold cmalloc, malloc_core. rewrite Hn. reflexivity. Qed.

Lemma raw_malloc_ovf_E : forall n (K : assnE PState), fstable K -> size_overflows n = true ->
mspecE sel X K (raw_malloc n) (fun r s mo tr => K s mo tr /\ r = None).
Proof.
intros n K HK Hn. unfold raw_malloc.
eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0);
[apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
rewrite (cmalloc_ovf _ _ Hn). cbn [membed].
eapply mspecE_bind with (Q1 := fun r s mo tr => K s mo tr /\ snd r = None).
{ apply mspecE_ret. intros s mo tr [H _]. split; [exact H| reflexivity]. }
intros [st' p]. apply mspecE_pure. cbn [snd]. intros ->.
eapply mspecE_seq with (R := K).
{ apply mspecE_upd. intros s mo tr H. eapply HK; [exact H| reflexivity| reflexivity| reflexivity]. }
intros _. apply mspecE_ret. intros s mo tr H. split; [exact H| reflexivity].
Qed.

Lemma raw_free_E : forall p (K : assnE PState), fstable K -> mspecE sel X K (raw_free p) (fun _ => K).
Proof.
intros p K HK. unfold raw_free.
eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0);
[apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
eapply mspecE_bind.
{ eapply mspecE_pre; [apply membed_E; [exact HK| apply oktree_true]| intros s mo tr [H _]; exact H]. }
intros st'. apply mspecE_upd. intros s mo tr [H _]. eapply HK; [exact H| reflexivity| reflexivity| reflexivity].
Qed.

End Embed.

Section RelAlloc.
Variable sel : option bool.
Variable X : list event -> Prop.
Variable K : PState -> Model -> Prop.
Hypothesis HK : fstable2 K.

Local Notation REL := (X1o3.REL sel X K).

Lemma p_overflows_eq : forall n, p_overflows n = size_overflows n.
Proof. reflexivity. Qed.

Lemma REL_raw_malloc : forall n, REL er_opt (raw_malloc n) (p_malloc n).
Proof.
intros n. constructor. intros tr0 q. destruct (size_overflows n) eqn:Hn.
- eapply mspecE_post; [apply raw_malloc_ovf_E; [apply TR_fstable; exact HK| exact Hn]|].
intros r s mo tr [HT ->]. exists q. split; [|exact HT]. unfold p_malloc. rewrite p_overflows_eq, Hn. reflexivity.
- eapply mspecE_post; [apply raw_malloc_E; [apply TR_fstable; exact HK| exact Hn]|].
intros r s mo tr [HT Hr]. exists q. split; [|exact HT]. unfold p_malloc. rewrite p_overflows_eq, Hn.
destruct r; [reflexivity| contradiction].
Qed.

Lemma REL_raw_calloc : forall m n, REL er_opt (raw_calloc m n) (p_calloc m n).
Proof.
intros m n. unfold raw_calloc, p_calloc. destruct (negb (n =? 0) && ((2 ^ 64 - 1) / n <? m)).
- apply REL_ret. reflexivity.
- apply REL_raw_malloc.
Qed.

Lemma REL_raw_free : forall p, REL (fun u : unit => u) (raw_free p) (p_free tt).
Proof.
intros p. constructor. intros tr0 q. eapply mspecE_post; [apply raw_free_E; apply TR_fstable; exact HK|].
intros [] s mo tr HT. exists q. split; [reflexivity| exact HT].
Qed.

Lemma REL_raw_realloc : forall p n, REL er_opt (raw_realloc p n) (p_realloc tt n).
Proof.
intros p n. constructor. intros tr0 q. pose proof (TR_fstable K tr0 q HK) as HT. unfold raw_realloc, p_realloc. rewrite p_overflows_eq.
destruct (size_overflows n) eqn:Hn.
{ apply mspecE_ret. intros s mo tr H. exists q. split; [reflexivity| exact H]. }
destruct (negb (ptop p)); [apply mspecE_munr|].
eapply mspecE_bind with (Q1 := fun s0 s mo tr => TR K tr0 q s mo tr /\ s = s0);
[apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0. cbv zeta.
destruct (s_slots (ps_m s0) !! fst p) as [[g idx]|]; [|apply mspecE_munr].
destruct (_ && _ && _).
{ apply mspecE_ret. intros s mo tr [H _]. exists q. split; [reflexivity| exact H]. }
destruct (_ && _); [apply mspecE_munr|].
eapply mspecE_bind.
{ eapply mspecE_pre; [apply raw_malloc_E; [exact HT| exact Hn]| intros s mo tr [H _]; exact H]. }
intros [r|]; [|apply mspecE_pure; intros []; reflexivity].
apply mspecE_pure. intros _.
eapply mspecE_seq; [apply raw_free_E; exact HT|]. intros _.
apply mspecE_ret. intros s mo tr H. exists q. split; [reflexivity| exact H].
Qed.

End RelAlloc.
