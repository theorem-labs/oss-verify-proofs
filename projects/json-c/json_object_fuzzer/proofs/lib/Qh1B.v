(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkRc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkRc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn5J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn5J.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition TK (Tn Ts : TSet) (κ : kind) : TSet :=
fun tr => (fst κ = true /\ Tn tr) \/ (snd κ = true /\ Ts tr).

#[using="Type"] Lemma TK_KN Tn Ts : t_eq (TK Tn Ts KN) Tn.
Proof. intros tr. unfold TK, KN. cbn. intuition. discriminate. Qed.
#[using="Type"] Lemma TK_KS Tn Ts : t_eq (TK Tn Ts KS) Ts.
Proof. intros tr. unfold TK, KS. cbn. intuition. discriminate. Qed.
#[using="Type"] Lemma TK_KNS Tn Ts : t_eq (TK Tn Ts KNS) (t_alt2 Tn Ts).
Proof. intros tr. unfold TK, KNS, t_alt2. cbn. intuition. Qed.
#[using="Type"] Lemma TK_single Tn Ts (b : bool) : t_eq (TK Tn Ts (ksingle b)) (if b then Ts else Tn).
Proof. destruct b; [apply TK_KS| apply TK_KN]. Qed.
#[using="Type"] Lemma TK_mono Tn Ts a b tr : kle a b -> TK Tn Ts a tr -> TK Tn Ts b tr.
Proof. intros [L1 L2] [[H1 H2]|[H1 H2]]; [left| right]; auto. Qed.
#[using="Type"] Lemma TK_join Tn Ts a b tr : TK Tn Ts (kjoin a b) tr <-> TK Tn Ts a tr \/ TK Tn Ts b tr.
Proof.
unfold TK, kjoin. cbn. rewrite !Bool.orb_true_iff. intuition.
Qed.

Section BridgeS.
Variable segs : list Segment.
Variable KL : mled -> Z -> Model -> Prop.
Variable vm_only : Model -> Model -> Prop.
Hypothesis vm_only_refl : forall md, vm_only md md.
Hypothesis vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Hypothesis KL_model_ok : forall L pbrk md, KL L pbrk md -> model_ok md.

Variable BUD : Model -> Z -> nat -> Prop.
Variable FEAS : ev -> Model -> Prop.
Variable ACC : ev -> Model -> Model -> Prop.
Hypothesis BUD_feas : forall md e W D,
BUD md (W + ecost e) (S D) -> eks e = true -> esz_ok e -> 0 <= W -> egrant e = true -> FEAS e md.
Hypothesis BUD_step : forall md md' e W D,
BUD md (W + ecost e) (S D) -> eks e = true -> esz_ok e -> 0 <= W -> ACC e md md' -> BUD md' W D.
Hypothesis BUD_mono : forall md W D W' D', BUD md W D -> 0 <= W' <= W -> (D' <= D)%nat -> BUD md W' D'.

Definition EVND (e : ev) (L : mled) (pbrk : Z) (md : Model) (ms1 : machine_state) : Prop :=
exists (I : Type) (rspf : I -> resp) (mdf : I -> Model) (zf : I -> Z) (i0 : I),
node_ok segs (mkCfg ms1 md) I (fun _ => []) (fun i => mkCfg (nret ms1 (rspf i)) (mdf i))
/\ (forall i, ev_dec e pbrk (rspf i) = Some (zf i) /\ answer_ok L e (zf i) = true
/\ KL (event_post L e (zf i)) (ps_brk (ev_post_state e (rspf i) (mkPS (minit 0 []) pbrk tt tt))) (mdf i)
/\ vm_only md (mdf i) /\ ACC e md (mdf i))

/\ (egrant e = true -> FEAS e md -> forall i, eclass e (zf i) = true).
Definition EVN : Prop :=
forall e L pbrk md ms1,
eks e = true -> KL L pbrk md -> event_pre L e -> ev_at segs e ms1 -> EVND e L pbrk md ms1.
Hypothesis evn : EVN.

#[using="Type"] Lemma rz_classes : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (U : TSet) (i0 : I),
node_ok segs c I (fun _ => []) nx ->
(forall i, realizes segs (nx i) (T i)) ->
(forall i tr, T i tr -> U tr) ->
(forall tr, U tr -> exists i, T i tr) ->
realizes segs c U.
Proof.
intros c I nx T U i0 Hnode HT Hsub Hcov.
apply (rz_conseq segs c (t_alt (fun i : I => t_emit [] (T i)))).
- apply (rz_node segs c I (fun _ => []) nx T i0 Hnode HT).
- intros tr. split.
+ intros [i Hi]. apply (Hsub i). exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (HT i)) tr) Hi).
+ intros HU. destruct (Hcov tr HU) as [i Hi]. exists i. exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (HT i)) tr) Hi).
Qed.

Section Inv.
Context {R : Type} (isS : R -> bool) (P : R -> Prop) (Wf : Z) (Df : nat).
#[using="Type"] Lemma KSUM_ret_inv L r κ W D : KSUM isS P Wf Df L (SRet r) κ W D -> κ = ksingle (isS r) /\ Wf <= W /\ (Df <= D)%nat /\ P r.
Proof. intros H. inversion H; subst; auto. Qed.
#[using="Type"] Lemma KSUM_ev_inv L e k κ W D : KSUM isS P Wf Df L (SVis e k) κ W D -> event_pre L e ->
exists kf kt W0 D0, eks e = true /\ esz_ok e /\ Wf <= W0 /\ W = W0 + ecost e /\ D = S D0
/\ (forall z, answer_ok L e z = true -> eclass e z = false -> KSUM isS P Wf Df (event_post L e z) (k z) kf W0 D0)
/\ (forall z, answer_ok L e z = true -> eclass e z = true  -> KSUM isS P Wf Df (event_post L e z) (k z) kt W0 D0)
/\ (egrant e = false -> kt = kf)
/\ κ = (if egrant e then kt else kf).
Proof. intros H PRE. inversion H; subst; [| destruct PRE]. exists kf, kt, W0, D0. repeat match goal with |- _ /\ _ => split end; auto. Qed.
End Inv.

#[using="Type"] Lemma eks_kernel e : eks e = true -> is_kernel_ev e = true.
Proof. destruct e; cbn; auto. Qed.
#[using="Type"] Lemma eks_node e : eks e = true -> exists n, ev_node e = Some n.
Proof. destruct e; cbn; intros; try discriminate; eauto. Qed.

#[using="vm_only_refl vm_only_trans KL_model_ok FEAS ACC BUD_feas BUD_step BUD_mono evn"] Theorem membed_realizes_strong {R} (isS : R -> bool) (P : R -> Prop) (Wf : Z) (Df : nat) :
forall (t : stree ev Z R) (Post : mled -> R -> Prop) s Q ms md L (Tn Ts : TSet) κ W D,
implM segs (membed t) s Q ms ->
ctree_ok L t Post ->
KL L (ps_brk s) md ->
BUD md W D -> 0 <= Wf ->
KSUM isS P Wf Df L t κ W D ->
(forall r s' ms' L' md',
Q r s' ms' -> Post L' r -> P r -> cpath L t L' r ->
ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
KL L' (ps_brk s') md' -> vm_only md md' -> BUD md' Wf Df ->
realizes segs (mkCfg ms' md') (if isS r then Ts else Tn)) ->
realizes segs (mkCfg ms md) (TK Tn Ts κ).
Proof.
intros t. induction t as [r|e k IH]; intros Post s Q ms md L Tn Ts κ W D H CT HK HB HWf KSM HQ.
-
cbn [membed] in H. unfold implM, mret in H. cbn [impl] in H.
apply KSUM_ret_inv in KSM as (-> & HW & HD & HPr).
apply rz_evt; [exact (KL_model_ok _ _ _ HK)|].
eapply evt_mono; [exact H|]. intros ms' HQ'. cbn in HQ'. cbn in CT. unfold RZ.
apply (rz_conseq segs _ (if isS r then Ts else Tn)); [| apply t_eq_sym; apply TK_single].
eapply (HQ r s ms' L md HQ' CT HPr (cpath_ret L r) eq_refl eq_refl eq_refl HK (vm_only_refl md)).
eapply BUD_mono; [exact HB| lia| lia].
-
cbn [membed] in H. apply implM_bind_inv in H.
cbn in CT. destruct CT as [PRE CT].
apply (KSUM_ev_inv isS P Wf Df) in KSM as (kf & kt & W0 & D0 & EK & SZ & HW0 & -> & -> & Hf & Ht & Hle & ->); [| exact PRE].
pose proof (eks_kernel e EK) as KE. destruct (eks_node e EK) as [n Hn].
pose proof (ev_step_implM segs e n s _ ms Hn KE H) as HE.
apply rz_evt; [exact (KL_model_ok _ _ _ HK)|].
eapply evt_mono; [exact HE|]. intros ms1 [Hat Hc]. unfold RZ.
destruct (evn e L (ps_brk s) md ms1 EK HK PRE ltac:(unfold ev_at; rewrite Hn; exact Hat))
as (I & rspf & mdf & zf & i0 & NODE & FACTS & CG).

assert (CH : forall i, realizes segs (mkCfg (nret ms1 (rspf i)) (mdf i)) (TK Tn Ts (if eclass e (zf i) then kt else kf))).
{ intros i. destruct (FACTS i) as (Hd & Hok & HK' & HV & HA).
specialize (Hc (rspf i) (zf i) Hd).
apply rz_evt; [exact (KL_model_ok _ _ _ HK')|].
eapply evt_mono; [exact Hc|]. intros ms2 H2. unfold RZ.
assert (HB' : BUD (mdf i) W0 D0) by (eapply BUD_step; eauto; lia).
eapply (IH (zf i) Post (ev_post_state e (rspf i) s) Q ms2 (mdf i) (event_post L e (zf i)) Tn Ts _ W0 D0).
+ exact H2.
+ apply CT. exact Hok.
+ rewrite ev_post_state_brk. exact HK'.
+ exact HB'.
+ exact HWf.
+ destruct (eclass e (zf i)) eqn:EC; [exact (Ht _ Hok EC)| exact (Hf _ Hok EC)].
+ intros r s' ms' L' md'' HQ' HP HPr CP Em Efa Eso HK'' HV' HB''.
eapply (HQ r s' ms' L' md''); eauto.
* econstructor; eauto.
* rewrite Em. apply ev_post_state_m.
* rewrite Efa. apply (proj1 (ev_post_state_fa e (rspf i) s)).
* rewrite Eso. apply (proj2 (ev_post_state_fa e (rspf i) s)). }
apply (rz_classes (mkCfg ms1 md) I _ (fun i => TK Tn Ts (if eclass e (zf i) then kt else kf)) _ i0 NODE CH).
+
intros i tr Hi. destruct (egrant e) eqn:EG.
* assert (HBf : FEAS e md) by (eapply BUD_feas; eauto; lia).
rewrite (CG eq_refl HBf i) in Hi. exact Hi.
* rewrite (Hle eq_refl) in Hi. destruct (eclass e (zf i)); exact Hi.
+
intros tr HU. destruct (egrant e) eqn:EG.
* assert (HBf : FEAS e md) by (eapply BUD_feas; eauto; lia).
exists i0. rewrite (CG eq_refl HBf i0). exact HU.
* exists i0. cbv beta. rewrite (Hle eq_refl). destruct (eclass e (zf i0)); exact HU.
Qed.

End BridgeS.

End RC__1.
