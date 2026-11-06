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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition is_kernel_ev (e : ev) : bool :=
match e with EPeek _ _ _ | EUndef _ => false | _ => true end.

Definition ev_node (e : ev) : option node :=
match e with
| EBrk req => Some (NBrk req)
| EMmap a len prot flags => Some (NMmap a len prot flags)
| EMunmap a len => Some (NMunmap a len)
| EMprotect a len prot => Some (NMprotect a len prot)
| EMremap old ol nl fl => Some (NMremap old ol nl fl)
| _ => None
end.

Definition ev_dec (e : ev) (pbrk : Z) (rsp : resp) : option Z :=
match e with
| EBrk req =>
if req =? 0 then dec_brk0 rsp
else match dec_brk pbrk req rsp with
| Some BrkGrown => Some req | Some BrkSame => Some pbrk | None => None end
| EMmap addr len prot flags =>
if negb (Z.land flags MAP_FIXED_Z =? 0) then
match dec_mmap_fixed addr len rsp with
| Some (FxKept e) => Some (neg_errno e) | Some FxDone => Some addr | Some (FxLost e) => Some (neg_errno e) | None => None end
else if prot =? 0 then
match dec_mmap_none len [] rsp with Some (MmErr e) => Some (neg_errno e) | Some (MmOk x) => Some x | None => None end
else
match dec_mmap len [] rsp with Some (MmErr e) => Some (neg_errno e) | Some (MmOk x) => Some x | None => None end
| EMunmap addr len =>
match dec_munmap addr len rsp with Some (RgErr e) => Some (neg_errno e) | Some (RgDone _) => Some 0 | None => None end
| EMprotect addr len prot =>
match dec_mprotect_rw addr len rsp with Some (RgErr e) => Some (neg_errno e) | Some (RgDone _) => Some 0 | None => None end
| EMremap old ol nl fl =>
match dec_mremap old ol nl [] rsp with
| Some (MrErr e) => Some (neg_errno e) | Some MrInPlace => Some old | Some (MrMoved a) => Some a | None => None end
| _ => None
end.

Definition ev_post_state (e : ev) (rsp : resp) (s : PState) : PState :=
match e with
| EBrk req =>
if req =? 0 then match dec_brk0 rsp with Some r => set_brk_ps r s | None => s end
else match dec_brk (ps_brk s) req rsp with Some BrkGrown => set_brk_ps req s | _ => s end
| _ => s
end.

#[using="Type"] Lemma ev_post_state_m e rsp s : ps_m (ev_post_state e rsp s) = ps_m s.
Proof. destruct e; cbn; try reflexivity. destruct (addr =? 0); [destruct (dec_brk0 rsp)| destruct (dec_brk _ _ rsp) as [[|]|]]; reflexivity. Qed.
#[using="Type"] Lemma ev_post_state_fa e rsp s : ps_fa (ev_post_state e rsp s) = ps_fa s /\ ps_so (ev_post_state e rsp s) = ps_so s.
Proof. destruct e; cbn; auto. destruct (addr =? 0); [destruct (dec_brk0 rsp)| destruct (dec_brk _ _ rsp) as [[|]|]]; auto. Qed.

Section Bridge.
Variable segs : list Segment.

Local Ltac evred H :=
cbn -[at_node evt nret dec_brk0 dec_brk dec_mmap dec_mmap_none dec_mmap_fixed dec_munmap dec_mprotect_rw dec_mremap
set_brk_ps neg_errno Z.eqb Z.land] in H.

#[using="Type"] Lemma ev_step_implM : forall e n s (Q : Z -> PState -> machine_state -> Prop) ms,
ev_node e = Some n -> is_kernel_ev e = true ->
implM segs (ev_step e) s Q ms ->
evt segs (fun ms1 => at_node segs n ms1 /\
forall rsp z, ev_dec e (ps_brk s) rsp = Some z ->
evt segs (Q z (ev_post_state e rsp s)) (nret ms1 rsp)) ms.
Proof.
intros e n s Q ms Hn Hk H.
destruct e as [req|a len prot flags|a len|a len prot|p c h|w|a ol nl fl]; cbn in Hn, Hk; try discriminate; inversion Hn; subst n; clear Hn;
unfold ev_step, implM, mbind, mget, msys, mupd, mret in H; cbn [ev_dec ev_post_state].
-
destruct (Z.eqb_spec req 0) as [->|NE].
+ evred H.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hc]. split; [exact Hat|].
intros rsp z Hd. specialize (Hc rsp). rewrite Hd in Hc |- *. evred Hc. exact Hc.
+ evred H.
destruct H as (ms0 & Hs0 & [Hat Hc]).
exists ms0. split; [exact Hs0|]. split; [exact Hat|].
intros rsp z Hd. specialize (Hc rsp). destruct (dec_brk (ps_brk s) req rsp) as [[|]|]; try discriminate;
inversion Hd; subst; evred Hc; exact Hc.
-
destruct (negb (Z.land flags MAP_FIXED_Z =? 0)) eqn:EF.
+ evred H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hc]. split; [exact Hat|].
intros rsp z Hd. specialize (Hc rsp). destruct (dec_mmap_fixed a len rsp) as [[e| |e]|]; try discriminate;
inversion Hd; subst; evred Hc; exact Hc.
+ destruct (prot =? 0) eqn:EP.
* evred H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hc]. split; [exact Hat|].
intros rsp z Hd. specialize (Hc rsp). destruct (dec_mmap_none len [] rsp) as [[e|x]|]; try discriminate;
inversion Hd; subst; evred Hc; exact Hc.
* evred H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hc]. split; [exact Hat|].
intros rsp z Hd. specialize (Hc rsp). destruct (dec_mmap len [] rsp) as [[e|x]|]; try discriminate;
inversion Hd; subst; evred Hc; exact Hc.
-
evred H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hc]. split; [exact Hat|].
intros rsp z Hd. specialize (Hc rsp). destruct (dec_munmap a len rsp) as [[e|b]|]; try discriminate;
inversion Hd; subst; evred Hc; exact Hc.
-
evred H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hc]. split; [exact Hat|].
intros rsp z Hd. specialize (Hc rsp). destruct (dec_mprotect_rw a len rsp) as [[e|b]|]; try discriminate;
inversion Hd; subst; evred Hc; exact Hc.
-
evred H. eapply evt_mono; [exact H|]. intros ms1 [Hat Hc]. split; [exact Hat|].
intros rsp z Hd. specialize (Hc rsp). destruct (dec_mremap a ol nl [] rsp) as [[e| |a']|]; try discriminate;
inversion Hd; subst; evred Hc; exact Hc.
Qed.

#[using="Type"] Lemma impl_ebind_inv : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B))
(Q : B -> machine_state -> Prop) ms,
impl segs (at_node segs) (ebind t f) (epost Q) ms ->
impl segs (at_node segs) t (epost (fun a ms' => impl segs (at_node segs) (f a) (epost Q) ms')) ms.
Proof.
intros A B t. induction t as [[|a]|n k IH]; intros f Q ms H; cbn in *.
- apply evt_done. exact I.
- apply evt_done. exact H.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
Qed.

#[using="Type"] Lemma implM_bind_inv : forall {A B} (m : M PState A) (f : A -> M PState B) s Q ms,
implM segs (mbind m f) s Q ms ->
implM segs m s (fun a s' ms' => implM segs (f a) s' Q ms') ms.
Proof.
intros A B m f s Q ms H. unfold implM, mbind in *.
pose proof (impl_ebind_inv (m s) (fun p => f (fst p) (snd p)) _ ms H) as H'.
eapply impl_epost_mono; [exact H'|]. intros [a s'] ms'; cbn; auto.
Qed.

Variable KL : mled -> Z -> Model -> Prop.
Variable vm_only : Model -> Model -> Prop.
Hypothesis vm_only_refl : forall md, vm_only md md.
Hypothesis vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Hypothesis KL_model_ok : forall L pbrk md, KL L pbrk md -> model_ok md.

Definition ev_at (e : ev) (ms1 : machine_state) : Prop :=
match ev_node e with Some n => at_node segs n ms1 | None => False end.

Definition EV_OK : Prop :=
forall e L pbrk md ms1 (J : config -> Prop),
is_kernel_ev e = true ->
NClosed segs J -> KL L pbrk md -> event_pre L e -> ev_at e ms1 ->
(forall rsp z md',
ev_dec e pbrk rsp = Some z -> answer_ok L e z = true ->
KL (event_post L e z) (ps_brk (ev_post_state e rsp (mkPS (minit 0 []) pbrk tt tt))) md' ->
vm_only md md' ->
J (mkCfg (nret ms1 rsp) md')) ->
J (mkCfg ms1 md).
Hypothesis ev_ok : EV_OK.

#[using="Type"] Lemma ev_post_state_brk e rsp s :
ps_brk (ev_post_state e rsp s) = ps_brk (ev_post_state e rsp (mkPS (minit 0 []) (ps_brk s) tt tt)).
Proof.
destruct e; cbn; try reflexivity. destruct (addr =? 0); [destruct (dec_brk0 rsp)| destruct (dec_brk _ _ rsp) as [[|]|]]; reflexivity.
Qed.

#[using="Type"] Lemma event_pre_kernel L e : event_pre L e -> is_kernel_ev e = true.
Proof. destruct e; cbn; intros H; auto; contradiction. Qed.

#[using="vm_only_refl vm_only_trans KL_model_ok ev_ok"] Theorem membed_realizes {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) s Q ms md L T,
implM segs (membed t) s Q ms ->
ctree_ok L t Post ->
KL L (ps_brk s) md ->
(forall r s' ms' L' md',
Q r s' ms' -> Post L' r -> cpath L t L' r ->
ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
KL L' (ps_brk s') md' -> vm_only md md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg ms md) T.
Proof.
intros t. induction t as [r|e k IH]; intros Post s Q ms md L T H CT HK HQ.
-
cbn [membed] in H. unfold implM, mret in H. cbn [impl] in H.
apply rz_evt; [exact (KL_model_ok _ _ _ HK)|].
eapply evt_mono; [exact H|]. intros ms' HQ'. cbn in HQ'. cbn in CT.
exact (HQ r s ms' L md HQ' CT (cpath_ret L r) eq_refl eq_refl eq_refl HK (vm_only_refl md)).
-
cbn [membed] in H. apply implM_bind_inv in H.
cbn in CT. destruct CT as [PRE CT].
pose proof (event_pre_kernel L e PRE) as KE.
assert (Hn : exists n, ev_node e = Some n) by (destruct e; cbn in KE |- *; try discriminate; eauto).
destruct Hn as [n Hn].
pose proof (ev_step_implM e n s _ ms Hn KE H) as HE.
apply rz_evt; [exact (KL_model_ok _ _ _ HK)|].
eapply evt_mono; [exact HE|]. intros ms1 [Hat Hc]. unfold RZ.
apply (ev_ok e L (ps_brk s) md ms1 (fun c => realizes segs c T) KE (nclosed_realizes segs T) HK PRE).
{ unfold ev_at. rewrite Hn. exact Hat. }
intros rsp z md' Hd Hok HK' HV.
specialize (Hc rsp z Hd).

apply rz_evt; [exact (KL_model_ok _ _ _ HK')|].
eapply evt_mono; [exact Hc|]. intros ms2 H2. unfold RZ.
eapply (IH z Post (ev_post_state e rsp s) Q ms2 md' (event_post L e z) T).
+ exact H2.
+ apply CT. exact Hok.
+ rewrite ev_post_state_brk. exact HK'.
+ intros r s' ms' L' md'' HQ' HP CP Em Efa Eso HK'' HV'.
eapply (HQ r s' ms' L' md''); eauto.
* econstructor; eauto.
* rewrite Em. apply ev_post_state_m.
* rewrite Efa. apply (proj1 (ev_post_state_fa e rsp s)).
* rewrite Eso. apply (proj2 (ev_post_state_fa e rsp s)).
Qed.

End Bridge.

End RC__1.
