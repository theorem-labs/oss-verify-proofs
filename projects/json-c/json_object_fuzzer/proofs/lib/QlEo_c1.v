(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsjA QEpW QZDE QbrW.
Import ListNotations.
Open Scope bv_scope.

Definition resp := SyscallEffect.
Definition nret (ms : machine_state) (eff : resp) : machine_state :=
advance_past_svc (apply_effect ms eff).

Lemma nret_svc : forall ms eff, ms_svc_pending (nret ms eff) = None.
Proof. reflexivity. Qed.

Module Exc.
#[universes(template)]
Inductive exc (A : Type) : Type := Unr | Ok (a : A).
Arguments Unr {A}.
Arguments Ok {A} a.
End Exc.
Import Exc.

Section ITree.

Variable node : Type.

Inductive itree (R : Type) : Type :=
| Ret (r : R)
| Vis (n : node) (k : resp -> itree R).
Arguments Ret {R} r.
Arguments Vis {R} n k.

Fixpoint bind {A B} (t : itree A) (f : A -> itree B) : itree B :=
match t with
| Ret r => f r
| Vis n k => Vis n (fun x => bind (k x) f)
end.

#[using="Type"] Lemma bind_ret : forall {A B} (r : A) (f : A -> itree B), bind (Ret r) f = f r.
Proof. reflexivity. Qed.

Variable segs : list Segment.

Variable at_node : node -> machine_state -> Prop.

Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.

Variable nsafe : node -> Model -> Prop.

Record node_sound : Prop := {

ns_lazy : forall mo, minv mo -> m_vm_lazy mo = [];

ns_pending : forall n ms, at_node n ms -> ms_svc_pending ms <> None;

ns_complete : forall n ms mo evs X, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
sstep segs (mkCfg ms mo) evs X ->
(exists rsp mo', X = SNext (mkCfg (nret ms rsp) mo') /\ nstep n mo rsp mo' evs)
\/ (exists code mo', X = SNext (mkCfg ms mo') /\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')]);

ns_sound : forall n ms mo rsp mo' evs, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
nstep n mo rsp mo' evs ->
m_halted mo' = None /\ minv mo'
/\ sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo'));
ns_exit : forall n ms mo code mo', at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
nexit n mo code mo' ->
m_halted mo' = Some code /\ sstep segs (mkCfg ms mo) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo'));

ns_progress : forall n ms mo, at_node n ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
(exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo')
}.

Fixpoint impl {R} (t : itree R) (Q : R -> machine_state -> Prop) (ms : machine_state) : Prop :=
match t with
| Ret r => evt segs (Q r) ms
| Vis n k => evt segs (fun ms1 => at_node n ms1 /\ forall rsp, impl (k rsp) Q (nret ms1 rsp)) ms
end.

#[using="Type"] Lemma impl_ret_intro : forall {R} (r : R) Q ms, evt segs (Q r) ms -> impl (Ret r) Q ms.
Proof. intros. exact H. Qed.

#[using="Type"] Lemma impl_mono : forall {R} (t : itree R) (Q Q' : R -> machine_state -> Prop) ms,
impl t Q ms -> (forall r ms', Q r ms' -> Q' r ms') -> impl t Q' ms.
Proof.
induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_mono; eauto.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. eapply IH; eauto.
Qed.

#[using="Type"] Lemma impl_evt : forall {R} (t : itree R) Q P ms,
evt segs P ms -> (forall ms', P ms' -> impl t Q ms') -> impl t Q ms.
Proof.
intros R t Q P ms H K. destruct t; cbn in *; eapply evt_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

#[using="Type"] Lemma impl_bind : forall {A B} (t : itree A) (f : A -> itree B) Q1 Q ms,
impl t Q1 ms -> (forall r ms', Q1 r ms' -> impl (f r) Q ms') -> impl (bind t f) Q ms.
Proof.
induction t as [r|n k IH]; intros f Q1 Q ms H Hf; cbn [bind].
- cbn in H. eapply impl_evt; [exact H|]. intros ms' HQ. exact (Hf _ _ HQ).
- cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Fixpoint ttrace {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
match t with
| Ret _ => tr = []
| Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
\/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ ttrace (k rsp) mo' tr' /\ tr = evs ++ tr')
end.

Fixpoint tsafe {R} (t : itree R) (mo : Model) : Prop :=
match t with
| Ret _ => True
| Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tsafe (k rsp) mo'
end.

Fixpoint tpath {R} (t : itree R) (mo : Model) (tr : list event) (r : R) (mo' : Model) : Prop :=
match t with
| Ret r0 => r0 = r /\ mo' = mo /\ tr = []
| Vis n k => exists rsp mo1 evs tr', nstep n mo rsp mo1 evs /\ tpath (k rsp) mo1 tr' r mo' /\ tr = evs ++ tr'
end.

Fixpoint texit {R} (t : itree R) (mo : Model) (tr : list event) : Prop :=
match t with
| Ret _ => False
| Vis n k => (exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')])
\/ (exists rsp mo' evs tr', nstep n mo rsp mo' evs /\ texit (k rsp) mo' tr' /\ tr = evs ++ tr')
end.

#[using="Type"] Lemma ttrace_split : forall {R} (t : itree R) mo tr,
ttrace t mo tr <-> texit t mo tr \/ exists r mo', tpath t mo tr r mo'.
Proof.
intros R t. induction t as [r|n k IH]; intros mo tr; cbn.
- split.
+ intros ->. right. exists r, mo. repeat split; reflexivity.
+ intros [F|(r' & mo' & _ & _ & ->)]; [destruct F|reflexivity].
- split.
+ intros [Hex|(rsp & mo' & evs & tr' & Hst & Ht & ->)]; [left; left; exact Hex|].
destruct (proj1 (IH rsp mo' tr') Ht) as [Hx|(r & mo'' & Hp)].
* left; right. exists rsp, mo', evs, tr'. repeat split; assumption.
* right. exists r, mo'', rsp, mo', evs, tr'. repeat split; assumption.
+ intros [[Hex|(rsp & mo' & evs & tr' & Hst & Hx & ->)]|(r & mo'' & rsp & mo' & evs & tr' & Hst & Hp & ->)].
* left; exact Hex.
* right. exists rsp, mo', evs, tr'. split; [assumption|]; split; [|reflexivity]. apply (proj2 (IH rsp mo' tr')). left; exact Hx.
* right. exists rsp, mo', evs, tr'. split; [assumption|]; split; [|reflexivity]. apply (proj2 (IH rsp mo' tr')). right; eauto.
Qed.

#[using="Type"] Lemma tpath_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr rb mo',
tpath (bind t f) mo tr rb mo' <->
exists tr1 r mo1 tr2, tpath t mo tr1 r mo1 /\ tpath (f r) mo1 tr2 rb mo' /\ tr = tr1 ++ tr2.
Proof.
intros A B t. induction t as [r|n k IH]; intros f mo tr rb mo'; cbn.
- split.
+ intros H. exists [], r, mo, tr. repeat split; auto.
+ intros (tr1 & r0 & mo1 & tr2 & (-> & -> & ->) & H & ->). exact H.
- split.
+ intros (rsp & mo1 & evs & tr' & Hst & Hp & ->).
destruct (proj1 (IH rsp f mo1 tr' rb mo') Hp) as (tr1 & r & mo2 & tr2 & H1 & H2 & ->).
exists (evs ++ tr1), r, mo2, tr2. split; [idtac|split; [exact H2|apply app_assoc]].
exists rsp, mo1, evs, tr1. repeat split; assumption.
+ intros (tr1 & r & mo2 & tr2 & (rsp & mo1 & evs & tr' & Hst & H1 & ->) & H2 & ->).
exists rsp, mo1, evs, (tr' ++ tr2). split; [assumption|split; [idtac|symmetry; apply app_assoc]].
apply (proj2 (IH rsp f mo1 _ rb mo')). exists tr', r, mo2, tr2. repeat split; assumption.
Qed.

#[using="Type"] Lemma texit_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr,
texit (bind t f) mo tr <->
texit t mo tr \/ exists tr1 r mo1 tr2, tpath t mo tr1 r mo1 /\ texit (f r) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
intros A B t. induction t as [r|n k IH]; intros f mo tr; cbn.
- split.
+ intros H. right. exists [], r, mo, tr. repeat split; auto.
+ intros [F|(tr1 & r0 & mo1 & tr2 & (-> & -> & ->) & H & ->)]; [destruct F|exact H].
- split.
+ intros [Hex|(rsp & mo1 & evs & tr' & Hst & Hx & ->)]; [left; left; exact Hex|].
destruct (proj1 (IH rsp f mo1 tr') Hx) as [H|(tr1 & r & mo2 & tr2 & H1 & H2 & ->)].
* left; right. exists rsp, mo1, evs, tr'. repeat split; assumption.
* right. exists (evs ++ tr1), r, mo2, tr2. split; [idtac|split; [exact H2|apply app_assoc]].
exists rsp, mo1, evs, tr1. repeat split; assumption.
+ intros [[Hex|(rsp & mo1 & evs & tr' & Hst & Hx & ->)]|(tr1 & r & mo2 & tr2 & (rsp & mo1 & evs & tr' & Hst & H1 & ->) & H2 & ->)].
* left; exact Hex.
* right. exists rsp, mo1, evs, tr'. split; [assumption|split; [idtac|reflexivity]].
apply (proj2 (IH rsp f mo1 tr')). left; exact Hx.
* right. exists rsp, mo1, evs, (tr' ++ tr2). split; [assumption|split; [idtac|symmetry; apply app_assoc]].
apply (proj2 (IH rsp f mo1 _)). right. exists tr', r, mo2, tr2. repeat split; assumption.
Qed.

#[using="Type"] Lemma ttrace_bind : forall {A B} (t : itree A) (f : A -> itree B) mo tr,
ttrace (bind t f) mo tr <->
texit t mo tr \/ exists tr1 r mo1 tr2, tpath t mo tr1 r mo1 /\ ttrace (f r) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
intros A B t f mo tr. rewrite ttrace_split, texit_bind. split.
- intros [[Hx|(tr1 & r & mo1 & tr2 & H1 & H2 & ->)]|(rb & mo' & Hp)].
+ left; exact Hx.
+ right. exists tr1, r, mo1, tr2. split; [assumption|split; [|reflexivity]]. apply ttrace_split. left; exact H2.
+ destruct (proj1 (tpath_bind t f mo tr rb mo') Hp) as (tr1 & r & mo1 & tr2 & H1 & H2 & ->).
right. exists tr1, r, mo1, tr2. split; [assumption|split; [|reflexivity]]. apply ttrace_split. right; eauto.
- intros [Hx|(tr1 & r & mo1 & tr2 & H1 & H2 & ->)].
+ left; left; exact Hx.
+ destruct (proj1 (ttrace_split _ _ _) H2) as [Hx|(rb & mo' & Hp)].
* left; right. exists tr1, r, mo1, tr2. repeat split; assumption.
* right. exists rb, mo'. apply (proj2 (tpath_bind t f mo _ rb mo')). exists tr1, r, mo1, tr2. repeat split; assumption.
Qed.

#[using="Type"] Lemma tsafe_bind : forall {A B} (t : itree A) (f : A -> itree B) mo,
tsafe (bind t f) mo <->
tsafe t mo /\ (forall tr r mo', tpath t mo tr r mo' -> tsafe (f r) mo').
Proof.
intros A B t. induction t as [r|n k IH]; intros f mo; cbn in *.
- split.
+ intros H. split; [exact I|]. intros tr r0 mo' (<- & -> & _). exact H.
+ intros [_ H]. apply (H [] r mo). repeat split; reflexivity.
- split.
+ intros [Hn Hk]. split.
* split; [exact Hn|]. intros rsp mo' evs Hst. exact (proj1 (proj1 (IH rsp f mo') (Hk _ _ _ Hst))).
* intros tr r mo' (rsp & mo1 & evs & tr' & Hst & Hp & ->).
exact (proj2 (proj1 (IH rsp f mo1) (Hk _ _ _ Hst)) tr' r mo' Hp).
+ intros [[Hn Hk] Hf]. split; [exact Hn|]. intros rsp mo' evs Hst.
apply (proj2 (IH rsp f mo')). split; [eapply Hk; eassumption|].
intros tr r mo'' Hp. apply (Hf (evs ++ tr)). exists rsp, mo', evs, tr. repeat split; assumption.
Qed.

Definition leaves_unreachable {R} (t : itree R) (ms : machine_state) : Prop :=
impl t (fun _ _ => False) ms.

Definition leaves_unreachable_m {R} (t : itree R) (mo : Model) : Prop :=
forall tr r mo', tpath t mo tr r mo' -> False.

#[using="Type"] Lemma leaves_unreachable_m_ret : forall {R} (r : R) mo, leaves_unreachable_m (Ret r) mo -> False.
Proof. intros R r mo H. apply (H [] r mo). cbn. repeat split; reflexivity. Qed.

#[using="Type"] Lemma leaves_unreachable_m_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
leaves_unreachable_m (Vis n k) mo -> nstep n mo rsp mo' evs -> leaves_unreachable_m (k rsp) mo'.
Proof.
intros R n k mo rsp mo' evs H Hst tr r mo'' Hp. apply (H (evs ++ tr) r mo''). cbn.
exists rsp, mo', evs, tr. repeat split; assumption.
Qed.

#[using="Type"] Lemma leaves_unreachable_impl_m : forall {R} (t : itree R) ms mo,
leaves_unreachable t ms -> leaves_unreachable_m t mo.
Proof.
intros R t. induction t as [r|n k IH]; intros ms mo Ht tr r' mo' Hp; cbn in *.
- destruct Ht as (ms' & _ & F). destruct F.
- destruct Ht as (ms1 & _ & _ & Hk). destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
exact (IH rsp (nret ms1 rsp) mo1 (Hk rsp) tr' r' mo' Hp).
Qed.

#[using="Type"] Lemma tsafe_trivial : (forall n mo, nsafe n mo) -> forall {R} (t : itree R) mo, tsafe t mo.
Proof. intros Hall R t. induction t as [r|n k IH]; intros mo; cbn; [exact I|]. split; [apply Hall|]. intros; apply IH. Qed.

#[using="Type"] Lemma tsafe_step : forall {R} n (k : resp -> itree R) mo rsp mo' evs,
tsafe (Vis n k) mo -> nstep n mo rsp mo' evs -> tsafe (k rsp) mo'.
Proof. intros R n k mo rsp mo' evs [_ Hk] Hst. eapply Hk; eassumption. Qed.

#[using="Type"] Lemma sstep_mstep_inv : forall ms mo ms' evs X,
m_vm_lazy mo = [] ->
mstep segs ms ms' ->
sstep segs (mkCfg ms mo) evs X ->
evs = [] /\ X = SNext (mkCfg ms' mo).
Proof.
intros ms mo ms' evs X Hlz [Hsvc Hstep] Hss.
inversion Hss; subst; try congruence;
match goal with H : mi_account_step segs ms mo = _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms mo Hlz) in H;
rewrite Hstep in H; inversion H; subst end.
split; reflexivity.
Qed.

#[using="Type"] Lemma sstep_not_halted : forall ms mo evs X,
sstep segs (mkCfg ms mo) evs X -> m_halted mo = None.
Proof. intros ms mo evs X Hss. inversion Hss; subst; assumption. Qed.

#[using="Type"] Lemma star_halted_nil : forall ms mo tr c',
m_halted mo <> None -> star segs (mkCfg ms mo) tr c' -> tr = [] /\ c' = mkCfg ms mo.
Proof.
intros ms mo tr c' Hh Hstar. inversion Hstar; subst.
- split; reflexivity.
- exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

#[using="Type"] Lemma mstep_sstep : forall ms ms' mo,
m_halted mo = None -> m_vm_lazy mo = [] -> mstep segs ms ms' ->
sstep segs (mkCfg ms mo) [] (SNext (mkCfg ms' mo)).
Proof.
intros ms ms' mo Hh Hlz [Hsvc Hstep]. apply sstep_instr; try assumption.
rewrite (mi_account_step_no_lazy segs ms mo Hlz). cbv beta. rewrite Hstep. reflexivity.
Qed.

#[using="Type"] Lemma msteps_star : forall ms ms' mo,
m_halted mo = None -> m_vm_lazy mo = [] -> msteps segs ms ms' ->
star segs (mkCfg ms mo) [] (mkCfg ms' mo).
Proof.
intros ms ms' mo Hh Hlz Hm. induction Hm as [ms|ms ms1 ms2 H1 H2 IH].
- apply star_refl.
- change ([] : list event) with ([] ++ [] : list event).
eapply star_step; [apply mstep_sstep; eassumption| exact IH].
Qed.

#[using="Type"] Lemma msteps_comparable : forall ms a b,
msteps segs ms a -> msteps segs ms b -> msteps segs a b \/ msteps segs b a.
Proof.
intros ms a b Ha; revert b. induction Ha as [ms|ms ms1 ms2 H1 H2 IH]; intros b Hb.
- left; exact Hb.
- inversion Hb; subst.
+ right. eapply msteps_cons; eassumption.
+ apply IH. match goal with Hm : mstep segs ms ?x, Hr : msteps segs ?x b |- _ =>
rewrite (mstep_det segs ms ms1 x H1 Hm); exact Hr end.
Qed.

#[using="Type"] Lemma msteps_from_svc : forall ms ms',
msteps segs ms ms' -> ms_svc_pending ms <> None -> ms' = ms.
Proof.
intros ms ms' Hm Hsvc. inversion Hm; subst; [reflexivity|].
exfalso. apply Hsvc. eapply mstep_not_svc; eassumption.
Qed.

#[using="Type"] Lemma msteps_svc_unique : forall ms a b,
msteps segs ms a -> msteps segs ms b ->
ms_svc_pending a <> None -> ms_svc_pending b <> None -> a = b.
Proof.
intros ms a b Ha Hb Hsa Hsb.
destruct (msteps_comparable ms a b Ha Hb) as [H|H].
- symmetry. exact (msteps_from_svc a b H Hsa).
- exact (msteps_from_svc b a H Hsb).
Qed.

#[using="Type"] Lemma is_prefix_app_l {A} : forall (l l1 l2 : list A),
is_prefix l1 l2 -> is_prefix (l ++ l1) (l ++ l2).
Proof. induction l; cbn; auto. Qed.

#[using="Type"] Lemma impl_inv : forall {R} (t : itree R) Q ms mo,
impl t Q ms -> leaves_unreachable_m t mo ->
exists n k ms1, t = Vis n k /\ msteps segs ms ms1 /\ at_node n ms1
/\ forall rsp, impl (k rsp) Q (nret ms1 rsp).
Proof.
intros R t Q ms mo H Hl. destruct t as [r|n k]; cbn in H.
- destruct (leaves_unreachable_m_ret r mo Hl).
- destruct H as (ms1 & Hm & Hat & Hk). exists n, k, ms1. repeat split; assumption.
Qed.

Definition tree_at {R} (t : itree R) Q (ms : machine_state) (mo : Model) : Prop :=
impl t Q ms /\ leaves_unreachable_m t mo /\ m_halted mo = None /\ minv mo /\ tsafe t mo.

#[using="Type"] Lemma tree_at_step : node_sound -> forall {R} n (k : resp -> itree R) Q ms1 mo rsp mo' evs,
at_node n ms1 -> (forall rsp, impl (k rsp) Q (nret ms1 rsp)) ->
leaves_unreachable_m (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafe (Vis n k) mo ->
nstep n mo rsp mo' evs ->
tree_at (k rsp) Q (nret ms1 rsp) mo' /\ sstep segs (mkCfg ms1 mo) evs (SNext (mkCfg (nret ms1 rsp) mo')).
Proof.
intros NS R n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst.
destruct (ns_sound NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (Hh' & Hinv' & Hss).
split; [|exact Hss]. split; [apply Hk|]. split; [eapply leaves_unreachable_m_step; eassumption|].
split; [exact Hh'|]. split; [exact Hinv'|]. eapply tsafe_step; eassumption.
Qed.

#[using="Type"] Lemma ttrace_exists : node_sound -> forall {R} (t : itree R) Q ms mo,
tree_at t Q ms mo -> exists full, ttrace t mo full.
Proof.
intros NS R t. induction t as [r|n k IH]; intros Q ms mo HT.
- destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret r mo Hl).
- destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
destruct (ns_progress NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
+ destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
destruct (IH rsp Q (nret ms1 rsp) mo' HT') as (full' & Hfull').
exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
+ exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
Qed.

#[using="Type"] Lemma impl_sstep_inv : node_sound -> forall {R} (t : itree R) Q ms mo evs X,
tree_at t Q ms mo ->
sstep segs (mkCfg ms mo) evs X ->
(exists ms', X = SNext (mkCfg ms' mo) /\ evs = [] /\ mstep segs ms ms' /\ tree_at t Q ms' mo)
\/ (exists n k rsp mo', t = Vis n k /\ at_node n ms /\ X = SNext (mkCfg (nret ms rsp) mo')
/\ nstep n mo rsp mo' evs /\ tree_at (k rsp) Q (nret ms rsp) mo')
\/ (exists n k code mo', t = Vis n k /\ at_node n ms /\ X = SNext (mkCfg ms mo')
/\ nexit n mo code mo' /\ evs = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code).
Proof.
intros NS R t Q ms mo evs X HT Hss. destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
destruct (impl_inv t Q ms mo Ht Hl) as (n & k & ms1 & -> & Hm & Hat & Hk).
inversion Hm; subst.
-
destruct (ns_complete NS n ms1 mo evs X Hat Hh Hinv (proj1 Hsf) Hss)
as [(rsp & mo' & HX & Hst)|(code & mo' & HX & Hex & Hevs)].
+ right; left. destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
exists n, k, rsp, mo'. split; [reflexivity|]. split; [exact Hat|]. split; [exact HX|]. split; [exact Hst|exact HT'].
+ right; right. destruct (ns_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
exists n, k, code, mo'. repeat split; auto.
-
left. match goal with H1 : mstep segs ms ?x, H2 : msteps segs ?x ms1 |- _ =>
destruct (sstep_mstep_inv ms mo x evs X (ns_lazy NS mo Hinv) H1 Hss) as (-> & ->);
exists x; split; [reflexivity|]; split; [reflexivity|]; split; [exact H1|];
split; [cbn; exists ms1; split; [exact H2|]; split; [exact Hat|exact Hk]|];
split; [exact Hl|]; split; [exact Hh|]; split; [exact Hinv|exact Hsf] end.
Qed.

Definition run_inv {R} Q (c : config) : Prop :=
(exists t : itree R, tree_at t Q (cfg_ms c) (cfg_model c))
\/ m_halted (cfg_model c) <> None.

#[using="Type"] Lemma run_inv_sstep : node_sound -> forall {R} Q c evs X,
run_inv (R:=R) Q c -> sstep segs c evs X -> exists c', X = SNext c' /\ run_inv (R:=R) Q c'.
Proof.
intros NS R Q [ms mo] evs X Hg Hss. destruct Hg as [(t & HT)|Hh]; cbn in *.
- destruct (impl_sstep_inv NS t Q ms mo evs X HT Hss)
as [(ms' & -> & _ & _ & HT')|[(n & k & rsp & mo' & _ & _ & -> & _ & HT')
|(n & k & code & mo' & _ & _ & -> & _ & _ & Hh')]].
+ eexists; split; [reflexivity|]. left. exists t. exact HT'.
+ eexists; split; [reflexivity|]. left. exists (k rsp). exact HT'.
+ eexists; split; [reflexivity|]. right. cbn. congruence.
- exfalso. apply Hh. eapply sstep_not_halted; eassumption.
Qed.

#[using="Type"] Lemma run_inv_star : node_sound -> forall {R} Q c tr c',
star segs c tr c' -> run_inv (R:=R) Q c -> run_inv (R:=R) Q c'.
Proof.
intros NS R Q c tr c' Hstar. induction Hstar as [c|c1 evs c2 tr c3 Hss Hstar IH]; intros Hg; [exact Hg|].
destruct (run_inv_sstep NS Q c1 evs (SNext c2) Hg Hss) as (c2' & E & Hg'). inversion E; subst. auto.
Qed.

#[using="Type"] Lemma star_ttrace_prefix : node_sound -> forall {R} Q c tr c',
star segs c tr c' ->
forall (t : itree R) ms mo, c = mkCfg ms mo -> tree_at t Q ms mo ->
exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
intros NS R Q c tr c' Hstar.
induction Hstar as [c|c1 evs c2 tr c3 Hss Hstar IH]; intros t ms mo -> HT.
- destruct (ttrace_exists NS t Q ms mo HT) as (full & Hf).
exists full. split; [exact Hf| apply is_prefix_nil].
- destruct (impl_sstep_inv NS t Q ms mo evs (SNext c2) HT Hss)
as [(ms' & E & -> & _ & HT')|[(n & k & rsp & mo' & -> & Hat & E & Hst & HT')
|(n & k & code & mo' & -> & Hat & E & Hex & -> & Hh')]]; inversion E; subst.
+ exact (IH t ms' mo eq_refl HT').
+ destruct (IH (k rsp) (nret ms rsp) mo' eq_refl HT') as (full' & Hf' & Hp').
exists (evs ++ full'). split.
* cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
* apply is_prefix_app_l. exact Hp'.
+ destruct (star_halted_nil ms mo' tr c3) as [-> _]; [congruence|exact Hstar|].
exists [ExitEv code (m_fs mo')]. split.
* cbn. left. exists code, mo'. split; [assumption|reflexivity].
* cbn. split; [reflexivity|exact I].
Qed.

#[using="Type"] Lemma ttrace_star : node_sound -> forall {R} (t : itree R) Q ms mo full,
ttrace t mo full -> tree_at t Q ms mo ->
exists c', star segs (mkCfg ms mo) full c'.
Proof.
intros NS R t. induction t as [r|n k IH]; intros Q ms mo full Hf HT.
- destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret r mo Hl).
- destruct HT as (Ht & Hl & Hh & Hinv & Hsf).
cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
pose proof (msteps_star ms ms1 mo Hh (ns_lazy NS mo Hinv) Hm) as Hs0.
cbn in Hf. destruct Hf as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & Hst & Hf' & ->)].
+ destruct (ns_exit NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss).
exists (mkCfg ms1 mo'). change [ExitEv code (m_fs mo')] with ([] ++ [ExitEv code (m_fs mo')]).
eapply star_trans; [exact Hs0|]. apply star_one. exact Hss.
+ destruct (tree_at_step NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' Hss].
destruct (IH rsp Q (nret ms1 rsp) mo' tr' Hf' HT') as (c' & Hs').
exists c'. change (evs ++ tr') with ([] ++ (evs ++ tr')).
eapply star_trans; [exact Hs0|]. eapply star_step; [exact Hss| exact Hs'].
Qed.

#[using="Type"] Theorem impl_run_traces2 : node_sound -> forall {R} (t : itree R) Q ms mo,
impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
ms_svc_pending ms = None ->
forall tr, obs_trace segs (mkCfg ms mo) tr <-> exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
intros NS R t Q ms mo Ht Hl Hh Hinv Hsf _ tr.
assert (HT : tree_at t Q ms mo) by (repeat split; assumption). split.
- intros (tr' & c & Hstar & Hp).
destruct (star_ttrace_prefix NS Q (mkCfg ms mo) tr' c Hstar t ms mo eq_refl HT) as (full & Hf & Hp').
exists full. split; [exact Hf| eapply is_prefix_trans; eassumption].
- intros (full & Hf & Hp).
destruct (ttrace_star NS t Q ms mo full Hf HT) as (c' & Hs).
exists full, c'. split; assumption.
Qed.

#[using="Type"] Theorem impl_run_safe2 : node_sound -> forall {R} (t : itree R) Q ms mo,
impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
ms_svc_pending ms = None ->
~ reaches_error segs (mkCfg ms mo).
Proof.
intros NS R t Q ms mo Ht Hl Hh Hinv Hsf _ (tr & c & evs & Hstar & Hss).
assert (Hg : run_inv (R:=R) Q c).
{ eapply run_inv_star; [exact NS|exact Hstar|]. left. exists t. cbn. repeat split; assumption. }
destruct (run_inv_sstep NS Q c evs SError Hg Hss) as (c' & E & _). discriminate E.
Qed.

#[using="Type"] Theorem impl_run_modeled2 : node_sound -> forall {R} (t : itree R) Q ms mo,
impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
ms_svc_pending ms = None ->
~ reaches_unmodeled segs (mkCfg ms mo).
Proof.
intros NS R t Q ms mo Ht Hl Hh Hinv Hsf Hsvc.
apply no_error_no_unmodeled. eapply impl_run_safe2; eassumption.
Qed.

#[using="Type"] Theorem impl_run_progress2 : node_sound -> forall {R} (t : itree R) Q ms mo tr ms' mo',
impl t Q ms -> leaves_unreachable_m t mo -> m_halted mo = None -> minv mo -> tsafe t mo ->
star segs (mkCfg ms mo) tr (mkCfg ms' mo') -> m_halted mo' = None ->
exists evs c'', sstep segs (mkCfg ms' mo') evs (SNext c'').
Proof.
intros NS R t Q ms mo tr ms' mo' Ht Hl Hh Hinv Hsf Hstar Hh'.
assert (Hg : run_inv (R:=R) Q (mkCfg ms' mo')).
{ eapply run_inv_star; [exact NS|exact Hstar|]. left. exists t. cbn. repeat split; assumption. }
destruct Hg as [(t' & Ht' & Hl' & _ & Hinv' & Hsf')|Hc]; cbn in *; [|congruence].
destruct (impl_inv t' Q ms' mo' Ht' Hl') as (n & k & ms1 & -> & Hm & Hat & Hk).
cbn in Hsf'. destruct Hsf' as [Hns _].
inversion Hm; subst.
- destruct (ns_progress NS n ms1 mo' Hat Hh' Hinv' Hns) as [(rsp & mo'' & evs & Hst)|(code & mo'' & Hex)].
+ destruct (ns_sound NS n ms1 mo' rsp mo'' evs Hat Hh' Hinv' Hns Hst) as (_ & _ & Hss). eauto.
+ destruct (ns_exit NS n ms1 mo' code mo'' Hat Hh' Hinv' Hns Hex) as (_ & Hss). eauto.
- do 2 eexists. apply mstep_sstep; [eassumption| exact (ns_lazy NS _ Hinv') | eassumption].
Qed.

#[using="Type"] Theorem impl_run_traces : node_sound -> forall {R} (t : itree R) ms mo,
leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
forall tr, obs_trace segs (mkCfg ms mo) tr <-> exists full, ttrace t mo full /\ is_prefix tr full.
Proof.
intros NS R t ms mo Ht. apply (impl_run_traces2 NS t _ ms mo Ht). eapply leaves_unreachable_impl_m; exact Ht.
Qed.

#[using="Type"] Theorem impl_run_safe : node_sound -> forall {R} (t : itree R) ms mo,
leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
~ reaches_error segs (mkCfg ms mo).
Proof.
intros NS R t ms mo Ht. apply (impl_run_safe2 NS t _ ms mo Ht). eapply leaves_unreachable_impl_m; exact Ht.
Qed.

#[using="Type"] Theorem impl_run_modeled : node_sound -> forall {R} (t : itree R) ms mo,
leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo -> ms_svc_pending ms = None ->
~ reaches_unmodeled segs (mkCfg ms mo).
Proof.
intros NS R t ms mo Ht. apply (impl_run_modeled2 NS t _ ms mo Ht). eapply leaves_unreachable_impl_m; exact Ht.
Qed.

#[using="Type"] Lemma impl_run_progress : node_sound -> forall {R} (t : itree R) ms mo tr ms' mo',
leaves_unreachable t ms -> m_halted mo = None -> minv mo -> tsafe t mo ->
star segs (mkCfg ms mo) tr (mkCfg ms' mo') -> m_halted mo' = None ->
exists evs c'', sstep segs (mkCfg ms' mo') evs (SNext c'').
Proof.
intros NS R t ms mo tr ms' mo' Ht. apply (impl_run_progress2 NS t _ ms mo tr ms' mo' Ht).
eapply leaves_unreachable_impl_m; exact Ht.
Qed.

Definition ebind {A B} (t : itree (exc A)) (f : A -> itree (exc B)) : itree (exc B) :=
bind t (fun r => match r with Unr => Ret Unr | Ok a => f a end).

Definition epost {A} (Q : A -> machine_state -> Prop) : exc A -> machine_state -> Prop :=
fun r ms => match r with Unr => True | Ok a => Q a ms end.

#[using="Type"] Lemma impl_ret_unr : forall {A} (Q : A -> machine_state -> Prop) ms, impl (Ret Unr) (epost Q) ms.
Proof. intros A Q ms. cbn. apply evt_done. exact I. Qed.

#[using="Type"] Lemma impl_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) Q1 Q ms,
impl t (epost Q1) ms -> (forall a ms', Q1 a ms' -> impl (f a) (epost Q) ms') ->
impl (ebind t f) (epost Q) ms.
Proof.
intros A B t f Q1 Q ms Ht Hf. unfold ebind. eapply impl_bind; [exact Ht|].
intros [|a] ms' H'; cbn in H'.
- apply impl_ret_unr.
- apply Hf. exact H'.
Qed.

#[using="Type"] Lemma impl_epost_mono : forall {A} (t : itree (exc A)) (Q Q' : A -> machine_state -> Prop) ms,
impl t (epost Q) ms -> (forall a ms', Q a ms' -> Q' a ms') -> impl t (epost Q') ms.
Proof.
intros A t Q Q' ms H HQ. eapply impl_mono; [exact H|]. intros [|a] ms'; cbn; auto.
Qed.

#[using="Type"] Lemma ebind_ret_ok : forall {A B} (a : A) (f : A -> itree (exc B)), ebind (Ret (Ok a)) f = f a.
Proof. reflexivity. Qed.
#[using="Type"] Lemma ebind_ret_unr : forall {A B} (f : A -> itree (exc B)), ebind (Ret Unr) f = Ret Unr.
Proof. reflexivity. Qed.
#[using="Type"] Lemma ebind_vis : forall {A B} n k (f : A -> itree (exc B)),
ebind (Vis n k) f = Vis n (fun rsp => ebind (k rsp) f).
Proof. reflexivity. Qed.

#[using="Type"] Lemma impl_ret_ok : forall {A} (Q : A -> machine_state -> Prop) a ms,
evt segs (Q a) ms -> impl (Ret (Ok a)) (epost Q) ms.
Proof. intros A Q a ms H. exact H. Qed.

Definition enode {A} (n : node) (pl : resp -> option A) : itree (exc A) :=
Vis n (fun rsp => match pl rsp with Some a => Ret (Ok a) | None => Ret Unr end).

#[using="Type"] Lemma impl_enode : forall {A} n (pl : resp -> option A) (Q : A -> machine_state -> Prop) ms,
evt segs (fun ms1 => at_node n ms1 /\ forall rsp a, pl rsp = Some a -> evt segs (Q a) (nret ms1 rsp)) ms ->
impl (enode n pl) (epost Q) ms.
Proof.
intros A n pl Q ms H. cbn. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn.
- apply Hk. reflexivity.
- apply evt_done. exact I.
Qed.

#[using="Type"] Lemma tpath_enode : forall {A} n (pl : resp -> option A) mo tr r mo',
tpath (enode n pl) mo tr r mo' <->
exists rsp, nstep n mo rsp mo' tr /\ r = match pl rsp with Some a => Ok a | None => Unr end.
Proof.
intros A n pl mo tr r mo'. cbn. split.
- intros (rsp & mo1 & evs & tr' & Hst & Hp & ->). exists rsp.
destruct (pl rsp) as [a|]; cbn in Hp; destruct Hp as (<- & -> & ->); rewrite app_nil_r; split; auto.
- intros (rsp & Hst & ->). exists rsp, mo', tr, []. split; [exact Hst|]. split; [|symmetry; apply app_nil_r].
destruct (pl rsp); cbn; repeat split; reflexivity.
Qed.

#[using="Type"] Lemma texit_enode : forall {A} n (pl : resp -> option A) mo tr,
texit (enode n pl) mo tr <-> exists code mo', nexit n mo code mo' /\ tr = [ExitEv code (m_fs mo')].
Proof.
intros A n pl mo tr. cbn. split.
- intros [H|(rsp & mo' & evs & tr' & _ & Hx & _)]; [exact H|]. destruct (pl rsp); destruct Hx.
- intros H. left. exact H.
Qed.

#[using="Type"] Lemma tsafe_enode : forall {A} n (pl : resp -> option A) mo,
tsafe (enode n pl) mo <-> nsafe n mo.
Proof.
intros A n pl mo. cbn. split; [intros [H _]; exact H|]. intros H. split; [exact H|].
intros rsp mo' evs _. destruct (pl rsp); exact I.
Qed.

#[using="Type"] Lemma tpath_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr r mo',
tpath (ebind t f) mo tr r mo' <->
(tpath t mo tr Unr mo' /\ r = Unr)
\/ exists tr1 a mo1 tr2, tpath t mo tr1 (Ok a) mo1 /\ tpath (f a) mo1 tr2 r mo' /\ tr = tr1 ++ tr2.
Proof.
intros A B t f mo tr r mo'. unfold ebind. rewrite tpath_bind. split.
- intros (tr1 & [|a] & mo1 & tr2 & H1 & H2 & ->).
+ cbn in H2. destruct H2 as (<- & -> & ->). left. rewrite app_nil_r. split; [exact H1|reflexivity].
+ right. exists tr1, a, mo1, tr2. repeat split; assumption.
- intros [[H1 ->]|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)].
+ exists tr, Unr, mo', []. split; [exact H1|]. split; [cbn; repeat split; reflexivity| symmetry; apply app_nil_r].
+ exists tr1, (Ok a), mo1, tr2. repeat split; assumption.
Qed.

#[using="Type"] Lemma texit_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr,
texit (ebind t f) mo tr <->
texit t mo tr \/ exists tr1 a mo1 tr2, tpath t mo tr1 (Ok a) mo1 /\ texit (f a) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
intros A B t f mo tr. unfold ebind. rewrite texit_bind. split.
- intros [H|(tr1 & [|a] & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H| destruct H2 |].
right. exists tr1, a, mo1, tr2. repeat split; assumption.
- intros [H|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H|].
right. exists tr1, (Ok a), mo1, tr2. repeat split; assumption.
Qed.

#[using="Type"] Lemma ttrace_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo tr,
ttrace (ebind t f) mo tr <->
texit t mo tr
\/ (exists mo', tpath t mo tr Unr mo')
\/ exists tr1 a mo1 tr2, tpath t mo tr1 (Ok a) mo1 /\ ttrace (f a) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
intros A B t f mo tr. unfold ebind. rewrite ttrace_bind. split.
- intros [H|(tr1 & [|a] & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H| |].
+ cbn in H2. subst tr2. right; left. exists mo1. rewrite app_nil_r. exact H1.
+ right; right. exists tr1, a, mo1, tr2. repeat split; assumption.
- intros [H|[(mo' & H)|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)]]; [left; exact H| |].
+ right. exists tr, Unr, mo', []. split; [exact H|]. split; [reflexivity| symmetry; apply app_nil_r].
+ right. exists tr1, (Ok a), mo1, tr2. repeat split; assumption.
Qed.

#[using="Type"] Lemma tsafe_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo,
tsafe (ebind t f) mo <->
tsafe t mo /\ (forall tr a mo', tpath t mo tr (Ok a) mo' -> tsafe (f a) mo').
Proof.
intros A B t f mo. unfold ebind. rewrite tsafe_bind. split.
- intros [Ht Hf]. split; [exact Ht|]. intros tr a mo' Hp. exact (Hf tr (Ok a) mo' Hp).
- intros [Ht Hf]. split; [exact Ht|]. intros tr [|a] mo' Hp; [exact I|]. exact (Hf tr a mo' Hp).
Qed.

#[using="Type"] Lemma leaves_unreachable_m_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) mo,
leaves_unreachable_m (ebind t f) mo <->
(forall tr mo', tpath t mo tr Unr mo' -> False)
/\ (forall tr a mo1, tpath t mo tr (Ok a) mo1 -> leaves_unreachable_m (f a) mo1).
Proof.
intros A B t f mo. unfold leaves_unreachable_m. split.
- intros H. split.
+ intros tr mo' Hp. apply (H tr Unr mo'). apply tpath_ebind. left. split; [exact Hp|reflexivity].
+ intros tr a mo1 Hp tr2 r mo' Hp2. apply (H (tr ++ tr2) r mo'). apply tpath_ebind. right.
exists tr, a, mo1, tr2. repeat split; assumption.
- intros [HU HO] tr r mo' Hp. apply tpath_ebind in Hp.
destruct Hp as [[Hp ->]|(tr1 & a & mo1 & tr2 & H1 & H2 & ->)].
+ exact (HU _ _ Hp).
+ exact (HO _ _ _ H1 _ _ _ H2).
Qed.

End ITree.

Arguments Ret {node R} r.
Arguments Vis {node R} n k.
Arguments impl {node} segs at_node {R} t Q ms.
Arguments ttrace {node} nstep nexit {R} t mo tr.
Arguments tsafe {node} nstep nsafe {R} t mo.
Arguments tpath {node} nstep {R} t mo tr r mo'.
Arguments texit {node} nstep nexit {R} t mo tr.
Arguments leaves_unreachable_m {node} nstep {R} t mo.
Arguments tree_at {node} segs at_node nstep minv nsafe {R} t Q ms mo.
Arguments ebind {node A B} t f.
Arguments enode {node A} n pl.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition ro_cells (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
cells_at segs m A cs.
Definition rw_cells (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
cells_at segs m A cs /\ wr_at segs m A (Z.of_nat (cells_size cs)).

#[using="Type"] Lemma rw_cells_read : forall m A cs k c,
rw_cells m A cs -> cell_at cs k = Some c ->
ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof. intros m A cs k c [H _]. apply cells_at_read. exact H. Qed.

#[using="Type"] Lemma ro_cells_read : forall m A cs k c,
ro_cells m A cs -> cell_at cs k = Some c ->
ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof. intros m A cs k c H. apply cells_at_read. exact H. Qed.

#[using="Type"] Lemma rw_cells_readn : forall m A cs k c n,
rw_cells m A cs -> cell_at cs k = Some c -> n = csize c ->
ov_read_bytes segs m (wa (A + Z.of_nat k)) n = Some (cbytes c).
Proof. intros; subst; eapply rw_cells_read; eauto. Qed.

#[using="Type"] Lemma ro_cells_readn : forall m A cs k c n,
ro_cells m A cs -> cell_at cs k = Some c -> n = csize c ->
ov_read_bytes segs m (wa (A + Z.of_nat k)) n = Some (cbytes c).
Proof. intros; subst; eapply ro_cells_read; eauto. Qed.

#[using="Type"] Lemma rw_cells_read_at : forall m A cs k c n a,
rw_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
ov_read_bytes segs m a n = Some (cbytes c).
Proof. intros; subst; eapply rw_cells_read; eauto. Qed.

#[using="Type"] Lemma ro_cells_read_at : forall m A cs k c n a,
ro_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
ov_read_bytes segs m a n = Some (cbytes c).
Proof. intros; subst; eapply ro_cells_read; eauto. Qed.

#[using="Type"] Lemma rw_cells_cb_split : forall m A cs cs2 k n,
rw_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> rw_cells m A cs2.
Proof.
intros m A cs cs2 k n [Hc Hw] Hok ->. split.
- apply cells_at_cb_split; assumption.
- rewrite cells_size_cb_split; [exact Hw| exact (cells_at_wf _ _ _ _ Hc) | exact Hok].
Qed.

#[using="Type"] Lemma ro_cells_cb_split : forall m A cs cs2 k n,
ro_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> ro_cells m A cs2.
Proof. intros m A cs cs2 k n Hc Hok ->. apply cells_at_cb_split; assumption. Qed.

#[using="Type"] Lemma cell_at_bound : forall cs k c, cell_at cs k = Some c -> (k + csize c <= cells_size cs)%nat.
Proof.
intros cs k c H. destruct (cell_at_split cs k c c H) as (pre & post & -> & Hsz & _).
rewrite cells_size_app. cbn. lia.
Qed.

#[using="Type"] Lemma rw_cells_store_ok : forall m A cs k c (j : nat),
rw_cells m A cs -> cell_at cs k = Some c -> j = csize c ->
store_ok segs m (wa (A + Z.of_nat k)) j = true.
Proof.
intros m A cs k c j [Hc Hw] Hk ->. pose proof (cell_at_bound _ _ _ Hk).
apply (wr_at_store_ok segs m A (Z.of_nat (cells_size cs))); [exact Hw| lia | lia].
Qed.

#[using="Type"] Lemma rw_cells_store_ok_at : forall m A cs k c (j : nat) a,
rw_cells m A cs -> cell_at cs k = Some c -> j = csize c -> a = wa (A + Z.of_nat k) ->
store_ok segs m a j = true.
Proof. intros; subst. eapply rw_cells_store_ok; eauto. Qed.

#[using="Type"] Lemma rw_cells_write : forall m A cs k c c',
rw_cells m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
rw_cells (write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) A (cell_upd cs k c').
Proof.
intros m A cs k c c' [Hc Hw] Hk Hsz Hwf. split.
- eapply cells_at_write; eauto.
- destruct (cell_at_split cs k c c' Hk) as (pre & post & -> & Hszp & ->).
rewrite cells_size_app in *. cbn [cells_size] in *. rewrite Hsz. apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma rw_cells_frame : forall m A cs (a : Z) bs,
rw_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
(A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
rw_cells (write_to_mem m (wa a) bs) A cs.
Proof.
intros m A cs a bs [Hc Hw] Ha Hl Hd. split.
- apply cells_at_frame; assumption.
- apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma ro_cells_frame : forall m A cs (a : Z) bs,
ro_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
(A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
ro_cells (write_to_mem m (wa a) bs) A cs.
Proof. intros. apply cells_at_frame; assumption. Qed.

#[using="Type"] Lemma rw_cells_bound : forall m A cs, rw_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. intros m A cs [H _]. eapply cells_at_bound; eauto. Qed.
#[using="Type"] Lemma ro_cells_bound : forall m A cs, ro_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. intros m A cs H. eapply cells_at_bound; eauto. Qed.

#[using="Type"] Lemma mem_inv_store_cbytes : forall m a c',
mem_inv segs m -> cell_wf c' -> store_ok segs m a (csize c') = true ->
mem_inv segs (write_to_mem m a (cbytes c')).
Proof.
intros m a c' Hinv Hwf Hok. apply mem_inv_store; [assumption|].
rewrite cbytes_length by assumption. exact Hok.
Qed.

End WithSegs.

Lemma unsigned_Z_to_bv_add : forall e d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) + d) = Z_to_bv 64 (e + d).
Proof.
intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_Z_to_bv_add_r : forall e d, Z_to_bv 64 (d + bv_unsigned (Z_to_bv 64 e)) = Z_to_bv 64 (d + e).
Proof.
intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma unsigned_Z_to_bv_sub : forall e d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) - d) = Z_to_bv 64 (e - d).
Proof.
intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma bv_add_canon : forall (x y : word), (x + y : word) = Z_to_bv 64 (bv_unsigned x + bv_unsigned y).
Proof. intros. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

Lemma Z_to_bv_lit_self : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma wa_of_Z_to_bv : forall E e, E = e -> wa e = Z_to_bv 64 E.
Proof. intros; subst; reflexivity. Qed.
Lemma wa_of_var : forall (x : word) e, bv_unsigned x = e -> wa e = x.
Proof. intros; subst. unfold wa. apply Z_to_bv_lit_self. Qed.

Lemma store_bytes_8' : forall v : word, Z_to_le_bytes 8 (bv_unsigned v) = le8 v.
Proof. exact store_bytes_8. Qed.
Lemma store_bytes_4' : forall v : word, Z_to_le_bytes 4 (bv_unsigned (low32 v)) = le4 v.
Proof. exact store_bytes_4. Qed.
Lemma store_bytes_2' : forall v : word, Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 v)) = le2 v.
Proof. exact store_bytes_2. Qed.
Lemma store_bytes_1' : forall v : word, Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 v)) = le1 v.
Proof. exact store_bytes_1. Qed.

Ltac slia := first [ exact I | lia | split; [lia|exact I] ]. Ltac mkr__slia_0 := first [ exact I | lia | split; [lia|exact I] ].

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac fold_closed_in_goal :=
repeat match goal with
| |- context [bv_unsigned (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_unsigned (@BV n z p)) in change (bv_unsigned (@BV n z p)) with v
| |- context [bv_signed (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_signed (@BV n z p)) in change (bv_signed (@BV n z p)) with v
| |- context [bv_signed (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_signed (bv_concat n a b)) in is_Zlit v; change (bv_signed (bv_concat n a b)) with v
| |- context [bv_unsigned (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_unsigned (bv_concat n a b)) in is_Zlit v; change (bv_unsigned (bv_concat n a b)) with v
| |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
| |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
| |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
| |- context [Z.shiftr ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
| |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
| |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
| |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
| |- context [bv_swrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_swrap n z) in
replace (bv_swrap n z) with v by (vm_compute; reflexivity)
| |- context [bv_wrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_wrap n z) in
replace (bv_wrap n z) with v by (vm_compute; reflexivity)
| |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
| |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
| |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
| |- context [Z.add (Z.add ?x ?a) ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in
replace (Z.add (Z.add x a) b) with (Z.add x v) by (exact (Z.add_assoc x a b))
| |- context [Z_to_bv 64 (Z.add ?x 0)] => rewrite (Z.add_0_r x)
end.

Ltac fold_lit_load :=
repeat match goal with
| |- context [bv_extract 0 ?n (le_bytes_to_word ?bs)] =>
lazymatch bs with (_ :: _)%list => idtac end;
let t := constr:(bv_extract 0 n (le_bytes_to_word bs)) in
let z := eval vm_compute in (bv_unsigned t) in
is_Zlit z;
rewrite (bv_lit_eq n t z) by (vm_compute; reflexivity)
| |- context [@sext ?k 64 (Z_to_bv ?k ?z)] =>
is_Zlit z;
let t := constr:(@sext k 64 (Z_to_bv k z)) in
let z' := eval vm_compute in (bv_unsigned t) in
rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
| |- context [@zext ?k 64 (Z_to_bv ?k ?z)] =>
is_Zlit z;
let t := constr:(@zext k 64 (Z_to_bv k z)) in
let z' := eval vm_compute in (bv_unsigned t) in
rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
| |- context [low32 (Z_to_bv 64 ?z)] =>
is_Zlit z;
let t := constr:(low32 (Z_to_bv 64 z)) in
let z' := eval vm_compute in (bv_unsigned t) in
rewrite (bv_lit_eq 32 t z') by (vm_compute; reflexivity)
| |- context [nan_box (Z_to_bv 32 ?z)] =>
is_Zlit z;
let t := constr:(nan_box (Z_to_bv 32 z)) in
let z' := eval vm_compute in (bv_unsigned t) in
rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
end.

Ltac simp_is_x0 :=
repeat match goal with
| |- context [is_x0 ?r] => let v := eval vm_compute in (is_x0 r) in change (is_x0 r) with v
end; cbv beta iota.

Ltac is_concrete_map R := lazymatch R with TNode _ _ _ => idtac | TEmpty => idtac end. Ltac mkr__is_concrete_map_1 R := lazymatch R with TNode _ _ _ => idtac | TEmpty => idtac end.
Ltac map_cbv_get := cbv beta iota delta [tget]. Ltac mkr__map_cbv_get_2 := cbv beta iota delta [tget].
Ltac map_cbv_set := cbv beta iota delta [tset]. Ltac mkr__map_cbv_set_3 := cbv beta iota delta [tset].

Ltac norm_fchain :=
repeat match goal with
| |- context [@bvmap_set 5 word ?k ?x (@bvmap_set 5 word ?k' ?y ?R)] =>
let a := eval vm_compute in (bv_unsigned k) in
let b := eval vm_compute in (bv_unsigned k') in
let c := eval vm_compute in (Z.compare a b) in
lazymatch c with
| Eq => rewrite (bvmap_set_set_same' k k' x y R) by reflexivity
| Gt => rewrite (bvmap_set_set_comm k k' x y R) by reflexivity
end
end.

Ltac simp_regs :=
repeat match goal with
| |- context [reg_get ?R ?r] =>
is_concrete_map R;
let p := eval vm_compute in (bv_key r) in
change (reg_get R r) with (match tget p R with Some v => v | None => w0 end);
map_cbv_get
| |- context [@bvmap_set 5 word ?r ?v ?R] =>
is_concrete_map R;
let p := eval vm_compute in (bv_key r) in
change (@bvmap_set 5 word r v R) with (tset p v R);
map_cbv_set
| |- context [reg_get (@bvmap_set 5 word ?k ?v ?R) ?r] =>
first [ rewrite (freg_get_same R k r v) by reflexivity
| rewrite (freg_get_other R k r v) by reflexivity ]
end;
norm_fchain.

Ltac exec_cbv :=
cbv beta iota zeta delta [lift_result interp_eff exec with_pc with_regs with_fregs with_fcsr with_resv
rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
width_bytes accrue fari_d fcmp_d fari_s fcmp_s].

Ltac vnorm_rw_for i :=
lazymatch i with
| OpImm ALU_ADD _ _ _ => rewrite ?alu_addi
| OpImm ALU_AND _ _ _ => rewrite ?alu_andi
| OpImm ALU_OR _ _ _ => rewrite ?alu_ori
| OpImm ALU_XOR _ _ _ => rewrite ?alu_xori
| OpImm ALU_SLT _ _ _ => rewrite ?alu_slti
| OpImm ALU_SLTU _ _ _ => rewrite ?alu_sltiu
| ShiftImm ALU_SLL _ _ _ => rewrite ?alu_slli
| ShiftImm ALU_SRL _ _ _ => rewrite ?alu_srli
| ShiftImm ALU_SRA _ _ _ => rewrite ?alu_srai
| Op ALU_ADD _ _ _ => rewrite ?alu_add
| Op ALU_SUB _ _ _ => rewrite ?alu_sub
| Op ALU_SLT _ _ _ => rewrite ?alu_slt
| Op ALU_SLTU _ _ _ => rewrite ?alu_sltu
| Op ALU_AND _ _ _ => rewrite ?alu_and
| Op ALU_OR _ _ _ => rewrite ?alu_or
| Op ALU_XOR _ _ _ => rewrite ?alu_xor
| Op ALU_SLL _ _ _ => rewrite ?alu_sll
| Op ALU_SRL _ _ _ => rewrite ?alu_srl
| Op ALU_SRA _ _ _ => rewrite ?alu_sra
| OpImm32 _ _ _ => rewrite ?w_addiw
| ShiftImm32 ALU_SLL _ _ _ => rewrite ?w_slliw
| ShiftImm32 ALU_SRL _ _ _ => rewrite ?w_srliw
| ShiftImm32 ALU_SRA _ _ _ => rewrite ?w_sraiw
| Op32 ALU_ADD _ _ _ => rewrite ?w_addw
| Op32 ALU_SUB _ _ _ => rewrite ?w_subw
| Op32 ALU_SLL _ _ _ => rewrite ?w_sllw
| Op32 ALU_SRL _ _ _ => rewrite ?w_srlw
| Op32 ALU_SRA _ _ _ => rewrite ?w_sraw
| Mul M_MUL _ _ _ => rewrite ?m_mul
| Mul M_MULH _ _ _ => rewrite ?m_mulh
| Mul M_MULHSU _ _ _ => rewrite ?m_mulhsu
| Mul M_MULHU _ _ _ => rewrite ?m_mulhu
| Mul M_DIV _ _ _ => rewrite ?m_div
| Mul M_REM _ _ _ => rewrite ?m_rem
| Mul32 M_MUL _ _ _ => rewrite ?w_mulw
| Mul32 M_DIV _ _ _ => rewrite ?w_divw
| Mul32 M_REM _ _ _ => rewrite ?w_remw
| Mul32 M_DIVU _ _ _ => rewrite ?w_divuw
| Mul32 M_REMU _ _ _ => rewrite ?w_remuw
| Lui _ _ => rewrite ?b_lui
| Auipc _ _ => rewrite ?b_auipc
| Load _ _ _ _ _ => rewrite ?b_addsext
| Store _ _ _ _ => rewrite ?b_addsext
| FLoad _ _ _ _ => rewrite ?b_addsext
| FStore _ _ _ _ => rewrite ?b_addsext
| Jalr _ _ _ => rewrite ?b_addsext
| Jal _ _ => rewrite ?b_addsext
| Branch _ _ _ _ => rewrite ?b_addsext

| Fsgnj _ _ _ _ _ => rewrite ?sgnj_self, ?sgnjx_self, ?sgnjn_self
| Fmv _ _ _ _ => rewrite ?fmv_x_w_val; fold_lit_load
| Fari _ _ _ _ _ _ => idtac
| Fcmp _ _ _ _ _ => idtac
| Fcvt _ _ _ _ _ => idtac
| Fsqrt _ _ _ _ => idtac
| Fminmax _ _ _ _ _ => idtac
| Fclass _ _ _ => idtac
| Csr _ _ _ _ => idtac
| CsrI _ _ _ _ => idtac
| _ =>
rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
?b_addsext, ?b_lui, ?b_auipc
end.

Ltac vnorm_tail :=
(match goal with |- context [@bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 _)] => rewrite ?lit_add_lit | _ => idtac end);
(match goal with |- context [w0] => rewrite ?w0_lit | _ => idtac end);
(match goal with |- context [w1] => rewrite ?w1_lit | _ => idtac end);
unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt;
(match goal with |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r | _ => idtac end);
fold_closed_in_goal;
(match goal with |- context [Z_to_bv 64 (bv_unsigned _)] => rewrite ?Z_to_bv_lit_self | _ => idtac end);
(match goal with |- context [bv_and _ (bv_not _)] => rewrite ?ret_pc_fold | _ => idtac end);

repeat match goal with
| |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.

Ltac vnorm_for i := vnorm_rw_for i; vnorm_tail.

Ltac vnorm :=
rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
?b_addsext, ?b_lui, ?b_auipc, ?lit_add_lit, ?w0_lit, ?w1_lit;
unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt;
rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r;
fold_closed_in_goal;
rewrite ?Z_to_bv_lit_self, ?ret_pc_fold;

repeat match goal with
| |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.

Ltac zlit a := lazymatch a with Z0 => a | Zpos _ => a | Zneg _ => a end.

Ltac addr_diff E A :=
lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end. Ltac mkr__addr_diff_4 E A := lazymatch E with
| Z.add ?X ?c1 =>
lazymatch A with
| Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
| X => zlit c1
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
| _ =>
lazymatch A with
| Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
| E => constr:(0%Z)
| _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
end
end.

Ltac addr_expr a :=
lazymatch a with
| Z_to_bv 64 ?E => E
| wa ?E => E
| _ => constr:(Z.add (bv_unsigned a) 0)
end.

Ltac addr_eq_tac := symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]. Ltac mkr__addr_eq_tac_5 := symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ].

Ltac cells_cbv := cbv beta iota zeta delta [cell_at cell_upd csize cells_size Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add cbytes].

Ltac eval_cb_split cs kn n :=
eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split cs kn n).
Ltac eval_cb_split_ok cs kn n :=
eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split_ok cs kn n).

Ltac split_for_access H segs m A cs kn n :=
let ok := eval_cb_split_ok cs kn n in
lazymatch ok with
| true =>
let cs2 := eval_cb_split cs kn n in
lazymatch cs2 with
| cs => idtac
| _ => first [ apply (rw_cells_cb_split segs m A cs cs2 kn n) in H
| apply (ro_cells_cb_split segs m A cs cs2 kn n) in H ];
[ | cells_cbv; reflexivity | cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app]; reflexivity ]
end
end.

Ltac eval_cell_at cs kn := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn).

Ltac load_post :=
cbv beta iota delta [cbytes];
rewrite ?load_u64, ?zext_extract_le4, ?sext_extract_le4, ?zext_extract_le2, ?sext_extract_le2,
?zext_extract_le1, ?sext_extract_le1, ?zext_extract_byte, ?sext_extract_byte;
fold_lit_load.

Ltac addr_near_bound := constr:(16384%Z).
Ltac addr_near k :=
let bnd := addr_near_bound in
let b := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k bnd))%Z in
lazymatch b with true => idtac | false => fail end.

Ltac solve_load_base :=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
addr_near k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
addr_near k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
|
replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post. Ltac mkr__solve_load_base_6 := match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
addr_near k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
addr_near k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
|
replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.

Ltac solve_load := solve_load_base. Ltac mkr__solve_load_7 := solve_load_base.

Ltac solve_store :=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
addr_near k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);

try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end. Ltac mkr__solve_store_8 := match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
addr_near k;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);

try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.

Ltac cell_of_bytes bs :=
lazymatch bs with
| le8 ?v => constr:(C8 v)
| le4 ?v => constr:(C4 v)
| le2 ?v => constr:(C2 v)
| [?b] => constr:(C1 b)
| le1 (zxb ?b) => constr:(C1 b)
end. Ltac mkr__cell_of_bytes_9 bs := lazymatch bs with
| le8 ?v => constr:(C8 v)
| le4 ?v => constr:(C4 v)
| le2 ?v => constr:(C2 v)
| [?b] => constr:(C1 b)
| le1 (zxb ?b) => constr:(C1 b)
end.

Ltac simpl_sizes :=
rewrite ?app_length;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].

Ltac transport_chunks segs m a bs :=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end. Ltac mkr__transport_chunks_10 segs m a bs := repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end.

Ltac mem_after_store :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
lazymatch goal with
| H : rw_cells segs m A ?cs |- _ =>
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>

try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; try clear m; try rename H' into H
end
end
end. Ltac mkr__mem_after_store_11 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
lazymatch goal with
| H : rw_cells segs m A ?cs |- _ =>
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>

try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; try clear m; try rename H' into H
end
end
end.

Ltac mem_after_store_opt :=
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
| _ => idtac
end. Ltac mkr__mem_after_store_opt_12 := lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
| _ => idtac
end.

Ltac rm_proof rm c :=
let z := eval vm_compute in (bv_unsigned rm) in
lazymatch z with
| 7%Z =>
lazymatch c with
| Core _ _ _ ?fc _ =>
lazymatch goal with
| FRM : frm0 fc |- _ => constr:(rmode_dyn rm c (@eq_refl Z 7%Z) FRM)
| _ => fail 100 "FP instruction with dynamic rounding mode: need a hypothesis [frm0" fc "]"
end
end
| _ =>
let md := eval vm_compute in (match rmode_of_Z z with Some md => md | None => RNE end) in
constr:(rmode_static rm c md (@eq_refl bool false) (@eq_refl (option rmode) (Some md)))
end.

Ltac exec_pre i :=
lazymatch goal with
| |- context [exec ?sz _ ?c] =>
lazymatch i with
| Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
| Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
| Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
| Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
| Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
| Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv zeta
| Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
| Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
| Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
| Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
| Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
| Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
| Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
| Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
| Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
| Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
| Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
| Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
| Csr ?op ?rd ?rs1 ?csr =>
let sl := eval vm_compute in (csr_slice csr) in
lazymatch sl with
| Some (?lo, ?len) =>
rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv iota
| None => fail 100 "CSR access to an unknown CSR:" csr
end
| CsrI ?op ?rd ?uimm ?csr =>
let sl := eval vm_compute in (csr_slice csr) in
lazymatch sl with
| Some (?lo, ?len) =>
rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv iota
| None => fail 100 "CSR access to an unknown CSR:" csr
end
| _ => idtac
end
end;

try match goal with
| FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
end. Ltac mkr__exec_pre_13 i := lazymatch goal with
| |- context [exec ?sz _ ?c] =>
lazymatch i with
| Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
| Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
| Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
| Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
| Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
| Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv zeta
| Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
| Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
| Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
| Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
| Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
| Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
| Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
| Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
| Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
| Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
| Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
| Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
| Csr ?op ?rd ?rs1 ?csr =>
let sl := eval vm_compute in (csr_slice csr) in
lazymatch sl with
| Some (?lo, ?len) =>
rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv iota
| None => fail 100 "CSR access to an unknown CSR:" csr
end
| CsrI ?op ?rd ?uimm ?csr =>
let sl := eval vm_compute in (csr_slice csr) in
lazymatch sl with
| Some (?lo, ?len) =>
rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv iota
| None => fail 100 "CSR access to an unknown CSR:" csr
end
| _ => idtac
end
end;

try match goal with
| FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
end.

Ltac prove_frm0 :=
first [ assumption
| apply frm0_accrue; prove_frm0
| apply frm0_slice_set_fflags; prove_frm0 ].

Ltac norm_fcsr :=
lazymatch goal with
| |- evt _ _ (MS _ _ _ ?fce _ _ _) =>
tryif is_var fce then idtac else
(let fcn := fresh "fc" in
let E := fresh "Efc" in
tryif (let H := fresh "FRM" in
assert (H : frm0 fce) by prove_frm0;
repeat match goal with
| H' : frm0 ?f |- _ => lazymatch f with fce => fail | _ => clear H' end
end;
remember fce as fcn eqn:E; clear E;
try rename H into FRM)
then idtac
else (remember fce as fcn eqn:E; clear E))
| _ => idtac
end.

Ltac post_step i :=
lazymatch i with
| Fari _ _ _ _ _ _ => norm_fcsr
| Fcmp _ _ _ _ _ => norm_fcsr
| Fcvt _ _ _ _ _ => norm_fcsr
| Fsqrt _ _ _ _ => norm_fcsr
| Fminmax _ _ _ _ _ => norm_fcsr
| Fma _ _ _ _ _ _ _ => norm_fcsr
| Csr _ _ _ _ => norm_fcsr
| CsrI _ _ _ _ => norm_fcsr
| _ => idtac
end.

Ltac step_core_old segs R F pc fc rv m ro :=
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with
| Some ?w =>
let ec := eval vm_compute in (is_ecall w) in
lazymatch ec with
| false =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_pre i;
exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store;
reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
| None => fail "undecodable instruction at" pc
end
| true => fail "ecall at" pc
end
| None => fail "no instruction at" pc
end.

Ltac step_core segs R F pc fc rv m ro := step_core_old segs R F pc fc rv m ro. Ltac mkr__step_core_14 segs R F pc fc rv m ro := step_core_old segs R F pc fc rv m ro.

Ltac step :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro
| |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
end. Ltac mkr__step_15 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro
| |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
end.

Ltac unfold_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb].

Ltac fold_lit_ux :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
| |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
end.
Ltac solve_cond_base :=
first [ reflexivity
| apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
| apply Z.leb_le; lia | apply Z.leb_gt; lia
| apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ].
Ltac solve_cond_rec :=
lazymatch goal with
| |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec
| |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec
| _ => solve_cond_base
end.
Ltac solve_cond := unfold_cond; fold_lit_ux; solve_cond_rec.
Ltac if_true :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with true; [cbv iota| symmetry; solve_cond]
end. Ltac mkr__if_true_16 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with true; [cbv iota| symmetry; solve_cond]
end.
Ltac if_false :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with false; [cbv iota| symmetry; solve_cond]
end. Ltac mkr__if_false_17 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with false; [cbv iota| symmetry; solve_cond]
end.
Ltac if_true_by H :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with true; [cbv iota| symmetry; exact H]
end.
Ltac if_false_by H :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with false; [cbv iota| symmetry; exact H]
end.

Ltac if_cases H :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
destruct c eqn:H; [ | ]
end.

Ltac fold_lit_ux_in H :=
repeat match type of H with
| context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
replace (bv_unsigned (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
| context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
replace (bv_signed (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
end.

Ltac zify_bool H :=
lazymatch type of H with
| negb _ = true => apply (proj1 (Bool.negb_true_iff _)) in H; zify_bool H
| negb _ = false => apply (proj1 (Bool.negb_false_iff _)) in H; zify_bool H
| Z.eqb (Z.b2z ?b) 0 = true => apply Z.eqb_eq in H; apply (proj1 (zb_b2z_zero b)) in H; zify_bool H
| Z.eqb (Z.b2z ?b) 0 = false => apply Z.eqb_neq in H; apply (proj1 (zb_b2z_nonzero b)) in H; zify_bool H
| Z.eqb _ _ = true => apply Z.eqb_eq in H
| Z.eqb _ _ = false => apply Z.eqb_neq in H
| Z.ltb _ _ = true => apply Z.ltb_lt in H
| Z.ltb _ _ = false => apply Z.ltb_ge in H
| Z.leb _ _ = true => apply Z.leb_le in H
| Z.leb _ _ = false => apply Z.leb_gt in H
| andb _ _ = true =>
apply andb_true_iff in H;
let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
| orb _ _ = false =>
apply orb_false_iff in H;
let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
| _ => idtac
end.

Ltac zify_cond H :=
rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H;
unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; zsimp_in H;
zify_bool H.

Ltac concretize_regs :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
let t := eval vm_compute in R in change R with t
end.

Ltac step_old :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core_old segs R F pc fc rv m ro
| |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
end.
Ltac zstep_old := step_old; zsimp.
Ltac zstep := step; zsimp. Ltac mkr__zstep_18 := step; zsimp.
