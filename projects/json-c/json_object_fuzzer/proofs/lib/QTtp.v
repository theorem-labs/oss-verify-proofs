(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi QdTb QHWH Q1lV Qcrs QUcd QCUT QwAs Qc6I Qsn5 QNqr QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I Qsn5.
Import QNqr QNqr.Mq0 QeDS.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section LoopCpsP.
Variable segs : list Segment.

Inductive slbwP (V : config -> Prop) (T : TSet) : Prop -> config -> Prop :=
| slbwP_exit : forall (P : Prop) c, srealizes segs c T -> slbwP V T P c
| slbwP_node : forall (P : Prop) c (I : Type) (nx : I -> config) (k : I -> option Prop),
node_ok segs c I (fun _ => []) nx ->
(forall i Q, k i = Some Q -> slbwP V T Q (nx i)) ->
(forall i, k i = None -> V (nx i)) ->
(P -> exists i Q, k i = Some Q /\ Q) ->
slbwP V T P c.

Lemma slbwP_slbody : forall V T P c, slbwP V T P c -> slbody segs V T c.
Proof.
intros V T P c H; induction H as [P c Hr | P c I nx k Hnode Hk IHk HV Hw].
- apply slb_exit. exact Hr.
- apply (slb_node segs V T c I nx (fun i => match k i with Some _ => true | None => false end) Hnode).
+ intros i Hi. destruct (k i) as [q|] eqn:E; [| discriminate Hi]. eapply IHk. exact E.
+ intros i Hi. destruct (k i) as [q|] eqn:E; [discriminate Hi |]. apply HV. exact E.
Qed.

Lemma slbwP_witness : forall V T P c, slbwP V T P c -> P ->
exists c_e, star_cfg segs (alloc_only_cfg false) c [] c_e /\ srealizes segs c_e T.
Proof.
intros V T P c H; induction H as [P c Hr | P c I nx k Hnode Hk IHk HV Hw]; intros Hp.
- exists c. split; [apply star_cfg_refl | exact Hr].
- destruct (Hw Hp) as (i & Q & Hi & HQ).
destruct (IHk i Q Hi HQ) as (c_e & Hs & He).
exists c_e. split; [| exact He].
destruct Hnode as [Hcomp _].
change ([] : list event) with ([] ++ [] : list event).
eapply star_cfg_step; [apply (Hcomp i) | exact Hs].
Qed.

Theorem srz_loop_wP : forall (V : config -> Prop) (T : TSet) c,
V c -> (forall c', V c' -> slbwP V T True c') -> srealizes segs c T.
Proof.
intros V T c HV Hbody.
destruct (slbwP_witness V T True c (Hbody c HV) I) as (c_e & Hs & He).
apply (srz_loop segs V T c c_e HV); [| exact Hs | exact He].
intros c' HV'. eapply slbwP_slbody. apply Hbody. exact HV'.
Qed.

Lemma slbwP_imp : forall V T (P P' : Prop) c, (P' -> P) -> slbwP V T P c -> slbwP V T P' c.
Proof.
intros V T P P' c HPP H. destruct H as [P c Hr | P c I nx k Hnode Hk HV Hw].
- apply slbwP_exit. exact Hr.
- apply (slbwP_node V T P' c I nx k Hnode Hk HV). intros HP'. exact (Hw (HPP HP')).
Qed.

Lemma slbwP_nclosedT : forall V T (P : Prop) c (I : Type) (nx : I -> config) (Q : I -> Prop),
node_ok segs c I (fun _ => []) nx -> (forall i, slbwP V T (Q i) (nx i)) -> (P -> exists i, Q i) -> slbwP V T P c.
Proof.
intros V T P c I nx Q Hnode Hc Hw.
apply (slbwP_node V T P c I nx (fun i => Some (Q i)) Hnode).
- intros i Q0 HQ0. injection HQ0 as <-. apply Hc.
- intros i H. discriminate H.
- intros HP. destruct (Hw HP) as [i Hi]. exists i, (Q i). split; [reflexivity| exact Hi].
Qed.

Lemma slbwP_nclosed : forall V T (P : Prop) c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx -> (forall i, slbwP V T P (nx i)) -> slbwP V T P c.
Proof.
intros V T P c I nx i0 Hnode Hc.
apply (slbwP_nclosedT V T P c I nx (fun _ => P) Hnode Hc). intros HP. exists i0. exact HP.
Qed.

Lemma slbwP_back1 : forall V T (P : Prop) c c', ~ P ->
node_ok segs c unit (fun _ => []) (fun _ => c') -> V c' -> slbwP V T P c.
Proof.
intros V T P c c' HnP Hn HV.
apply (slbwP_node V T P c unit (fun _ => c') (fun _ => None) Hn).
- intros [] q Hq. discriminate Hq.
- intros [] _. exact HV.
- intros HP. exfalso. exact (HnP HP).
Qed.

Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.

Definition JLP (VV : config -> machine_state -> Prop) (T : TSet) (X : TSet) : config -> Prop :=
slbwP (Vof L VV) T (X []).

Lemma jlp_nclosed : forall VV T X c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx -> (forall i, JLP VV T X (nx i)) -> JLP VV T X c.
Proof. intros VV T X. apply slbwP_nclosed. Qed.

Lemma jlp_silent_closed : forall VV T X, silent_closed L segs (JLP VV T X).
Proof.
intros VV T X ms mo ms' mo' Hnode _ _ _ _ HJ.
apply (jlp_nclosed VV T X (mkCfg ms mo) unit (fun _ => mkCfg ms' mo') tt Hnode). intros []. exact HJ.
Qed.

Lemma jlp_conseq : forall VV T X X' c, t_eq X X' -> JLP VV T X c -> JLP VV T X' c.
Proof. intros VV T X X' c E H. unfold JLP in *. eapply slbwP_imp; [| exact H]. intros H'. apply (proj2 (E [])). exact H'. Qed.

Lemma vjP_exit : forall VV T X c msv, VJ L (JS segs T) c msv -> VJ L (JLP VV T X) c msv.
Proof. intros VV T X c msv H ms mo Hr. apply slbwP_exit. exact (H ms mo Hr). Qed.

Lemma vjP_back1 : forall (VV : config -> machine_state -> Prop) T X c msv msv',
~ X [] -> mstep segs msv msv' -> VV c msv' -> VJ L (JLP VV T X) c msv.
Proof.
intros VV T X c msv msv' HnX Hst HVV ms mo (Hv & Hd & HI & Hh & Hhid).
rewrite <- Hv in Hst.
destruct (mstep_view L segs Hwx Hsegs mo ms msv' HI Hh Hst) as (ms1 & mo1 & _ & Hss & Hdet & Hv1 & Hd1 & Hhid1 & _).
apply (slbwP_back1 (Vof L VV) T (X []) (mkCfg ms mo) (mkCfg ms1 mo1) HnX).
- split; [intros []; exact Hss|]. intros e st Hst'. exists tt. exact (Hdet e st Hst').
- exists c, msv'. split; [exact HVV|]. cbn [cfg_ms cfg_model].
pose proof (drift_frame L _ _ Hd1) as (_ & _ & Hh1 & _).
repeat split.
+ exact Hv1.
+ exact (drift_trans L _ _ _ Hd Hd1).
+ exact (lv_inv_drift L _ _ HI Hd1).
+ rewrite Hh1. exact Hh.
+ intros a Ha. rewrite Hhid1 by (rewrite (hidden_ext L _ _ (drift_vmeq L _ _ Hd)); exact Ha). apply Hhid. exact Ha.
Qed.

Lemma vjP_back : forall (VV : config -> machine_state -> Prop) T X c, ~ X [] ->
forall msv1 msv', msteps segs msv1 msv' -> forall msv, mstep segs msv msv1 -> VV c msv' -> VJ L (JLP VV T X) c msv.
Proof.
intros VV T X c HnX msv1 msv' Hms. induction Hms as [m0 | m0 m1 m2 Hst01 Hms12 IH]; intros msv Hst HVV.
- exact (vjP_back1 VV T X c msv m0 HnX Hst HVV).
- apply (vj_evt segs L Hwx Hsegs _ (jlp_silent_closed VV T X)).
exists m0. split; [apply msteps_one; exact Hst|]. exact (IH m0 Hst01 HVV).
Qed.

Lemma vjP_back_evt : forall (VV : config -> machine_state -> Prop) T X c msv, ~ X [] ->
~ VV c msv -> evt segs (VV c) msv -> VJ L (JLP VV T X) c msv.
Proof.
intros VV T X c msv HnX HnV (msv' & Hms & HVV).
destruct Hms as [m0 | m0 m1 m2 Hst Hms]; [exfalso; exact (HnV HVV)|].
exact (vjP_back VV T X c HnX m1 m2 Hms m0 Hst HVV).
Qed.

Theorem vj_loopP : forall (VV : config -> machine_state -> Prop) T (Xw : TSet) c0 msv0,
Xw [] -> VV c0 msv0 ->
(forall c msv, VV c msv -> VJ L (JLP VV T Xw) c msv) ->
VJ L (JS segs T) c0 msv0.
Proof.
intros VV T Xw c0 msv0 Hw H0 Hbody ms mo Hr. unfold JS.
apply (srz_loop_wP (Vof L VV) T (mkCfg ms mo)).
- exists c0, msv0. split; [exact H0| exact Hr].
- intros [ms' mo'] (c & msv & HVV & Hr'). pose proof (Hbody c msv HVV ms' mo' Hr') as Hb. unfold JLP in Hb.
eapply slbwP_imp; [| exact Hb]. intros _. exact Hw.
Qed.

End LoopCpsP.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHWH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS.Mq1.
Import ListNotations.
Open Scope Z_scope.

Section ImplVisCps.
Variable node : Type.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.
Variable at_node : node -> machine_state -> Prop.
Variable nstep_raw : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit_raw : node -> Model -> word -> Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable xinv : Model -> Prop.
Variable is_spin : node -> bool.
Variable rvar : node -> resp -> resp -> Prop.
Variable jinv : Model -> (word -> option byte) -> Prop.
Hypothesis jinv_stable : forall mo mo' m m',
vmeq mo mo' -> (forall a, hidden L mo a = true -> m' a = m a) -> jinv mo m -> jinv mo' m'.
Hypothesis NS : node_soundA node segs L at_node nstep_raw nexit_raw nsafe xinv is_spin rvar jinv.

Notation cinvA := (cinv L xinv jinv).
Notation nstA := (nstepA L nstep_raw).
Notation tpathA := (tpath nstA).

Fixpoint tsetK {R} (t : itree node R) (Tk : R -> TSet) (mo : Model) : TSet :=
match t with
| Ret r => Tk r
| Vis n k => fun tr =>
tr = []
\/ (exists mo1 rsp mo' evs, drift L mo mo1 /\ nstep_raw n mo1 rsp mo' evs /\ t_emit evs (tsetK (k rsp) Tk mo') tr)
\/ (exists mo1 code mo', drift L mo mo1 /\ nexit_raw n mo1 code mo' /\ is_prefix tr [ExitEv code (m_fs mo')])
end.

Fixpoint tnospin {R} (t : itree node R) : Prop :=
match t with
| Ret _ => True
| Vis n k => is_spin n = false /\ forall r, tnospin (k r)
end.

Lemma tsetK_msim : forall {R} (t : itree node R) Tk moA moB tr, msim moA moB -> tsetK t Tk moA tr -> tsetK t Tk moB tr.
Proof.
intros R t Tk. induction t as [r|n k IH]; intros moA moB tr Hs H; [exact H|].
cbn in H |- *. destruct H as [H|[(mo1 & rsp & mo' & evs & Hd & Hr & He)|(mo1 & code & mo' & Hd & Hx & Hp)]].
- left; exact H.
- right; left.
assert (Hs1 : msim mo1 moB).
{ eapply msim_trans; [apply msim_sym; eapply drift_msim; exact Hd| exact Hs]. }
destruct (nsA_msim _ _ _ _ _ _ _ _ _ _ _ NS n mo1 moB rsp mo' evs Hs1 Hr) as (mo'b & Hr' & Hs').
exists moB, rsp, mo'b, evs. split; [apply drift_refl|]. split; [exact Hr'|].
eapply t_emit_mono; [|exact He]. intros tr0. apply IH. exact Hs'.
- right; right.
assert (Hs1 : msim mo1 moB).
{ eapply msim_trans; [apply msim_sym; eapply drift_msim; exact Hd| exact Hs]. }
destruct (nsA_msim_exit _ _ _ _ _ _ _ _ _ _ _ NS n mo1 moB code mo' Hs1 Hx) as (mo'b & Hx' & Hs').
exists moB, code, mo'b. split; [apply drift_refl|]. split; [exact Hx'|].
pose proof (msim_facts L _ _ Hs') as (_ & Hfs & _). rewrite Hfs. exact Hp.
Qed.

Lemma tsetK_msim_eq : forall {R} (t : itree node R) Tk moA moB, msim moA moB -> t_eq (tsetK t Tk moA) (tsetK t Tk moB).
Proof. intros R t Tk moA moB Hs tr. split; apply tsetK_msim; [exact Hs| apply msim_sym; exact Hs]. Qed.

Theorem impl_vj_vis : forall {R} (t : itree node R) (Tk : R -> TSet) (Q : R -> machine_state -> Prop) c0 msv,
impl segs at_node t Q msv ->
cinvA (cfg_ms c0) (cfg_model c0) ->
tsafe nstA nsafe t (cfg_model c0) -> tobliv rvar t -> tnospin t ->
(forall r evs c1 msv1,
evt segs (Q r) msv1 ->
tpathA t (cfg_model c0) evs r (cfg_model c1) ->
cinvA (cfg_ms c1) (cfg_model c1) ->
msview L (cfg_model c1) (cfg_ms c1) = msv1 \/ (c1 = c0 /\ msv1 = msv) ->
VJ L (JS segs (Tk r)) c1 msv1) ->
VJ L (JS segs (tsetK t Tk (cfg_model c0))) c0 msv.
Proof.
intros R t Tk. induction t as [r|n k IH]; intros Q c0 msv Himpl HC Hsafe Hobl Hnsp HK.
- cbn [impl] in Himpl. cbn [tsetK].
apply (HK r [] c0 msv Himpl); [cbn; auto| exact HC| right; split; reflexivity].
- cbn [impl] in Himpl. cbn [tsafe] in Hsafe. destruct Hsafe as [Hns Hks].
cbn [tobliv] in Hobl. destruct Hobl as [Hobn Hobk]. cbn [tnospin] in Hnsp. destruct Hnsp as [Hsp Hspk].
apply (vj_evt segs L Hwx Hsegs _ (silent_closed_srealizes segs L _)).
eapply evt_mono; [exact Himpl|]. cbv beta. intros ms1 [Hat Hk].
apply (vj_vis_k node segs L at_node nstep_raw nexit_raw nsafe xinv is_spin rvar jinv jinv_stable NS
n (fun rsp mo' _ => tsetK (k rsp) Tk mo') _ c0 ms1 Hsp Hat HC Hns).
+ intros r r2 mo' mo2 evs Hrv Hs. rewrite (Hobn r r2 Hrv). apply tsetK_msim_eq. exact Hs.
+ intros mo1 rsp evs c1 Hd Hr HC1 Hh1 Hv1.
assert (HstA : nstA n (cfg_model c0) rsp (cfg_model c1) evs) by (exists mo1; split; assumption).
apply (IH rsp Q c1 (nret ms1 rsp)); [apply Hk| exact HC1| exact (Hks rsp _ evs HstA)| apply Hobk| apply Hspk|].
intros r evs2 c2 msv2 HQ Hp HC2 Hc2. apply (HK r (evs ++ evs2) c2 msv2 HQ); [|exact HC2|].
* cbn [tpath]. exists rsp, (cfg_model c1), evs, evs2. split; [exact HstA|]. split; [exact Hp| reflexivity].
* destruct Hc2 as [Hc2|[-> ->]]; [left; exact Hc2|]. left. exact Hv1.
+ intros mo1 Hd tr. cbn [tsetK]. split.
* intros [H|[(mo1' & rsp & mo' & evs & Hd' & Hr & He)|(mo1' & code & mo' & Hd' & Hx & Hp)]].
-- left; exact H.
-- right; left.
assert (Hs1 : msim mo1' mo1).
{ eapply msim_trans; [apply msim_sym; eapply drift_msim; exact Hd'| eapply drift_msim; exact Hd]. }
destruct (nsA_msim _ _ _ _ _ _ _ _ _ _ _ NS n mo1' mo1 rsp mo' evs Hs1 Hr) as (mo'b & Hr' & Hs').
exists rsp, mo'b, evs. split; [exact Hr'|].
eapply t_emit_mono; [|exact He]. intros tr0. apply tsetK_msim. exact Hs'.
-- right; right.
assert (Hs1 : msim mo1' mo1).
{ eapply msim_trans; [apply msim_sym; eapply drift_msim; exact Hd'| eapply drift_msim; exact Hd]. }
destruct (nsA_msim_exit _ _ _ _ _ _ _ _ _ _ _ NS n mo1' mo1 code mo' Hs1 Hx) as (mo'b & Hx' & Hs').
exists code, mo'b. split; [exact Hx'|].
pose proof (msim_facts L _ _ Hs') as (_ & Hfs & _). rewrite Hfs. exact Hp.
* intros [H|[(rsp & mo' & evs & Hr & He)|(code & mo' & Hx & Hp)]].
-- left; exact H.
-- right; left. exists mo1, rsp, mo', evs. split; [exact Hd|]. split; [exact Hr| exact He].
-- right; right. exists mo1, code, mo'. split; [exact Hd|]. split; [exact Hx| exact Hp].
Qed.

End ImplVisCps.
