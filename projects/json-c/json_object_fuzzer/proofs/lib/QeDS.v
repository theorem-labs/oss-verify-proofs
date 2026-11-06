(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi QdTb QHWH Q1lV Qcrs QUcd QCUT QwAs Qc6I Qsn5 QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I Qsn5.
Import QNqr QNqr.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section LoopCps.
Variable segs : list Segment.

Inductive slbw (V : config -> Prop) (T : TSet) : bool -> config -> Prop :=
| slbw_exit : forall p c, srealizes segs c T -> slbw V T p c
| slbw_node : forall p c (I : Type) (nx : I -> config) (k : I -> option bool),
node_ok segs c I (fun _ => []) nx ->
(forall i q, k i = Some q -> slbw V T q (nx i)) ->
(forall i, k i = None -> V (nx i)) ->
(p = true -> exists i, k i = Some true) ->
slbw V T p c.

Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.

Definition Vof (VV : config -> machine_state -> Prop) : config -> Prop :=
fun cfg => exists c msv, VV c msv /\ vrel L c msv (cfg_ms cfg) (cfg_model cfg).

End LoopCps.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I Qsn5 Qknc.
Import QNqr QNqr.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section NodeCps.
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

Lemma obs_trace_halted' : forall ms mo tr, m_halted mo <> None -> obs_trace_cfg segs (alloc_only_cfg false) (mkCfg ms mo) tr -> tr = [].
Proof.
intros ms mo tr Hh (tr' & c & Hstar & Hp).
destruct (star_halted_nil segs ms mo tr' c Hh (star_cfg_sub segs _ _ _ _ Hstar)) as [-> _].
destruct tr; [reflexivity| destruct Hp].
Qed.

Theorem vj_vis : forall (n : node) (Tk : resp -> Model -> list event -> TSet) (T : TSet) c0 msv,
is_spin n = false ->
at_node n msv ->
cinvA (cfg_ms c0) (cfg_model c0) ->
nsafe n (cfg_model c0) ->
(forall r r2 mo' mo2 evs, rvar n r r2 -> msim mo' mo2 -> t_eq (Tk r mo' evs) (Tk r2 mo2 evs)) ->
(forall mo1 rsp mo' evs ms', drift L (cfg_model c0) mo1 -> nstep_raw n mo1 rsp mo' evs ->
cinvA ms' mo' -> m_halted mo' = None -> msview L mo' ms' = nret msv rsp ->
srealizes segs (mkCfg ms' mo') (Tk rsp mo' evs)) ->
(forall mo1, drift L (cfg_model c0) mo1 ->
t_eq T (fun tr => tr = []
\/ (exists rsp mo' evs, nstep_raw n mo1 rsp mo' evs /\ t_emit evs (Tk rsp mo' evs) tr)
\/ (exists code mo', nexit_raw n mo1 code mo' /\ is_prefix tr [ExitEv code (m_fs mo')]))) ->
VJ L (JS segs T) c0 msv.
Proof.
intros n Tk T [ms0 mo0] msv Hsp Hat HC Hns Hobl HK HT ms1 mo1 (Hv1 & Hd1 & HI1 & Hh1 & Hhid1). cbn [cfg_ms cfg_model] in *.
unfold JS.
assert (HC1 : cinvA ms1 mo1).
{ eapply (cinv_drift node segs L at_node nstep_raw nexit_raw nsafe xinv is_spin rvar jinv jinv_stable NS); [exact Hd1| exact Hhid1| exact HC]. }
assert (Hat1 : at_node n (msview L mo1 ms1)) by (rewrite Hv1; exact Hat).
assert (Hns1 : nsafe n mo1) by (eapply (nsA_safe_drift _ _ _ _ _ _ _ _ _ _ _ NS); eassumption).
set (c1 := mkCfg ms1 mo1).
set (Ix := { x : list event * config | sstep_cfg segs (alloc_only_cfg false) c1 (fst x) (SNext (snd x)) }).
assert (Hnode : node_ok segs c1 Ix (fun i => fst (proj1_sig i)) (fun i => snd (proj1_sig i))).
{ split; [intros [x Hx]; exact Hx|]. intros e st Hst.
destruct (nsA_complete _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 e st Hsp Hat1 Hh1 HC1 Hns1 Hst)
as [(rsp & ms' & mo' & -> & _)|(code & mo' & -> & _)].
- exists (exist _ (e, mkCfg ms' mo') Hst). split; reflexivity.
- exists (exist _ (e, mkCfg ms1 mo') Hst). split; reflexivity. }
assert (Hcont : forall i : Ix, srealizes segs (snd (proj1_sig i)) (obs_trace_cfg segs (alloc_only_cfg false) (snd (proj1_sig i)))).
{ intros [[e [ms' mo']] Hst]. cbn [fst snd proj1_sig] in *.
destruct (nsA_complete _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 e _ Hsp Hat1 Hh1 HC1 Hns1 Hst)
as [(rsp & ms'' & mo'' & E & Hv' & Hr & HC' & Hh')|(code & mo'' & E & Hx & -> & Hh')].
- injection E as <- <-.
assert (Hsr : srealizes segs (mkCfg ms' mo') (Tk rsp mo' e)).
{ apply (HK mo1 rsp mo' e ms' Hd1 Hr HC' Hh'). rewrite Hv', Hv1. reflexivity. }
eapply srz_conseq; [exact Hsr|]. intros tr. symmetry. apply srealizes_obs_iff. exact Hsr.
- injection E as <- <-.
eapply srz_conseq; [apply srz_halt; cbn; rewrite Hh'; discriminate|].
intros tr. split; [intros ->; exists [], (mkCfg ms' mo'); split; [apply star_cfg_refl| apply is_prefix_nil]|]. intros Ho. eapply obs_trace_halted'; [|exact Ho]. rewrite Hh'. discriminate. }
assert (Hi0 : exists i : Ix, True).
{ destruct (nsA_progress _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 Hsp Hat1 Hh1 HC1 Hns1) as [(rsp & mo' & evs & Hr)|(code & mo' & Hx)].
- destruct (nsA_sound _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 rsp mo' evs Hsp Hat1 Hh1 HC1 Hns1 Hr) as (ms' & mo2 & rsp2 & Hst & _).
exists (exist _ (evs, mkCfg ms' mo2) Hst). exact I.
- destruct (nsA_exit _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 code mo' Hsp Hat1 Hh1 HC1 Hns1 Hx) as [_ Hst].
exists (exist _ ([ExitEv code (m_fs mo')], mkCfg ms1 mo') Hst). exact I. }
destruct Hi0 as [i0 _].
eapply srz_conseq.
{ apply (srz_node segs c1 Ix (fun i => fst (proj1_sig i)) (fun i => snd (proj1_sig i))
(fun i => obs_trace_cfg segs (alloc_only_cfg false) (snd (proj1_sig i))) i0 Hnode Hcont). }
intros tr. rewrite (HT mo1 Hd1 tr). split.
- intros [[[e [ms' mo']] Hst] Hem]. cbn [fst snd proj1_sig] in Hem.
destruct (nsA_complete _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 e _ Hsp Hat1 Hh1 HC1 Hns1 Hst)
as [(rsp & ms'' & mo'' & E & Hv' & Hr & HC' & Hh')|(code & mo'' & E & Hx & -> & Hh')].
+ injection E as <- <-. right; left. exists rsp, mo', e. split; [exact Hr|].
eapply t_emit_mono; [|exact Hem]. intros tr0 Ho.
assert (Hsr : srealizes segs (mkCfg ms' mo') (Tk rsp mo' e)).
{ apply (HK mo1 rsp mo' e ms' Hd1 Hr HC' Hh'). rewrite Hv', Hv1. reflexivity. }
apply (srealizes_obs_iff segs _ _ Hsr). exact Ho.
+ injection E as <- <-. right; right. exists code, mo'. split; [exact Hx|].
destruct Hem as [Hp|(tr' & -> & Ho)]; [exact Hp|].
rewrite (obs_trace_halted' ms' mo' tr'); [rewrite app_nil_r; apply is_prefix_refl| rewrite Hh'; discriminate| exact Ho].
- intros [->|[(rsp & mo' & evs & Hr & Hem)|(code & mo' & Hx & Hp)]].
+ exists i0. left. apply is_prefix_nil.
+ destruct (nsA_sound _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 rsp mo' evs Hsp Hat1 Hh1 HC1 Hns1 Hr) as (ms' & mo2 & rsp2 & Hst & Hv' & Hr2 & Hs2 & Hrv & Hh2).
exists (exist _ (evs, mkCfg ms' mo2) Hst). cbn [fst snd proj1_sig].
eapply t_emit_mono; [|exact Hem]. intros tr0 Ht0.
destruct (nsA_complete _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 evs _ Hsp Hat1 Hh1 HC1 Hns1 Hst)
as [(rsp1 & ms'' & mo'' & E & _ & _ & HC' & Hh')|(code & mo'' & E & _ & _ & Hh')].
2:{ exfalso. injection E as _ E2. rewrite <- E2, Hh2 in Hh'. discriminate. }
injection E as E1 E2. subst ms'' mo''.
assert (Hsr : srealizes segs (mkCfg ms' mo2) (Tk rsp2 mo2 evs)).
{ apply (HK mo1 rsp2 mo2 evs ms' Hd1 Hr2 HC' Hh'). rewrite Hv', Hv1. reflexivity. }
apply (srealizes_obs_iff segs _ _ Hsr). apply (Hobl rsp rsp2 mo' mo2 evs Hrv Hs2). exact Ht0.
+ destruct (nsA_exit _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 code mo' Hsp Hat1 Hh1 HC1 Hns1 Hx) as [Hhb Hst].
exists (exist _ ([ExitEv code (m_fs mo')], mkCfg ms1 mo') Hst). cbn [fst snd proj1_sig].
left. exact Hp.
Qed.

Corollary vj_vis_k : forall (n : node) (Tk : resp -> Model -> list event -> TSet) (T : TSet) c0 msv,
is_spin n = false ->
at_node n msv ->
cinvA (cfg_ms c0) (cfg_model c0) ->
nsafe n (cfg_model c0) ->
(forall r r2 mo' mo2 evs, rvar n r r2 -> msim mo' mo2 -> t_eq (Tk r mo' evs) (Tk r2 mo2 evs)) ->
(forall mo1 rsp evs c1, drift L (cfg_model c0) mo1 -> nstep_raw n mo1 rsp (cfg_model c1) evs ->
cinvA (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
msview L (cfg_model c1) (cfg_ms c1) = nret msv rsp ->
VJ L (JS segs (Tk rsp (cfg_model c1) evs)) c1 (nret msv rsp)) ->
(forall mo1, drift L (cfg_model c0) mo1 ->
t_eq T (fun tr => tr = []
\/ (exists rsp mo' evs, nstep_raw n mo1 rsp mo' evs /\ t_emit evs (Tk rsp mo' evs) tr)
\/ (exists code mo', nexit_raw n mo1 code mo' /\ is_prefix tr [ExitEv code (m_fs mo')]))) ->
VJ L (JS segs T) c0 msv.
Proof.
intros n Tk T c0 msv Hsp Hat HC Hns Hobl HK HT.
apply (vj_vis n Tk T c0 msv Hsp Hat HC Hns Hobl); [|exact HT].
intros mo1 rsp mo' evs ms' Hd Hr HC' Hh' Hv'.
pose proof (HK mo1 rsp evs (mkCfg ms' mo') Hd Hr HC' Hh' Hv') as HV. cbn [cfg_ms cfg_model] in HV.
apply HV. rewrite <- Hv'. apply vrel_refl; [exact (proj1 (proj2 HC'))| exact Hh'].
Qed.

End NodeCps.
End Mq1.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.
Import ListNotations.
Open Scope Z_scope.

Section ImplCps.
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

Variable J : config -> Prop.
Hypothesis J_nclosed : forall c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx -> (forall i, J (nx i)) -> J c.

Lemma J_silent_closed : silent_closed L segs J.
Proof.
intros ms mo ms' mo' Hnode _ _ _ _ HJ.
apply (J_nclosed (mkCfg ms mo) unit (fun _ => mkCfg ms' mo') tt Hnode). intros []. exact HJ.
Qed.

Fixpoint tcps {R} (t : itree node R) (mo : Model) : Prop :=
match t with
| Ret _ => True
| Vis n k => is_spin n = false /\ nsafe n mo
/\ (forall mo1 code mo', drift L mo mo1 -> ~ nexit_raw n mo1 code mo')
/\ (forall rsp mo' evs, nstA n mo rsp mo' evs -> evs = [] /\ tcps (k rsp) mo')
end.

Notation tpathA := (tpath nstA).

Theorem impl_vj : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) c0 msv,
impl segs at_node t Q msv ->
cinvA (cfg_ms c0) (cfg_model c0) ->
tcps t (cfg_model c0) ->
(forall r c1 msv1,
evt segs (Q r) msv1 ->
tpathA t (cfg_model c0) [] r (cfg_model c1) ->
cinvA (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
msview L (cfg_model c1) (cfg_ms c1) = msv1 \/ (c1 = c0 /\ msv1 = msv) ->
VJ L J c1 msv1) ->
VJ L J c0 msv.
Proof.
intros R t. induction t as [r|n k IH]; intros Q c0 msv Himpl HC Hcps HK.
-
cbn [impl] in Himpl. intros ms mo Hrel.
assert (Hh0 : m_halted (cfg_model c0) = None).
{ destruct Hrel as (_ & Hd & _ & Hh & _).
pose proof (drift_frame L _ _ Hd) as (_ & _ & Hh1 & _). rewrite Hh1 in Hh. exact Hh. }
assert (Hp : tpathA (Ret r) (cfg_model c0) [] r (cfg_model c0)) by (cbn; auto).
exact (HK r c0 msv Himpl Hp HC Hh0 (or_intror (conj eq_refl eq_refl)) ms mo Hrel).
- cbn [impl] in Himpl. destruct Himpl as (msr1 & Hms & Hat & Hk).
cbn [tcps] in Hcps. destruct Hcps as (Hsp & Hns & Hnx & Hstep).
intros ms mo (Hv & Hd & HI & Hh & Hhid). destruct c0 as [ms0 mo0]. cbn [cfg_ms cfg_model] in *.

apply (msteps_view L segs Hwx Hsegs J J_silent_closed msv msr1 Hms mo ms (eq_sym Hv) HI Hh).
intros ms1 mo1 Hv1 Hd1 HI1 Hh1 Hhid1.
assert (Hd01 : drift L mo0 mo1) by exact (drift_trans L _ _ _ Hd Hd1).
assert (Hhid01 : forall a, hidden L mo0 a = true -> ms_mem ms1 a = ms_mem ms0 a).
{ intros a Ha. rewrite Hhid1 by (rewrite (hidden_ext L _ _ (drift_vmeq L _ _ Hd)); exact Ha). apply Hhid. exact Ha. }
assert (HC1 : cinvA ms1 mo1).
{ eapply (cinv_drift node segs L at_node nstep_raw nexit_raw nsafe xinv is_spin rvar jinv jinv_stable NS); [exact Hd01| exact Hhid01| exact HC]. }
assert (Hat1 : at_node n (msview L mo1 ms1)) by (rewrite Hv1; exact Hat).
assert (Hns1 : nsafe n mo1) by (eapply (nsA_safe_drift _ _ _ _ _ _ _ _ _ _ _ NS); eassumption).
set (c1 := mkCfg ms1 mo1).
set (Ix := { x : list event * config | sstep_cfg segs (alloc_only_cfg false) c1 (fst x) (SNext (snd x)) }).

assert (Hexpl : forall e st, sstep_cfg segs (alloc_only_cfg false) c1 e st ->
exists rsp ms' mo', st = SNext (mkCfg ms' mo') /\ e = [] /\ msview L mo' ms' = nret (msview L mo1 ms1) rsp /\
nstep_raw n mo1 rsp mo' e /\ cinvA ms' mo' /\ m_halted mo' = None).
{ intros e st Hst.
destruct (nsA_complete _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 e st Hsp Hat1 Hh1 HC1 Hns1 Hst)
as [(rsp & ms' & mo' & -> & Hv' & Hr & HC' & Hh')|(code & mo' & _ & Hx & _)].
- exists rsp, ms', mo'. destruct (Hstep rsp mo' e (ex_intro _ mo1 (conj Hd01 Hr))) as [-> _].
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hv'|]. split; [exact Hr|]. split; [exact HC'| exact Hh'].
- exfalso. exact (Hnx mo1 code mo' Hd01 Hx). }
assert (Hnode : node_ok segs c1 Ix (fun _ => []) (fun i => snd (proj1_sig i))).
{ split.
- intros [[e c'] Hst]. cbn [fst snd proj1_sig] in *. destruct (Hexpl e _ Hst) as (_ & _ & _ & _ & -> & _). exact Hst.
- intros e st Hst. destruct (Hexpl e st Hst) as (rsp & ms' & mo' & -> & -> & _).
exists (exist _ ([], mkCfg ms' mo') Hst). split; reflexivity. }
assert (Hi0 : exists i : Ix, True).
{ destruct (nsA_progress _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 Hsp Hat1 Hh1 HC1 Hns1) as [(rsp & mo' & evs & Hr)|(code & mo' & Hx)].
- destruct (nsA_sound _ _ _ _ _ _ _ _ _ _ _ NS n ms1 mo1 rsp mo' evs Hsp Hat1 Hh1 HC1 Hns1 Hr) as (ms' & mo2 & rsp2 & Hst & _).
exists (exist _ (evs, mkCfg ms' mo2) Hst). exact I.
- exfalso. exact (Hnx mo1 code mo' Hd01 Hx). }
destruct Hi0 as [i0 _].
apply (J_nclosed c1 Ix (fun i => snd (proj1_sig i)) i0 Hnode).
intros [[e c'] Hst]. cbn [fst snd proj1_sig].
destruct (Hexpl e _ Hst) as (rsp & ms' & mo' & E & -> & Hv' & Hr & HC' & Hh'). injection E as ->.
assert (HstA : nstA n mo0 rsp mo' []) by (exists mo1; split; assumption).
destruct (Hstep rsp mo' [] HstA) as [_ Hcps'].

apply (vj_enter L J ms' mo' (proj1 (proj2 HC')) Hh').
apply (IH rsp Q (mkCfg ms' mo') (msview L mo' ms')).
+ rewrite Hv', Hv1. apply Hk.
+ exact HC'.
+ exact Hcps'.
+ intros r c2 msv2 HQ Hp HC2 Hh2 Hc2. apply (HK r c2 msv2 HQ); auto.
* cbn [tpath]. exists rsp, mo', [], []. split; [exact HstA|]. split; [exact Hp| reflexivity].
* destruct Hc2 as [Hc2| [-> ->]]; [left; exact Hc2|]. left. reflexivity.
Qed.

Corollary vj_silent : forall (n : node) c0 msv,
at_node n msv ->
cinvA (cfg_ms c0) (cfg_model c0) ->
is_spin n = false -> nsafe n (cfg_model c0) ->
(forall mo1 code mo', drift L (cfg_model c0) mo1 -> ~ nexit_raw n mo1 code mo') ->
(forall rsp mo' evs, nstA n (cfg_model c0) rsp mo' evs -> evs = []) ->
(forall rsp c1, nstA n (cfg_model c0) rsp (cfg_model c1) [] ->
cinvA (cfg_ms c1) (cfg_model c1) -> m_halted (cfg_model c1) = None ->
VJ L J c1 (nret msv rsp)) ->
VJ L J c0 msv.
Proof.
intros n c0 msv Hat HC Hsp Hns Hnx Hsil HK.
apply (impl_vj (Vis n (fun rsp => Ret rsp)) (fun rsp ms => ms = nret msv rsp) c0 msv).
- cbn [impl]. apply evt_done. split; [exact Hat|]. intros rsp. cbn [impl]. apply evt_done. reflexivity.
- exact HC.
- cbn [tcps]. split; [exact Hsp|]. split; [exact Hns|]. split; [exact Hnx|].
intros rsp mo' evs Hst. split; [exact (Hsil rsp mo' evs Hst)| exact I].
- intros r c1 msv1 HQ Hp HC1 Hh1 _.
cbn [tpath] in Hp. destruct Hp as (rsp & mo' & evs1 & evs2 & Hst & Hp & Hevs). cbn [tpath] in Hp. destruct Hp as (<- & E2 & ->).
rewrite app_nil_r in Hevs. subst evs1. rewrite <- E2 in Hst.
apply (vj_evt segs L Hwx Hsegs J J_silent_closed). eapply evt_mono; [exact HQ|].
intros ms' ->. exact (HK rsp c1 Hst HC1 Hh1).
Qed.

End ImplCps.
