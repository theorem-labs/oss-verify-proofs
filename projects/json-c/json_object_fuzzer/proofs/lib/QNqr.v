(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi QdTb QHWH Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QQIi QdTb QHWH Q1lV.
Import ListNotations.

Section SrzCps.
Variable segs : list Segment.

Lemma srz_silent : forall c (I : Type) (nx : I -> config) (i0 : I) T,
node_ok segs c I (fun _ => []) nx ->
(forall i, srealizes segs (nx i) T) ->
srealizes segs c T.
Proof.
intros c I nx i0 T Hnode Hc.
assert (HT0 : T []) by (eapply srealizes_nonempty; apply (Hc i0)).
apply (srz_conseq segs c (t_alt (fun i : I => t_emit [] T))).
- apply (srz_node segs c I (fun _ => []) nx (fun _ => T) i0 Hnode Hc).
- intros tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

Definition JS (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Lemma js_nclosed : forall T c (I : Type) (nx : I -> config) (i0 : I),
node_ok segs c I (fun _ => []) nx -> (forall i, JS T (nx i)) -> JS T c.
Proof. intros T c I nx i0 Hn Hc. exact (srz_silent c I nx i0 T Hn Hc). Qed.

End SrzCps.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5.
Import ListNotations.
Open Scope Z_scope.

Section ViewCps.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.

Definition vrel (c0 : config) (msv : machine_state) (ms : machine_state) (mo : Model) : Prop :=
msview L mo ms = msv /\ drift L (cfg_model c0) mo /\ lv_inv L mo /\ m_halted mo = None /\
(forall a, hidden L (cfg_model c0) a = true -> ms_mem ms a = ms_mem (cfg_ms c0) a).

Definition VJ (J : config -> Prop) (c0 : config) (msv : machine_state) : Prop :=
forall ms mo, vrel c0 msv ms mo -> J (mkCfg ms mo).

Lemma vrel_refl : forall ms mo, lv_inv L mo -> m_halted mo = None -> vrel (mkCfg ms mo) (msview L mo ms) ms mo.
Proof. intros ms mo HI Hh. repeat split; auto. apply drift_refl. Qed.

Lemma vj_enter : forall J ms mo, lv_inv L mo -> m_halted mo = None ->
VJ J (mkCfg ms mo) (msview L mo ms) -> J (mkCfg ms mo).
Proof. intros J ms mo HI Hh H. apply H. apply vrel_refl; assumption. Qed.

Theorem vj_evt : forall J, silent_closed L segs J ->
forall c0 msv, evt segs (VJ J c0) msv -> VJ J c0 msv.
Proof.
intros J HJ c0 msv (msv' & Hms & Hk) ms mo (Hv & Hd & HI & Hh & Hhid).
apply (msteps_view L segs Hwx Hsegs J HJ msv msv' Hms mo ms (eq_sym Hv) HI Hh).
intros ms' mo' Hv' Hd' HI' Hh' Hhid'. apply Hk. repeat split; auto.
- exact (drift_trans L _ _ _ Hd Hd').
- intros a Ha. rewrite Hhid' by (rewrite (hidden_ext L _ _ (drift_vmeq L _ _ Hd)); exact Ha). apply Hhid. exact Ha.
Qed.

Lemma silent_closed_srealizes : forall T, silent_closed L segs (fun c => srealizes segs c T).
Proof.
intros T ms mo ms' mo' Hnode _ _ _ _ Hr.
exact (srz_silent1 segs (mkCfg ms mo) (mkCfg ms' mo') T Hnode Hr).
Qed.

End ViewCps.
