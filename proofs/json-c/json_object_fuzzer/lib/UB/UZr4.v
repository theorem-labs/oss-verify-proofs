(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module GwI.
Definition segs := rsegs.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rimpl_vis_unfold' : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq8.rimpl_vis_unfold') [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.rimpl_vis_unfold') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.rimpl_vis_unfold')]. Qed.

#[using="Type"] Lemma impl_bind_inv' : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq8.impl_bind_inv') [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.impl_bind_inv') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.impl_bind_inv')]. Qed.

#[using="Type"] Lemma implM_bind_inv' : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq8.implM_bind_inv') [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_bind_inv') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_bind_inv')]. Qed.

#[using="Type"] Lemma implM_ret_inv' : forall {St A} (a : A) (s : St) Q ms,
implM rsegs (mret a) s Q ms -> evt rsegs (Q a s) ms.
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_ret_inv') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_ret_inv')]. Qed.

#[using="Type"] Lemma implM_upd_inv' : forall {St} (f : St -> St) s Q ms,
implM rsegs (mupd f) s Q ms -> evt rsegs (Q tt (f s)) ms.
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_upd_inv') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_upd_inv')]. Qed.

#[using="Type"] Lemma implM_get_inv' : forall {St} (s : St) Q ms,
implM rsegs mget s Q ms -> evt rsegs (Q s s) ms.
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_get_inv') | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_get_inv')]. Qed.

#[using="Type"] Lemma implM_msys_inv : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq8.implM_msys_inv) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_msys_inv) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_msys_inv)]. Qed.

#[using="Type"] Lemma ev_step_set_m : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq8.ev_step_set_m) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.ev_step_set_m) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.ev_step_set_m)]. Qed.

#[using="Type"] Lemma implM_membed_set_m : ltac2:(Q6nq.ty1 'GwI.segs '(@Q91D.Mq8.implM_membed_set_m) [] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_membed_set_m) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.implM_membed_set_m)]. Qed.

#[using="Type"] Lemma set_m_set_m cs cs' s : set_m cs (set_m cs' s) = set_m cs s.
Proof. first [GwApply.gw_by_name GwI.segs (@Q91D.Mq8.set_m_set_m) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq8.set_m_set_m)]. Qed.

End RC__1.
