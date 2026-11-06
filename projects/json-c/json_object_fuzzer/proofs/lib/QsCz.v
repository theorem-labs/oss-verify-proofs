(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QQIi QdTb Q1lV Qcrs QUcd QCUT QwAs Qc6I QJFf Qsn5 Qknc QBrp Q2ui Q1KO QNqr QeDS QLiw QFL8 QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import QQIi QdTb Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import QNqr QeDS QNqr.Mq0 QLiw.
Import QFL8 QRGF.
Import ListNotations.
Open Scope Z_scope.

Section NodeRulesAB.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.

End NodeRulesAB.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFL8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFL8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF.
Import ListNotations.
Open Scope Z_scope.

Section AjInstG.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Variable Jf : OS.TSet -> config -> Prop.
Hypothesis Jf_sc : forall T, silent_closed LV segs (Jf T).
Hypothesis Jf_conseq : forall T T' c, OS.t_eq T T' -> Jf T c -> Jf T' c.

Definition AJg (T : OS.TSet) (c : config) (ms : machine_state) : Prop := VJ LV (Jf T) c ms.

Lemma AJg_evt : forall T c ms, O.evt segs (AJg T c) ms -> AJg T c ms.
Proof.
intros T c ms H. unfold AJg in *. apply (vj_evt segs LV Hwx Hsegs _ (Jf_sc T)).
apply evt_bridge. exact H.
Qed.

Lemma AJg_conseq : forall T T' c ms, AJg T c ms -> OS.t_eq T T' -> AJg T' c ms.
Proof. intros T T' c ms H E ms1 mo1 Hr. exact (Jf_conseq T T' _ E (H ms1 mo1 Hr)). Qed.

Definition aj_base_g : JH.aj_base segs :=
JH.AJB segs AJg (CKv LV) (CNEXTv LV) AJg_evt AJg_conseq
(fun c H => proj2 H) (fun c c' H => proj1 H)
(fun a b c H1 H2 => conj (proj1 H2) (vmrel_trans LV _ _ _ (proj2 H1) (proj2 H2))).

End AjInstG.
