(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTtp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTtp.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFL8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFL8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsCz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsCz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNLn.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module PE := QsRG.Mq0.
Module AN := Q9ox.Mq0.
Module MGT := Qwm6.Mq3.
Module HIF := QCcH.

Section LoopBase.
Context {fF : PE.FPF} {fC : PE.FPC}.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Variable VV : config -> machine_state -> Prop.
Variable T : OS.TSet.

Definition aj_base_loop : JH.aj_base segs :=
aj_base_g segs LV Hwx Hsegs (JLP segs LV VV T) (jlp_silent_closed segs LV VV T) (fun X X' c E H => jlp_conseq segs LV VV T X X' c E H).

Definition lwit (X : OS.TSet) : Prop := X [].
Definition lTw : OS.TSet := fun _ => True.
Definition lTn : OS.TSet := fun _ => False.
Lemma lwit_w : lwit lTw. Proof. exact I. Qed.
Lemma lwit_n : ~ lwit lTn. Proof. intros H. exact H. Qed.

Local Notation J := (aj_base_vj segs LV Hwx Hsegs).

Lemma loop_exit : forall X c ms, JH.AJ J T c ms -> JH.AJ aj_base_loop X c ms.
Proof. intros X c ms H. exact (vjP_exit segs LV VV T X c ms H). Qed.

Lemma loop_back : forall c ms, ~ VV c ms -> O.evt segs (VV c) ms -> JH.AJ aj_base_loop lTn c ms.
Proof.
intros c ms HnV H. apply (vjP_back_evt segs LV Hwx Hsegs VV T lTn c ms lwit_n HnV).
apply evt_bridge. exact H.
Qed.

Theorem loop_rule_base : forall c0 ms0, VV c0 ms0 ->
(forall c ms, VV c ms -> JH.AJ aj_base_loop lTw c ms) -> JH.AJ J T c0 ms0.
Proof. intros c0 ms0 H0 Hbody. exact (vj_loopP segs LV VV T lTw c0 ms0 lwit_w H0 Hbody). Qed.

Lemma drift_vm_only : forall mo mo', drift LV mo mo' -> HIF.model_vm_only mo mo'.
Proof.
intros mo mo' (P & _ & _ & ->). unfold HIF.model_vm_only. repeat split.
Qed.

Theorem loop_getrandom : MGT.aj_getrandom_tagged_stmt segs aj_base_loop lwit.
Proof.
intros regs pc mem rom c buf len X Kf HCK H17 H10 H11 H12 Hlen Htop Hwr HW HK.
change (VJ LV (JLP segs LV VV T X) c (AN.epend regs pc mem rom (PE.getr regs 17))).
destruct HCK as [HC Hh].
apply (vjA_getrandom_tagged segs LV Hsegs (Vof LV VV) T (X []) (fun ms' => Kf ms' []) buf len c _); [| exact HC | |].
- cbn [at_g]. rewrite H17. split; [reflexivity|]. rewrite !areg_epend_g by discriminate.
split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact Hlen|]. split; [exact Htop| exact Hwr].
- intros HX. exact (HW HX).
- intros bs c1 Hbs Hd HC1 Hh1.
apply (HK bs c1 Hbs).
+ split; [split; assumption| exact (vmrel_drift LV _ _ Hd)].
+ exact (drift_vm_only _ _ Hd).
Qed.

End LoopBase.
