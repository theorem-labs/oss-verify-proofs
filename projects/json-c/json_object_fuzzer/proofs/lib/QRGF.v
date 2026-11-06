(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFL8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFL8.
Import ListNotations.
Open Scope Z_scope.

Module OS := QRjH.
Module JH := QZsi.

Section AjInst.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.

Definition AJv (T : OS.TSet) (c : config) (ms : machine_state) : Prop := VJ LV (JS segs T) c ms.
Definition CKv (c : config) : Prop := cinvA LV (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None.
Definition vmrel (mo mo' : Model) : Prop := m_vmmaps mo' = m_vmmaps mo /\ Phi LV mo' = Phi LV mo.
Definition CNEXTv (c c' : config) : Prop := CKv c' /\ vmrel (cfg_model c) (cfg_model c').

Lemma vmrel_refl : forall mo, vmrel mo mo. Proof. intros; split; reflexivity. Qed.
Lemma vmrel_trans : forall a b c, vmrel a b -> vmrel b c -> vmrel a c.
Proof. intros a b c [H1 H2] [H3 H4]. split; congruence. Qed.
Lemma vmrel_drift : forall mo mo', drift LV mo mo' -> vmrel mo mo'.
Proof. intros mo mo' Hd. split; [exact (proj1 (drift_vmeq LV _ _ Hd))| exact (drift_Phi LV _ _ Hd)]. Qed.

Lemma AJv_evt : forall T c ms, O.evt segs (AJv T c) ms -> AJv T c ms.
Proof.
intros T c ms H. unfold AJv in *. apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply evt_bridge. exact H.
Qed.

Lemma AJv_conseq : forall T T' c ms, AJv T c ms -> OS.t_eq T T' -> AJv T' c ms.
Proof.
intros T T' c ms H E ms1 mo1 Hr. unfold JS. eapply srz_conseq; [exact (H ms1 mo1 Hr)|]. exact E.
Qed.

Definition aj_base_vj : JH.aj_base segs :=
JH.AJB segs AJv CKv CNEXTv AJv_evt AJv_conseq
(fun c H => proj2 H) (fun c c' H => proj1 H)
(fun a b c H1 H2 => conj (proj1 H2) (vmrel_trans _ _ _ (proj2 H1) (proj2 H2))).

Section Ledger.
Variable L : Q6sh.ALay.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.

Lemma KI_vmrel : forall g mo mo', vmrel mo mo' -> xinvA LV mo' ->
KI LV BUDGET PERM TOT0 N0 g mo -> KI LV BUDGET PERM TOT0 N0 g mo'.
Proof.
intros g mo mo' [Hvm HPhi] Hx K.
constructor; try (rewrite Hvm; apply K).
- exact Hx.
- intros x y Hx1 Hy. rewrite Hvm. exact (ki_em _ _ _ _ _ _ _ K x y Hx1 Hy).
- apply (ki_nd _ _ _ _ _ _ _ K).
- apply (ki_sp0 _ _ _ _ _ _ _ K).
- rewrite HPhi, Hvm. apply K.
Qed.

Corollary KI_cnext : forall g c c', CNEXTv c c' ->
KI LV BUDGET PERM TOT0 N0 g (cfg_model c) -> KI LV BUDGET PERM TOT0 N0 g (cfg_model c').
Proof. intros g c c' [[HC _] Hv] K. exact (KI_vmrel g _ _ Hv (proj1 HC) K). Qed.
End Ledger.

End AjInst.
