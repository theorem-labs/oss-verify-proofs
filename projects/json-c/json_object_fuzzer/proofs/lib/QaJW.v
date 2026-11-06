(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QwAs Qc6I QJFf QVsB Qsn5 Qknc QBrp Q2ui Q1KO QCiC Qpj5 QvDJ QPa2 QOb0 Qt4u Q6sh QQwg QKTr QzgH QNqr QeDS QCrt QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB.
Import Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import QCiC.Mq1 Qpj5.Mq1 QCiC QvDJ.Mq1 QPa2 QOb0.Mq0 Qt4u.Mq0.
Import Q6sh QQwg Qpj5.Mq0 QvDJ QKTr QzgH.
Import QNqr QeDS QCrt.Mq0 QgTJ.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section TcpsBind.
Variable node : Type.
Variable LV : lvp.
Variable nstep_raw : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit_raw : node -> Model -> word -> Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable is_spin : node -> bool.

End TcpsBind.

Section AllocCps.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.

End AllocCps.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq0.
Import ListNotations.
Open Scope Z_scope.

Section AllocSpecG.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.

Notation KIx := (KI LV BUDGET PERM TOT0 N0).
Notation MSPEC := (mspec (nstepsA LV) (nsafeA LV)).

Theorem membedA_specG {R} (t : T R) (P : R -> Prop) (RG : ghost -> R -> Prop) (g : ghost) (s : PStateA) (mo0 : Model) :
tall aokG (rokS P) t -> teva L BUDGET aokG RG g t -> KIx g mo0 ->
MSPEC (fun s0 mo => s0 = s /\ mo = mo0) (membedA t)
(fun r s' mo' => s' = s /\ P r /\ vm_onlyA mo0 mo' /\ exists g', RG g' r /\ KIx g' mo').
Proof.
revert g mo0. induction t as [[r| |w]|e k IH]; intros g mo0 Ht Hg K.
- cbn [membedA]. apply mspec_ret. intros s0 mo [-> ->]. split; [reflexivity|]. split; [exact Ht|].
split; [apply vm_onlyA_refl|]. exists g. split; [exact Hg| exact K].
- destruct Ht.
- destruct Ht.
- cbn [membedA]. destruct Hg as [Ge Gk]. change (forall a, aokG e a -> tall aokG (rokS P) (k a)) in Ht.
apply (mspec_bind _ _ (ev_stepA e) (fun a => membedA (k a)) _
(fun a s' mo' => s' = s /\ aokG e a /\ vm_onlyA mo0 mo' /\ KIx (gstep g e a) mo')).
+ rewrite ev_stepA_eq. apply mspec_sys. intros s0 mo [-> ->]. split; [apply (ev_safe L LV BUDGET PERM TOT0 N0 LL g mo0 e K Ge)|].
intros rsp mo' evs (mo1 & Hd & Hst).
pose proof (KI_drift LV BUDGET PERM TOT0 N0 g mo0 mo1 Hd K) as K1.
destruct (ev_step L LV BUDGET PERM TOT0 N0 LL g mo1 e rsp mo' evs K1 Ge Hst) as (a & Hdec & Ha & K').
exists a. split; [exact Hdec|]. split; [reflexivity|].
split; [split; [exact Ha| exact (ev_step_grant LV e mo1 rsp mo' evs a Hst Hdec)]|]. split; [| exact K'].
eapply vm_onlyA_trans; [eapply vm_onlyA_drift; exact Hd| eapply (vm_onlyA_nstep_raw L LV BUDGET PERM TOT0 N0 LL); eauto].
+ intros a s0 mo [-> (Ha & Hv & K')].
eapply etwf_mono; [eapply (IH a (gstep g e a) mo (Ht a Ha) (Gk a Ha) K'); split; reflexivity|].
intros [r s1] mo1 H1. cbn [fst snd] in H1. destruct H1 as (-> & HP & Hv1 & Hg1).
cbn [fst snd]. split; [reflexivity|]. split; [exact HP|]. split; [| exact Hg1].
eapply vm_onlyA_trans; [exact Hv| exact Hv1].
Qed.

End AllocSpecG.
