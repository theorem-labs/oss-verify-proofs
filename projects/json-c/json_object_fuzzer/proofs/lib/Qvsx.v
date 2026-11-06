(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QwAs Qc6I QJFf QVsB Qsn5 QBrp Q1KO QCiC Qpj5 QvDJ QOb0 Qt4u Q6sh QjWq QQwg QKTr QzgH Qk8e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf QVsB Qsn5 QJFf.Mq1 QBrp Q1KO.
Import QCiC.Mq1 Qpj5.Mq1 QCiC QvDJ.Mq1 QOb0.Mq0 Qt4u.Mq0 QCiC.Mq0 Q6sh.Mq1 QjWq.
Import Q6sh QQwg Qpj5.Mq0 QvDJ QKTr QzgH Qk8e.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.

Lemma aptr_eqb_eq p q : aptr_eqb p q = true <-> p = q.
Proof.
destruct p as [i n|a n], q as [j m|b m]; cbn; rewrite ?andb_true_iff, ?N.eqb_eq, ?Z.eqb_eq; split; intros H;
try discriminate; try (destruct H; subst; reflexivity); inversion H; subst; auto.
Qed.

Section T2A.
Variable L : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok L LV BUDGET PERM TOT0 N0.

Definition szok (x : aptr * Z) : Prop := pshape (snd x) (fst x).

Definition kMaxSecs : Z := 16000.

Definition cap_ok (X : list aptr) : Prop :=
(forall n, 0 <= n -> from_primary n = true ->
class_size (class_of n) * (cntc (class_of n) X + 17) + qcap (class_of n) <= kFreeArrayOffset) /\
zlen (secs X) + 1 <= kMaxSecs.

Lemma cap_ok_room X a n : ainv X a -> cap_ok X -> 0 <= n -> malloc_room X a n.
Proof.
intros AI [C1 C2] Hn. split.
- intros Hp. pose proof (class_of_facts n Hn Hp) as (Hc & _ & _).
pose proof (tot_bound X a (class_of n) AI ltac:(lia)) as T. specialize (C1 n Hn Hp).
pose proof (class_facts (class_of n) ltac:(lia)) as (Hsz & _ & _). nia.
- intros Hp. pose proof (reg_bound X a AI). unfold kQTotal, kQMaxCache, kQMaxSize, kMaxNumChunks, kMaxSecs in *. nia.
Qed.

Lemma cap_ok_reg X a : ainv X a -> cap_ok X -> zlen (as_reg a) + 1 <= kMaxCnt.
Proof. intros AI [_ C2]. pose proof (reg_bound X a AI). unfold kQTotal, kQMaxCache, kQMaxSize, kMaxSecs, kMaxCnt in *. nia. Qed.

Lemma class_of_7000 : class_of 7000 = kBatchClass /\ from_primary 7000 = true.
Proof. split; reflexivity. Qed.

Lemma cap_ok_room24 X a : ainv X a -> cap_ok X ->
class_size kBatchClass * (tot X [] 0 a kBatchClass + 17) <= kFreeArrayOffset.
Proof.
intros AI [C1 _]. pose proof kBatchClass_range as H24. destruct class_of_7000 as [E P].
pose proof (tot_bound X a kBatchClass AI H24) as T. specialize (C1 7000 ltac:(lia) P). rewrite E in C1.
pose proof (class_facts kBatchClass H24) as (Hsz & _ & _). nia.
Qed.

Lemma secs_cons_le (x : aptr) l : zlen (secs l) <= zlen (secs (x :: l)) <= zlen (secs l) + 1.
Proof. destruct x; cbn [secs]; rewrite ?zlen_cons; lia. Qed.

Definition frame_okA (G : PStateA -> Model -> Prop) : Prop :=
forall ps ps' mo mo', ps_soa ps' = ps_soa ps -> ps_xa ps' = ps_xa ps -> vm_onlyA mo mo' -> G ps mo -> G ps' mo'.

Definition AOWN (X : owned aptr) (R : Z) (G : PStateA -> Model -> Prop) : assn PStateA := fun ps mo =>
(exists g, GS (ps_a ps) g /\ KI LV BUDGET PERM TOT0 N0 g mo) /\ ainv (map fst X) (ps_a ps) /\
0 <= R /\ CAPS + as_spent (ps_a ps) + R <= BUDGET /\ Forall szok X /\ cap_ok (map fst X) /\ G ps mo.

Variable MH : owned aptr -> Z -> Prop.
Definition cap_hook : Prop :=
forall X n, MH X n -> 0 <= n -> Forall szok X -> cap_ok (map fst X) ->
too_big n = false /\ n <= kMaxReq /\ forall p, pshape n p -> cap_ok (p :: map fst X).
Hypothesis HMH : cap_hook.

End T2A.

Section MHcapsA.

Definition X0_ok (X0 : owned aptr) : Prop :=
Forall szok X0 /\ (forall c, cntc c (map fst X0) <= 64) /\ zlen (secs (map fst X0)) <= 64.

Lemma from_primary_le n : 0 <= n -> from_primary n = true -> n <= 64512.
Proof.
intros Hn Hp. destruct (Z.le_gt_cases n 64512) as [H|H]; [exact H|]. exfalso.
unfold from_primary, needed, kMaxSize in Hp. apply Z.leb_le in Hp.
pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)). unfold rz_size in Hp.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [lia|]. destruct (Z.leb_spec n 448); [lia|].
destruct (Z.leb_spec n 3968); [lia|]. destruct (Z.leb_spec n 16128); [lia|]. destruct (Z.leb_spec n 32256); [lia|].
destruct (Z.leb_spec n 64512); lia.
Qed.

Lemma too_big_small n : 0 <= n <= 2^30 -> too_big n = false.
Proof.
intros Hn. unfold too_big, kMaxAllowedMalloc. pose proof (rz_size_bound n).
assert (needed n <= n + 8 + 2048 + 8).
{ unfold needed. pose proof (round_up_lt (Z.max n 8) 8 ltac:(lia)). lia. }
destruct (Z.ltb_spec n 0); [lia|]. cbn [orb]. apply Z.ltb_ge. destruct (from_primary n); lia.
Qed.

Definition cap_row (c : Z) (hist : Z) : bool :=
class_size c * (hist + 102) + qcap c <=? kFreeArrayOffset.

Definition hist_cap (L0 c : Z) : Z :=
if c =? 3 then RUNS_CAP L0 else if c =? 2 then PNODES_CAP L0 else if c =? 17 then ROWS_CAP else 0.

End MHcapsA.
End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= Stdlib.omega.PreOmega.Z.to_euclidean_division_equations.
Local Set Keyed Unification.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy7F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy7F. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsc9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsc9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcxL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcxL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QchP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QchP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyFv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyFv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV5O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV5O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhA8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhA8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTxS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTxS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjEq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfGI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfGI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHMY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHMY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qecj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qecj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwLV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwLV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoeL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoeL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZPm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZPm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qum6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qum6.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= QdTa.mkr__zify_internal_to_euclidean_division_equations_5.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Set Implicit Arguments.

Fixpoint lafter {R} (L : mled) (t : M R) (ans : list Z) {struct t} : mled :=
match t, ans with
| SRet _, _ => L
| SVis (EUndef _) _, _ => L
| SVis e k, a :: ans' => lafter (event_post L e a) (k a) ans'
| SVis _ _, [] => L
end.

Fixpoint followk {R} (t : M R) (ans : list Z) {struct t} : option (R * list Z) :=
match t, ans with
| SRet r, _ => Some (r, ans)
| SVis (EUndef _) _, _ => None
| SVis _ k, a :: ans' => followk (k a) ans'
| SVis _ _, [] => None
end.

Unset Implicit Arguments.

Section SIM.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

End SIM.
