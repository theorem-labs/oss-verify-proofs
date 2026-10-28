(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj Q6WR Q6q3 Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma nx_of_app_lt : forall tbl es e' j, (S j < length es)%nat -> nx_of tbl (es ++ [e']) j = nx_of tbl es j.
Proof. intros. unfold nx_of. rewrite nth_error_app1 by lia. reflexivity. Qed.

Lemma nx_of_app_new : forall tbl es e' j, (j = length es)%nat -> nx_of tbl (es ++ [e']) j = 0.
Proof. intros. unfold nx_of. rewrite nth_error_app2 by lia. replace (S j - length es)%nat with 1%nat by lia. reflexivity. Qed.
Lemma nx_of_last : forall tbl es j, (S j = length es)%nat -> nx_of tbl es j = 0.
Proof. intros. unfold nx_of. destruct (nth_error es (S j)) eqn:E; [|reflexivity].
exfalso. pose proof (proj1 (nth_error_Some es (S j)) ltac:(rewrite E; discriminate)). lia. Qed.
Lemma pv_of_app_le : forall tbl es e' j, (j <= length es)%nat -> pv_of tbl (es ++ [e']) j = pv_of tbl es j.
Proof. intros. unfold pv_of. destruct j; [reflexivity|]. rewrite nth_error_app1 by lia. reflexivity. Qed.

Lemma last_nth_error : forall (es : list lent) j e d, nth_error es j = Some e -> (S j = length es)%nat -> last es d = e.
Proof.
induction es as [|a es IH]; intros j e d E Hj; [discriminate|].
destruct es as [|b es'].
- cbn in Hj. assert (j = 0%nat) by lia. subst j. cbn in E. injection E as ->. reflexivity.
- destruct j as [|j]; [cbn in Hj; lia|]. cbn in E. change (last (a :: b :: es') d) with (last (b :: es') d).
eapply IH; [exact E|]. cbn in Hj |- *. lia.
Qed.
Lemma tl_of_last : forall tbl es j e, nth_error es j = Some e -> (S j = length es)%nat -> tl_of tbl es = ent_addr tbl (le_ix e).
Proof.
intros tbl es j e E Hj. unfold tl_of. destruct es as [|e0 es'] eqn:EES; [discriminate|]. rewrite <- EES in *.
rewrite (last_nth_error es j e _ E Hj). reflexivity.
Qed.
Lemma tl_of_app : forall tbl es e', tl_of tbl (es ++ [e']) = ent_addr tbl (le_ix e').
Proof. intros. unfold tl_of. destruct (es ++ [e']) eqn:E; [destruct es; discriminate|]. rewrite <- E, last_last. reflexivity. Qed.

Section Snoc.
Variables (tbl : Z) (es : list lent) (svs : list slotv) (g : nat) (sg : slotv) (k kn : Z) (ks : list byte) (v : Z).
Let e' := LE g k kn ks v.

Hypothesis LINK : lh_link tbl es svs.
Hypothesis Hg : (g < length svs)%nat.
Hypothesis Esg : nth_error svs g = Some sg.
Hypothesis FREE : ~ In g (map le_ix es).
Hypothesis Hk : 0 < k /\ k + kn < LH_FREEDv /\ kn <= 2^31.
Hypothesis Hv : 0 <= v < 2^64.
Hypothesis Htbl : 0 < tbl.

End Snoc.

Section OpenSnoc.
Variable segs : list Segment.
Variable fn : fnaddrs.

End OpenSnoc.
