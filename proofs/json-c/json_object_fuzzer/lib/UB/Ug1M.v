(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Umd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Umd7.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Definition kv (e : lent) : Z * Z := (le_k e, le_v e).
Lemma strip_kv : forall es' es, map strip es' = map strip es -> map kv es' = map kv es.
Proof.
induction es' as [|e' es' IH]; intros [|e es] H; cbn in H; try discriminate; [reflexivity|].
injection H as Ek Ekn Eks Ev H2. change (kv e' :: map kv es' = kv e :: map kv es). rewrite (IH _ H2). unfold kv. rewrite Ek, Ev. reflexivity.
Qed.

Lemma strip_length : forall es' es, map strip es' = map strip es -> length es' = length es.
Proof. intros es' es H. rewrite <- (length_map strip es'), <- (length_map strip es), H. reflexivity. Qed.

Lemma upd_split_at : forall (es : list lent) j e v',
nth_error es j = Some e ->
exists pre post, es = pre ++ e :: post /\ length pre = j /\ upd es j (with_v e v') = pre ++ with_v e v' :: post.
Proof.
intros es j e v' Hj.
assert (Hlt : (j < length es)%nat) by (apply (proj1 (nth_error_Some es j)); rewrite Hj; discriminate).
destruct (upd_app_split es j (with_v e v') Hlt) as (pre & y & post & E & Hlen & Hupd).
assert (y = e).
{ rewrite E in Hj. rewrite nth_error_app2 in Hj by lia. rewrite Hlen, Nat.sub_diag in Hj. cbn in Hj. congruence. }
subst y. exists pre, post. auto.
Qed.

Lemma lh_blocks_upd_v : forall t tbl size es j e v',
nth_error es j = Some e -> lh_blocks t tbl size (upd es j (with_v e v')) = lh_blocks t tbl size es.
Proof.
intros t tbl size es j e v' Hj. destruct (upd_split_at es j e v' Hj) as (pre & post & E & _ & Hupd).
unfold lh_blocks. rewrite Hupd. replace (map (fun e0 : lent => (le_k e0, le_kn e0)) es) with (map (fun e0 : lent => (le_k e0, le_kn e0)) (pre ++ e :: post)) by (rewrite <- E; reflexivity).
rewrite !map_app. cbn [map le_k le_kn with_v]. reflexivity.
Qed.

Lemma kv_upd_v : forall es j e v' pre post,
nth_error es j = Some e -> es = pre ++ e :: post -> length pre = j ->
map kv (upd es j (with_v e v')) = map kv pre ++ (le_k e, v') :: map kv post.
Proof.
intros es j e v' pre post Hj E Hlen. subst es. revert j Hj Hlen. induction pre as [|x pre IH]; intros j Hj Hlen.
- cbn in Hlen. subst j. cbn. reflexivity.
- cbn in Hlen. subst j. cbn. rewrite (IH (length pre)); [reflexivity | | reflexivity].
cbn in Hj. exact Hj.
Qed.

