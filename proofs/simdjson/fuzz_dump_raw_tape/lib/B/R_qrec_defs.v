(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Mem Cells Frame Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_cache_defs R_glue_defs R_depot_defs R_quar_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Fixpoint merge_walk (cur : batch) (rest : list batch) : list batch * list batch :=
  match rest with
  | [] => ([cur], [])
  | nxt :: rest' =>
      if (Z.of_nat (length (snd cur) + length (snd nxt)) <=? 1021) then
        let kx := merge_walk (fst cur, snd cur ++ snd nxt) rest' in (fst kx, (fst nxt, []) :: snd kx)
      else
        let kx := merge_walk nxt rest' in (cur :: fst kx, snd kx)
  end.

Definition merge_all (bs : list batch) : list batch * list batch :=
  match bs with [] => ([], []) | cur :: rest => merge_walk cur rest end.

Lemma merge_walk_bytes : forall rest cur,
  qbytes (fst (merge_walk cur rest)) + qbytes (snd (merge_walk cur rest)) = qbytes (cur :: rest).
Proof.
  induction rest as [|nxt rest IH]; intros [b e]; [cbn; lia|].
  cbn [merge_walk fst snd]. destruct (_ <=? _).
  - cbn [fst snd]. pose proof (IH (b, e ++ snd nxt)) as H. unfold qbytes in *. cbn [fold_right fst snd] in *.
    rewrite bsum_app in H. unfold bsum in *. cbn. lia.
  - cbn [fst snd]. pose proof (IH nxt) as H. unfold qbytes in *. cbn [fold_right fst snd] in *. lia.
Qed.

Lemma merge_all_bytes : forall bs, qbytes (fst (merge_all bs)) + qbytes (snd (merge_all bs)) = qbytes bs.
Proof. intros [|cur rest]; [reflexivity| apply merge_walk_bytes]. Qed.

Lemma merge_walk_ne : forall rest cur, fst (merge_walk cur rest) <> [].
Proof.
  induction rest as [|nxt rest IH]; intros cur; cbn [merge_walk]; [discriminate|].
  destruct (_ <=? _); cbn [fst]; [apply IH| discriminate].
Qed.

Lemma merge_walk_extracted : forall rest cur, Forall (fun e => snd e = []) (snd (merge_walk cur rest)).
Proof.
  induction rest as [|nxt rest IH]; intros cur; cbn [merge_walk]; [constructor|].
  destruct (_ <=? _); cbn [snd]; [constructor; [reflexivity| apply IH]| apply IH].
Qed.

Definition bivs (bs : list batch) : list (Z * Z) := map (fun e => (fst e, fst e + 8192)) bs.

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto.
Qed.

Lemma outside_bivs : forall bs x, outside (bivs bs) x <-> Forall (fun e => ~ (fst e <= x < fst e + 8192)) bs.
Proof.
  induction bs as [|e bs IH]; intros x; cbn [bivs map outside]; [split; [constructor| tauto]|].
  rewrite IH. split; [intros (A & B); constructor; assumption| intros H; inversion H; subst; tauto].
Qed.

Lemma inside_bivs : forall bs e x, In e bs -> fst e <= x < fst e + 8192 -> ~ outside (bivs bs) x.
Proof.
  intros bs e x Hin Hx H. apply outside_bivs in H. pose proof (proj1 (Forall_forall _ _) H e Hin) as Hn. cbn in Hn. tauto.
Qed.

Lemma disjoint_bivs : forall bs a n, Forall (fun e => a + n <= fst e \/ fst e + 8192 <= a) bs -> disjoint_from (bivs bs) a n.
Proof.
  induction bs as [|e bs IH]; intros a n H; cbn [bivs map disjoint_from]; [exact I|].
  inversion H; subst. split; [assumption| apply IH; assumption].
Qed.

Lemma disjoint_from_app : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a n H1 H2; cbn in *; [exact H2|]. destruct H1 as (A & B). split; [exact A| apply IH; assumption]. Qed.

Definition merge_cond (bs : list batch) : bool :=
  (8192 * Z.of_nat (length bs) <? qbytes bs) && (qbytes bs * 100 <? Z.of_nat (length bs) * 0x190000).
Definition rec_merge (bs : list batch) : list batch * list batch := if merge_cond bs then merge_all bs else (bs, []).

Fixpoint deq (bs : list batch) (bytes min : Z) : list batch * list batch :=
  match bs with
  | [] => ([], [])
  | b :: bs' => if bytes <=? min then ([], bs) else let dr := deq bs' (bytes - (8192 + bsum (snd b))) min in (b :: fst dr, snd dr)
  end.

Lemma deq_app : forall bs bytes min, fst (deq bs bytes min) ++ snd (deq bs bytes min) = bs.
Proof.
  induction bs as [|b bs IH]; intros bytes min; [reflexivity|]. cbn [deq]. destruct (bytes <=? min); [reflexivity|].
  cbn [fst snd app]. rewrite IH. reflexivity.
Qed.

Lemma rec_merge_bytes : forall bs, qbytes (fst (rec_merge bs)) + qbytes (snd (rec_merge bs)) = qbytes bs.
Proof. intros bs. unfold rec_merge. destruct (merge_cond bs); [apply merge_all_bytes| cbn [fst snd]; rewrite qbytes_nil; lia]. Qed.
