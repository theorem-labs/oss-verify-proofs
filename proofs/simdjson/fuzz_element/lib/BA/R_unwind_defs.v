(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition unwindfast_entry : Z := 0xa3fb4.
Definition unwind_entry : Z := 0xa4610.
Definition unwindimpl_entry : Z := 0x8b4e0.

Definition kStackTraceMax : nat := 255.

Definition fr_ok (lo hi v : Z) : bool := (lo <? v) && (v <? hi) && (v mod 8 =? 0).

Fixpoint uw_loop (pc page hi maxd : Z) (ch : list (Z * Z)) (f : Z) (acc : list Z) : option (list Z) :=
  match ch with
  | [] => None
  | (ra, fp) :: ch' =>
      if maxd <=? Z.of_nat (length acc) then Some acc
      else if ra <? page then Some acc
      else let acc' := if ra =? pc then acc else acc ++ [ra] in
           if fr_ok f hi fp then uw_loop pc page hi maxd ch' fp acc' else Some acc'
  end.

Definition unwind_trace (pc page bot top maxd bp : Z) (ch : list (Z * Z)) : option (list Z) :=
  if top / 4096 =? 0 then Some [pc]
  else if fr_ok bot (top - 16) bp then uw_loop pc page (top - 16) maxd ch bp [pc]
  else Some [pc].

Fixpoint chain_cells (W : list (Z * Z)) (m : mem) (f : Z) (ch : list (Z * Z)) : Prop :=
  match ch with
  | [] => True
  | (ra, fp) :: ch' =>
      rw_cells asegs m (f + -16) [C8 (Z_to_bv 64 fp); C8 (Z_to_bv 64 ra)]
      /\ (0 <= ra < 2^64 /\ 0 <= fp < 2^64 /\ 16 <= f < 2^64)
      /\ disjoint_from W (f + -16) 16
      /\ chain_cells W m fp ch'
  end.

Lemma chain_cells_frame : forall W (m m' : mem) f ch, chain_cells W m f ch -> munch W m m' -> wmono asegs m m' ->
  chain_cells W m' f ch.
Proof.
  intros W m m' f ch. revert f. induction ch as [|[ra fp] ch IH]; intros f H MU WM; cbn in *; [exact I|].
  destruct H as (H1 & H2 & H3 & H4). split; [| split; [exact H2| split; [exact H3| apply IH; assumption]]].
  apply (rw_cells_transport asegs W m m' _ _ H1 MU WM). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
  exact H3.
Qed.

Definition wr_trace (tr : list Z) (tb : list word) : list word := map (Z_to_bv 64) tr ++ skipn (length tr) tb.

Lemma wr_trace_length : forall tr tb, (length tr <= length tb)%nat -> length (wr_trace tr tb) = length tb.
Proof. intros tr tb H. unfold wr_trace. rewrite app_length, map_length, skipn_length. lia. Qed.

Lemma upd_app_r : forall {X} (l1 l2 : list X) i x, (length l1 <= i)%nat -> upd (l1 ++ l2) i x = l1 ++ upd l2 (i - length l1) x.
Proof.
  intros X l1. induction l1 as [|y l1 IH]; intros l2 i x H; cbn in *; [f_equal; lia|].
  destruct i as [|i]; [lia|]. f_equal. rewrite IH by lia. f_equal.
Qed.

Lemma upd_skipn_head : forall {X} (l : list X) k x, (k < length l)%nat -> upd (skipn k l) 0 x = x :: skipn (S k) l.
Proof.
  intros X l. induction l as [|y l IH]; intros k x H; cbn in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn]. apply IH. lia.
Qed.

Lemma wr_trace_snoc : forall tr tb x, (length tr < length tb)%nat ->
  upd (wr_trace tr tb) (length tr) (Z_to_bv 64 x) = wr_trace (tr ++ [x]) tb.
Proof.
  intros tr tb x H. unfold wr_trace. rewrite upd_app_r by (rewrite map_length; lia).
  rewrite map_length, Nat.sub_diag, upd_skipn_head by lia.
  rewrite map_app, <- app_assoc. cbn [map app]. rewrite app_length. cbn [length]. f_equal. f_equal. f_equal. lia.
Qed.

Lemma wr_trace_one : forall pc tb, (1 <= length tb)%nat -> upd tb 0 (Z_to_bv 64 pc) = wr_trace [pc] tb.
Proof.
  intros pc tb H. unfold wr_trace. destruct tb as [|w tb]; cbn in *; [lia|]. reflexivity.
Qed.

Lemma uw_loop_head : forall pc page hi maxd ch f acc tr, uw_loop pc page hi maxd ch f acc = Some tr ->
  exists sfx, tr = acc ++ sfx.
Proof.
  intros pc page hi maxd ch. induction ch as [|[ra fp] ch IH]; intros f acc tr H; cbn in H; [discriminate|].
  destruct (maxd <=? Z.of_nat (length acc)); [injection H as <-; exists []; rewrite app_nil_r; reflexivity|].
  destruct (ra <? page); [injection H as <-; exists []; rewrite app_nil_r; reflexivity|].
  destruct (fr_ok f hi fp).
  - destruct (IH _ _ _ H) as (sfx & ->). destruct (ra =? pc); [exists sfx; reflexivity|].
    exists (ra :: sfx). rewrite <- app_assoc. reflexivity.
  - injection H as <-. destruct (ra =? pc); [exists []; rewrite app_nil_r; reflexivity| exists [ra]; reflexivity].
Qed.

Lemma uw_loop_length : forall pc page hi maxd ch f acc tr, uw_loop pc page hi maxd ch f acc = Some tr ->
  (Z.of_nat (length acc) <= maxd)%Z -> (Z.of_nat (length tr) <= maxd)%Z.
Proof.
  intros pc page hi maxd ch. induction ch as [|[ra fp] ch IH]; intros f acc tr H Hl; cbn in H; [discriminate|].
  destruct (Z.leb_spec maxd (Z.of_nat (length acc))); [injection H as <-; lia|].
  destruct (ra <? page); [injection H as <-; lia|].
  assert (L : (Z.of_nat (length (if ra =? pc then acc else acc ++ [ra])) <= maxd)%Z).
  { destruct (ra =? pc); [lia| rewrite app_length; cbn [length]; lia]. }
  destruct (fr_ok f hi fp); [eapply IH; eassumption| injection H as <-; exact L].
Qed.

Lemma unwind_trace_head : forall pc page bot top maxd bp ch tr, unwind_trace pc page bot top maxd bp ch = Some tr ->
  exists sfx, tr = pc :: sfx.
Proof.
  intros until tr. unfold unwind_trace. intros H.
  destruct (top / 4096 =? 0); [injection H as <-; exists []; reflexivity|].
  destruct (fr_ok bot (top - 16) bp); [| injection H as <-; exists []; reflexivity].
  destruct (uw_loop_head _ _ _ _ _ _ _ _ H) as (sfx & ->). exists sfx. reflexivity.
Qed.

Lemma unwind_trace_length : forall pc page bot top maxd bp ch tr, unwind_trace pc page bot top maxd bp ch = Some tr ->
  (1 <= maxd)%Z -> (1 <= Z.of_nat (length tr) <= maxd)%Z.
Proof.
  intros until tr. intros H Hm. destruct (unwind_trace_head _ _ _ _ _ _ _ _ H) as (sfx & E).
  split; [rewrite E; cbn [length]; lia|].
  unfold unwind_trace in H.
  destruct (top / 4096 =? 0); [injection H as <-; cbn; lia|].
  destruct (fr_ok bot (top - 16) bp); [| injection H as <-; cbn; lia].
  eapply uw_loop_length; [exact H| cbn; lia].
Qed.
