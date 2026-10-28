(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import R_unwind_defs R_depot_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition rng64 (x : Z) : Prop := 0 <= x < 2 ^ 64.

Lemma wr_trace_split : forall tr tb, wr_trace tr tb = map (Z_to_bv 64) tr ++ skipn (length tr) tb.
Proof. reflexivity. Qed.

Lemma map_unsigned_lits : forall tr, Forall rng64 tr -> map bv_unsigned (map (Z_to_bv 64) tr) = tr.
Proof.
  induction tr as [|x tr IH]; intros HF; [reflexivity|]. inversion HF as [|? ? Hx Htr]; subst.
  cbn [map]. rewrite unsigned_lit by (unfold rng64 in Hx; lia). f_equal. apply IH. exact Htr.
Qed.

Lemma depot_put_lits : forall D tr, Forall rng64 tr -> depot_put D (map bv_unsigned (map (Z_to_bv 64) tr)) = depot_put D tr.
Proof. intros D tr HF. rewrite map_unsigned_lits by exact HF. reflexivity. Qed.

Lemma chain_cells_ras : forall W (m : mem) f ch, chain_cells W m f ch -> Forall (fun p => rng64 (fst p)) ch.
Proof.
  intros W m f ch. revert f. induction ch as [|[ra fp] ch IH]; intros f H; [constructor|].
  destruct H as (_ & (Hra & _) & _ & H). constructor; [exact Hra| exact (IH _ H)].
Qed.

Lemma uw_loop_rng : forall pc page hi maxd ch f acc tr, uw_loop pc page hi maxd ch f acc = Some tr ->
  Forall rng64 acc -> Forall (fun p => rng64 (fst p)) ch -> Forall rng64 tr.
Proof.
  intros pc page hi maxd ch. induction ch as [|[ra fp] ch IH]; intros f acc tr H Ha Hc; cbn in H; [discriminate|].
  inversion Hc as [|? ? Hra Hch]; subst. cbn [fst] in Hra.
  assert (Ha' : Forall rng64 (if ra =? pc then acc else acc ++ [ra])).
  { destruct (ra =? pc); [exact Ha| apply Forall_app; split; [exact Ha| constructor; [exact Hra| constructor]]]. }
  destruct (maxd <=? Z.of_nat (length acc)); [injection H as <-; exact Ha|].
  destruct (ra <? page); [injection H as <-; exact Ha|].
  destruct (fr_ok f hi fp); [eapply IH; eassumption| injection H as <-; exact Ha'].
Qed.

Lemma unwind_trace_rng : forall pc page bot top maxd bp ch tr, unwind_trace pc page bot top maxd bp ch = Some tr ->
  rng64 pc -> Forall (fun p => rng64 (fst p)) ch -> Forall rng64 tr.
Proof.
  intros until tr. intros H Hpc Hc. unfold unwind_trace in H.
  assert (H1 : Forall rng64 [pc]) by (constructor; [exact Hpc| constructor]).
  destruct (top / 4096 =? 0); [injection H as <-; exact H1|].
  destruct (fr_ok bot (top - 16) bp); [eapply uw_loop_rng; eassumption| injection H as <-; exact H1].
Qed.
