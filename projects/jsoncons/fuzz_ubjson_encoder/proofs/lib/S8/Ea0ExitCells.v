(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StepTac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Inductive axv : Type := AX0 | AXc.

Definition AXLO : Z := 0x695ad0.
Definition AXHI : Z := 0x695cf0.
Definition SSLO : Z := 0x674088.
Definition SSHI : Z := 0x674088.

Definition AX_CELLS (ax : axv) : list (Z * Z * Z) :=
  match ax with
  | AX0 => [(6904532, 4, 0); (6904536, 4, 2); (6904544, 8, 6904552); (6904552, 8, 0); (6904560, 8, 1156008); (6904568, 8, 1156008); (6904816, 8, 622312); (6904824, 8, 690352)]
  | AXc => [(6904532, 4, 0); (6904536, 4, 4); (6904544, 8, 6904552); (6904552, 8, 0); (6904560, 8, 1156008); (6904568, 8, 1156008); (6904576, 8, 877016); (6904584, 8, 451616); (6904816, 8, 622312); (6904824, 8, 690352); (6904832, 8, 1300720); (6904840, 8, 0)]
  end.

Definition ax_cell (MV : word -> option byte) (c : Z * Z * Z) : Prop :=
  rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c))).

Definition atexit_cellsA (MV : word -> option byte) (ax : axv) : Prop := Forall (ax_cell MV) (AX_CELLS ax).

Lemma ax_cells_in : forall (ax : axv) (c : Z * Z * Z), In c (AX_CELLS ax) ->
  ((AXLO <= fst (fst c) /\ fst (fst c) + snd (fst c) <= AXHI) \/ (SSLO <= fst (fst c) /\ fst (fst c) + snd (fst c) <= SSHI)) /\ 0 <= snd (fst c) <= 8.
Proof.
  intros ax c Hc. unfold AXLO, AXHI, SSLO, SSHI. destruct ax; cbn [In AX_CELLS] in Hc;
    repeat (destruct Hc as [<-|Hc]; [cbn [fst snd]; lia|]); destruct Hc.
Qed.

Lemma atexit_cellsA_frame : forall (M M' : word -> option byte) (ax : axv),
  (forall a : Z, AXLO <= a < AXHI -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a : Z, SSLO <= a < SSHI -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> atexit_cellsA M ax -> atexit_cellsA M' ax.
Proof.
  intros M M' ax AG1 AG2 H. unfold atexit_cellsA in *. rewrite Forall_forall in *. intros c Hc.
  pose proof (ax_cells_in ax c Hc) as (BB & B3). specialize (H c Hc). unfold ax_cell in *.
  unfold AXLO, AXHI, SSLO, SSHI in *.
  rewrite <- H. apply rdn_ext; [rewrite u_Z2bv by lia; rewrite Z2Nat.id by lia; lia|].
  intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite Z2Nat.id in Hx by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). destruct BB as [BB|BB]; [apply AG1 | apply AG2]; lia.
Qed.

Definition cell_eqb (c d : Z * Z * Z) : bool := (Z.eqb (fst (fst c)) (fst (fst d)) && Z.eqb (snd (fst c)) (snd (fst d)) && Z.eqb (snd c) (snd d))%bool.
Definition ax_inb (c : Z * Z * Z) (ax : axv) : bool := existsb (cell_eqb c) (AX_CELLS ax).
Lemma atexit_cellsA_atb : forall (MV : word -> option byte) (ax : axv) a n v,
  atexit_cellsA MV ax -> ax_inb (a, n, v) ax = true ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof.
  intros MV ax a n v H Hin. unfold atexit_cellsA in H. rewrite Forall_forall in H. unfold ax_inb in Hin.
  apply existsb_exists in Hin as ([[a' n'] v'] & Hd & Heq). unfold cell_eqb in Heq. cbn [fst snd] in Heq.
  apply andb_prop in Heq as [Heq H3]. apply andb_prop in Heq as [H1 H2]. apply Z.eqb_eq in H1, H2, H3. subst a' n' v'.
  exact (H (a, n, v) Hd).
Qed.
