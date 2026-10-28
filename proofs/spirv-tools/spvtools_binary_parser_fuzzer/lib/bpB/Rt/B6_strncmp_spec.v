(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsIface.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition nthZ (j : nat) (l : list Z) : Z := nth j (l ++ [0]) 0.

Lemma nthZ_app_rest : forall j l rest, (j <= length l)%nat -> nth j (l ++ 0 :: rest) 0 = nthZ j l.
Proof.
  intros j l rest Hj. unfold nthZ. destruct (Nat.lt_ge_cases j (length l)) as [L|G].
  - rewrite !app_nth1 by lia. reflexivity.
  - assert (j = length l) as -> by lia. rewrite !app_nth2, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma nthZ_lt : forall j l, (j < length l)%nat -> nthZ j l = nth j l 0.
Proof. intros. unfold nthZ. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma nthZ_len : forall l, nthZ (length l) l = 0.
Proof. intros. unfold nthZ. rewrite app_nth2, Nat.sub_diag by lia. reflexivity. Qed.

Fixpoint cmpi (e t : list Z) (n : nat) {struct n} : nat :=
  match n with
  | O => O
  | S n' => match e, t with
            | c1 :: e', c2 :: t' => if Z.eqb c1 c2 then S (cmpi e' t' n') else O
            | _, _ => O
            end
  end.

Lemma cmpi_charact : forall n e t j,
  (j <= n)%nat -> (j <= length e)%nat -> (j <= length t)%nat ->
  (forall j', (j' < j)%nat -> nth j' e 0 = nth j' t 0) ->
  (j = n \/ nthZ j e = 0 \/ nthZ j e <> nthZ j t) ->
  Forall (fun c => 0 < c < 256) e ->
  cmpi e t n = j.
Proof.
  induction n as [|n IH]; intros e t j Hn He Ht PRE STOP FE; [cbn; lia|].
  destruct j as [|j].
  - cbn. destruct e as [|c1 e'], t as [|c2 t']; try reflexivity.
    destruct (Z.eqb_spec c1 c2); [|reflexivity]. exfalso.
    destruct STOP as [?|[S0|SN]]; [lia| |].
    + rewrite nthZ_lt in S0 by (cbn; lia). cbn in S0. inversion FE; subst. lia.
    + rewrite !nthZ_lt in SN by (cbn; lia). cbn in SN. congruence.
  - destruct e as [|c1 e']; [cbn in He; lia|]. destruct t as [|c2 t']; [cbn in Ht; lia|]. cbn.
    pose proof (PRE O ltac:(lia)) as P0. cbn in P0. subst c2. rewrite Z.eqb_refl. f_equal.
    apply IH; cbn in *; try lia.
    + intros j' Hj'. exact (PRE (S j') ltac:(lia)).
    + destruct STOP as [?|[S0|SN]]; [left; lia| right; left | right; right].
      * unfold nthZ in *. cbn in S0. exact S0.
      * unfold nthZ in *. cbn in SN. exact SN.
    + inversion FE; assumption.
Qed.

Lemma zstrncmp_cmpi : forall n e t,
  Forall (fun c => 0 < c < 256) e -> Forall (fun c => 0 < c < 256) t ->
  let i := cmpi e t n in
  ((i < n)%nat -> zstrncmp e t n = nthZ i e - nthZ i t) /\ ((i >= n)%nat -> zstrncmp e t n = 0).
Proof.
  induction n as [|n IH]; intros e t FE FT; cbn [cmpi].
  - split; intros; [lia|]. reflexivity.
  - destruct e as [|c1 e'], t as [|c2 t'].
    + split; intros; [| lia]. cbn. reflexivity.
    + split; intros; [| lia]. cbn. unfold nthZ. cbn. reflexivity.
    + split; intros; [| lia]. cbn. unfold nthZ. cbn. lia.
    + inversion FE; inversion FT; subst.
      destruct (Z.eqb_spec c1 c2) as [E|NE].
      * subst c2. destruct (IH e' t' ltac:(assumption) ltac:(assumption)) as [IH1 IH2].
        assert (STEP : zstrncmp (c1 :: e') (c1 :: t') (S n) = zstrncmp e' t' n).
        { cbn. rewrite Z.eqb_refl. destruct (Z.eqb_spec c1 0); [lia| reflexivity]. }
        rewrite STEP. split; intros Hi.
        -- rewrite IH1 by lia. unfold nthZ. cbn. reflexivity.
        -- apply IH2. lia.
      * split; intros; [| lia]. cbn. destruct (Z.eqb_spec c1 c2); [lia|]. unfold nthZ. cbn. reflexivity.
Qed.

Lemma zstrncmp_sign : forall n e t (C1 C2 : Z),
  Forall (fun c => 0 < c < 256) e -> Forall (fun c => 0 < c < 256) t ->
  let i := cmpi e t n in
  ((i < n)%nat -> C1 = nthZ i e /\ C2 = nthZ i t) -> ((i >= n)%nat -> C1 = C2) ->
  (zstrncmp e t n = 0 <-> C1 = C2) /\ (zstrncmp e t n < 0 <-> C1 < C2).
Proof.
  intros n e t C1 C2 FE FT i Hlt Hge.
  destruct (zstrncmp_cmpi n e t FE FT) as [Z1 Z2]. fold i in Z1, Z2.
  destruct (Nat.lt_ge_cases i n) as [L|G].
  - destruct (Hlt L) as [-> ->]. rewrite (Z1 L). lia.
  - rewrite (Z2 G). specialize (Hge G). lia.
Qed.
