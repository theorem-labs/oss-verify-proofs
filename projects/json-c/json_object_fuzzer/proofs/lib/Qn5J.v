(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition kind : Type := (bool * bool)%type.
Definition KN : kind := (true, false).
Definition KS : kind := (false, true).
Definition KNS : kind := (true, true).
Definition KO : kind := (false, false).
Definition kjoin (a b : kind) : kind := (fst a || fst b, snd a || snd b).
Definition kle (a b : kind) : Prop := (fst a = true -> fst b = true) /\ (snd a = true -> snd b = true).
Definition ksingle (isS : bool) : kind := if isS then KS else KN.

#[using="Type"] Lemma kle_refl a : kle a a. Proof. split; auto. Qed.
#[using="Type"] Lemma kle_KO a : kle KO a. Proof. split; intros H; discriminate. Qed.
#[using="Type"] Lemma kle_join_l a b : kle a (kjoin a b). Proof. destruct a as [[|] [|]], b as [[|] [|]]; split; cbn; auto. Qed.
#[using="Type"] Lemma kle_join_r a b : kle b (kjoin a b). Proof. destruct a as [[|] [|]], b as [[|] [|]]; split; cbn; auto. Qed.
#[using="Type"] Lemma kjoin_idem a : kjoin a a = a. Proof. destruct a as [[|] [|]]; reflexivity. Qed.
#[using="Type"] Lemma kjoin_comm a b : kjoin a b = kjoin b a. Proof. destruct a as [[|] [|]], b as [[|] [|]]; reflexivity. Qed.
#[using="Type"] Lemma kjoin_KN_KS : kjoin KN KS = KNS. Proof. reflexivity. Qed.
#[using="Type"] Lemma kjoin_KNS_l a : kjoin KNS a = KNS. Proof. destruct a as [[|] [|]]; reflexivity. Qed.
#[using="Type"] Lemma kjoin_KNS_r a : kjoin a KNS = KNS. Proof. destruct a as [[|] [|]]; reflexivity. Qed.
#[using="Type"] Lemma kle_kjoin_lub a b c : kle a c -> kle b c -> kle (kjoin a b) c.
Proof. destruct a as [[|] [|]], b as [[|] [|]], c as [[|] [|]]; cbv; intuition. Qed.

Definition is_fixed (flags : Z) : bool := negb (Z.land flags MAP_FIXED =? 0).

Definition eks (e : ev) : bool :=
match e with
| EBrk _ | EMunmap _ _ | EMprotect _ _ _ => true
| EMmap a len prot flags => true
| _ => false
end.

Definition eclass (e : ev) (z : Z) : bool :=
match e with
| EBrk req => if req =? 0 then false else z =? req
| EMmap a len prot flags => if is_fixed flags then false else negb (is_err z)
| EMunmap _ _ => false
| EMprotect _ _ _ => negb (is_err z && negb (z =? TWO64 - ENOSYS))
| _ => false
end.

Definition egrant (e : ev) : bool :=
match e with
| EMmap a len prot flags => negb (is_fixed flags)
| EMprotect _ _ _ => true
| _ => false
end.

Definition ecost (e : ev) : Z :=
match e with
| EBrk req => if req =? 0 then 0 else 2 * PGSZ
| EMmap a len prot flags => if is_fixed flags then PGSZ else round_up_pg len
| EMunmap _ _ => 0
| EMprotect _ _ _ => 0
| _ => 0
end.

Definition esz_ok (e : ev) : Prop :=
match e with
| EMmap a len prot flags => is_fixed flags = false -> 0 <= len /\ round_up_pg len <= 2^30
| _ => True
end.

Section KS.
Context {R : Type} (isS : R -> bool) (P : R -> Prop) (Wf : Z) (Df : nat).

Inductive KSUM : mled -> stree ev Z R -> kind -> Z -> nat -> Prop :=
| ks_ret L r W D : P r -> Wf <= W -> (Df <= D)%nat -> KSUM L (SRet r) (ksingle (isS r)) W D
| ks_ev L e k (kf kt : kind) W D :
eks e = true -> esz_ok e -> Wf <= W ->
(forall z, answer_ok L e z = true -> eclass e z = false -> KSUM (event_post L e z) (k z) kf W D) ->
(forall z, answer_ok L e z = true -> eclass e z = true  -> KSUM (event_post L e z) (k z) kt W D) ->
(egrant e = false -> kt = kf) ->

KSUM L (SVis e k) (if egrant e then kt else kf) (W + ecost e) (S D)

| ks_peek L p c h k κ W D :
Wf <= W ->
(forall v, 0 <= v < 256 -> KSUM L (k v) κ W D) ->
KSUM L (SVis (EPeek p c h) k) κ W D.

#[using="Type"] Lemma KSUM_mono L t κ W D W' D' : KSUM L t κ W D -> W <= W' -> (D <= D')%nat -> KSUM L t κ W' D'.
Proof.
intros H. revert W' D'. induction H as [L r W D HP HW HD| L e k kf kt W D EK SZ HW Hf IHf Ht IHt Hle| L p c h k κ W D HW Hk IH]; intros W' D' LW LD.
- constructor; [exact HP| lia| lia].
- destruct D' as [|D']; [lia|]. replace W' with ((W' - ecost e) + ecost e) by lia.
constructor; auto; try lia.
+ intros z A C. apply (IHf z A C); lia.
+ intros z A C. apply (IHt z A C); lia.
- apply ks_peek; [lia|]. intros v Hv. apply (IH v Hv); lia.
Qed.

#[using="Type"] Lemma ks_ev' L e k (kf kt κ : kind) W D W' :
eks e = true -> esz_ok e -> Wf <= W -> W' = W + ecost e ->
(forall z, answer_ok L e z = true -> eclass e z = false -> KSUM (event_post L e z) (k z) kf W D) ->
(forall z, answer_ok L e z = true -> eclass e z = true  -> KSUM (event_post L e z) (k z) kt W D) ->
(egrant e = false -> kt = kf) ->
κ = (if egrant e then kt else kf) ->
KSUM L (SVis e k) κ W' (S D).
Proof. intros; subst; constructor; auto. Qed.

End KS.
End RC__1.
Arguments KSUM {RC__} {R} isS P Wf Df.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma KSUM_monoP {R} (isS : R -> bool) (P P' : R -> Prop) (Wf Wf' : Z) (Df Df' : nat) L t κ W D :
KSUM isS P Wf Df L t κ W D -> (forall r, P r -> P' r) -> Wf' <= Wf -> (Df' <= Df)%nat -> KSUM isS P' Wf' Df' L t κ W D.
Proof.
intros H HP HWf HDf. induction H as [L r W D HPr HW HD| L e k kf kt W D EK SZ HW Hf IHf Ht IHt Hle| L p c h k κ W D HW Hk IH].
- constructor; auto; lia.
- constructor; auto. lia.
- apply ks_peek; auto. lia.
Qed.

End RC__2.
