(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtSizes CtWire.
From Stdlib Require Import ZArith List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition scts_wire {ptr : Type} (l : list (sctr ptr)) : Z := fold_right Z.add 0 (map (fun x => 2 + i2o_sct_len x) l).
Definition sk_wire {ptr : Type} (k : skr ptr) : Z := scts_wire (sk_items k).

Lemma scts_wire_nil : forall {ptr : Type}, scts_wire (@nil (sctr ptr)) = 0.
Proof. intros. reflexivity. Qed.

Lemma scts_wire_cons : forall {ptr : Type} (x : sctr ptr) (l : list (sctr ptr)), scts_wire (x :: l) = 2 + i2o_sct_len x + scts_wire l.
Proof. intros ptr x l. unfold scts_wire. cbn [map fold_right]. lia. Qed.

Lemma scts_wire_app : forall {ptr : Type} (l1 l2 : list (sctr ptr)), scts_wire (l1 ++ l2) = scts_wire l1 + scts_wire l2.
Proof.
  intros ptr l1 l2. induction l1 as [|x l1 IH]; [reflexivity|].
  cbn [app]. rewrite !scts_wire_cons, IH. lia.
Qed.

Lemma sk_wire_nil : forall {ptr : Type} (b : ptr) (d : option (ptr * Z)), sk_wire (mkSK b d []) = 0.
Proof. intros. reflexivity. Qed.

Lemma sk_wire_items : forall {ptr : Type} (k : skr ptr), sk_wire k = scts_wire (sk_items k).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sk_wire_snoc : forall {ptr : Type} (b : ptr) (d : option (ptr * Z)) (l : list (sctr ptr)) (x : sctr ptr),
  sk_wire (mkSK b d (l ++ [x])) = sk_wire (mkSK b d l) + 2 + i2o_sct_len x.
Proof. intros ptr b d l x. unfold sk_wire. cbn [sk_items]. rewrite scts_wire_app, scts_wire_cons. change (scts_wire (@nil (sctr ptr))) with 0. lia. Qed.

(* [comment removed for export] *)
Lemma i2o_sct_len_nonneg : forall {ptr : Type} (x : sctr ptr),
  0 <= sc_extlen x -> 0 <= sc_siglen x -> 0 <= sc_bloblen x -> 0 <= i2o_sct_len x.
Proof. intros ptr x H1 H2 H3. unfold i2o_sct_len. destruct (sc_version x =? 0); lia. Qed.

Lemma scts_wire_nonneg : forall {ptr : Type} (l : list (sctr ptr)),
  Forall (fun x => 0 <= i2o_sct_len x) l -> 0 <= scts_wire l.
Proof.
  intros ptr l H. induction l as [|x l IH]; [unfold scts_wire; cbn; lia|].
  apply Forall_cons_iff in H as [Hx Hl]. rewrite scts_wire_cons. specialize (IH Hl). lia.
Qed.

Lemma sk_wire_nonneg : forall {ptr : Type} (k : skr ptr),
  Forall (fun x => 0 <= i2o_sct_len x) (sk_items k) -> 0 <= sk_wire k.
Proof. intros ptr k H. unfold sk_wire. apply scts_wire_nonneg. exact H. Qed.

(* [comment removed for export] *)
Lemma scts_wire_ge3 : forall {ptr : Type} (l : list (sctr ptr)),
  Forall (fun x => 1 <= i2o_sct_len x) l -> 3 * zlength l <= scts_wire l.
Proof.
  intros ptr l H. induction l as [|x l IH]; [unfold scts_wire, zlength; cbn; lia|].
  apply Forall_cons_iff in H as [Hx Hl]. rewrite scts_wire_cons. specialize (IH Hl).
  unfold zlength in *. cbn [length]. rewrite Nat2Z.inj_succ. lia.
Qed.
