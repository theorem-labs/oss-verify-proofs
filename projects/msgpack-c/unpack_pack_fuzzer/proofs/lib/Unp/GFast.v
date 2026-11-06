(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import U32.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS U32.
Open Scope Z_scope.
Unset Lia Cache.

Module GFast.

Definition decide_ltu_tf (fs : list fact) (a b : sv) : option bool :=
  let vs := sv_vs a (sv_vs b []) in
  match decide_ltu (rel_facts vs fs) a b with
  | Some false => Some false
  | _ => match decide_ltu (rel_facts (close_vs fs vs vs) fs) a b with
         | Some false => Some false
         | _ => decide_ltu fs a b
         end
  end.
Lemma decide_ltu_tf_sound : forall E fs, facts_hold E fs -> forall a b r, decide_ltu_tf fs a b = Some r -> bv_ltu (den E a) (den E b) = r.
Proof.
  intros E fs Hfs a b r H. unfold decide_ltu_tf in H. cbv zeta in H.
  destruct (decide_ltu (rel_facts (sv_vs a (sv_vs b [])) fs) a b) as [[|]|] eqn:D1.
  2: { injection H as <-. exact (decide_ltu_sound E _ (rel_facts_hold E _ fs Hfs) _ _ _ D1). }
  all: destruct (decide_ltu (rel_facts (close_vs fs (sv_vs a (sv_vs b [])) (sv_vs a (sv_vs b []))) fs) a b) as [[|]|] eqn:D2;
       try (injection H as <-; exact (decide_ltu_sound E _ (rel_facts_hold E _ fs Hfs) _ _ _ D2));
       exact (decide_ltu_sound E fs Hfs _ _ _ H).
Qed.

Definition decide_eq0_tf (fs : list fact) (v : sv) : option bool :=
  match decide_eq0 (rel_facts (sv_vs v []) fs) v with
  | Some false => Some false
  | _ => decide_eq0 fs v
  end.
Lemma decide_eq0_tf_sound : forall E fs, facts_hold E fs -> forall v r, decide_eq0_tf fs v = Some r -> bv_eqb (den E v) (Z_to_bv 64 0) = r.
Proof.
  intros E fs Hfs v r H. unfold decide_eq0_tf in H.
  destruct (decide_eq0 (rel_facts (sv_vs v []) fs) v) as [[|]|] eqn:D1;
    try exact (decide_eq0_sound E fs Hfs _ _ H).
  injection H as <-. exact (decide_eq0_sound E _ (rel_facts_hold E _ fs Hfs) _ _ D1).
Qed.

Definition eq0b_false (fs : list fact) (v : sv) : bool := match decide_eq0_b fs v with Some false => true | _ => false end.
Definition nz_known_f (fs : list fact) (c : sv) : bool :=
  if eq0b_false fs c then true
  else let x := core32 c in
       if (if negb (sv_eqb x c) then if sx32_shaped x then eq0b_false fs x else false else false) then true
       else nz_known fs c.
Lemma nz_known_f_eq : forall fs c, nz_known_f fs c = nz_known fs c.
Proof.
  intros fs c. unfold nz_known_f, eq0b_false. cbv zeta.
  assert (B : forall v, decide_eq0_b fs v = Some false -> decide_eq0 fs v = Some false).
  { intros v D. unfold decide_eq0. rewrite D. reflexivity. }
  destruct (decide_eq0_b fs c) as [[|]|] eqn:D1; try (unfold nz_known; rewrite (B c D1); reflexivity).
  all: destruct (negb (sv_eqb (core32 c) c)) eqn:NE; [|reflexivity];
       destruct (sx32_shaped (core32 c)) eqn:SX; [|reflexivity];
       destruct (decide_eq0_b fs (core32 c)) as [[|]|] eqn:D2; try reflexivity;
       unfold nz_known; cbv zeta; rewrite NE, SX, (B _ D2); cbn [andb];
       destruct (decide_eq0 fs c) as [[|]|]; reflexivity.
Qed.
Definition bounded_count_f (fs : list fact) (c : sv) : bool :=
  match decide_ltu fs c (VL (wlit 1001%uint63)) with Some true => nz_known_f fs c | _ => false end.
Lemma bounded_count_f_eq : forall fs c, bounded_count_f fs c = bounded_count fs c.
Proof. intros fs c. unfold bounded_count_f, bounded_count. rewrite nz_known_f_eq. reflexivity. Qed.

Fixpoint exists_lazy {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | a :: t => if f a then true else exists_lazy f t end.
Lemma exists_lazy_eq : forall A (f : A -> bool) l, exists_lazy f l = existsb f l.
Proof. induction l as [|a t IH]; cbn [exists_lazy existsb]; [reflexivity|]. rewrite IH. destruct (f a); reflexivity. Qed.
Definition exists_2p {A} (q f : A -> bool) (l : list A) : bool := if exists_lazy q l then true else exists_lazy f l.
Lemma exists_2p_inv : forall A (q f : A -> bool) l, exists_2p q f l = true -> exists x, In x l /\ (q x = true \/ f x = true).
Proof.
  intros A q f l H. unfold exists_2p in H. destruct (exists_lazy q l) eqn:Q.
  - rewrite exists_lazy_eq in Q. apply existsb_exists in Q as (x & Hx & Qx). exists x. auto.
  - rewrite exists_lazy_eq in H. apply existsb_exists in H as (x & Hx & Fx). exists x. auto.
Qed.

End GFast.
