(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Corelib Require Import PrimInt63.
From Corelib Require Uint63Axioms.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AHK.
Import AX2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Fixpoint hnat4 (n : nat) (acc : int) : int :=
  match n with
  | S (S (S (S m))) => hnat4 m (add acc 4%uint63)
  | S m => hnat4 m (add acc 1%uint63)
  | O => acc
  end.
(* [comment removed for export] *)
Fixpoint hpos (p : positive) (k : nat) (acc : int) : int :=
  match k with
  | O => acc
  | S k' => match p with
            | xI q => hpos q k' (add (add acc acc) 1%uint63)
            | xO q => hpos q k' (add acc acc)
            | xH => add (add acc acc) 1%uint63
            end
  end.
Definition hz (z : Z) : int :=
  match z with Z0 => 0%uint63 | Zpos p => hpos p 16 1%uint63 | Zneg p => hpos p 16 3%uint63 end.
Definition hmix (h x : int) : int := add (sub (lsl h 5%uint63) h) x.   (* [comment removed for export] *)
Fixpoint ehash (e : expr) : int :=
  match e with
  | ELit z => hmix 1%uint63 (hz z)
  | EVar n => hnat4 n 2%uint63
  | EAlu _ a b => hmix (hmix 3%uint63 (ehash a)) (ehash b)
  | EAluw _ a b => hmix (hmix 4%uint63 (ehash a)) (ehash b)
  | EMd _ a b => hmix (hmix 5%uint63 (ehash a)) (ehash b)
  | EMdw _ a b => hmix (hmix 6%uint63 (ehash a)) (ehash b)
  | EExt _ _ _ a => hmix 7%uint63 (ehash a)
  | EBlob _ _ i _ => hmix 8%uint63 (hz i)
  end.
Definition sahash (a : saddr) : int := hmix (ehash (a_base a)) (hz (a_off a)).
Definition khash (K : kentry) : int :=
  match K with
  | KWord a _ v => hmix (hmix 11%uint63 (sahash a)) (ehash v)
  | KZero a n => hmix (hmix 12%uint63 (sahash a)) (ehash n)
  | KBlob a n _ => hmix (hmix 13%uint63 (sahash a)) (ehash n)
  | KImg lo _ => hmix 14%uint63 (hz lo)
  | KAlign e m => hmix (hmix 15%uint63 (ehash e)) (hz m)
  | KRange e lo _ => hmix (hmix 16%uint63 (ehash e)) (hz lo)
  | KWr a n => hmix (hmix 17%uint63 (sahash a)) (ehash n)
  | KDisj a1 n1 a2 _ => hmix (hmix (hmix 18%uint63 (sahash a1)) (ehash n1)) (sahash a2)
  | KFill a n _ => hmix (hmix 19%uint63 (sahash a)) (ehash n)
  | KUnk a n => hmix (hmix 20%uint63 (sahash a)) (ehash n)
  | KShOk a n => hmix (hmix 21%uint63 (sahash a)) (ehash n)
  | KFpc v lo _ => hmix (hmix 22%uint63 (ehash v)) (ehash lo)
  end.
(* [comment removed for export] *)
Lemma hash_guard : forall (A : Type) (h : A -> int) (f : A -> A -> bool), (forall x y, f x y = true -> x = y) ->
  forall x y, (if eqb (h x) (h y) then f x y else false) = f x y.
Proof.
  intros A h f Hf x y. destruct (f x y) eqn:E.
  - pose proof (Hf x y E) as Exy. subst y. rewrite Uint63Axioms.eqb_refl. reflexivity.
  - destruct (eqb (h x) (h y)); reflexivity.
Qed.
End AHK.
