(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From Stdlib Require Import Uint63 PrimString PArray.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VFarkas VLpTabS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition lpans : Type := (int * hint)%type.
Definition bucket : Type := list (int * lpans).

Local Notation "a + b" := (PrimInt63.add a b).
Local Notation "a - b" := (PrimInt63.sub a b).

Definition c6 (s : string) (i : int) : int := PrimString.get s i - 35%uint63.

(* [comment removed for export] *)
Fixpoint rd_var (f : nat) (s : string) (i sh acc : int) : int * int :=
  match f with
  | O => (acc, i)
  | S f' =>
      let d := c6 s i in
      if PrimInt63.ltb d 32%uint63 then (PrimInt63.lor acc (PrimInt63.lsl d sh), i + 1%uint63)
      else rd_var f' s (i + 1%uint63) (sh + 5%uint63) (PrimInt63.lor acc (PrimInt63.lsl (d - 32%uint63) sh))
  end.

Definition rdv (s : string) (i : int) : int * int := rd_var 13 s i 0%uint63 0%uint63.

(* [comment removed for export] *)
Fixpoint rd_key (f : nat) (s : string) (i sh acc : int) : int :=
  match f with
  | O => acc
  | S f' => rd_key f' s (i + 1%uint63) (sh + 6%uint63) (PrimInt63.lor acc (PrimInt63.lsl (c6 s i) sh))
  end.

(* [comment removed for export] *)
Fixpoint i2p (f : nat) (x : int) : positive :=
  match f with
  | O => xH
  | S f' =>
      if PrimInt63.leb x 1%uint63 then xH
      else let q := i2p f' (PrimInt63.lsr x 1%uint63) in
           if PrimInt63.eqb (PrimInt63.land x 1%uint63) 0%uint63 then xO q else xI q
  end.

Definition i2n (x : int) : N := if PrimInt63.eqb x 0%uint63 then N0 else Npos (i2p 64 x).

Fixpoint rd_lams (f : nat) (s : string) (i n : int) (acc : list (N * positive)) : list (N * positive) * int :=
  match f with
  | O => (rev acc, i)
  | S f' =>
      if PrimInt63.eqb n 0%uint63 then (rev acc, i) else
      let '(ix, i1) := rdv s i in
      let '(lam, i2) := rdv s i1 in
      rd_lams f' s i2 (n - 1%uint63) ((i2n ix, i2p 64 lam) :: acc)
  end.

Definition rd_hint (s : string) (i : int) : hint * int :=
  if PrimInt63.eqb (c6 s i) 0%uint63 then (HBox, i + 1%uint63) else
  let '(k, i1) := rdv s (i + 1%uint63) in
  let '(n, i2) := rdv s i1 in
  let '(l, i3) := rd_lams 64 s i2 n [] in
  (HIdx (i2p 64 k) l, i3).

Definition rd_entry (s : string) (i : int) : (int * lpans) * int :=
  let key := rd_key 11 s i 0%uint63 0%uint63 in
  let tag := c6 s (i + 11%uint63) in
  if PrimInt63.leb tag 1%uint63 then
    let '(h, i1) := rd_hint s (i + 12%uint63) in ((key, (tag, h)), i1)
  else ((key, (tag, HBox)), i + 12%uint63).

Definition MASK : int := PrimInt63.sub (PrimInt63.lsl 1%uint63 LPT_BITS) 1%uint63.

Definition lpt_step (s : string) (st : array bucket * int * int) : array bucket * int * int :=
  let '(tab, i, n) := st in
  if PrimInt63.eqb n 0%uint63 then st else
  let '(e, i') := rd_entry s i in
  let b := PrimInt63.land (fst e) MASK in
  (PArray.set tab b (e :: PArray.get tab b), i', n - 1%uint63).

Fixpoint lpt_loopA (f : nat) (s : string) (st : array bucket * int * int) : array bucket * int * int :=
  match f with O => st | S f' => lpt_loopA f' s (lpt_step s st) end.

Fixpoint lpt_loopB (f : nat) (s : string) (st : array bucket * int * int) : array bucket * int * int :=
  match f with
  | O => st
  | S f' => if PrimInt63.eqb (snd st) 0%uint63 then st else lpt_loopB f' s (lpt_loopA 1024 s st)
  end.

Fixpoint lpt_fill (l : list (string * int)) (tab : array bucket) : array bucket :=
  match l with
  | [] => tab
  | (s, n) :: t => lpt_fill t (fst (fst (lpt_loopB 1024 s (tab, 0%uint63, n))))
  end.

(* [comment removed for export] *)
Definition LPT : array bucket := lpt_fill LPT_PIECES (PArray.make (PrimInt63.lsl 1%uint63 LPT_BITS) []).

Fixpoint bfind (l : bucket) (k : int) : option lpans :=
  match l with
  | [] => None
  | (k', a) :: t => if PrimInt63.eqb k k' then Some a else bfind t k
  end.

(* [comment removed for export] *)
Definition lpt_find (k : int) : option lpans :=
  if PrimInt63.eqb k k then bfind (PArray.get LPT (PrimInt63.land k MASK)) k else None.

#[global] Opaque LPT.

(* [comment removed for export] *)
Definition tag_opt (t : int) : bool := PrimInt63.eqb t 0%uint63.
Definition tag_inf (t : int) : bool := PrimInt63.eqb t 1%uint63.
Definition tag_unb (t : int) : bool := PrimInt63.eqb t 2%uint63.
