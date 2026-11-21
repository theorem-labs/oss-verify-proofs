(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint brev (w : nat) (c : Z) : Z :=
  match w with
  | O => 0
  | S w' => (c mod 2) * 2 ^ Z.of_nat w' + brev w' (c / 2)
  end.
Definition rev (w c : Z) : Z := brev (Z.to_nat w) c.

Fixpoint sumn (f : Z -> Z) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => sumn f lo n' + f (lo + Z.of_nat n')
  end.
Definition sumz (f : Z -> Z) (lo hi : Z) : Z := sumn f lo (Z.to_nat (hi - lo)).

Fixpoint zsearch (p : Z -> bool) (lo : Z) (n : nat) : Z :=
  match n with
  | O => lo
  | S n' => if p lo then lo else zsearch p (lo + 1) n'
  end.

Definition applyw (ws : list (Z * Z)) (a : arr) : arr :=
  fold_left (fun a iv => arr_set a (fst iv) (snd iv)) ws a.

Definition countz (x : Z) (l : list Z) : Z := zlength (filter (Z.eqb x) l).

Section Sig.

  Variable wl : list Z.
Variable ll : list Z.

  Definition NC : Z := zlength ll.
  Definition LofS (s : Z) : Z := nth (Z.to_nat s) ll 0.

  Definition W (l : Z) : Z := nth (Z.to_nat l) wl 0.

  Definition OFF (l : Z) : Z := sumz W 1 l.

  Definition NZ : Z := OFF 16.
  Definition MAXL : Z := 15 - zsearch (fun i => negb (W (15 - i) =? 0)) 0 15.
  Definition MINL : Z := zsearch (fun l => negb (W l =? 0)) 1 (Z.to_nat (MAXL - 1)).

  Definition LEFT : Z := 2 ^ 15 - sumz (fun l => W l * 2 ^ (15 - l)) 1 16.

  Definition TM (l : Z) : Z := sumz (fun l' => W l' * 2 ^ (MAXL - l')) 1 (l + 1).

  Definition len_at (k : Z) : Z := zsearch (fun l => k <? OFF (l + 1)) 1 15.
  Definition rank_at (k : Z) : Z := k - OFF (len_at k).
  Definition Apos (k : Z) : Z := TM (len_at k - 1) + rank_at k * 2 ^ (MAXL - len_at k).
  Definition code (k : Z) : Z := Apos k / 2 ^ (MAXL - len_at k).

  Definition syms_of (l : Z) : list Z :=
    filter (fun s => LofS s =? l) (map Z.of_nat (seq 0 (Z.to_nat NC))).
  Definition SYM (l r : Z) : Z := nth (Z.to_nat r) (syms_of l) 0.
  Definition wsym (k : Z) : Z := SYM (len_at k) (rank_at k).

  Definition sort_writes : list (Z * Z) :=
    flat_map (fun s => let l := LofS s in
                       if l =? 0 then []
                       else [(OFF l + countz l (firstn (Z.to_nat s) ll), s)])
             (map Z.of_nat (seq 0 (Z.to_nat NC))).
  Section Root.
    Variable root : Z.
    Definition GR : Z := 2 ^ (MAXL - root).
    Definition Pfx (k : Z) : Z := Apos k / GR.
    Definition islong (k : Z) : bool := root <? len_at k.

    Definition newtable (k : Z) : bool :=
      islong k && (negb (islong (k - 1)) || negb (Pfx k =? Pfx (k - 1))).

    Definition cstar (P c0 : Z) : Z :=
      zsearch (fun c => (MAXL <=? root + c) || ((P + 1) * GR <=? TM (root + c))) c0 16.

    Fixpoint lay_n (k : nat) : Z * Z * Z :=
      match k with
      | O => (0, root, 2 ^ root)
      | S k' => let '(no, cu, us) := lay_n k' in
                let kz := Z.of_nat k in
                if newtable kz then
                  let c := cstar (Pfx kz) (len_at kz - root) in
                  (no + 2 ^ cu, c, us + 2 ^ c)
                else (no, cu, us)
      end.
    Definition lay (k : Z) : Z * Z * Z := lay_n (Z.to_nat k).
    Definition noff (k : Z) : Z := fst (fst (lay k)).
    Definition curr (k : Z) : Z := snd (fst (lay k)).
    Definition used (k : Z) : Z := snd (lay k).
    Definition drop (k : Z) : Z := if islong k then root else 0.
    Definition low (k : Z) : Z := if islong k then rev root (Pfx k) else 4294967295.

    Definition hf (k : Z) : Z :=
      if k =? 0 then 0
      else let j := k - 1 in
           if code j + 1 <? 2 ^ len_at j then rev (len_at j) (code j + 1) else 0.

    Section Ty.
      Variable ty : codetype.
Variable table : Z.

      Definition entry (s : Z) : Z * Z :=
        match ty with
        | CODES => (0, s)
        | LENS => if s + 1 <? 257 then (0, s)
                  else if 257 <=? s then (wrap8 (nth (Z.to_nat (s - 257)) lext_l 0), nth (Z.to_nat (s - 257)) lbase_l 0)
                  else (96, 0)
        | DISTS => (wrap8 (nth (Z.to_nat s) dext_l 0), nth (Z.to_nat s) dbase_l 0)
        end.
      Definition here (k : Z) : Z :=
        let '(op, val) := entry (wsym k) in code_pack op (len_at k - drop k) val.

      Definition fill_writes (k : Z) : list (Z * Z) :=
        let l := len_at k - drop k in
        let e := curr k - l in
        let base := table + noff k + hf k / 2 ^ drop k in
        map (fun j => (base + Z.of_nat j * 2 ^ l, here k)) (List.rev (seq 0 (Z.to_nat (2 ^ e)))).

      Definition fails_at (k : Z) : bool :=
        (k + 1 <? NZ) && newtable (k + 1) && it_not_enough ty (used (k + 1)).
      Definition link_writes (k : Z) : list (Z * Z) :=
        if (k + 1 <? NZ) && newtable (k + 1) && negb (it_not_enough ty (used (k + 1)))
        then [(table + rev root (Pfx (k + 1)), code_pack (curr (k + 1)) root (noff (k + 1)))]
        else [].
      Definition trip_writes (k : Z) : list (Z * Z) := fill_writes k ++ link_writes k.

      Definition first_fail : Z := zsearch fails_at 0 (Z.to_nat (NZ - 1)).
      Definition trips_writes (n : Z) : list (Z * Z) :=
        flat_map (fun k => trip_writes (Z.of_nat k)) (seq 0 (Z.to_nat n)).
      Definition final_writes : list (Z * Z) :=
        if hf NZ =? 0 then []
        else [(table + noff (NZ - 1) + hf NZ, code_pack 64 (len_at (NZ - 1) - drop (NZ - 1)) 0)].

      Definition loop_abs (bits : Z) : Z * list (Z * Z) * Z * Z :=
        if first_fail <? NZ - 1
        then (1, trips_writes (first_fail + 1), table, bits)
        else (0, trips_writes NZ ++ final_writes, table + used (NZ - 1), root).
    End Ty.
  End Root.

  Definition ROOT (bits : Z) : Z := Z.max (Z.min bits MAXL) MINL.

  Definition it_abs (ty : codetype) (table bits : Z) : Z * list (Z * Z) * Z * Z * list (Z * Z) :=
    if MAXL =? 0 then
      let e := code_pack 64 1 0 in (0, [(table, e); (table + 1, e)], table + 2, 1, [])
    else if LEFT <? 0 then (-1, [], table, bits, [])
    else if (0 <? LEFT) && (codetype_eqb ty CODES || negb (MAXL =? 1)) then (-1, [], table, bits, [])
    else
      let root := ROOT bits in
      if it_not_enough ty (2 ^ root) then (1, [], table, bits, sort_writes)
      else let '(ret, ws, toff, bits') := loop_abs root ty table bits in
           (ret, ws, toff, bits', sort_writes).
End Sig.

Definition wl_of (ll : list Z) : list Z := map (fun l => countz (Z.of_nat l) ll) (seq 0 16).

Definition lens_list (lens : arr) (lens_ofs codes : Z) : list Z :=
  map (fun i => arr_get lens (lens_ofs + Z.of_nat i)) (seq 0 (Z.to_nat codes)).
