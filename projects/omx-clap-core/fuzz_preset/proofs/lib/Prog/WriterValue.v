From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Open Scope Z_scope.

Definition wind (p : bool) (d : Z) : list (list Z) :=
  if p then [10] :: repeat [32; 32] (Z.to_nat d) else [].

Definition wsep (p : bool) : list Z := if p then [58; 32] else [58].

Definition wcomma (i : nat) : list (list Z) := if Nat.eqb i 0 then [] else [[44]].

Fixpoint wvpieces (t : jv) (p : bool) (d : Z) {struct t} : list (list Z) :=
  match t with
  | JNull => [[110; 117; 108; 108]]
  | JFalse => [[102; 97; 108; 115; 101]]
  | JTrue => [[116; 114; 117; 101]]
  | JNum txt _ => [txt]
  | JStr s => spieces s
  | JArr items =>
      [91] ::
      (fix go (i : nat) (l : list jv) {struct l} : list (list Z) :=
         match l with
         | [] => []
         | x :: r => wcomma i ++ wind p (d + 1) ++ wvpieces x p (d + 1) ++ go (S i) r
         end) 0%nat items
      ++ (match items with [] => [] | _ :: _ => wind p d end) ++ [[93]]
  | JObj members =>
      [123] ::
      (fix go (i : nat) (l : list (list Z * jv)) {struct l} : list (list Z) :=
         match l with
         | [] => []
         | (k, x) :: r => wcomma i ++ wind p (d + 1) ++ spieces k ++ [wsep p] ++ wvpieces x p (d + 1) ++ go (S i) r
         end) 0%nat members
      ++ (match members with [] => [] | _ :: _ => wind p d end) ++ [[125]]
  end.

Definition wdpieces (t : jv) (p : bool) : list (list Z) := wvpieces t p 0 ++ (if p then [[10]] else []).

Definition wdoc (t : jv) (p : bool) : list Z := concat (wdpieces t p).
