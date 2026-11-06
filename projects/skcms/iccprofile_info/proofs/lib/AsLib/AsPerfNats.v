(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From Ltac2 Require Import Ltac2.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PerfNats.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac2 Type heads_as := { hS : constr; hO : constr; hEF : constr; hE2 : constr; hLF : constr; hL2 : constr;
                      hZp : constr; hZn : constr; hIdn : constr }.
Ltac2 mk_heads_as () : heads_as :=
  { hS := constr:(S); hO := constr:(O); hEF := constr:(ASX.EVar); hE2 := constr:(ASX.EVar);
    hLF := constr:(ASX.ELit); hL2 := constr:(ASX.ELit); hZp := constr:(Zpos); hZn := constr:(Zneg); hIdn := constr:(idn) }.

(* [comment removed for export] *)
Ltac2 rec nat_walk_as (c : constr) (acc : int) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => Some acc
  | Constr.Unsafe.App _ args => nat_walk_as (Array.get args 0) (Int.add acc 1)
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 nat_lit_as (h : heads_as) (c : constr) (acc : int) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => if Constr.equal c (h.(hO)) then Some acc else None
  | Constr.Unsafe.App f args => if Constr.equal f (h.(hS)) then nat_walk_as (Array.get args 0) (Int.add acc 1) else None
  | _ => None
  end.

Ltac2 leaf_as (h : heads_as) (m : (constr * constr) list) (n : constr) : constr * (constr * constr) list :=
  let v := match nat_lit_as h n 0 with
           | Some k => if Int.lt k 512 then vn_of k else Constr.Unsafe.make (Constr.Unsafe.App (h.(hIdn)) [| n |])
           | None => Constr.Unsafe.make (Constr.Unsafe.App (h.(hIdn)) [| n |])
           end in
  (v, m).

Ltac2 rec binzm_as (h : heads_as) (c : constr) (m : (constr * constr) list) : constr * (constr * constr) list :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Constr.equal f (h.(hEF)) then
        let (v, m') := leaf_as h m (Array.get args 0) in (Constr.Unsafe.make (Constr.Unsafe.App f [| v |]), m')
      else if Constr.equal f (h.(hE2)) then
        let (v, m') := leaf_as h m (Array.get args 0) in (Constr.Unsafe.make (Constr.Unsafe.App f [| v |]), m')
      else if Constr.equal f (h.(hLF)) then (c, m)
      else if Constr.equal f (h.(hL2)) then (c, m)
      else if Constr.equal f (h.(hZp)) then (c, m)
      else if Constr.equal f (h.(hZn)) then (c, m)
      else
        let n := Array.length args in
        let res := Array.make n c in
        let rec go i m :=
          if Int.equal i n then m
          else let (a, m2) := binzm_as h (Array.get args i) m in (Array.set res i a; go (Int.add i 1) m2) in
        let m' := go 0 m in
        (Constr.Unsafe.make (Constr.Unsafe.App f res), m')
  | _ => (c, m)
  end.

Ltac2 binz_as (c : constr) : constr := let h := mk_heads_as () in let (t, _) := binzm_as h c [] in t.

(* [comment removed for export] *)
Ltac binarize_as_k c k := let f := ltac2:(c k |- let t := binz_as (Option.get (Ltac1.to_constr c)) in Ltac1.apply k [Ltac1.of_constr t] Ltac1.run) in f c k.



Goal True.
  binarize_as_k constr:([ASX.EVar 64; ASX.EVar 3; ASX.EVar 600]) ltac:(fun t =>
    lazymatch t with [ASX.EVar vn64; ASX.EVar vn3; ASX.EVar (idn 600)] => idtac | _ => fail end).
  exact I.
Qed.
