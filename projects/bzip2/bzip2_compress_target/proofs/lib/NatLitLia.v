(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac natlit_is_pos_lit p :=
  lazymatch p with xH => idtac | xO ?q => natlit_is_pos_lit q | xI ?q => natlit_is_pos_lit q end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac natlit_hyp H :=
  repeat (lazymatch type of H with
          | context C [S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ?k)))))))))))))))] =>
              let K := constr:(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k)))))))))))))))) in
              let p := eval vm_compute in (Pos.of_nat K) in
              natlit_is_pos_lit p;
              let T' := context C [Pos.to_nat p] in
              change_no_check T' in H
          end).
Ltac natlit_goal :=
  repeat (lazymatch goal with
          | |- context G [S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ?k)))))))))))))))] =>
              let K := constr:(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k)))))))))))))))) in
              let p := eval vm_compute in (Pos.of_nat K) in
              natlit_is_pos_lit p;
              let G' := context G [Pos.to_nat p] in
              change_no_check G'
          end).
(* [comment removed for export] *)
Ltac natlit_is_nat_lit k := lazymatch k with O => idtac | S ?k' => natlit_is_nat_lit k' end.
Ltac natlit_ofnat_goal :=
  repeat match goal with
         | |- context [Z.of_nat ?k] =>
             natlit_is_nat_lit k;
             let z := eval vm_compute in (Z.of_nat k) in
             change (Z.of_nat k) with z
         end.
Ltac natlit_ofnat_hyp H :=
  repeat match type of H with
         | context [Z.of_nat ?k] =>
             natlit_is_nat_lit k;
             let z := eval vm_compute in (Z.of_nat k) in
             change (Z.of_nat k) with z in H
         end.
Ltac natlit_fix_hyp H := natlit_hyp H; natlit_ofnat_hyp H.
Ltac natlit_fix_goal := natlit_ofnat_goal; natlit_goal.

(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Ltac1 Control List Constr Array Int Env.
Set Default Proof Mode "Classic".

Ltac2 rec nl_s_tower (s : constr) (c : constr) (n : int) : bool :=
  if Int.le n 0 then true else
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Constr.equal f s then
        (if Int.equal (Array.length args) 1 then nl_s_tower s (Array.get args 0) (Int.sub n 1) else false)
      else false
  | _ => false
  end.

Ltac2 nl_lit_head (s : constr) (o : constr) (c : constr) : bool :=
  if Constr.equal c o then true else
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => Constr.equal f s
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec nl_has_target (s : constr) (o : constr) (zofnat : constr) (nums : constr list) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Constr.equal f zofnat then
        (if Int.equal (Array.length args) 1 then
           (if nl_lit_head s o (Array.get args 0) then true else nl_has_target s o zofnat nums (Array.get args 0))
         else false)
      else if Constr.equal f s then nl_s_tower s c 16
      else if List.exist (fun h => Constr.equal f h) nums then false
      else (if nl_has_target s o zofnat nums f then true
            else Array.exist (fun a => nl_has_target s o zofnat nums a) args)
  | Constr.Unsafe.Prod bnd b =>
      if nl_has_target s o zofnat nums (Constr.Binder.type bnd) then true else nl_has_target s o zofnat nums b
  | Constr.Unsafe.Lambda _ b => nl_has_target s o zofnat nums b
  | Constr.Unsafe.Cast a _ _ => nl_has_target s o zofnat nums a
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec nl_arith (z : constr) (n : constr) (heads : constr list) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if List.exist (fun h => Constr.equal f h) heads then
        (* [comment removed for export] *)
        (match Constr.Unsafe.kind f with
         | Constr.Unsafe.Ind _ _ =>
             if Int.equal (Array.length args) 3 then
               (let t := Array.get args 0 in if Constr.equal t z then true else Constr.equal t n)
             else (* [comment removed for export] *)
               (if Int.equal (Array.length args) 2 then
                  (if nl_arith z n heads (Array.get args 0) then true
                   else if nl_arith z n heads (Array.get args 1) then true
                   else (* [comment removed for export] *) Constr.equal f (List.hd heads))
                else false)
         | _ => true
         end)
      else false
  | Constr.Unsafe.Prod bnd b =>
      if nl_arith z n heads (Constr.Binder.type bnd) then true else nl_arith z n heads b
  | _ => false
  end.

Ltac2 nl_flagged () : constr list * bool :=
  (* [comment removed for export] *)
  let s := Env.instantiate reference:(S) in let o := Env.instantiate reference:(O) in
  let zofnat := Env.instantiate reference:(Z.of_nat) in
  let z := Env.instantiate reference:(Z) in let n := Env.instantiate reference:(nat) in
  let nums := [Env.instantiate reference:(Zpos); Env.instantiate reference:(Zneg); Env.instantiate reference:(xO);
               Env.instantiate reference:(xI); Env.instantiate reference:(Npos)] in
  let heads := [Env.instantiate reference:(le); Env.instantiate reference:(eq); Env.instantiate reference:(and);
                Env.instantiate reference:(or); Env.instantiate reference:(lt); Env.instantiate reference:(ge);
                Env.instantiate reference:(gt); Env.instantiate reference:(Z.le); Env.instantiate reference:(Z.lt);
                Env.instantiate reference:(Z.ge); Env.instantiate reference:(Z.gt); Env.instantiate reference:(not);
                Env.instantiate reference:(iff)] in
  let hs := List.filter (fun (_, _, ty) => if nl_arith z n heads ty then nl_has_target s o zofnat nums ty else false) (Control.hyps ()) in
  let g := Control.goal () in
  let gb := (if nl_arith z n heads g then nl_has_target s o zofnat nums g else false) in
  (List.map (fun (id, _, _) => Control.hyp id) hs, gb).

Ltac2 nl_pre (strict : bool) : unit :=
  let (hs, g) := nl_flagged () in
  match hs with
  | [] => if g then ltac1:(natlit_fix_goal) else (if strict then Control.zero (Tactic_failure None) else ())
  | _ :: _ =>
      List.iter (fun h => ltac1:(h |- natlit_fix_hyp h) (Ltac1.of_constr h)) hs;
      if g then ltac1:(natlit_fix_goal) else ()
  end.
(* [comment removed for export] *)
Ltac2 nl_pre_goal () : unit :=
  let s := Env.instantiate reference:(S) in let o := Env.instantiate reference:(O) in
  let zofnat := Env.instantiate reference:(Z.of_nat) in
  let nums := [Env.instantiate reference:(Zpos); Env.instantiate reference:(Zneg); Env.instantiate reference:(xO);
               Env.instantiate reference:(xI); Env.instantiate reference:(Npos)] in
  if nl_has_target s o zofnat nums (Control.goal ()) then ltac1:(natlit_fix_goal) else Control.zero (Tactic_failure None).
(* [comment removed for export] *)
Ltac natlit_pre_goal_strict := ltac2:(Control.enter nl_pre_goal).
(* [comment removed for export] *)
Ltac natlit_pre_strict := ltac2:(Control.enter (fun () => nl_pre true)).

Ltac lia_natlit_goal :=
  tryif noncert_goal_has_var
  then first [ solve [ natlit_pre_goal_strict; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ]
  else first [ solve [ noncert_clear_all; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].
Ltac lia_natlit :=
  tryif noncert_goal_has_var
  then first [ solve [ natlit_pre_strict; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ]
  else first [ solve [ noncert_clear_all; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Section NatLitSelfTest.
Variable path : list nat.
Hypothesis Hplen : (length path <= 4095)%nat.
Local Ltac lia ::= lia_natlit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End NatLitSelfTest.
