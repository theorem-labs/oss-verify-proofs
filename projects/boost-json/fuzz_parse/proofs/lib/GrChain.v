(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import bitvector.definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec.
From Ltac2 Require Import Ltac2.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq37Corelib4Init9Datatypesla4boolla5falsek13not3h5LinuxProcessSemantics5Riscv7Preludeo76bv_eqb" s.
#[global] Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma gr_reg_neq_of_eqb : ltac2:(zQ "70!h9!jc!l5!n2!n9!o1!qd>1a@1$1@1$0#5>1b@1$1@1$0#5>0@3$2$3@3$6@1$0#5^2^1$4@1$5@3$2@1$1@1$0#5^3^2").
Proof. intros a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.

(* [comment removed for export] *)
Ltac2 rec gr_layers (x : constr) (r : constr) (acc : (constr * constr) list) : constr * (constr * constr) list * bool :=
  match Constr.Unsafe.kind x with
  | Constr.Unsafe.App h args =>
      if Bool.and (Constr.equal h 'regupd) (Int.equal (Array.length args) 3) then
        let y := Array.get args 0 in let rd := Array.get args 1 in let v := Array.get args 2 in
        if Constr.equal rd r then (y, (rd, v) :: acc, true)
        else gr_layers y r ((rd, v) :: acc)
      else (x, acc, false)
  | _ => (x, acc, false)
  end.

Ltac2 gr_app (f : constr) (args : constr list) : constr := Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args)).
Ltac2 gr_rel (i : int) : constr := Constr.Unsafe.make (Constr.Unsafe.Rel i).
Ltac2 gr_let (nm : ident) (ty : constr) (v : constr) (body : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.LetIn (Constr.Binder.make (Some nm) ty) v body).

(* [comment removed for export] *)
Ltac2 gr_proof (x : constr) (r : constr) : constr :=
  let (rest, layers, found) := gr_layers x r [] in
  let k := List.length layers in
  if Int.equal k 0 then gr_app '(@eq_refl word) [gr_app 'getr [x; r]] else
  let t := Int.mul 2 k in
  let wordt := 'word in
  let rt := '(bvmap 5 word) in
  let yref (j : int) := gr_rel (Int.sub t (Int.mul 2 j)) in
  let wref (j : int) := gr_rel (Int.add (Int.sub t (Int.mul 2 j)) 1) in
  let neq (rd : constr) := gr_app 'gr_reg_neq_of_eqb [r; rd; '(@eq_refl bool false)] in
  let z := if found then wref 1 else gr_app 'getr [yref 0; r] in
  (* [comment removed for export] *)
  let rec chain (j : int) (ls : (constr * constr) list) (p : constr option) : constr :=
    match ls with
    | [] => match p with Some p => p | None => gr_app '(@eq_refl word) [z] end
    | l :: tl =>
        let (rd, _) := l in
        let pj :=
          if Bool.and found (Int.equal j 1) then gr_app 'getr_same [yref 0; r; wref 1; neq '(0%bv : reg)]
          else
            let step := gr_app 'getr_other [yref (Int.sub j 1); rd; wref j; r; neq rd] in
            match p with
            | None => step
            | Some p' =>
                gr_app '(@eq_trans word)
                  [gr_app 'getr [gr_app 'regupd [yref (Int.sub j 1); rd; wref j]; r]; gr_app 'getr [yref (Int.sub j 1); r]; z; step; p']
            end in
        chain (Int.add j 1) tl (Some pj)
    end in
  let body := chain 1 layers None in
  (* [comment removed for export] *)
  let rec wrap (j : int) (ls : (constr * constr) list) (body : constr) : constr :=
    (* [comment removed for export] *)
    match ls with
    | [] => body
    | l :: tl =>
        let (rd, v) := l in
        let wn := Option.get (Ident.of_string (String.concat "" ["Wg"; Message.to_string (Message.of_int j)])) in
        let yn := Option.get (Ident.of_string (String.concat "" ["Yg"; Message.to_string (Message.of_int j)])) in
        let body := if Int.equal j k then body else gr_let yn rt (gr_app 'regupd [gr_rel 2; rd; gr_rel 1]) body in
        wrap (Int.sub j 1) tl (gr_let wn wordt v body)
    end in
  gr_let @Yg0 rt rest (wrap k (List.rev layers) body).

(* [comment removed for export] *)
Ltac2 gr_checked (x : constr) (r : constr) : constr :=
  match Constr.Unsafe.check (gr_proof x r) with
  | Val p => p
  | Err e => Control.zero e
  end.
(* [comment removed for export] *)
Ltac2 rec gr_is_num (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constructor _ _ => Array.for_all gr_is_num args
      | _ => false
      end
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 gr_reg_num (r : constr) : constr option :=
  match Constr.Unsafe.kind r with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 3 then
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constructor _ _ =>
            let z := Array.get args 1 in
            if Bool.and (gr_is_num (Array.get args 0)) (gr_is_num z) then Some z else None
        | _ => None
        end
      else None
  | _ => None
  end.
Ltac2 gr_fast (x : constr) (r : constr) : constr :=
  match gr_reg_num r with
  | None => gr_checked x r
  | Some zr =>
      let (_, layers, found) := gr_layers x r [] in
      (* [comment removed for export] *)
      let others := if found then List.tl layers else layers in
      let ok_layer (l : constr * constr) : bool :=
        let (rd, _) := l in
        match gr_reg_num rd with
        | Some zd => Bool.neg (Constr.equal zd zr)
        | None => false
        end in
      let ok_hit := if found then Bool.neg (Constr.equal zr 'Z0) else true in
      if Bool.and ok_hit (List.for_all ok_layer others) then gr_proof x r else gr_checked x r
  end.
Ltac gr_rewrite X r := let f := ltac2:(x r |- let p := gr_fast (Option.get (Ltac1.to_constr x)) (Option.get (Ltac1.to_constr r)) in
                                          ltac1:(p |- rewrite p) (Ltac1.of_constr p)) in f X r.
