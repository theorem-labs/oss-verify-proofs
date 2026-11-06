(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module SzSec.
  Import Ltac2.
  Ltac2 last_hyps (k : int) : constr list :=
    let hs := Control.hyps () in
    List.map (fun h => let (id, _, _) := h in Control.hyp id) (List.skipn (Int.sub (List.length hs) k) hs).
  Ltac2 fail_msg (s : string) := Control.throw (Tactic_failure (Some (Message.of_string s))).
  (* [comment removed for export] *)
  Ltac2 rec walk (t : constr) (pat : string) (i : int) (vs : constr list) (hyps : constr list) : constr * constr list :=
    if Int.equal i (String.length pat) then (t, List.rev hyps)
    else
      match Constr.Unsafe.kind (Std.eval_hnf t) with
      | Constr.Unsafe.Prod b body =>
          let c := Char.to_int (String.get pat i) in
          if Int.equal c 118   (* [comment removed for export] *)
          then match vs with
               | v :: vs' => walk (Constr.Unsafe.substnl [v] 0 body) pat (Int.add i 1) vs' hyps
               | [] => fail_msg "SzSec: fewer Section variables than the pattern says"
               end
          else if Int.equal c 107   (* [comment removed for export] *)
          then walk (Constr.Unsafe.substnl ['I] 0 body) pat (Int.add i 1) vs hyps
          else walk (Constr.Unsafe.substnl ['I] 0 body) pat (Int.add i 1) vs (Constr.Binder.type b :: hyps)
      | _ => fail_msg "SzSec: the statement has fewer binders than the pattern"
      end.
  Ltac2 count_v (pat : string) : int :=
    let rec go (i : int) (n : int) : int :=
      if Int.equal i (String.length pat) then n
      else go (Int.add i 1) (if Int.equal (Char.to_int (String.get pat i)) 118 then Int.add n 1 else n) in
    go 0 0.
  (* [comment removed for export] *)
  Ltac2 tyP (stmt : constr) (pat : string) : unit :=
    Control.enter (fun () =>
      let (t, _) := walk stmt pat 0 (last_hyps (count_v pat)) [] in
      match Constr.Unsafe.kind (Std.eval_hnf t) with
      | Constr.Unsafe.Prod b _ => let a := Constr.Binder.type b in Control.refine (fun () => a)
      | _ => fail_msg "SzSec.tyP: the statement has fewer binders than the pattern"
      end).
  (* [comment removed for export] *)
  Ltac2 rec walkM (t : constr) (pat : string) (i : int) (vs : constr list) : constr :=
    if Int.equal i (String.length pat) then fail_msg "SzSec.tyM: every variable of the pattern is already declared"
    else
      match Constr.Unsafe.kind (Std.eval_hnf t) with
      | Constr.Unsafe.Prod b body =>
          if Int.equal (Char.to_int (String.get pat i)) 118
          then match vs with
               | v :: vs' => walkM (Constr.Unsafe.substnl [v] 0 body) pat (Int.add i 1) vs'
               | [] => Constr.Binder.type b
               end
          else walkM (Constr.Unsafe.substnl ['I] 0 body) pat (Int.add i 1) vs
      | _ => fail_msg "SzSec.tyM: the statement has fewer binders than the pattern"
      end.
  (* [comment removed for export] *)
  Ltac2 rec walkMf (t : constr) (pat : string) (i : int) (vs : constr list) (pend : constr list) : constr :=
    if Int.equal i (String.length pat) then fail_msg "SzSec.tyM: every variable of the pattern is already declared"
    else
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Prod b body =>
          if Int.equal (Char.to_int (String.get pat i)) 118
          then match vs with
               | v :: vs' => walkMf body pat (Int.add i 1) vs' (v :: pend)
               | [] => Constr.Unsafe.substnl pend 0 (Constr.Binder.type b)
               end
          else walkMf body pat (Int.add i 1) vs ('I :: pend)
      | _ => walkM (Constr.Unsafe.substnl pend 0 t) pat i vs
      end.
  Ltac2 tyM (stmt : constr) (pat : string) (first : ident) : unit :=
    Control.enter (fun () =>
      let rec from (l : (ident * constr option * constr) list) : (ident * constr option * constr) list :=
        match l with
        | [] => []
        | h :: l' => let (id, _, _) := h in if Ident.equal id first then l else from l'
        end in
      let vs := List.map (fun h => let (id, _, _) := h in Control.hyp id) (from (Control.hyps ())) in
      let a := walkMf (Std.eval_hnf stmt) pat 0 vs [] in
      Control.refine (fun () => a)).
  (* [comment removed for export] *)
  Ltac2 rec build (t : constr) (pat : string) (i : int) (vs : constr list) (hyps : constr list) : constr :=
    if Int.equal i (String.length pat) then List.fold_right (fun p q => constr:($p -> $q)) (List.rev hyps) t
    else
      match Constr.Unsafe.kind (Std.eval_hnf t) with
      | Constr.Unsafe.Prod b body =>
          let c := Char.to_int (String.get pat i) in
          if Int.equal c 118
          then match vs with
               | v :: vs' => build (Constr.Unsafe.substnl [v] 0 body) pat (Int.add i 1) vs' hyps
               | [] => fail_msg "SzSec: fewer Section variables than the pattern says"
               end
          else if Int.equal c 107
          then match Constr.Binder.name b with
               | Some id =>
                   let lam := Constr.in_context id (Constr.Binder.type b) (fun () =>
                                let r := build (Constr.Unsafe.substnl [Control.hyp id] 0 body) pat (Int.add i 1) vs hyps in
                                Control.refine (fun () => r)) in
                   match Constr.Unsafe.kind lam with
                   | Constr.Unsafe.Lambda b' bd => Constr.Unsafe.make (Constr.Unsafe.Prod b' bd)
                   | _ => fail_msg "SzSec.build: in_context did not return an abstraction"
                   end
               | None => fail_msg "SzSec.build: a kept binder without a name"
               end
          else build (Constr.Unsafe.substnl ['I] 0 body) pat (Int.add i 1) vs (Constr.Binder.type b :: hyps)
      | _ => fail_msg "SzSec: the statement has fewer binders than the pattern"
      end.
  Ltac2 bodyP (stmt : constr) (pat : string) : unit :=
    Control.enter (fun () => let r := build stmt pat 0 (last_hyps (count_v pat)) [] in Control.refine (fun () => r)).
  (* [comment removed for export] *)
  Ltac2 closeP (body : constr) (pat : string) : unit :=
    Control.enter (fun () =>
      let hs := last_hyps (String.length pat) in
      let rec part3 (i : int) (l : constr list) (vs : constr list) (ks : constr list) (ps : constr list) : constr list * constr list * constr list :=
        match l with
        | [] => (List.rev vs, List.rev ks, List.rev ps)
        | x :: l' => let c := Char.to_int (String.get pat i) in
                     if Int.equal c 118 then part3 (Int.add i 1) l' (x :: vs) ks ps
                     else if Int.equal c 107 then part3 (Int.add i 1) l' vs (x :: ks) ps
                     else part3 (Int.add i 1) l' vs ks (x :: ps)
        end in
      let (vs, ks, ps) := part3 0 hs [] [] [] in
      let rec args (t : constr) (vs : constr list) (acc : constr list) : constr list :=
        match vs with
        | [] => List.rev acc
        | v :: vs' =>
            match Constr.Unsafe.kind t with
            | Constr.Unsafe.Prod b bd =>
                let same := match Constr.Binder.name b with
                            | Some nm => (match Constr.Unsafe.kind v with Constr.Unsafe.Var id => Ident.equal id nm | _ => false end)
                            | None => false
                            end in
                if same then args bd vs' (v :: acc) else args t vs' acc
            | _ => List.rev acc
            end
        end in
      let a := args (Constr.type body) vs [] in
      let app := Constr.Unsafe.make (Constr.Unsafe.App body (Array.of_list (List.append a (List.append ks ps)))) in
      Control.refine (fun () => app)).
  (* [comment removed for export] *)
  Ltac2 ty (stmt : constr) (k : int) : unit := tyP stmt (String.make k (Char.of_int 118)).
  Ltac2 body (stmt : constr) (n : int) : unit := bodyP stmt (String.make n (Char.of_int 118)).
End SzSec.
