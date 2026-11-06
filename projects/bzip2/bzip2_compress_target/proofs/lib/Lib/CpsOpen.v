(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2 Ltac1 Std Control Constr Ident List Int Bool Message Option Array Env Fresh.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module CpsCore.
(* [comment removed for export] *)
Inductive tele : Type :=
| TNil (P : Prop)
| TAnd (A : Prop) (t : tele)
| TEx (T : Type) (f : T -> tele).
Fixpoint tprop (t : tele) : Prop :=
  match t with
  | TNil P => P
  | TAnd A t => A /\ tprop t
  | TEx T f => exists x : T, tprop (f x)
  end.
Fixpoint tcur (t : tele) (G : Prop) : Prop :=
  match t with
  | TNil P => P -> G
  | TAnd A t => A -> tcur t G
  | TEx T f => forall x : T, tcur (f x) G
  end.
(* [comment removed for export] *)
Fixpoint tele_elim (t : tele) (G : Prop) {struct t} : tprop t -> tcur t G -> G :=
  match t return tprop t -> tcur t G -> G with
  | TNil P => fun h k => k h
  | TAnd A t' => fun h k => match h with conj a r => tele_elim t' G r (k a) end
  | TEx T f => fun h k => match h with ex_intro _ x r => tele_elim (f x) G r (k x) end
  end.

Lemma cps_id : forall P : Prop, P -> P.
Proof. intros P p; exact p. Qed.

Module CPS.
Import Ltac2.Ltac2.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac2 mutable mode : int := 1.

Ltac2 fail_with (s : string) := Control.zero (Tactic_failure (Some (Message.of_string s))).

(* [comment removed for export] *)
Ltac2 rec ren_list (s : bool list) (p : int) : constr list :=
  match s with
  | [] => []
  | e :: r => if e then Constr.Unsafe.make (Constr.Unsafe.Rel p) :: ren_list r (Int.add p 1) else ren_list r (Int.add p 1)
  end.
(* [comment removed for export] *)
Ltac2 rename (s : bool list) (c : constr) : constr :=
  match ren_list s 1 with
  | [] => c
  | l => Constr.Unsafe.substnl l 0 c
  end.

Ltac2 Type consts := { c_and : constr; c_ex : constr; c_nil : constr; c_tand : constr; c_tex : constr }.

(* [comment removed for export] *)
Ltac2 rec build (cs : consts) (ty : constr) (k : int) (s : bool list) (g : constr) : constr * constr :=
  let anon (t : constr) := Constr.Binder.unsafe_make None Constr.Binder.Relevant t in
  if Int.le k 1 then
    (Constr.Unsafe.make (Constr.Unsafe.App (cs.(c_nil)) [| ty |]),
     Constr.Unsafe.make (Constr.Unsafe.Prod (anon (rename s ty)) g))
  else
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App h args =>
        if Int.equal (Array.length args) 2 then
          if Constr.equal h (cs.(c_and)) then
            let a := Array.get args 0 in
            let (t, ar) := build cs (Array.get args 1) (Int.sub k 1) (false :: s) g in
            (Constr.Unsafe.make (Constr.Unsafe.App (cs.(c_tand)) [| a; t |]),
             Constr.Unsafe.make (Constr.Unsafe.Prod (anon (rename s a)) ar))
          else if Constr.equal h (cs.(c_ex)) then
            let xt := Array.get args 0 in
            match Constr.Unsafe.kind (Array.get args 1) with
            | Constr.Unsafe.Lambda b body =>
                let (t, ar) := build cs body (Int.sub k 1) (true :: s) g in
                (Constr.Unsafe.make (Constr.Unsafe.App (cs.(c_tex)) [| xt; Constr.Unsafe.make (Constr.Unsafe.Lambda b t) |]),
                 Constr.Unsafe.make (Constr.Unsafe.Prod
                   (Constr.Binder.unsafe_make (Some @x) Constr.Binder.Relevant (rename s xt)) ar))   (* [comment removed for export] *)
            | _ => fail_with "cps_destruct: existential over a non-lambda predicate"
            end
          else fail_with "cps_destruct: not a syntactic and/ex chain"
        else fail_with "cps_destruct: not a syntactic and/ex chain"
    | _ => fail_with "cps_destruct: not a syntactic and/ex chain"
    end.

Ltac2 is_and_ex (cs : consts) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 2 then Bool.or (Constr.equal h (cs.(c_and))) (Constr.equal h (cs.(c_ex))) else false
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec next_of (h : ident) (l : (ident * constr option * constr) list) : ident option :=
  match l with
  | [] => None
  | x :: r => let (id, _, _) := x in
      if Ident.equal id h then match r with [] => None | y :: _ => let (id', _, _) := y in Some id' end
      else next_of h r
  end.
(* [comment removed for export] *)
Ltac2 is_section_var (id : ident) : bool :=
  List.exist (fun r => match r with Std.VarRef v => Ident.equal v id | _ => false end) (Env.expand [id]).

(* [comment removed for export] *)
Ltac2 rec flatten_and (oap : Std.or_and_intro_pattern) : Std.intro_pattern list option :=
  let two (p : Std.intro_pattern) (q : Std.intro_pattern) : Std.intro_pattern list option :=
    match q with
    | Std.IntroAction a =>
        match a with
        | Std.IntroOrAndPattern o => match flatten_and o with Some r => Some (p :: r) | None => Some [p; q] end
        | _ => Some [p; q]
        end
    | _ => Some [p; q]
    end in
  match oap with
  | Std.IntroAndPattern l => match l with [p; q] => two p q | _ => None end
  | Std.IntroOrPattern ll => match ll with [l] => (match l with [p; q] => two p q | _ => None end) | _ => None end
  end.

(* [comment removed for export] *)
Ltac2 rec intro_comps (pats : Std.intro_pattern list) (loc : Std.move_location option) (wild : ident list) : unit :=
  match pats with
  | [] => (match wild with [] => () | _ :: _ => Std.clear wild end)
  | p :: rest =>
      match p with
      | Std.IntroNaming n =>
          (match n with
           | Std.IntroIdentifier id => Std.intro (Some id) loc
           | Std.IntroFresh id => Std.intro (Some (Fresh.in_goal id)) loc
           | Std.IntroAnonymous => Std.intro None loc
           end);
          intro_comps rest loc wild
      | Std.IntroAction a =>
          match a with
          | Std.IntroWildcard =>
              let tmp := Fresh.in_goal @_cps_w in
              Std.intro (Some tmp) loc; intro_comps rest loc (tmp :: wild)
          | Std.IntroOrAndPattern oap =>
              let tmp := Fresh.in_goal @_cps_t in
              Std.intro (Some tmp) loc;
              let plain () :=
                Std.destruct false [ { Std.indcl_arg := Std.ElimOnIdent tmp; Std.indcl_eqn := None; Std.indcl_as := Some oap; Std.indcl_in := None } ] None in
              (* [comment removed for export] *)
              (match flatten_and oap with
               | Some l =>
                   if Int.ge (List.length l) 3 then
                     match Control.case (fun () => cps_open_one (Control.hyp tmp) l false) with
                     | Val _ => ()
                     | Err _ => plain ()
                     end
                   else plain ()
               | None => plain ()
               end);
              Control.enter (fun () => intro_comps rest loc wild)
          | _ =>
              (* [comment removed for export] *)
              let tmp := Fresh.in_goal @_cps_t in
              Std.intro (Some tmp) loc;
              Std.apply true false [ (fun () => ('cps_id, Std.NoBindings)) ] (Some (tmp, Some p));
              Control.enter (fun () => intro_comps rest loc wild)
          end
      | Std.IntroForthcoming _ => fail_with "cps_destruct: forthcoming pattern"
      end
  end
with cps_open_one (h : constr) (pats : Std.intro_pattern list) (keep : bool) : unit :=
  let cs := { c_and := '@and; c_ex := '@ex; c_nil := '@TNil; c_tand := '@TAnd; c_tex := '@TEx } in
  (* [comment removed for export] *)
  let nfbi (c : constr) : constr :=
    Std.eval_lazy { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
                    Std.rZeta := false; Std.rDelta := false; Std.rConst := [] } c in
  let g := nfbi (Control.goal ()) in
  let ty1 := nfbi (Constr.type h) in
  (* [comment removed for export] *)
  let ty := if is_and_ex cs ty1 then ty1 else nfbi (Std.eval_hnf ty1) in
  let (t, ar) := build cs ty (List.length pats) [] g in
  let hid := if keep then None else match Constr.Unsafe.kind h with Constr.Unsafe.Var id => Some id | _ => None end in
  (match hid with
   | Some id => (if is_section_var id then fail_with "cps_destruct: section hypothesis" else ())
   | None => ()
   end);
  let loc := match hid with
             | Some id => (match next_of id (Control.hyps ()) with Some nx => Some (Std.MoveAfter nx) | None => None end)
             | None => None
             end in
  Control.refine (fun () => let e := '(_ :> $ar) in '(tele_elim $t $g $h $e));
  (match hid with Some id => Std.clear [id] | None => () end);
  intro_comps pats loc [].

(* [comment removed for export] *)
Ltac2 cps_open (h : constr) (pats : Std.intro_pattern list) (keep : bool) (first : bool) : unit :=
  let hvar := match Constr.Unsafe.kind h with Constr.Unsafe.Var id => Some id | _ => None end in
  match hvar with
  | Some id =>
      if Bool.and first (Bool.neg keep) then
        match pats with
        | p1 :: rest =>
            if Int.le (List.length rest) 1 then fail_with "cps_destruct: two components (plain destruct)"
            else if is_section_var id then fail_with "cps_destruct: section hypothesis"
            else
              let tmp := Fresh.in_goal @_cps_r in
              Std.destruct false [ { Std.indcl_arg := Std.ElimOnIdent id; Std.indcl_eqn := None;
                                     Std.indcl_as := Some (Std.IntroAndPattern [p1; Std.IntroNaming (Std.IntroIdentifier tmp)]);
                                     Std.indcl_in := None } ] None;
              Control.enter (fun () => cps_open_one (Control.hyp tmp) rest false)
        | [] => fail_with "cps_destruct: no pattern"
        end
      else cps_open_one h pats keep
  | None => cps_open_one h pats keep
  end.

(* [comment removed for export] *)
Ltac2 Type snapshot := ((ident * constr option) list * constr option) list.
Ltac2 Type exn ::= [ Snap (snapshot) ].
Ltac2 noev (c : constr) : constr option := if Constr.has_evar c then None else Some c.
Ltac2 snap () : snapshot :=
  let acc : snapshot ref := { contents := [] } in
  Control.enter (fun () =>
    acc.(contents) := (List.map (fun h => let (id, _, ty) := h in (id, noev ty)) (Control.hyps ()), noev (Control.goal ())) :: acc.(contents));
  List.rev (acc.(contents)).
Ltac2 probe (tac : unit -> unit) : snapshot option :=
  match Control.case (fun () => tac (); Control.zero (Snap (snap ()))) with
  | Val _ => None
  | Err e => match e with Snap s => Some s | _ => None end
  end.
Ltac2 msg3 (a : string) (x : constr) (b : string) (y : constr) : message :=
  Message.concat (Message.of_string a) (Message.concat (Message.of_constr x) (Message.concat (Message.of_string b) (Message.of_constr y))).
Ltac2 same_term (a : constr option) (b : constr option) : (constr * constr) option :=
  match a with
  | None => None
  | Some x => match b with None => None | Some y => if Constr.equal x y then None else Some (x, y) end
  end.
Ltac2 rec same_hyps (a : (ident * constr option) list) (b : (ident * constr option) list) : message option :=
  match a with
  | [] => match b with [] => None | x :: _ => let (id, _) := x in Some (Message.concat (Message.of_string "extra hypothesis ") (Message.of_ident id)) end
  | x :: ar =>
      match b with
      | [] => let (id, _) := x in Some (Message.concat (Message.of_string "missing hypothesis ") (Message.of_ident id))
      | y :: br =>
          let (ia, ta) := x in let (ib, tb) := y in
          if Bool.neg (Ident.equal ia ib) then
            Some (Message.concat (Message.concat (Message.of_string "name/order: destruct gives ") (Message.of_ident ia))
                                 (Message.concat (Message.of_string " where cps gives ") (Message.of_ident ib)))
          else
            match same_term ta tb with
            | Some d => let (u, v) := d in
                Some (Message.concat (Message.concat (Message.of_string "type of ") (Message.of_ident ia)) (msg3 ": destruct gives " u " where cps gives " v))
            | None => same_hyps ar br
            end
      end
  end.
Ltac2 rec same_goals (a : snapshot) (b : snapshot) : message option :=
  match a with
  | [] => match b with [] => None | _ :: _ => Some (Message.of_string "cps leaves more goals") end
  | x :: ar =>
      match b with
      | [] => Some (Message.of_string "cps leaves fewer goals")
      | y :: br =>
          let (ha, ga) := x in let (hb, gb) := y in
          match same_hyps ha hb with
          | Some m => Some m
          | None =>
              match same_term ga gb with
              | Some d => let (u, v) := d in Some (msg3 "conclusion: destruct gives " u " where cps gives " v)
              | None => same_goals ar br
              end
          end
      end
  end.

(* [comment removed for export] *)
Ltac2 entry (geth : unit -> constr) (p : Std.intro_pattern) (keep : bool) (first : bool) (fb : unit -> unit) : unit :=
  let pats := match p with
              | Std.IntroAction a => (match a with Std.IntroOrAndPattern o => flatten_and o | _ => None end)
              | _ => None
              end in
  match pats with
  | None => fb ()
  | Some pats =>
      let run () := cps_open (geth ()) pats keep first in
      if Int.equal mode 0 then fb ()
      else if Int.equal mode 1 then
        match Control.case run with
        | Val _ => ()
        | Err _ => fb ()
        end
      else
        match probe run with
        | None => fb ()
        | Some sn =>
            match probe fb with
            | None =>
                if Int.equal mode 2 then Control.throw (Tactic_failure (Some (Message.of_string "CPS-DIFF: cps opening succeeds where destruct fails")))
                else (Message.print (Message.of_string "CPS-DIFF-LOG: cps opening succeeds where destruct fails"); fb ())
            | Some so =>
                match same_goals so sn with
                | Some msg =>
                    if Int.equal mode 2 then Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "CPS-DIFF: ") msg)))
                    else (Message.print (Message.concat (Message.of_string "CPS-DIFF-LOG: ") msg); fb ())
                | None => run ()
                end
            end
        end
  end.
Ltac2 get_h (v : Ltac1.t) : constr :=
  match Ltac1.to_constr v with
  | Some c => c
  | None => match Ltac1.to_ident v with Some id => Control.hyp id | None => fail_with "cps_destruct: neither a term nor a hypothesis name" end
  end.
Ltac2 get_pat (v : Ltac1.t) : Std.intro_pattern :=
  match Ltac1.to_intro_pattern v with Some p => p | None => fail_with "cps_destruct: not an intro pattern" end.
(* [comment removed for export] *)
Ltac2 intro_h () : constr := let id := Fresh.in_goal @_cps_h in Std.intro (Some id) None; Control.hyp id.
End CPS.
End CpsCore.

(* [comment removed for export] *)
Ltac cps_open1 := ltac2:(h p fb |- Ltac2.Control.enter (fun () => CpsCore.CPS.entry (fun () => CpsCore.CPS.get_h h) (CpsCore.CPS.get_pat p) Ltac2.Init.false Ltac2.Init.true (fun () => Ltac2.Ltac1.run fb))).
Ltac cps_pose1 := ltac2:(h p fb |- Ltac2.Control.enter (fun () => CpsCore.CPS.entry (fun () => CpsCore.CPS.get_h h) (CpsCore.CPS.get_pat p) Ltac2.Init.true Ltac2.Init.false (fun () => Ltac2.Ltac1.run fb))).
Ltac cps_intros1 := ltac2:(p fb |- Ltac2.Control.enter (fun () => CpsCore.CPS.entry CpsCore.CPS.intro_h (CpsCore.CPS.get_pat p) Ltac2.Init.false Ltac2.Init.false (fun () => Ltac2.Ltac1.run fb))).
Tactic Notation "cps_destruct" constr(H) "as" simple_intropattern(p) := cps_open1 H p ltac:(destruct H as p).
Tactic Notation "cps_pose" constr(H) "as" simple_intropattern(p) := cps_pose1 H p ltac:(pose proof H as p).
Tactic Notation "cps_intros" simple_intropattern(p) := cps_intros1 p ltac:(intros p).

(* [comment removed for export] *)
Module CpsOpenTests.
Ltac2 Set CpsCore.CPS.mode := 2.
Goal forall (P Q R S : Prop) (x : nat), P -> Q /\ R /\ (S /\ x = x) -> x = 0 -> R /\ S.
Proof.
  intros P Q R S x p H e.
  cps_destruct H as (q & r & s).
  split; [exact r | exact (proj1 s)].
Qed.
Goal forall (P : nat -> Prop) (Q : nat -> bool -> Prop) (R : Prop),
  (exists n, P n /\ exists b : bool, Q n b /\ (R <-> P n) /\ R) -> forall z : nat, z = z -> exists n b, P n /\ Q n b.
Proof.
  intros P Q R H z E.
  cps_destruct H as (n & pn & b & q & (rp & pr) & _).
  exists n, b. split; assumption.
Qed.
Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof. intros P Q H p. cps_destruct H as (pq & qp). exact (pq p). Qed.
Goal forall (A : Type) (P Q : A -> Prop), (forall a, exists b, P a /\ Q b /\ a = a) -> forall a : A, (exists b, Q b) /\ P a.
Proof.
  intros A P Q F a.
  cps_pose (F a) as (b & pa & qb & _).
  cps_destruct (F b) as (c & ? & ? & e).
  split; [exists b; exact qb | exact pa].
Qed.
Goal forall (P Q R : Prop), P /\ Q /\ R -> R /\ P.
Proof. intros P Q R. cps_intros (p & q & r). split; assumption. Qed.
(* [comment removed for export] *)
Goal forall (n m : nat) (pr : nat * nat), pr = (n, m) -> fst pr = n.
Proof. intros n m pr E. cps_destruct pr as (a & b). cbn. congruence. Qed.
(* [comment removed for export] *)
Goal forall (P Q : Prop) (H : P /\ Q), H = H.
Proof. intros P Q H. cps_destruct H as (p & q). reflexivity. Qed.
End CpsOpenTests.
