(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import List.
From Ltac2 Require Import Ltac2 Printf.
Import ListNotations.
Set Default Proof Mode "Classic".

Fixpoint sfpred (ts : list Type) (R : Type) : Type :=
match ts with [] => R | A :: ts' => A -> sfpred ts' R end.
Fixpoint sfexs (ts : list Type) : sfpred ts Prop -> Prop :=
match ts with [] => fun P => P | A :: ts' => fun P => exists x : A, sfexs ts' (P x) end.
Fixpoint sfandsT (l : list Prop) (T : Prop) : Prop :=
match l with [] => T | A :: l' => A /\ sfandsT l' T end.
Fixpoint sfimpsT (l : list Prop) (T G : Prop) : Prop :=
match l with [] => T -> G | A :: l' => A -> sfimpsT l' T G end.
Fixpoint sfbody (ts : list Type) : sfpred ts (list Prop) -> sfpred ts Prop -> sfpred ts Prop :=
match ts with [] => fun L T => sfandsT L T | A :: ts' => fun L T x => sfbody ts' (L x) (T x) end.
Fixpoint sfall (ts : list Type) : sfpred ts (list Prop) -> sfpred ts Prop -> Prop -> Prop :=
match ts with [] => fun L T G => sfimpsT L T G | A :: ts' => fun L T G => forall x : A, sfall ts' (L x) (T x) G end.
Fixpoint sfintro (ts : list Type) : sfpred ts Prop -> Prop -> Prop :=
match ts with [] => fun P R => P -> R | A :: ts' => fun P R => forall w : A, sfintro ts' (P w) R end.

Lemma sfands_elim : forall l T G, sfandsT l T -> sfimpsT l T G -> G.
Proof. induction l as [|A l IH]; intros T G H K; cbn in *; [exact (K H)|]. destruct H as [a H]. exact (IH T G H (K a)). Qed.
Lemma sf_elim : forall ts L T (G : Prop), sfexs ts (sfbody ts L T) -> sfall ts L T G -> G.
Proof.
induction ts as [|A ts IH]; intros L T G H K; cbn in *; [exact (sfands_elim L T G H K)|].
destruct H as [x H]. exact (IH (L x) (T x) G H (K x)).
Qed.
Lemma sf_intro_gen : forall ts P (R : Prop), (sfexs ts P -> R) -> sfintro ts P R.
Proof.
induction ts as [|A ts IH]; intros P R H; cbn in *; [exact H|].
intros w. apply IH. intros E. apply H. exists w. exact E.
Qed.
Definition sf_intro ts P : sfintro ts P (sfexs ts P) := sf_intro_gen ts P (sfexs ts P) (fun x => x).

Ltac2 mutable lx_report : bool := false.
Ltac2 lx_say (s : string) : unit := if lx_report then printf "%s" s else ().
Ltac2 lx_fail (s : string) := Control.zero (Tactic_failure (Some (Message.of_string s))).
Ltac2 lx_app (f : constr) (a : constr array) : constr := Constr.Unsafe.make (Constr.Unsafe.App f a).
Ltac2 lx_ref (r : Std.reference) : constr := Env.instantiate r.
Ltac2 lx_is (r : Std.reference) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Ind i _ => (match r with Std.IndRef j => Ind.equal i j | _ => false end)
| _ => false
end.
Ltac2 rec lx_nat (c : constr) : int :=
lazy_match! c with
| O => 0
| S ?n => Int.add 1 (lx_nat n)
end.

Ltac2 rec lx_list (ty : constr) (l : constr list) : constr :=
match l with
| [] => lx_app (lx_ref reference:(nil)) [| ty |]
| x :: r => lx_app (lx_ref reference:(cons)) [| ty; x; lx_list ty r |]
end.

Ltac2 rec lx_lams (bs : binder list) (body : constr) : constr :=
match bs with
| [] => body
| b :: r => Constr.Unsafe.make (Constr.Unsafe.Lambda b (lx_lams r body))
end.
Ltac2 rec lx_prods (bs : binder list) (body : constr) : constr :=
match bs with
| [] => body
| b :: r => Constr.Unsafe.make (Constr.Unsafe.Prod b (lx_prods r body))
end.

Ltac2 lx_ex (c : constr) : (binder * constr * constr) option :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App h args =>
if lx_is reference:(ex) h then
(if Int.equal (Array.length args) 2 then
(match Constr.Unsafe.kind (Array.get args 1) with
| Constr.Unsafe.Lambda b body => Some (b, Array.get args 0, body)
| _ => None
end)
else None)
else None
| _ => None
end.
Ltac2 lx_and (c : constr) : (constr * constr) option :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App h args =>
if lx_is reference:(and) h then
(if Int.equal (Array.length args) 2 then Some (Array.get args 0, Array.get args 1) else None)
else None
| _ => None
end.

Ltac2 lx_checked (c : constr) : constr :=
match Constr.Unsafe.check c with
| Val c' => c'
| Err e => Control.zero e
end.

Ltac2 lx_sort_of (lemma : constr) : constr :=
match Constr.Unsafe.kind (Constr.type lemma) with
| Constr.Unsafe.Prod b _ =>
(match Constr.Unsafe.kind (Constr.Binder.type b) with
| Constr.Unsafe.App _ args => Array.get args 0
| _ => lx_fail "lx_sort_of"
end)
| _ => lx_fail "lx_sort_of"
end.

Ltac2 rec lx_exs (n : int) (c : constr) : binder list * constr list * constr :=
if Int.le n 0 then ([], [], c) else
match lx_ex c with
| Some (b, a, body) =>
if Constr.Unsafe.closedn 0 a then
(let (bs, tys, inner) := lx_exs (Int.sub n 1) body in (b :: bs, a :: tys, inner))
else ([], [], c)
| None => ([], [], c)
end.
Ltac2 rec lx_ands (n : int) (c : constr) : constr list * constr :=
if Int.le n 0 then ([], c) else
match lx_and c with
| Some (x, y) => let (l, t) := lx_ands (Int.sub n 1) y in (x :: l, t)
| None => ([], c)
end.

Ltac2 lx_eexists (n : int) : unit :=
let g0 := Control.goal () in

let g := match lx_ex g0 with Some _ => g0 | None => Std.eval_hnf g0 end in
let (bs, tys, body) := lx_exs n g in
let m := List.length tys in
(if Int.equal m 0 then lx_fail "sf_eexists: not an existential" else ());
let lem := lx_ref reference:(sf_intro) in
let ts := lx_checked (lx_list (lx_sort_of lem) tys) in
let p := lx_lams bs body in
let ws := List.map (fun a => let e := open_constr:(_ : $a) in
match Constr.Unsafe.kind e with Constr.Unsafe.Cast c _ _ => c | _ => e end) tys in

let newg := Constr.Unsafe.substnl (List.rev ws) 0 body in
let k := open_constr:(_ : $newg) in
let k := match Constr.Unsafe.kind k with Constr.Unsafe.Cast c _ _ => c | _ => k end in
let term := lx_app lem (Array.of_list (List.append [ts; p] (List.append ws [k]))) in
(match Constr.Unsafe.kind k with
| Constr.Unsafe.Evar ev _ => Std.exact_no_check term; Control.new_goal ev; lx_say "LEANEX-OK e"
| _ => lx_fail "sf_eexists: continuation"
end);

let rec rest (i : int) := if Int.le i 0 then () else (ltac1:(eexists); rest (Int.sub i 1)) in
rest (Int.sub n m).

Ltac2 lx_destruct (k : int) (h : ident) : unit :=
let hc := Control.hyp h in
let g := Control.goal () in
let ty0 := Constr.type hc in
let ty := match lx_ex ty0 with
| Some _ => ty0
| None => (match lx_and ty0 with Some _ => ty0 | None => Std.eval_hnf ty0 end)
end in
let want := Int.sub k 1 in
let (bs, tys, inner) := lx_exs want ty in
let d := List.length tys in
let (l, t) := lx_ands (Int.sub want d) inner in
let j := List.length l in
(if Int.equal (Int.add d j) want then () else lx_fail "sf_destruct: spine too short");
(if Int.equal want 0 then lx_fail "sf_destruct: nothing to do" else ());
let lem := lx_ref reference:(sf_elim) in
let ts := lx_checked (lx_list (lx_sort_of lem) tys) in
let ll := lx_lams bs (lx_list 'Prop l) in
let tt := lx_lams bs t in

let arrow (x : constr) (body : constr) := Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.unsafe_make None Constr.Binder.Relevant x) body) in
let rec arrows (i : int) (xs : constr list) : constr :=
match xs with
| [] => arrow (Constr.Unsafe.liftn i 1 t) g
| x :: r => arrow (Constr.Unsafe.liftn i 1 x) (arrows (Int.add i 1) r)
end in
let kty := lx_prods bs (arrows 0 l) in

(match List.last_opt (Control.hyps ()) with
| Some (idl, _, _) =>
if Ident.equal idl h then ()
else (ltac1:(pose proof I as sfM_); Std.move @sfM_ (Std.MoveAfter h); ltac1:(pose proof I as sfN_))
| None => ()
end);
let g := Control.goal () in
let hc := Control.hyp h in
let kk := open_constr:(_ : $kty) in
let kk := match Constr.Unsafe.kind kk with Constr.Unsafe.Cast c _ _ => c | _ => kk end in
let term := lx_app lem [| ts; ll; tt; g; hc; kk |] in
match Constr.Unsafe.kind kk with
| Constr.Unsafe.Evar ev _ => Std.exact_no_check term; Control.new_goal ev; lx_say "LEANEX-OK d"
| _ => lx_fail "sf_destruct: continuation"
end.

Ltac2 lx_fix_order () : unit :=
let hs := List.map (fun (id, _, _) => id) (Control.hyps ()) in
if Bool.neg (List.exist (Ident.equal @sfM_) hs) then () else
let rec after (l : ident list) : ident list :=
match l with [] => [] | x :: r => if Ident.equal x @sfM_ then r else after r end in
let rec upto (l : ident list) : ident list :=
match l with [] => [] | x :: r => if Ident.equal x @sfN_ then [] else x :: upto r end in
let trailing := upto (after hs) in
List.iter (fun id => Std.move id Std.MoveLast) trailing;
Std.clear [@sfM_; @sfN_].
Ltac sf_fix_order := ltac2:(Control.enter lx_fix_order).

Ltac2 lx_ident (v : Ltac1.t) : ident :=
match Ltac1.to_ident v with
| Some i => i
| None =>
match Ltac1.to_constr v with
| Some c => (match Constr.Unsafe.kind c with Constr.Unsafe.Var i => i | _ => lx_fail "LeanEx: not a hypothesis" end)
| None => lx_fail "LeanEx: not a hypothesis"
end
end.
Ltac2 lx_constr (v : Ltac1.t) : constr :=
match Ltac1.to_constr v with Some c => c | None => lx_fail "LeanEx: not a term" end.

Ltac2 lx_count_exs (c : constr) : int := let (_, tys, _) := lx_exs 1000 c in List.length tys.

Ltac2 lx_exs_then_all (h : ident) : unit :=
let hc := Control.hyp h in
let ty0 := Constr.type hc in
let ty := match lx_ex ty0 with
| Some _ => ty0
| None => (match lx_and ty0 with Some _ => ty0 | None => Std.eval_hnf ty0 end)
end in
let (_, tys, inner) := lx_exs 1000 ty in
let (l, _) := lx_ands 1000 inner in
let k := Int.add (Int.add (List.length tys) (List.length l)) 1 in
(if Int.le k 1 then lx_fail "lx_exs_then_all: nothing to do" else ());
lx_destruct k h;

List.iter (fun _ => let x := Fresh.in_goal @x in Std.intros false [Std.IntroNaming (Std.IntroIdentifier x)]) tys.
Ltac2 lx_exs_then_all1 (h : ident) : unit := Control.enter (fun () => lx_exs_then_all h).
Ltac sf_exs_then_all H := let f := ltac2:(h |- lx_exs_then_all1 (lx_ident h)) in let c := constr:(H) in f c.

Ltac2 lx_eexists_all () : unit :=
let n := lx_count_exs (Control.goal ()) in
if Int.equal n 0 then () else lx_eexists n.
Ltac sf_eexists_all := ltac2:(Control.enter lx_eexists_all).

Ltac2 lx_eexists1 (n : constr) : unit := Control.enter (fun () => lx_eexists (lx_nat n)).
Ltac2 lx_destruct1 (k : constr) (h : ident) : unit := Control.enter (fun () => lx_destruct (lx_nat k) h).

Ltac sf_eexists_core n :=
let f := ltac2:(n |- lx_eexists1 (lx_constr n)) in f n.
Ltac sf_destruct_core k H :=
let f := ltac2:(k h |- lx_destruct1 (lx_constr k) (lx_ident h)) in let c := constr:(H) in f k c.

Ltac2 lx_is_secvar (h : ident) : bool :=
match Env.get [h] with
| Some r => (match r with Std.VarRef _ => true | _ => false end)
| None => false
end.
Ltac2 lx_clear (h : ident) : unit :=
if lx_is_secvar h then () else Control.enter (fun () => Control.plus (fun () => Std.clear [h]) (fun _ => ())).
Ltac sf_clear H := first [ let f := ltac2:(h |- lx_clear (lx_ident h)) in let c := constr:(H) in f c | idtac ].

Ltac sf_fb := ltac2:(lx_say "LEANEX-FB").

Ltac sf_do_eexists n := lazymatch n with O => idtac | S ?m => eexists; sf_do_eexists m end.
Tactic Notation "sf_eexists" constr(n) := first [ sf_eexists_core n | sf_fb; sf_do_eexists n ].

Tactic Notation "sf_destruct" constr(k) hyp(H) "as" ne_simple_intropattern_list(ps) :=
sf_destruct_core k H; intros ps; sf_clear H; sf_fix_order.

Ltac sf_curry_stock k H :=
lazymatch k with
| S O => revert H
| S ?k' => let x := fresh "sfx" in let H' := fresh "sfH" in
destruct H as [x H']; sf_curry_stock k' H'; revert x
end.
Ltac sf_curry k H := first [ sf_destruct_core k H | sf_fb; sf_curry_stock k H ].
