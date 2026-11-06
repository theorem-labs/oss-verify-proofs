(* Instances of a sectioned development.

   [gen] is a module whose constants were closed over section variables; [inst] is a module that defines
   one constant per section variable, under the same name; [tgt] is the module being filled, a sibling of
   [inst].  [mk] takes a reference to one constant of [gen], a reference to one constant of [inst], the
   short name of [tgt] and the [manifest] names; [ty]/[body]/[proof] produce, for the constant [n] of [gen]:
   - its type with every leading binder [x] such that [inst.x] exists instantiated by [inst.x];
   - its body (delta of [gen.n], then beta with exactly those arguments);
   - the application [gen.n inst.x ...], cast to that type.
   In types and bodies every application [gen.m inst.x ...] (to the same arguments) is replaced by
   [tgt.m], or by [inst.m] when [m] is listed in [manifest]; any other occurrence of a constant of [gen]
   is an error. *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Env Ident String Char Array Control List Std.

Ltac2 Type exn ::= [ FillByNameError (string) ].
Ltac2 fbn_fail (s : string) := Control.throw (FillByNameError s).

Ltac2 Type config := { gen : ident list; inst : ident list; tgt : ident list; manifest : ident list }.

Ltac2 drop_last (l : ident list) : ident list := List.firstn (Int.sub (List.length l) 1) l.

Ltac2 mk (gen : Std.reference) (inst : Std.reference) (tgt : ident) (manifest : ident list) : config :=
  let ip := drop_last (Env.path inst) in
  { gen := drop_last (Env.path gen); inst := ip; tgt := List.append (drop_last ip) [tgt]; manifest := manifest }.

Ltac2 member (m : ident list) (x : ident) : Std.reference option := Env.get (List.append m [x]).

Ltac2 global_ref (m : ident list) (x : ident) : Std.reference :=
  match member m x with
  | Some r => r
  | None => fbn_fail (String.app "FillByName: no global " (Ident.to_string x))
  end.

Ltac2 global (m : ident list) (x : ident) : constr := Env.instantiate (global_ref m x).

Ltac2 mk_app (f : constr) (args : constr list) : constr :=
  match args with
  | [] => f
  | _ => Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args))
  end.

Ltac2 rec fill (inst : ident list) (ty : constr) : constr list * constr :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Prod b body =>
      (match Constr.Binder.name b with
       | Some x =>
           (match member inst x with
            | Some r =>
                let a := Env.instantiate r in
                let (args, rest) := fill inst (Constr.Unsafe.substnl [a] 0 body) in
                (a :: args, rest)
            | None => ([], ty)
            end)
       | None => ([], ty)
       end)
  | _ => ([], ty)
  end.

Ltac2 gen_member (c : config) (h : constr) : ident option :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant k _ =>
      let p := Env.path (Std.ConstRef k) in
      let n := List.length (c.(gen)) in
      if Int.equal (List.length p) (Int.add n 1) then
        (if List.equal Ident.equal (List.firstn n p) (c.(gen)) then Some (List.nth p n) else None)
      else None
  | _ => None
  end.

Ltac2 replacement (c : config) (x : ident) : constr :=
  if List.mem Ident.equal x (c.(manifest)) then global (c.(inst)) x else global (c.(tgt)) x.

Ltac2 fill_of (c : config) (x : ident) : constr list :=
  let (args, _) := fill (c.(inst)) (Constr.type (global (c.(gen)) x)) in args.

Ltac2 unexpected (x : ident) := fbn_fail (String.app "FillByName: unexpected occurrence of " (Ident.to_string x)).

Ltac2 rec fold_term (c : config) (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      (match gen_member c h with
       | Some x =>
           let fa := fill_of c x in
           let al := Array.to_list args in
           let m := List.length fa in
           if Int.lt (List.length al) m then unexpected x
           else if List.equal Constr.equal (List.firstn m al) fa
           then mk_app (replacement c x) (List.map (fold_term c) (List.skipn m al))
           else unexpected x
       | None => Constr.Unsafe.map (fold_term c) t
       end)
  | Constr.Unsafe.Constant _ _ =>
      (match gen_member c t with
       | Some x => (match fill_of c x with [] => replacement c x | _ => unexpected x end)
       | None => t
       end)
  | _ => Constr.Unsafe.map (fold_term c) t
  end.

Ltac2 rec beta (f : constr) (args : constr list) : constr :=
  match args with
  | [] => f
  | a :: rest =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Lambda _ body => beta (Constr.Unsafe.substnl [a] 0 body) rest
       | _ => fbn_fail "FillByName: body has fewer binders than its instance arguments"
       end)
  end.

Ltac2 inst_type (c : config) (x : ident) : constr :=
  let (_, rest) := fill (c.(inst)) (Constr.type (global (c.(gen)) x)) in fold_term c rest.

Ltac2 delta_only (r : Std.reference) : Std.red_flags :=
  { Std.rStrength := Std.Norm; Std.rBeta := false; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
    Std.rZeta := false; Std.rDelta := false; Std.rConst := [r] }.

Ltac2 ty (c : config) (x : ident) : unit :=
  let t := inst_type c x in
  Control.refine (fun () => t).

Ltac2 body (c : config) (x : ident) : unit :=
  let r := global_ref (c.(gen)) x in
  let g := Env.instantiate r in
  let (args, _) := fill (c.(inst)) (Constr.type g) in
  let t := fold_term c (beta (Std.eval_cbv (delta_only r) g) args) in
  Control.refine (fun () => t).

Ltac2 proof (c : config) (x : ident) : unit :=
  let g := global (c.(gen)) x in
  let (args, _) := fill (c.(inst)) (Constr.type g) in
  let t := Constr.Unsafe.make (Constr.Unsafe.Cast (mk_app g args) Constr.Cast.default (inst_type c x)) in
  Control.refine (fun () => t).
