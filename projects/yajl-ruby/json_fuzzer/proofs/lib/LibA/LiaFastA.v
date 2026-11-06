(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require StoreFast ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma dm_lit : forall x y : Z, 0 < y -> x = y * (x / y) + x mod y /\ 0 <= x mod y < y.
Proof. intros x y H. split; [apply Z.div_mod; intros E; rewrite E in H; discriminate H | apply Z.mod_pos_bound; exact H]. Qed.

Ltac2 le_isc (h : constr) (r : Std.reference) : bool :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant c _ => (match r with Std.ConstRef c' => Constant.equal c c' | _ => false end)
  | Constr.Unsafe.Ind i _ => (match r with Std.IndRef i' => Ind.equal i i' | _ => false end)
  | Constr.Unsafe.Constructor k _ => (match r with Std.ConstructRef k' => Constructor.equal k k' | _ => false end)
  | _ => false
  end.
Ltac2 rec le_pos_lit (p : constr) : bool :=
  match Constr.Unsafe.kind p with
  | Constr.Unsafe.App c args =>
      if Int.equal (Array.length args) 1 then
        (match Constr.Unsafe.kind c with Constr.Unsafe.Constructor _ _ => le_pos_lit (Array.get args 0) | _ => false end)
      else false
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.
Ltac2 le_zpos_lit (y : constr) : bool :=
  match Constr.Unsafe.kind y with
  | Constr.Unsafe.App c args =>
      if Int.equal (Array.length args) 1 then (if le_isc c reference:(Z.pos) then le_pos_lit (Array.get args 0) else false) else false
  | _ => false
  end.
Ltac2 Type le_acc := { mutable le_pairs : (constr * constr) list; mutable le_done : (constr * constr) list; mutable le_qr : bool }.
Ltac2 le_mem (x : constr) (y : constr) (l : (constr * constr) list) : bool :=
  List.exist (fun p => let (x', y') := p in if Constr.equal y y' then Constr.equal x x' else false) l.
Ltac2 rec le_scan (a : le_acc) (c : constr) : unit :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      Array.iter (le_scan a) args;
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant _ _ =>
           if Int.equal (Array.length args) 2 then
             (if Bool.or (le_isc f reference:(Z.div)) (le_isc f reference:(Z.modulo)) then
                (let x := Array.get args 0 in let y := Array.get args 1 in
                 if Bool.and (Constr.Unsafe.is_closed x) (Constr.Unsafe.is_closed y) then
                   (if le_mem x y (a.(le_pairs)) then () else a.(le_pairs) := (x, y) :: a.(le_pairs))
                 else ())
              else if Bool.or (le_isc f reference:(Z.quot)) (le_isc f reference:(Z.rem)) then a.(le_qr) := true
              else ())
           else ()
       | _ => le_scan a f
       end)
  | Constr.Unsafe.Var _ => () | Constr.Unsafe.Rel _ => () | Constr.Unsafe.Constant _ _ => ()
  | Constr.Unsafe.Constructor _ _ => () | Constr.Unsafe.Ind _ _ => () | Constr.Unsafe.Sort _ => ()
  | _ => Constr.Unsafe.iter (le_scan a) c
  end.
Ltac2 le_arith_ty (t : constr) : bool :=
  if le_isc t reference:(Z) then true else if le_isc t reference:(nat) then true else if le_isc t reference:(N) then true
  else if le_isc t reference:(positive) then true else if le_isc t reference:(bool) then true else le_isc t reference:(comparison).
Ltac2 rec le_prop (a : le_acc) (t : constr) : unit :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b body => le_prop a (Constr.Binder.type b); le_prop a body
  | Constr.Unsafe.LetIn _ v body => le_scan a v; le_prop a body
  | Constr.Unsafe.Cast c _ _ => le_prop a c
  | Constr.Unsafe.App h args =>
      if le_isc h reference:(eq) then (if le_arith_ty (Array.get args 0) then Array.iter (le_scan a) args else ())
      else if Bool.or (Bool.or (le_isc h reference:(and)) (le_isc h reference:(or))) (Bool.or (le_isc h reference:(not)) (le_isc h reference:(iff)))
      then Array.iter (le_prop a) args
      else if le_isc h reference:(ex) then Array.iter (le_prop a) args
      else if le_isc h reference:(LiaTuning.zify_done) then
        (if Int.equal (Array.length args) 2 then a.(le_done) := (Array.get args 0, Array.get args 1) :: a.(le_done) else ())
      else if Bool.or (Bool.or (Bool.or (le_isc h reference:(Z.le)) (le_isc h reference:(Z.lt))) (Bool.or (le_isc h reference:(Z.ge)) (le_isc h reference:(Z.gt))))
                      (Bool.or (Bool.or (le_isc h reference:(le)) (le_isc h reference:(lt))) (Bool.or (le_isc h reference:(ge)) (le_isc h reference:(gt))))
      then Array.iter (le_scan a) args
      else if Bool.or (le_isc h reference:(Z.divide)) (Bool.or (le_isc h reference:(N.le)) (le_isc h reference:(N.lt))) then Array.iter (le_scan a) args
      else ()
  | Constr.Unsafe.Lambda _ body => le_prop a body
  | _ => ()
  end.
Ltac2 le_euclid_pass () : unit :=
  let a := { le_pairs := []; le_done := []; le_qr := false } in
  le_prop a (Control.goal ());
  List.iter (fun h => let (_, body, ty) := h in
               le_prop a ty;
               match body with Some b => le_scan a b | None => () end) (Control.hyps ());
  let todo := List.filter (fun p => let (x, y) := p in Bool.neg (le_mem x y (a.(le_done)))) (List.rev (a.(le_pairs))) in
  List.iter (fun p => let (x, y) := p in
     if le_zpos_lit y then
       (let t := constr:(dm_lit $x $y (@eq_refl comparison Lt)) in
        let id := Fresh.in_goal @zdm in
        Std.assert (Std.AssertValue id t);
        let mk := constr:(I : LiaTuning.zify_done $x $y) in
        let id2 := Fresh.in_goal @zdmk in
        Std.assert (Std.AssertValue id2 mk))
     else ltac1:(x y |- LiaTuning.zify_new_dm x y) (Ltac1.of_constr x) (Ltac1.of_constr y)) todo;
  (if a.(le_qr) then ltac1:(repeat LiaTuning.zify_qr_step) else ());
  match todo with
  | [] => if a.(le_qr) then ltac1:(cbv beta) else ()
  | _ :: _ => ltac1:(cbv beta)
  end.
Ltac le_euclid_pass := ltac2:(Control.enter le_euclid_pass).
(* [comment removed for export] *)
Ltac le_has_dm :=
  match goal with
  | |- context [Z.div _ _] => idtac | |- context [Z.modulo _ _] => idtac
  | _ : context [Z.div _ _] |- _ => idtac | _ : context [Z.modulo _ _] |- _ => idtac
  | |- context [Z.quot _ _] => idtac | |- context [Z.rem _ _] => idtac
  | _ : context [Z.quot _ _] |- _ => idtac | _ : context [Z.rem _ _] |- _ => idtac
  end.
Ltac zify_fast_euclid3 :=
  Z.divide_to_equations';
  first [ le_has_dm; le_euclid_pass | idtac ];
  Z.euclidean_division_equations_cleanup.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac policy_close1_cheap H :=
  eapply H; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve [ eauto | LiaA.lia_probe | ZBridge.zsimp; LiaA.lia_probe ].

(* [comment removed for export] *)
Ltac2 pp_candidates_sc () : (ident * int) list :=
  let g := Control.goal () in
  let p := LiaA.pp_head g in
  let av := match Constr.Unsafe.kind g with
            | Constr.Unsafe.App _ args =>
                let n := Array.length args in
                if Int.lt 0 n then LiaA.pp_vars p (Array.get args (Int.sub n 1)) else []
            | _ => []
            end in
  let lit := match av with [] => true | _ :: _ => false end in
  let hs := List.rev (Control.hyps ()) in
  let cands := List.map_filter (fun h => let (id, _, ty) := h in
                 if Constr.equal (LiaA.pp_head (LiaA.pp_codomain ty)) p then
                   (let hv := LiaA.pp_vars p ty in
                    let score := if StoreFast.SF2.meets hv av then 0
                                 else if Bool.and lit (match hv with [] => true | _ :: _ => false end) then 1
                                 else 2 in
                    Some (id, score))
                 else None) hs in
  let pick := fun k => List.filter (fun c => let (_, sc) := c in Int.equal sc k) cands in
  List.append (pick 0) (List.append (pick 1) (pick 2)).

(* [comment removed for export] *)
Ltac2 pp_try2 (cheap1 : Ltac1.t) (close1 : Ltac1.t) : unit :=
  let cs := pp_candidates_sc () in
  let c0 := List.map_filter (fun c => let (id, sc) := c in if Int.equal sc 0 then Some id else None) cs in
  let cr := List.map_filter (fun c => let (id, sc) := c in if Int.equal sc 0 then None else Some id) cs in
  let rec go cl ids := match ids with
    | [] => Control.zero (Tactic_failure None)
    | id :: rest =>
        Control.plus (fun () => Ltac1.apply cl [Ltac1.of_constr (Control.hyp id)] (fun t => Ltac1.run t))
                     (fun _ => go cl rest)
    end in
  Control.once (fun () =>
    match c0 with
    | _ :: _ => go close1 (List.append c0 cr)     (* [comment removed for export] *)
    | [] => Control.plus (fun () => go cheap1 cr) (fun _ => go close1 cr)
    end).
Ltac LiaA.policy_pick ::=
  ltac2:(Control.enter (fun () => pp_try2 ltac1val:(fun H => policy_close1_cheap H) ltac1val:(fun H => LiaA.policy_close1 H))).

(* [comment removed for export] *)
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid3.
Goal forall x s : Z, 0 <= x -> s = 2147450880 + x / 8 -> 2147450880 <= s /\ s * 8 <= 17179607040 + x.
Proof. intros. lia. Qed.
Goal forall x y s : Z, 0 < y -> 0 <= x -> s = x / y + (x + 1) mod 4096 -> 0 <= s.
Proof. intros. assert (0 <= x / y) by (apply Z.div_pos; lia). lia. Qed.
Goal forall x : Z, 0 <= x -> Z.quot x 8 <= x /\ x / 8 <= x.
Proof. intros. lia. Qed.
Goal forall (P : Z * nat -> Prop) (lo hi a : Z), (forall b k, lo <= b -> b + Z.of_nat k <= hi -> P (b, k)) ->
  (forall b k, 5 <= b -> b + Z.of_nat k <= 7 -> P (b, k)) -> lo <= a / 8 -> a / 8 + 8 <= hi -> P (a / 8, 8%nat).
Proof. intros P lo hi a H1 H2 A B. LiaA.policy_pick. Qed.
