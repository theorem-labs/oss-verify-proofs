(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac2 rec lm_closed_num (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constructor _ _ => Array.for_all lm_closed_num args
      | _ => false
      end
  | _ => false
  end.

Ltac2 lm_is_op (h : constr) : bool :=
  if Constr.equal h '@Z.add then true else if Constr.equal h '@Z.sub then true else if Constr.equal h '@Z.mul then true
  else if Constr.equal h '@Z.opp then true else if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
  else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true else if Constr.equal h '@and then true
  else if Constr.equal h '@or then true else if Constr.equal h '@not then true else if Constr.equal h '@Z.max then true
  else if Constr.equal h '@Z.min then true else false.

Ltac2 rec lm_mem (t : constr) (l : constr list) : bool :=
  match l with [] => false | x :: r => if Constr.equal x t then true else lm_mem t r end.

Ltac2 rec lm_atoms (t : constr) (acc : constr list) : constr list :=
  if lm_closed_num t then acc else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lm_is_op h then Array.fold_left (fun a x => lm_atoms x a) acc args
      else if Constr.equal h '@eq then
        (* [comment removed for export] *)
        (if Constr.equal (Array.get args 0) 'Z then lm_atoms (Array.get args 2) (lm_atoms (Array.get args 1) acc)
         else if lm_mem t acc then acc else t :: acc)
      else if lm_mem t acc then acc else t :: acc
  | _ => if lm_mem t acc then acc else t :: acc
  end.

(* [comment removed for export] *)
Ltac2 rec lm_plain (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Constr.equal h '@and then (if lm_plain (Array.get args 0) then lm_plain (Array.get args 1) else false)
      else if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true else if Constr.equal h '@Z.ge then true
      else if Constr.equal h '@Z.gt then true else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
      else if Constr.equal h '@lt then true else false
  | _ => if Constr.equal t 'True then true else false
  end.

(* [comment removed for export] *)
Ltac2 rec lm_arith_tree (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Constr.equal h '@and then (if lm_arith_tree (Array.get args 0) then lm_arith_tree (Array.get args 1) else false)
      else if Constr.equal h '@or then (if lm_arith_tree (Array.get args 0) then lm_arith_tree (Array.get args 1) else false)
      else if Constr.equal h '@not then lm_arith_tree (Array.get args 0)
      else if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true else if Constr.equal h '@Z.ge then true
      else if Constr.equal h '@Z.gt then true
      else if Constr.equal h '@eq then Constr.equal (Array.get args 0) 'Z
      else false
  | _ => false
  end.

Ltac2 rec lm_subset (l : constr list) (s : constr list) : bool :=
  match l with [] => true | x :: r => if lm_mem x s then lm_subset r s else false end.

(* [comment removed for export] *)
Ltac2 rec lm_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => lm_codomain b
  | Constr.Unsafe.LetIn _ _ b => lm_codomain b
  | Constr.Unsafe.Cast c _ _ => lm_codomain c
  | _ => t
  end.
Ltac2 rec lm_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => lm_head f
  | Constr.Unsafe.Cast c _ _ => lm_head c
  | _ => t
  end.
Ltac2 lm_ends_in_prop (ty : constr) : bool :=
  lazy_match! lm_codomain ty with Prop => true | _ => false end.
Ltac2 lm_sort_is_prop (ty : constr) : bool :=
  let h := lm_head (lm_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => lm_ends_in_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => lm_ends_in_prop (Constr.type h)
  | Constr.Unsafe.Var _ => lm_ends_in_prop (Constr.type h)
  | _ => false
  end.

Ltac2 lm_prune (subj : ident list) : unit :=
  let g := Control.goal () in
  let s := List.fold_left (fun acc id => lm_atoms (Constr.type (Control.hyp id)) acc) (lm_atoms g []) subj in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None =>
                    if List.exist (fun x => Ident.equal x id) subj then None
                    else if lm_plain ty then None
                    else if lm_arith_tree ty then (if lm_subset (lm_atoms ty []) s then None else Some id)
                    else if lm_sort_is_prop ty then Some id else None
                end) (Control.hyps ()) in
  (* [comment removed for export] *)
  List.iter (fun id => Control.plus (fun () => Std.clear [id]) (fun _ => ())) ids.

(* [comment removed for export] *)
Ltac2 lm_subjects () : ident list :=
  let hs := List.map (fun h => let (id, _, _) := h in id) (Control.hyps ()) in
  List.filter (fun s => List.exist (fun id => Ident.equal id s) hs) [@Ha__; @Ha; @NO].
Ltac2 lm_has_subject () : bool :=
  let hs := List.map (fun h => let (id, _, _) := h in id) (Control.hyps ()) in
  if List.exist (fun id => Ident.equal id @Ha__) hs then true else List.exist (fun id => Ident.equal id @Ha) hs.

Ltac munch_has := ltac2:(Control.enter (fun () => if lm_has_subject () then () else Control.zero (Tactic_failure None))).
Ltac munch_prune := ltac2:(Control.enter (fun () => lm_prune (lm_subjects ()))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac munch_tier tac := munch_has; solve [ munch_prune; tac ].

(* [comment removed for export] *)
Lemma nat_le_4095_Z : forall (A : Type) (l : list A), (length l <= 4095)%nat -> (Z.of_nat (length l) <= 4095)%Z.
Proof. intros A l H. apply Nat2Z.inj_le in H. exact H. Qed.
Ltac hplen_pre :=
  lazymatch goal with
  | Hp : (length _ <= 4095)%nat |- _ => (let H := fresh "HplenZ" in pose proof (nat_le_4095_Z _ _ Hp) as H); clear Hp
  end.

Local Open Scope Z_scope.
Goal forall (sp VEP x y : Z) (P : Z -> Prop), P x -> (VEP + 312 <= x \/ x + 40 <= VEP) -> (y + 1 <= x \/ x + 1 <= y) -> 100 <= VEP -> VEP + 1000 <= sp - 8800 -> x + 40 <= sp - 9000 ->
  forall a__, (x <= a__ < x + 40) -> ~ (sp - 8800 <= a__ < sp) /\ ~ (VEP <= a__ < VEP + 312) /\ True.
Proof.
  intros sp VEP x y P HP D1 D2 B1 B2 B3 a__ Hb. Fail munch_tier ltac:(lia). rename Hb into Ha__.
  assert_succeeds (munch_prune; lazymatch goal with _ : (y + 1 <= x \/ _) |- _ => fail "D2 kept" | _ : P _ |- _ => fail "HP kept" | _ => idtac end;
                   lazymatch goal with _ : (VEP + 312 <= x \/ _) |- _ => idtac end).
  munch_tier ltac:(lia).
Qed.
