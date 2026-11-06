(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith Lia.
From Stdlib Require Import PreOmega.
From Ltac2 Require Ltac2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lia_mod := Z.to_euclidean_division_equations; lia.

Ltac nia_mod := Z.to_euclidean_division_equations; nia.

Module LiaFastL2.
  Import Ltac2.

  Ltac2 rec arith_prop (ty : constr) : bool :=
    lazy_match! ty with
    | ?a /\ ?b => Bool.and (arith_prop a) (arith_prop b)
    | ?a \/ ?b => Bool.and (arith_prop a) (arith_prop b)
    | ?a <-> ?b => Bool.and (arith_prop a) (arith_prop b)
    | ~ ?a => arith_prop a
    | ?a -> ?b => Bool.and (arith_prop a) (arith_prop b)
    | True => true
    | False => true
    | @eq Z _ _ => true
    | @eq nat _ _ => true
    | @eq N _ _ => true
    | @eq positive _ _ => true
    | @eq bool _ _ => true
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
    | N.le _ _ => true | N.lt _ _ => true | N.ge _ _ => true | N.gt _ _ => true
    | Z.divide _ _ => true
    | _ => false
    end.

  Ltac2 arith_hyp (h : ident * constr option * constr) : bool :=
    let (_, body, ty) := h in
    match body with
    | Some _ => true
    | None => arith_prop ty
    end.

  Ltac2 prune_arith_ctx1 () :=
    let hs := Control.hyps () in
    let ids := List.map (fun (h : ident * constr option * constr) => let (id, _, _) := h in id)
                 (List.filter arith_hyp hs) in
    Std.keep ids.

  Ltac2 prune_arith_ctx0 () := Control.enter prune_arith_ctx1.

  Ltac2 is_arith (t : constr) : bool :=
    lazy_match! t with
    | _ /\ _ => true | _ <-> _ => true | _ = _ => true | _ <> _ => true | ~ _ => true
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
    | N.le _ _ => true | N.lt _ _ => true | Pos.le _ _ => true | Pos.lt _ _ => true
    | _ \/ _ => true
    | Z => true | nat => true | N => true | positive => true
    | _ => false
    end.

  Ltac2 prune () :=
    List.iter (fun h => match h with (id, _, ty) =>
                 if is_arith ty then () else
                 match Control.case (fun () => Std.clear [id]) with
                 | Val _ => () | Err _ => () end end)
              (List.rev (Control.hyps ())).
End LiaFastL2.

Ltac prune_arith_ctx := ltac2:(LiaFastL2.prune_arith_ctx0 ()).
Ltac alia := prune_arith_ctx; lia.
Ltac ania := prune_arith_ctx; nia.

Ltac flia_prune1 := ltac2:(Ltac2.Control.enter LiaFastL2.prune).
Ltac flia_clear_mod0 := repeat match goal with H : (_ mod _ = 0)%Z |- _ => clear H end.

Ltac flia1 :=
  flia_prune1;
  first [ solve [flia_clear_mod0; Zify.zify; xlia zchecker]
        | lazymatch goal with
          | |- context [Z.modulo _ _] => Zify.zify; xlia zchecker
          | |- context [Z.div _ _] => Zify.zify; xlia zchecker
          end ].

Ltac flia_lin :=
  lazymatch goal with
  | |- context [Z.modulo _ _] => fail
  | |- context [Z.div _ _] => fail
  | _ => flia_prune1;
         repeat match goal with
                | H : context [Z.modulo _ _] |- _ => clear H
                | H : context [Z.div _ _] |- _ => clear H
                end;
         Zify.zify; xlia zchecker
  end.

Ltac flia_full1 := flia_prune1; Zify.zify; xlia zchecker.

Ltac flia2 := first [ solve [flia_lin] | flia_full1 ].

Ltac lia_closed_has_var :=
  match goal with |- ?G => match G with context [?x] => is_var x end end.
Ltac lia_clear_all := repeat match goal with H : _ |- _ => clear H end.

Ltac clia :=
  tryif lia_closed_has_var then (Zify.zify; xlia zchecker)
  else first [ solve [lia_clear_all; Zify.zify; xlia zchecker]
             | Zify.zify; xlia zchecker ].

Ltac cnia :=
  tryif lia_closed_has_var then (Zify.zify; xnia zchecker)
  else first [ solve [lia_clear_all; Zify.zify; xnia zchecker]
             | Zify.zify; xnia zchecker ].

Ltac is_zlit t :=
  lazymatch t with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.pow ?a ?b => is_zlit a; is_zlit b
  | Z.add ?a ?b => is_zlit a; is_zlit b
  | Z.sub ?a ?b => is_zlit a; is_zlit b
  | Z.mul ?a ?b => is_zlit a; is_zlit b
  | Z.opp ?a => is_zlit a
  | Z.of_nat ?n => is_nlit n
  end
with is_nlit t :=
  lazymatch t with
  | O => idtac | S ?n => is_nlit n
  | Nat.add ?a ?b => is_nlit a; is_nlit b
  end.

Ltac zlit :=
  lazymatch goal with
  | |- ?a /\ ?b => split; zlit
  | |- (?a <= ?b)%Z => is_zlit a; is_zlit b; apply (proj1 (Z.leb_le a b)); vm_compute; reflexivity
  | |- (?a < ?b)%Z => is_zlit a; is_zlit b; apply (proj1 (Z.ltb_lt a b)); vm_compute; reflexivity
  | |- (?a <= ?b)%nat => is_nlit a; is_nlit b; apply (proj1 (PeanoNat.Nat.leb_le a b)); vm_compute; reflexivity
  | |- (?a < ?b)%nat => is_nlit a; is_nlit b; apply (proj1 (PeanoNat.Nat.ltb_lt a b)); vm_compute; reflexivity
  | |- @eq Z ?a ?b => first [is_zlit a; is_zlit b; vm_compute; reflexivity | ring]
  end.

Ltac plia := first [ zlit | alia ].

Ltac bvwf_has_var t := match t with context [?x] => is_var x end.
Ltac solve_BvWf_fast :=
  lazymatch goal with
  | |- BvWf ?n ?v =>
      tryif bvwf_has_var v then fail else
      tryif bvwf_has_var n then fail else
      tryif has_evar v then fail else
      tryif has_evar n then fail else
      (vm_compute; exact I)
  end.
#[export] Hint Extern 9 (BvWf _ _) => solve_BvWf_fast : typeclass_instances.

Module LiaFastSelfTest.
  Local Open Scope Z_scope.

  Goal forall (x y : Z) (l : list Z) (b : bool),
    length l = 3%nat -> b = true -> 0 <= x -> x < y -> x < y + 1.
  Proof. intros. alia. Qed.

  Goal forall (x y : Z) (l : list Z), length l = 3%nat -> 0 <= x -> x < y -> x * x < y * y.
  Proof. intros. ania. Qed.

  Goal forall x : Z, 0 <= x -> x mod 4 = 0 -> exists q, x = 4 * q.
  Proof. intros x Hx Hm. exists (x / 4). lia_mod. Qed.

  Goal forall (x : Z) (l : list Z), length l = 2%nat -> 5 <= x -> x mod 8 = 0 -> 8 <= x.
  Proof. intros. flia2. Qed.

  Goal forall (x : Z) (l : list Z), length l = 2%nat -> 5 <= x -> x < 7 -> x <= 6.
  Proof. intros. flia_lin. Qed.

  Goal forall (x : Z), 5 <= x -> x mod 8 = 0 -> x / 8 >= 1.
  Proof. intros. flia1. Qed.

  Goal (2 ^ 17 + 20 <= 2 ^ 64)%Z /\ (5 < 41)%nat.
  Proof. zlit. Qed.

  Goal forall (x : Z) (H : x = 3), (1 <= 8)%Z.
  Proof. intros. clia. Qed.

  Goal forall (x : Z) (H : x = 3), (1 <= x)%Z.
  Proof. intros. clia. Qed.

  Goal forall (x : Z), 0 <= x -> (0 <= 118464 < 2 ^ 64)%Z.
  Proof. intros. plia. Qed.

  Goal BvWf 64%N 3%Z.
  Proof. solve_BvWf_fast. Qed.

  Goal BvWf 8%N 255%Z.
  Proof. typeclasses eauto. Qed.
End LiaFastSelfTest.
