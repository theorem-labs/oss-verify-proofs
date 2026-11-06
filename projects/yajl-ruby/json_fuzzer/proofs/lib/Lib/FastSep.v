(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fold_left_add_le : forall (b : Z) (l r : list Z),
  (fold_left Z.add l 0 <=? fold_left Z.add r 0) = true -> fold_left Z.add l b <= fold_left Z.add r b.
Proof.
  intros b l r H. apply Z.leb_le in H.
  assert (E : forall l0 a, fold_left Z.add l0 a = a + fold_left Z.add l0 0).
  { induction l0 as [|x l0 IH]; intros a; cbn [fold_left]; [lia|]. rewrite IH, (IH (0 + x)). lia. }
  rewrite (E l b), (E r b). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fs_natok n :=
  lazymatch n with
  | O => constr:(true) | S ?k => fs_natok k
  | @length _ _ => constr:(true)
  | context [Z.to_nat] => constr:(false) | context [N.to_nat] => constr:(false) | context [Pos.to_nat] => constr:(false)
  | _ => constr:(true)
  end.
Ltac fs_parse e acc :=
  lazymatch e with
  | (?x + ?t)%Z =>
      lazymatch t with
      | Z0 => fs_parse x constr:(t :: acc)
      | Zpos _ => fs_parse x constr:(t :: acc)
      | Zneg _ => fs_parse x constr:(t :: acc)
      | Z.of_nat ?k => lazymatch fs_natok k with true => fs_parse x constr:(t :: acc) | false => constr:((e, acc)) end
      | _ => constr:((e, acc))
      end
  | (?x - ?t)%Z =>
      lazymatch t with
      | Z0 => fs_parse x constr:((- t)%Z :: acc)
      | Zpos _ => fs_parse x constr:((- t)%Z :: acc)
      | Z.of_nat ?k => lazymatch fs_natok k with true => fs_parse x constr:((- t)%Z :: acc) | false => constr:((e, acc)) end
      | _ => constr:((e, acc))
      end
  | _ => constr:((e, acc))
  end.

Ltac fs_le :=
  lazymatch goal with
  | |- (?L <= ?R)%Z =>
      let pl := fs_parse L constr:(@nil Z) in
      let pr := fs_parse R constr:(@nil Z) in
      lazymatch pl with
      | (?b, ?l) => lazymatch pr with
                    | (?b', ?r) => constr_eq b b'; exact (fold_left_add_le b l r eq_refl)
                    end
      end
  end.

(* [comment removed for export] *)
Ltac fast_sep :=
  lazymatch goal with
  | |- (_ <= _)%Z \/ (_ <= _)%Z => first [ left; fs_le | right; fs_le ]
  end.

(* [comment removed for export] *)
Goal forall CA sp : Z, (CA + 2480 + Z.of_nat 16 <= CA + 80 + Z.of_nat 4 \/ CA + 80 + Z.of_nat 4 + 4 <= CA + 2480)
                    /\ (sp - 64 + Z.of_nat 8 <= sp - 32 \/ sp - 32 + 8 <= sp - 64)
                    /\ (CA + 8 <= CA \/ CA + 4 <= CA + 8).
Proof. intros. split; [fast_sep| split; fast_sep]. Qed.
Goal forall CA X : Z, X + 4 <= CA -> (CA + 16 <= X \/ X + 4 <= CA).
Proof. intros. Fail fast_sep. right; assumption. Qed.
