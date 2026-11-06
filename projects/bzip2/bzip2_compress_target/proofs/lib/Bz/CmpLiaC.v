(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSa CmpFast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams CmpLiaP.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac pc_is_plit p := lazymatch p with xH => idtac | xO ?q => pc_is_plit q | xI ?q => pc_is_plit q end.
(* [comment removed for export] *)
Ltac pc_is_zclosed z :=
  lazymatch z with
  | Z0 => idtac | Zpos ?p => pc_is_plit p | Zneg ?p => pc_is_plit p
  | Z.add ?a ?b => pc_is_zclosed a; pc_is_zclosed b
  | Z.sub ?a ?b => pc_is_zclosed a; pc_is_zclosed b
  | Z.mul ?a ?b => pc_is_zclosed a; pc_is_zclosed b
  | Z.opp ?a => pc_is_zclosed a
  end.
Ltac pc_is_nlit n := lazymatch n with O => idtac | S ?k => pc_is_nlit k end.
Ltac pc_closed_prop P :=
  lazymatch P with
  | ?A /\ ?B => pc_closed_prop A; pc_closed_prop B
  | Z.le ?a ?b => pc_is_zclosed a; pc_is_zclosed b
  | Z.lt ?a ?b => pc_is_zclosed a; pc_is_zclosed b
  | Z.ge ?a ?b => pc_is_zclosed a; pc_is_zclosed b
  | Z.gt ?a ?b => pc_is_zclosed a; pc_is_zclosed b
  | @eq Z ?a ?b => pc_is_zclosed a; pc_is_zclosed b
  | Peano.lt ?a ?b => pc_is_nlit a; pc_is_nlit b
  | Peano.le ?a ?b => pc_is_nlit a; pc_is_nlit b
  end.
Ltac pc_closed_leaf :=
  lazymatch goal with
  | |- _ /\ _ => split; pc_closed_leaf
  | |- Z.le ?a ?b => exact (proj1 (Z.leb_le a b) (@eq_refl bool true))
  | |- Z.lt ?a ?b => exact (proj1 (Z.ltb_lt a b) (@eq_refl bool true))
  | |- Z.ge ?a ?b => apply Z.le_ge; exact (proj1 (Z.leb_le b a) (@eq_refl bool true))
  | |- Z.gt ?a ?b => apply Z.lt_gt; exact (proj1 (Z.ltb_lt b a) (@eq_refl bool true))
  | |- @eq Z ?a ?b => exact (proj1 (Z.eqb_eq a b) (@eq_refl bool true))
  | |- Peano.lt ?a ?b => exact (proj1 (Nat.ltb_lt a b) (@eq_refl bool true))
  | |- Peano.le ?a ?b => exact (proj1 (Nat.leb_le a b) (@eq_refl bool true))
  end.
Ltac closed_arith := lazymatch goal with |- ?G => pc_closed_prop G end; solve [ pc_closed_leaf ].

(* [comment removed for export] *)
Ltac pc_has_euclid :=
  match goal with
  | |- context [Z.div _ _] => idtac | |- context [Z.modulo _ _] => idtac | |- context [Z.quot _ _] => idtac
  | |- context [Z.rem _ _] => idtac | |- context [Z.divide _ _] => idtac
  | |- context [Nat.div _ _] => idtac | |- context [Nat.modulo _ _] => idtac | |- context [N.div _ _] => idtac | |- context [N.modulo _ _] => idtac
  | _ : context [Nat.div _ _] |- _ => idtac | _ : context [Nat.modulo _ _] |- _ => idtac | _ : context [N.div _ _] |- _ => idtac | _ : context [N.modulo _ _] |- _ => idtac
  | _ : context [Z.div _ _] |- _ => idtac | _ : context [Z.modulo _ _] |- _ => idtac | _ : context [Z.quot _ _] |- _ => idtac
  | _ : context [Z.rem _ _] |- _ => idtac | _ : context [Z.divide _ _] |- _ => idtac
  end.
Ltac pc_has_inst_evar :=
  match goal with
  | |- context [@alloc_ceiling ?i] => is_evar i | |- context [@run_guard ?i] => is_evar i | |- context [@run_secret ?i] => is_evar i
  | |- context [@p_bs ?i] => is_evar i | |- context [@p_wf ?i] => is_evar i | |- context [@budget_q ?i] => is_evar i
  | _ : context [@p_bs ?i] |- _ => is_evar i | _ : context [@p_wf ?i] |- _ => is_evar i | _ : context [@budget_q ?i] |- _ => is_evar i
  end.
(* [comment removed for export] *)
Ltac pc_t5_useful :=
  first [ lazymatch goal with
          | _ : (0x7fff7f800000 <= alloc_ceiling)%Z |- _ => fail
          | _ : context [alloc_ceiling] |- _ => idtac
          | |- context [alloc_ceiling] => idtac
          end
        | lazymatch goal with
          | _ : (0 <= run_secret < _)%Z |- _ => fail
          | _ : context [run_secret] |- _ => idtac
          | |- context [run_secret] => idtac
          end
        | lazymatch goal with
          | _ : (0 <= run_guard < _)%Z |- _ => fail
          | _ : context [run_guard] |- _ => idtac
          | |- context [run_guard] => idtac
          end
        | lazymatch goal with
          | _ : (1 <= p_bs)%Z |- _ => fail
          | |- context [p_bs] => idtac
          | _ : context [p_bs] |- _ => idtac
          | |- context [p_wf] => idtac
          | _ : context [p_wf] |- _ => idtac
          | |- context [@budget_q _] => idtac
          | _ : context [@budget_q _] |- _ => idtac
          end ].

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module PCG.
  Import Ltac2.
  Ltac2 rec has_arith (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        if Constr.equal f '@Z.le then true else if Constr.equal f '@Z.lt then true else if Constr.equal f '@Z.ge then true
        else if Constr.equal f '@Z.gt then true else if Constr.equal f '@eq then true else if Constr.equal f '@le then true
        else if Constr.equal f '@lt then true else if Constr.equal f '@ge then true else if Constr.equal f '@gt then true
        else if Constr.equal f '@N.le then true else if Constr.equal f '@N.lt then true else if Constr.equal f '@Z.divide then true
        else Array.exist has_arith args
    | Constr.Unsafe.Prod b body => if has_arith (Constr.Binder.type b) then true else has_arith body
    | _ => false
    end.
  Ltac2 logic_head (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f _ =>
        if Constr.equal f '@and then true else if Constr.equal f '@or then true else if Constr.equal f '@not then true
        else if Constr.equal f '@iff then true else false
    | Constr.Unsafe.Prod _ body => Constr.Unsafe.closedn 0 body   (* [comment removed for export] *)
    | _ => false
    end.
  Ltac2 plain_head (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f _ =>
        if Constr.equal f '@Z.le then true else if Constr.equal f '@Z.lt then true else if Constr.equal f '@Z.ge then true
        else if Constr.equal f '@Z.gt then true else if Constr.equal f '@eq then true else if Constr.equal f '@le then true
        else if Constr.equal f '@lt then true else false
    | _ => false
    end.
  Ltac2 rec plain_conj (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        if Constr.equal f '@and then (if plain_conj (Array.get args 0) then plain_conj (Array.get args 1) else false) else plain_head t
    | _ => false
    end.
  Ltac2 has_logic_hyp () : unit :=
    if List.exist (fun (_, body, ty) =>
         match body with
         | Some _ => false
         | None => if logic_head ty then (if plain_conj ty then false else has_arith ty) else false
         end) (Control.hyps ())
    then () else Control.zero (Tactic_failure None).
End PCG.
Ltac pc_has_logic_hyp := ltac2:(Control.enter PCG.has_logic_hyp).

(* [comment removed for export] *)
Ltac pc_goal_env :=
  lazymatch goal with
  | |- context [alloc_ceiling] => idtac | |- context [run_secret] => idtac | |- context [run_guard] => idtac
  | |- context [p_bs] => idtac | |- context [p_wf] => idtac | |- context [@budget_q _] => idtac
  end.

(* [comment removed for export] *)
Ltac lia_c :=
  first [ closed_arith
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | pc_goal_env; pc_t5_useful; bz_ceil; bz_params_occ; zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | pc_has_euclid; zify_prune; Zify.zify; xlia zchecker
        | pc_has_logic_hyp; Zify.zify; xlia zchecker
        | pc_has_inst_evar; aceil_evars; bzp_evars; Zify.zify; xlia zchecker
        | first [ pc_has_inst_evar | pc_t5_useful ]; bz_ceil; bz_params_occ; Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac lia_rest :=
  first [ pc_goal_env; pc_t5_useful; bz_ceil; bz_params_occ; zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | pc_has_euclid; zify_prune; Zify.zify; xlia zchecker
        | pc_has_logic_hyp; Zify.zify; xlia zchecker
        | pc_has_inst_evar; aceil_evars; bzp_evars; Zify.zify; xlia zchecker
        | first [ pc_has_inst_evar | pc_t5_useful ]; bz_ceil; bz_params_occ; Zify.zify; xlia zchecker ].
Ltac lia_sa :=
  first [ closed_arith
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | first [ tryif CmpSa.sa_prepare then lia_rest else fail 1 | fail 2 ]
        | lia_rest ].
Ltac CmpFast.mlia_lia ::= lia_sa.

Goal (0 <= 13 < 50)%Z /\ (3 < 5)%nat /\ (7 >= 2)%Z /\ (7 > 2)%Z /\ (4 <= 4)%nat /\ (5 = 2 + 3)%Z /\ (4 * 13 + 2 < 4128)%Z. Proof. closed_arith. Qed.
Goal (0 <= 13 < 5)%Z -> False. Proof. intros H. Fail closed_arith. lia_c. Qed.
Goal forall x, (0 <= x -> 0 <= x + 1)%Z. Proof. intros. Fail closed_arith. lia_c. Qed.
Goal forall (f : Z -> Z) x k, (0 <= k < 0 -> f x = f (x - 1))%Z. Proof. intros. lia_sa. Qed.                 (* [comment removed for export] *)
Goal forall x : Z, (0 <= x < 2^32 -> True)%Z. Proof. intros x H. first [ assert (0 <= x < 2^31)%Z by CmpFast.mlia_fast | exact I ]. Qed.   (* [comment removed for export] *)
Goal forall x : Z, (0 <= x < 2^32 -> 0 <= x mod 16 < 2^31)%Z. Proof. intros x H. CmpFast.mlia_fast. Qed.
