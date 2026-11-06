(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim FPSteps.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMK.

Definition frm_ok (fx : FPState) : Prop := frm_zero (@fp_csr fx).

Lemma frm_ok_fx0 : frm_ok fx0.
Proof. exact fp_frm_zero_fx0. Qed.

Lemma frm_ok_unfold fx : frm_ok fx = frm_zero (@fp_csr fx).
Proof. reflexivity. Qed.

Lemma frm_ok_mkFP_same fr (fx : FPState) : frm_ok fx -> frm_ok (mkFP fr (@fp_csr fx)).
Proof. intros H. exact H. Qed.
Lemma frm_ok_mkFP fr cs : frm_zero cs -> frm_ok (mkFP fr cs).
Proof. intros H. exact H. Qed.

Lemma frm_ok_of_eq (fx fx' : FPState) :
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 -> frm_ok fx -> frm_ok fx'.
Proof. intros E H. unfold frm_ok, frm_zero in *. rewrite E. exact H. Qed.

Definition msteps_keep_ty (segs : list Segment) : Prop :=
  forall (fx fx' : FPState) R R' pc pc' M M',
    msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').

Ltac frm_solve_with L :=
  lazymatch goal with
  | |- frm_ok ?fx => change (frm_zero (@fp_csr fx)); frm_solve_with L
  | |- frm_zero (@fp_csr ?fx) =>
      first [ assumption
            | exact fp_frm_zero_fx0
            | lazymatch fx with
              | mkFP _ (@fp_csr ?f1) => change (frm_zero (@fp_csr f1)); frm_solve_with L
              | mkFP _ ?cs => cbn [fp_csr]; frm_solve_with L
              end
            | match goal with
              | MS : msteps _ (@mkst ?f0 _ _ _ _) (@mkst fx _ _ _ _) |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (L _ _ _ _ _ _ _ _ MS); frm_solve_with L
              | E : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr ?f0)) 5) 7 |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (frm_ok_of_eq f0 fx E); change (frm_zero (@fp_csr f0)); frm_solve_with L
              | E : _ /\ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = Z.land (Z.shiftr (bv_unsigned (@fp_csr ?f0)) 5) 7 |- _ =>
                  lazymatch f0 with fx => fail | _ => idtac end;
                  apply (frm_ok_of_eq f0 fx (proj2 E)); change (frm_zero (@fp_csr f0)); frm_solve_with L
              | H : frm_ok fx |- _ => exact H
              end
            | fail 1 "frm_solve: no frm fact for" fx ]
  | |- frm_zero ?cs => first [ assumption | fail 1 "frm_solve: no frm fact for csr" cs ]
  | |- _ => fail "frm_solve: goal is not an frm obligation"
  end.

End FRMK.
