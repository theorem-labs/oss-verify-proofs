(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec.
Import ListNotations.
Local Open Scope bv_scope.

Section GresFast.
Context {fx : FPState}.

Fixpoint regs_upds (base : bvmap 5 word) (l : list (reg * word)) : bvmap 5 word :=
  match l with [] => base | (r, v) :: t => regupd (regs_upds base t) r v end.

Fixpoint rlook (l : list (reg * word)) (r : reg) : option word :=
  match l with [] => None | (r', v) :: t => if bv_eqb r' r then Some v else rlook t r end.

Lemma bv_eqb_true_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. destruct (bv_eq_dec n a b) as [E|E]; [exact E|]. rewrite (bv_eqb_neq a b E) in H. discriminate. Qed.

Lemma getr_upds_found : forall base l r v, bv_eqb r 0 = false -> rlook l r = Some v -> getr (regs_upds base l) r = v.
Proof.
  intros base l r v H0. induction l as [|[r' v'] t IH]; cbn [rlook regs_upds]; [discriminate|].
  destruct (bv_eqb r' r) eqn:E; intros Hl.
  - injection Hl as <-. apply bv_eqb_true_eq in E. subst r'. apply getr_same. intros ->. discriminate H0.
  - rewrite getr_other; [exact (IH Hl)|]. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma getr_upds_base : forall base l r, rlook l r = None -> getr (regs_upds base l) r = getr base r.
Proof.
  intros base l r. induction l as [|[r' v'] t IH]; cbn [rlook regs_upds]; [reflexivity|].
  destruct (bv_eqb r' r) eqn:E; intros Hl; [discriminate|].
  rewrite getr_other; [exact (IH Hl)|]. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

(* [comment removed for export] *)
Lemma getr_upds_test : forall (t : reg -> bool) base l r,
  forallb (fun p => t (fst p)) l = true -> t r = false -> getr (regs_upds base l) r = getr base r.
Proof.
  intros t base l r. induction l as [|[r' v'] tl IH]; cbn [forallb regs_upds fst]; [reflexivity|].
  intros Hl Hr. apply andb_prop in Hl as [H1 H2].
  rewrite getr_other; [exact (IH H2 Hr)|]. intros ->. rewrite H1 in Hr. discriminate.
Qed.
End GresFast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac gf_reify R :=
  lazymatch R with
  | regupd ?R' ?r ?v => let t := gf_reify R' in lazymatch t with (?base, ?l) => constr:((base, (r, v) :: l)) end
  | _ => constr:((R, @nil (reg * word)))
  end.

(* [comment removed for export] *)
Ltac gf_find l r :=
  lazymatch l with
  | nil => constr:(@None word)
  | (?r', ?v) :: ?t => lazymatch constr:((r', r)) with (?x, ?x) => constr:(Some v) | _ => gf_find t r end
  end.

(* [comment removed for export] *)
Ltac gres_chain :=
  match goal with
  | |- context [getr (regupd ?R0 ?r0 ?v0) _] =>
      let R := constr:(regupd R0 r0 v0) in
      tryif has_evar R then fail else
      let bl := gf_reify R in
      lazymatch bl with
      | (?base, ?l) =>
          let RR := fresh "GRES_R" in let LL := fresh "GRES_L" in
          set (RR := R); pose (LL := l);
          repeat match goal with
                 | |- context [getr RR ?r] =>
                     let f := gf_find l r in
                     lazymatch f with
                     | Some ?v => rewrite (getr_upds_found base LL r v eq_refl eq_refl : getr RR r = v)
                     | None => rewrite (getr_upds_base base LL r eq_refl : getr RR r = getr base r)
                     end
                 end;
          clear LL; subst RR
      end
  end.

(* [comment removed for export] *)
Ltac gres_chain_in T :=
  match type of T with
  | context [getr (regupd ?R0 ?r0 ?v0) _] =>
      let R := constr:(regupd R0 r0 v0) in
      tryif has_evar R then fail else
      let bl := gf_reify R in
      lazymatch bl with
      | (?base, ?l) =>
          let RR := fresh "GRES_R" in let LL := fresh "GRES_L" in
          set (RR := R) in T; pose (LL := l);
          repeat match type of T with
                 | context [getr RR ?r] =>
                     let f := gf_find l r in
                     lazymatch f with
                     | Some ?v => rewrite (getr_upds_found base LL r v eq_refl eq_refl : getr RR r = v) in T
                     | None => rewrite (getr_upds_base base LL r eq_refl : getr RR r = getr base r) in T
                     end
                 end;
          clear LL; subst RR
      end
  end.

(* [comment removed for export] *)
Ltac gf_reg_neq := let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.

(* [comment removed for export] *)
Ltac gres_loop_old := repeat first [ rewrite getr_same by gf_reg_neq | rewrite getr_other by gf_reg_neq ].
Ltac gres_loop_new := repeat first [ progress gres_chain | rewrite getr_same by gf_reg_neq | rewrite getr_other by gf_reg_neq ].
Ltac gres_loop_old_in T := repeat first [ rewrite getr_same in T by gf_reg_neq | rewrite getr_other in T by gf_reg_neq ].
Ltac gres_loop_new_in T :=
  repeat first [ progress (gres_chain_in T) | rewrite getr_same in T by gf_reg_neq | rewrite getr_other in T by gf_reg_neq ].

(* [comment removed for export] *)
Ltac gres_dual_flag := constr:(false).
Ltac gres_loop :=
  lazymatch gres_dual_flag with
  | true =>
      lazymatch goal with
      | |- ?G0 =>
          assert_succeeds (
            gres_loop_new;
            lazymatch goal with
            | |- ?Gn => assert_succeeds (cut G0; [ | gres_loop_old;
                           lazymatch goal with |- ?Go => first [ constr_eq Go Gn | fail 100 "GRES DUAL MODE: goals differ" ] end ])
            end)
      end;
      gres_loop_new
  | _ => gres_loop_new
  end.
Ltac gres_loop_in T := gres_loop_new_in T.
