(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rch : Type :=
| RNil : rch
| RCons : reg -> word -> rch -> rch.

Definition reg_eqb (a b : reg) : bool := Z.eqb (bv_unsigned a) (bv_unsigned b).

Lemma reg_eqb_true : forall a b, reg_eqb a b = true -> a = b.
Proof. intros a b H. apply bv_eq. apply Z.eqb_eq. exact H. Qed.

Lemma reg_eqb_false : forall a b, reg_eqb a b = false -> a <> b.
Proof. intros a b H E. subst b. unfold reg_eqb in H. rewrite Z.eqb_refl in H. discriminate H. Qed.

Section WithFP.
Context {fx : FPState}.

Fixpoint rch_den (base : bvmap 5 word) (l : rch) : bvmap 5 word :=
  match l with
  | RNil => base
  | RCons r v tl => regupd (rch_den base tl) r v
  end.

(* [comment removed for export] *)
Fixpoint rch_hit (l : rch) (r : reg) (v : word) : Prop :=
  match l with
  | RNil => False
  | RCons r' v' tl => if reg_eqb r' r then v' = v else rch_hit tl r v
  end.

(* [comment removed for export] *)
Fixpoint rch_miss (l : rch) (r : reg) : bool :=
  match l with
  | RNil => true
  | RCons r' _ tl => if reg_eqb r' r then false else rch_miss tl r
  end.

Lemma getr_rch_hit : forall base l (r : reg) v,
  reg_eqb r 0 = false -> rch_hit l r v -> getr (rch_den base l) r = v.
Proof.
  intros base l r v H0. induction l as [|r' v' tl IH]; cbn [rch_hit rch_den]; intro H.
  - destruct H.
  - destruct (reg_eqb r' r) eqn:E.
    + apply reg_eqb_true in E. subst r'. rewrite getr_same by (apply reg_eqb_false; exact H0). exact H.
    + rewrite getr_other by (intro X; subst r'; unfold reg_eqb in E; rewrite Z.eqb_refl in E; discriminate E).
      apply IH. exact H.
Qed.

Lemma getr_rch_miss : forall base l (r : reg),
  rch_miss l r = true -> getr (rch_den base l) r = getr base r.
Proof.
  intros base l r. induction l as [|r' v' tl IH]; cbn [rch_miss rch_den]; intro H.
  - reflexivity.
  - destruct (reg_eqb r' r) eqn:E; [discriminate H|].
    rewrite getr_other by (intro X; subst r'; unfold reg_eqb in E; rewrite Z.eqb_refl in E; discriminate E).
    apply IH. exact H.
Qed.

End WithFP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac reg_lit_z r :=
  lazymatch r with
  | @BV _ ?z _ => let _ := match goal with _ => is_Z_lit z end in z
  end.

(* [comment removed for export] *)
Ltac rch_walk ch zr :=
  lazymatch ch with
  | regupd ?c ?r' ?v' =>
      let z' := reg_lit_z r' in
      lazymatch z' with
      | zr => constr:((RCons r' v' RNil, Some v'))
      | _ =>
          let res := rch_walk c zr in
          lazymatch res with
          | (?l, ?o) => constr:((RCons r' v' l, o))
          end
      end
  | _ => constr:((RNil, @None word))
  end.

(* [comment removed for export] *)
Ltac rch_base ch l :=
  lazymatch l with
  | RNil => ch
  | RCons _ _ ?tl => lazymatch ch with regupd ?c _ _ => rch_base c tl end
  end.

(* [comment removed for export] *)
Ltac wf_chain_of ch :=
  match goal with
  | _ => let _ := match goal with _ => is_var ch end in
         let b := eval unfold ch in ch in b
  | _ => ch
  end.

(* [comment removed for export] *)
Ltac gres_fast1 :=
  match goal with
  | |- context [getr ?ch0 ?r] =>
      let ch := wf_chain_of ch0 in
      lazymatch ch with regupd _ _ _ => idtac end;
      let zr := reg_lit_z r in
      lazymatch zr with
      | Z0 => rewrite (getr_zero ch0)
      | _ =>
        let res := rch_walk ch zr in
        lazymatch res with
        | (?l, Some ?v) =>
            let base := rch_base ch l in
            let E := constr:(getr_rch_hit base l r v (@eq_refl bool false) (@eq_refl word v) : getr ch0 r = v) in
            rewrite E
        | (?l, None) =>
            lazymatch l with RNil => fail | _ => idtac end;
            let base := rch_base ch l in
            let E := constr:(getr_rch_miss base l r (@eq_refl bool true) : getr ch0 r = getr base r) in
            rewrite E
        end
      end
  end.

(* [comment removed for export] *)
Ltac gres_slow :=
  lazymatch goal with
  | |- context [getr (regupd _ _ _) _] =>
      repeat first [ rewrite getr_same by reg_neq_tac
                   | rewrite getr_other by reg_neq_tac ]
  | _ => idtac
  end;
  tryif (match goal with
         | |- context [getr _ ?r] =>
             lazymatch r with
             | @BV _ (Zpos _) _ => fail
             | _ => idtac
             end
         end)
  then rewrite ?getr_zero else idtac.

Ltac gres_fast := repeat gres_fast1; gres_slow.

(* [comment removed for export] *)
Ltac rw0_fast :=
  tryif (match goal with
         | |- context [v_addi _ ?k] =>
             lazymatch k with Zpos _ => fail | Zneg _ => fail | _ => idtac end
         end)
  then rewrite ?v_addi_0 else idtac;
  tryif (match goal with
         | |- context [v_add ?a ?b] =>
             lazymatch b with
             | Z_to_bv _ (Zpos _) => lazymatch a with Z_to_bv _ (Zpos _) => fail | Z_to_bv _ (Zneg _) => fail | _ => idtac end
             | Z_to_bv _ (Zneg _) => lazymatch a with Z_to_bv _ (Zpos _) => fail | Z_to_bv _ (Zneg _) => fail | _ => idtac end
             | _ => idtac
             end
         end)
  then rewrite ?v_add_0_r, ?v_add_0_l else idtac.

Ltac vnorm_fast := gres_fast; imm_norm; rw0_fast; vals_lit.

(* [comment removed for export] *)
Ltac skipn0_fast :=
  tryif (match goal with
         | |- context [skipn ?n _] => lazymatch n with S _ => fail | _ => idtac end
         end)
  then rewrite ?skipn_O else idtac.

Ltac step_simpl_fast := reduce_bv_eqb_ifs; skipn0_fast; norm_pc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition reg_inb (r : reg) (l : list reg) : bool := existsb (fun x => reg_eqb x r) l.

Lemma reg_inb_false_notin : forall (r : reg) (l : list reg), reg_inb r l = false -> ~ In r l.
Proof.
  intros r l H Hin.
  assert (X : reg_inb r l = true).
  { unfold reg_inb. apply existsb_exists. exists r. split; [exact Hin|]. unfold reg_eqb. apply Z.eqb_refl. }
  rewrite H in X. discriminate X.
Qed.

Ltac not_in_regs :=
  lazymatch goal with
  | |- ~ In ?r ?l => apply (reg_inb_false_notin r l); reflexivity
  end.


(* [comment removed for export] *)
Lemma reg_inb_true_in : forall (r : reg) (l : list reg), reg_inb r l = true -> In r l.
Proof.
  intros r l H. unfold reg_inb in H. apply existsb_exists in H. destruct H as (x & Hin & E).
  apply reg_eqb_true in E. subst x. exact Hin.
Qed.

Ltac in_regs :=
  lazymatch goal with
  | |- In ?r ?l => apply (reg_inb_true_in r l); reflexivity
  end.
