(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma reg_neq_of_eqb : forall a b : reg, bv_eqb a b = false -> a <> b.
Proof. intros a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.

Ltac getr_proof X r :=
  lazymatch X with
  | regupd ?Y ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in
             uconstr:(getr_same Y r v (reg_neq_of_eqb r (0%bv) (@eq_refl bool false)))
      | _ => let p := getr_proof Y r in
             uconstr:(eq_trans (getr_other Y rd v r (reg_neq_of_eqb r rd (@eq_refl bool false))) p)
      end
  | _ => uconstr:(@eq_refl word (getr X r))
  end.

(* [comment removed for export] *)
Fixpoint chain_apply (base : bvmap 5 word) (l : list (reg * word)) : bvmap 5 word :=
  match l with
  | nil => base
  | (r, v) :: l' => regupd (chain_apply base l') r v
  end.
Fixpoint chain_lookup (l : list (reg * word)) (r : reg) : option word :=
  match l with
  | nil => None
  | (r', v) :: l' => if bv_eqb r r' then Some v else chain_lookup l' r
  end.

Lemma chain_bv_eqb_true : forall (a b : reg), bv_eqb a b = true -> a = b.
Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma getr_chain_hit : forall base l r v,
  bv_eqb r 0 = false -> chain_lookup l r = Some v -> getr (chain_apply base l) r = v.
Proof.
  intros base l r v Hr. induction l as [|[r' v'] l IH]; cbn [chain_lookup chain_apply]; intros H; [discriminate H|].
  destruct (bv_eqb r r') eqn:E.
  - apply chain_bv_eqb_true in E. subst r'. injection H as ->. apply getr_same.
    intros ->. rewrite bv_eqb_refl in Hr. discriminate Hr.
  - rewrite getr_other; [exact (IH H)|]. intros ->. rewrite bv_eqb_refl in E. discriminate E.
Qed.

Lemma getr_chain_miss : forall base l r,
  chain_lookup l r = None -> getr (chain_apply base l) r = getr base r.
Proof.
  intros base l r. induction l as [|[r' v'] l IH]; cbn [chain_lookup chain_apply]; intros H; [reflexivity|].
  destruct (bv_eqb r r') eqn:E; [discriminate H|].
  rewrite getr_other; [exact (IH H)|]. intros ->. rewrite bv_eqb_refl in E. discriminate E.
Qed.

Ltac chain_base X := lazymatch X with regupd ?Y _ _ => chain_base Y | _ => X end.
Ltac chain_list X :=
  lazymatch X with
  | regupd ?Y ?rd ?v => let l := chain_list Y in uconstr:(@cons (reg * word) (@pair reg word rd v) l)
  | _ => uconstr:(@nil (reg * word))
  end.
(* [comment removed for export] *)
Ltac chain_find X r :=
  lazymatch X with
  | regupd ?Y ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in v
      | _ => chain_find Y r
      end
  end.
Ltac chain_deep X := lazymatch X with regupd (regupd (regupd (regupd _ _ _) _ _) _ _) _ _ => idtac end.
Ltac getr_proof_fast X r :=
  let b := chain_base X in
  let l := chain_list X in
  match tt with
  | _ => let v := chain_find X r in
         constr:(getr_chain_hit b l r v (@eq_refl bool false) (@eq_refl (option word) (Some v)) : getr X r = v)
  | _ => constr:(getr_chain_miss b l r (@eq_refl (option word) None) : getr X r = getr b r)
  end.

Ltac gres :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             first [ chain_deep X; let p := getr_proof_fast X r in rewrite p
                   | let p := getr_proof X r in
                     let p' := constr:(p) in rewrite p' ]
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.

(* [comment removed for export] *)
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Ltac is_pos_lit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_pos_lit q
  | xI ?q => is_pos_lit q
  end.
Ltac is_Z_lit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => is_pos_lit p
  | Zneg ?p => is_pos_lit p
  end.

(* [comment removed for export] *)
Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

(* [comment removed for export] *)
Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

(* [comment removed for export] *)
Ltac vnorm :=
  gres; imm_norm;
  match goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | _ => idtac end;
  match goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  match goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.

(* [comment removed for export] *)
Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

(* [comment removed for export] *)
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

(* [comment removed for export] *)
Ltac stepb_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

Ltac stepb_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

(* [comment removed for export] *)
Ltac stepsd F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepld F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
