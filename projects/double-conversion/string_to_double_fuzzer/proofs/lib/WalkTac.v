(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Lemma reg_neq_of_eqb : forall a b : reg, bv_eqb a b = false -> a <> b.
Proof. intros a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.

(* [comment removed for export] *)
Inductive rlist : Type := rnil | rcons (r : reg) (v : word) (l : rlist).
Fixpoint rupds (l : rlist) (B : bvmap 5 word) : bvmap 5 word :=
  match l with
  | rnil => B
  | rcons r v l' => regupd (rupds l' B) r v
  end.
Fixpoint rlook (r : reg) (l : rlist) : option word :=
  match l with
  | rnil => None
  | rcons r' v l' => if bv_eqb r r' then Some v else rlook r l'
  end.
Lemma getr_rupds_some : forall l B r v,
  bv_eqb r 0 = false -> rlook r l = Some v -> getr (rupds l B) r = v.
Proof.
  induction l as [|r' v' l IH]; intros B r v H0 H; cbn [rupds rlook] in *; [discriminate H|].
  destruct (bv_eqb r r') eqn:E.
  - injection H as <-.
    assert (Er : r = r').
    { destruct (bv_eq_dec 5 r r') as [Er|Nr]; [exact Er|].
      rewrite (bv_eqb_neq r r' Nr) in E. discriminate E. }
    subst r'. apply getr_same. apply reg_neq_of_eqb. exact H0.
  - rewrite getr_other by (apply reg_neq_of_eqb; exact E). apply IH; assumption.
Qed.
Lemma getr_rupds_none : forall l B r,
  rlook r l = None -> getr (rupds l B) r = getr B r.
Proof.
  induction l as [|r' v' l IH]; intros B r H; cbn [rupds rlook] in *; [reflexivity|].
  destruct (bv_eqb r r') eqn:E; [discriminate H|].
  rewrite getr_other by (apply reg_neq_of_eqb; exact E). apply IH; assumption.
Qed.

Ltac getr_list X :=
  lazymatch X with
  | regupd ?Y ?rd ?v => let l := getr_list Y in uconstr:(rcons rd v l)
  | _ => uconstr:(rnil)
  end.
Ltac getr_base X :=
  lazymatch X with
  | regupd ?Y _ _ => getr_base Y
  | _ => X
  end.
Ltac getr_find X r :=
  lazymatch X with
  | regupd ?Y ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in constr:(@Some word v)
      | _ => getr_find Y r
      end
  | _ => constr:(@None word)
  end.
Ltac getr_proof X r :=
  let l := getr_list X in
  let B := getr_base X in
  let f := getr_find X r in
  lazymatch f with
  | Some ?v => uconstr:(getr_rupds_some l B r v (@eq_refl bool false) (@eq_refl (option word) (@Some word v)) : getr X r = v)
  | None => uconstr:(getr_rupds_none l B r (@eq_refl (option word) (@None word)) : getr X r = getr B r)
  end.

(* [comment removed for export] *)
Ltac hid_def X := let b := eval unfold X in X in b.
Ltac rl_find L r :=
  lazymatch L with
  | rcons ?rd ?v ?l' =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in constr:(@Some word v)
      | _ => rl_find l' r
      end
  | rnil => constr:(@None word)
  | _ => let Lb := hid_def L in rl_find Lb r      (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Ltac getr_proof_hid RH r :=
  let b := hid_def RH in
  lazymatch b with
  | rupds ?L ?B =>
      let f := rl_find L r in
      lazymatch f with
      | Some ?v => uconstr:(getr_rupds_some L B r v (@eq_refl bool false) (@eq_refl (option word) (@Some word v)) : getr RH r = v)
      | None => uconstr:(getr_rupds_none L B r (@eq_refl (option word) (@None word)) : getr RH r = getr B r)
      end
  end.

Ltac gres :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let p := getr_proof X r in
             let p' := constr:(p) in rewrite p'
         | RH := rupds _ _ |- context [getr ?X ?r] =>
             constr_eq X RH;
             let p := getr_proof_hid RH r in
             let p' := constr:(p) in rewrite p'
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.

Ltac subst_var_in t x y :=
  match tt with
  | _ => let chk := match tt with _ => constr_eq x y end in t
  | _ => lazymatch t with
         | context C [x] => let t' := context C [y] in subst_var_in t' x y
         | _ => t
         end
  end.
(* [comment removed for export] *)
Ltac find_def b nm k :=
  tryif is_var b then k b else
  match goal with
  | H := ?b' |- _ => let chk := match tt with _ => constr_eq b' b end in k H
  | _ => let H := fresh nm in pose (H := b); k H
  end.
(* [comment removed for export] *)
Ltac hide_regs R k :=
  let full _ :=
    let l := getr_list R in let B := getr_base R in
    let LH := fresh "LH" in let RH := fresh "RH" in
    pose (LH := l); pose (RH := rupds LH B); k RH in
  match R with
  | regupd ?Y ?rd ?v =>
      match goal with
      | RHp := rupds ?Lp ?Bp |- _ =>
          let chk := match tt with _ => unify Y RHp end in
          let LH := fresh "LH" in let RH := fresh "RH" in
          pose (LH := rcons rd v Lp); pose (RH := rupds LH Bp); k RH
      end
  | regupd (regupd ?Y ?rd1 ?v1) ?rd ?v =>
      match goal with
      | RHp := rupds ?Lp ?Bp |- _ =>
          let chk := match tt with _ => unify Y RHp end in
          let LH := fresh "LH" in let RH := fresh "RH" in
          pose (LH := rcons rd v (rcons rd1 v1 Lp)); pose (RH := rupds LH Bp); k RH
      end
  | _ =>
      match goal with
      | RHp := rupds ?Lp ?Bp |- _ => let chk := match tt with _ => unify R RHp end in k RHp
      end
  | _ => full tt
  end.
(* [comment removed for export] *)
Ltac with_state_hidden_m tac :=
  lazymatch goal with
  | |- msteps ?segs (mkst ?R ?pc ?m ?rom) ?F =>
      hide_regs R ltac:(fun RH =>
      find_def m ident:(MEMH) ltac:(fun MH =>
      find_def F ident:(sFIN) ltac:(fun FH =>
      change (msteps segs (mkst RH pc MH rom) FH);
      tac ltac:(idtac; try (unfold MH in *));
      lazymatch goal with
      | |- msteps _ (mkst ?R1 ?pc1 ?m1 ?rom1) _ =>
          let R2 := subst_var_in R1 RH R in
          let m2 := subst_var_in m1 MH m in
          change (msteps segs (mkst R2 pc1 m2 rom1) F)
      end)))
  | |- _ => tac ltac:(idtac)
  end.
Ltac with_state_hidden tac := with_state_hidden_m ltac:(fun _ => tac ()).

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
Ltac stepn_raw F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

(* [comment removed for export] *)
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepn F D := with_state_hidden ltac:(fun _ => stepn_raw F D).
Ltac stepv F D v := with_state_hidden ltac:(fun _ => stepiv F D v vres).

(* [comment removed for export] *)
Ltac stepb_tk_raw F D tac :=
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

Ltac stepb_ft_raw F D tac :=
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

Ltac stepb_tk F D tac := with_state_hidden ltac:(fun _ => stepb_tk_raw F D tac).
Ltac stepb_ft F D tac := with_state_hidden ltac:(fun _ => stepb_ft_raw F D tac).

(* [comment removed for export] *)
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

(* [comment removed for export] *)
Ltac stepret_raw F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

Ltac stepret F D k tac := with_state_hidden ltac:(fun _ => stepret_raw F D k tac).

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
