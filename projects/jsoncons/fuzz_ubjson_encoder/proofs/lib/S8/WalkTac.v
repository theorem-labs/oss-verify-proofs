(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint wf_chain (l : list (reg * word)) (R : bvmap 5 word) : bvmap 5 word :=
  match l with nil => R | cons (r, v) l' => regupd (wf_chain l' R) r v end.
Fixpoint wf_look (l : list (reg * word)) (r : reg) : option word :=
  match l with nil => None | cons (r', v) l' => if bv_eqb r r' then Some v else wf_look l' r end.
Lemma wf_getr_chain : forall l R r, bv_eqb r 0 = false ->
  getr (wf_chain l R) r = match wf_look l r with Some v => v | None => getr R r end.
Proof.
  induction l as [|[r' v] l IH]; intros R r Hr; cbn [wf_chain wf_look]; [reflexivity|].
  assert (Hr0 : r <> 0). { intros E. rewrite E in Hr. rewrite PropExec.bv_eqb_refl in Hr. discriminate Hr. }
  destruct (bv_eqb r r') eqn:E.
  - assert (r = r') as ->. { apply bv_eq. unfold bv_eqb in E. apply Z.eqb_eq in E. exact E. }
    apply PropExec.getr_same. exact Hr0.
  - rewrite PropExec.getr_other. { apply IH. exact Hr. }
    intros E2. rewrite E2 in E. rewrite PropExec.bv_eqb_refl in E. discriminate E.
Qed.
Ltac wf_chain_list RS := lazymatch RS with regupd ?R' ?r' ?v => let l := wf_chain_list R' in constr:(cons (r', v) l) | _ => constr:(@nil (reg * word)) end.
Ltac wf_chain_base RS := lazymatch RS with regupd ?R' _ _ => wf_chain_base R' | _ => RS end.
Ltac wf_find RS r := lazymatch RS with
  | regupd ?R' ?r' ?v => let b := eval vm_compute in (bv_eqb r r') in
      lazymatch b with true => v | false => wf_find R' r end
  | _ => constr:(getr RS r) end.
Ltac wf_gres_one :=
  match goal with
  | |- context [getr (regupd ?R0 ?r' ?v0) ?r] =>
      let RS := constr:(regupd R0 r' v0) in
      let z := eval vm_compute in (bv_eqb r 0) in
      lazymatch z with
      | true => change (getr RS r) with (Z_to_bv 64 0)
      | false =>
          let l := wf_chain_list RS in let B := wf_chain_base RS in
          let val := wf_find RS r in
          let H := fresh "gH" in
          pose proof (wf_getr_chain l B r (@eq_refl bool false) : getr RS r = val) as H;
          rewrite H; clear H
      end
  end.
Ltac gres_old :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ].
Ltac gres :=
  repeat wf_gres_one;
  lazymatch goal with |- context [getr (regupd _ _ _) _] => gres_old | _ => idtac end;
  lazymatch goal with |- context [getr _ 0%bv] => rewrite ?getr_zero | _ => idtac end.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.

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
End FPX_1.

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

Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

Ltac vnorm := gres; imm_norm;
  lazymatch goal with |- context [v_addi _ 0%Z] => rewrite ?v_addi_0 | _ => idtac end;
  lazymatch goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  lazymatch goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.

Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

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

Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

Ltac stepsd F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].

Ltac stepld F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
