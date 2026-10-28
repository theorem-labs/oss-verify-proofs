(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BExitSim BPropExec BCatExec BCatSim BSeqExec BStreamExec BMmapSim BWallSim BStreamSim BDrainSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.

Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section WithFP1.
Context {fx : DFP}.

End WithFP1.
Ltac chain_step :=
  first [ eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply BMmapSim.twmt_step
        | eapply tmw_step
        | eapply BStreamSim.twr_step
        | eapply BStreamSim.trd_step
        | eapply BWallSim.twt_step
        | eapply BWallSim.twe_step
        | eapply BDrainSim.tout_step
        | eapply BDrainSim.trd_step
        | eapply te_step ].

Section WithFP2.
Context {fx : DFP}.

End WithFP2.
Ltac step_intro := chain_step.

Section WithFP3.
Context {fx : DFP}.

End WithFP3.
Ltac expand_ctx_defs p :=
  match goal with
  | H := _ |- _ =>
      lazymatch p with
      | context [H] => let p' := eval unfold H in p in expand_ctx_defs p'
      end
  | _ => p
  end.

Section WithFP4.
Context {fx : DFP}.

End WithFP4.
Ltac check_closed_term p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term:" p "contains an evar"
  else tryif (match p' with context [?x] => is_var x end)
  then fail 0 "check_closed_term:" p "mentions a context variable"
  else idtac.

Section WithFP5.
Context {fx : DFP}.

End WithFP5.
Ltac vm_eval t :=
  let _ := match goal with _ => check_closed_term t end in
  eval vm_compute in t.

Section WithFP6.
Context {fx : DFP}.

End WithFP6.
Ltac word_lit p :=
  let u := vm_eval (bv_unsigned p) in
  constr:(@BV 64 u ltac:(vm_compute; exact I)).

Section WithFP7.
Context {fx : DFP}.

End WithFP7.
Ltac wlit_replace p :=
  let l := word_lit p in
  replace p with l by (apply bv_eq; vm_compute; reflexivity).

Section WithFP8.
Context {fx : DFP}.

End WithFP8.
Ltac wlit p :=
  try (lazymatch p with
       | @BV _ _ _ => idtac
       | _ => wlit_replace p
       end).

Section WithFP9.
Context {fx : DFP}.

End WithFP9.
Ltac wlits :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_replace (v_addi a b)
  | |- context [btgt ?a ?b] => wlit_replace (btgt a b)
  | |- context [v_jalr ?a ?b] => wlit_replace (v_jalr a b)
  | |- context [v_auipc ?a ?b] => wlit_replace (v_auipc a b)
  end.

Section WithFP10.
Context {fx : DFP}.

End WithFP10.
Ltac norm_pc_state st :=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => wlit p
       | _ => idtac
       end.

Ltac norm_pc :=
  try lazymatch goal with
  | |- msteps _ ?st _ => norm_pc_state st
  | |- to_wexit _ ?st _ _ => norm_pc_state st
  | |- twm _ ?st _ _ _ => norm_pc_state st
  | |- BMmapSim.twm_pend _ ?st _ _ _ _ => norm_pc_state st
  | |- BMmapSim.twm_tail _ ?st _ _ _ _ => norm_pc_state st
  | |- tmw _ ?st _ _ _ _ _ => norm_pc_state st
  | |- BStreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- BStreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- BWallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- BWallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- BWallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
  | |- to_exit _ _ ?st => norm_pc_state st
  | |- BDrainSim.to_out _ _ ?st => norm_pc_state st
  | |- BDrainSim.to_rd _ _ _ _ _ _ _ ?st => norm_pc_state st
  end.

Section WithFP12.
Context {fx : DFP}.

End WithFP12.
Ltac reduce_bv_eqb_ifs :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let v := eval vm_compute in (bv_eqb a b) in
              lazymatch v with
              | true => change (if bv_eqb a b then x else y) with x
              | false => change (if bv_eqb a b then x else y) with y
              end
          end
      end
  end.

Section WithFP13.
Context {fx : DFP}.

End WithFP13.
Ltac step_simpl :=
  reduce_bv_eqb_ifs;
  match goal with |- context [skipn O _] => rewrite ?skipn_O | _ => idtac end;
  norm_pc.

Section WithFP14.
Context {fx : DFP}.

End WithFP14.
Ltac stepi_search F D :=
  first
    [ exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (BPropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)

    | exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D) ].

Section WithFP15.
Context {fx : DFP}.

End WithFP15.
Ltac stepi F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLT _ _ _, _) =>
        exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_AND _ _ _, _) =>
        exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_OR _ _ _, _) =>
        exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_XOR _ _ _, _) =>
        exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) =>
        exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) =>
        exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRA _ _ _, _) =>
        exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLT _ _ _, _) =>
        exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLTU _ _ _, _) =>
        exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_ADD _ _ _, _) =>
        exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) =>
        exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SLL _ _ _, _) =>
        exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRL _ _ _, _) =>
        exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRA _ _ _, _) =>
        exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        exact (BPropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SLL _ _ _, _) =>
        exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRL _ _ _, _) =>
        exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRA _ _ _, _) =>
        exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Auipc _ _, _) =>
        exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Lui _ _, _) =>
        exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULH _ _ _, _) =>
        exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHSU _ _ _, _) =>
        exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHU _ _ _, _) =>
        exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIV _ _ _, _) =>
        exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_REM _ _ _, _) =>
        exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIVU _ _ _, _) =>
        eapply step_divu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul M_REMU _ _ _, _) =>
        eapply step_remu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul32 M_MUL _ _ _, _) =>
        exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIV _ _ _, _) =>
        exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIVU _ _ _, _) =>
        exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REM _ _ _, _) =>
        exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REMU _ _ _, _) =>
        exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | _ => stepi_search F D
    end
  | step_simpl ].

Section WithFP16.
Context {fx : DFP}.

End WithFP16.
Ltac stepiv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        eapply step_addi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        eapply step_andi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        eapply step_ori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        eapply step_xori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        eapply step_sltiu_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        eapply step_slli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        eapply step_srli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        eapply step_srai_at with (v := vv)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        eapply step_add_at with (v := vv)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        eapply step_sub_at with (v := vv)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        eapply step_addiw_at with (v := vv)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        eapply step_mul_at with (v := vv)
    | decode_any _ = Some (Lui _ _, _) =>
        eapply step_lui_at with (v := vv)
    | decode_any _ = Some (Auipc _ _, _) =>
        eapply step_auipc_at with (v := vv)
    | _ => eapply step_addi_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP17.
Context {fx : DFP}.

End WithFP17.
Ltac stepiwv F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_addiw_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP18.
Context {fx : DFP}.

End WithFP18.
Ltac stepj F D :=
  chain_step;
  [ reflexivity
  | first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
          | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
  | step_simpl ].

Section WithFP19.
Context {fx : DFP}.

End WithFP19.
Ltac stepjr F D tv tac :=
  chain_step;
  [ reflexivity
  | first [ eapply step_jalr_x0 with (tgt := tv);
            [ exact F | reflexivity | exact D | tac ]
          | eapply step_jalr_link with (tgt := tv);
            [ exact F | reflexivity | exact D | reflexivity | tac ] ]
  | step_simpl ].

Section WithFP20.
Context {fx : DFP}.

Lemma u_Z2bv : forall z, (0 <= z)%Z -> (z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
  exact Hhi.
Qed.

Lemma v_addi_m1 : forall x, (1 <= bv_unsigned x)%Z ->
  v_addi x (-1) = Z_to_bv 64 (bv_unsigned x - 1).
Proof. intros x H1. apply (v_addi_m x 1); lia. Qed.

Lemma v_addi_m16 : forall x, (16 <= bv_unsigned x)%Z ->
  v_addi x (-16) = Z_to_bv 64 (bv_unsigned x - 16).
Proof. intros x H16. apply (v_addi_m x 16); lia. Qed.

Lemma v_addi_m32 : forall x, (32 <= bv_unsigned x)%Z ->
  v_addi x (-32) = Z_to_bv 64 (bv_unsigned x - 32).
Proof. intros x H32. apply (v_addi_m x 32); lia. Qed.

Lemma v_addi_m48 : forall x, (48 <= bv_unsigned x)%Z ->
  v_addi x (-48) = Z_to_bv 64 (bv_unsigned x - 48).
Proof. intros x H48. apply (v_addi_m x 48); lia. Qed.

Lemma v_addi_m64 : forall x, (64 <= bv_unsigned x)%Z ->
  v_addi x (-64) = Z_to_bv 64 (bv_unsigned x - 64).
Proof. intros x H64. apply (v_addi_m x 64); lia. Qed.

Lemma v_addi_m80 : forall x, (80 <= bv_unsigned x)%Z ->
  v_addi x (-80) = Z_to_bv 64 (bv_unsigned x - 80).
Proof. intros x H80. apply (v_addi_m x 80); lia. Qed.

Lemma v_addi_nneg_t : forall x imm, (0 <= imm)%Z ->
  (bv_unsigned x + imm < 2^64)%Z ->
  v_addi x imm = Z_to_bv 64 (bv_unsigned x + imm).
Proof. intros x imm _ _. reflexivity. Qed.

End WithFP20.
Ltac u_norm :=
  repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 _)] => idtac end;
          rewrite u_Z2bv by lia).

Section WithFP21.
Context {fx : DFP}.

End WithFP21.
Ltac imm_norm :=
  repeat match goal with
  | |- context [bv_signed ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_signed b) in
          change (bv_signed b) with v
      end
  | |- context [bv_unsigned ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_unsigned b) in
          change (bv_unsigned b) with v
      end
  end.

Section WithFP22.
Context {fx : DFP}.

End WithFP22.
Ltac sp_norm :=
  imm_norm;
  repeat (match goal with
  | |- context [v_addi ?x ?i] =>
      lazymatch x with
      | context [v_addi _ _] => fail
      | _ => first [ rewrite (v_addi_m80 x) by (u_norm; lia)
                   | rewrite (v_addi_m64 x) by (u_norm; lia)
                   | rewrite (v_addi_m48 x) by (u_norm; lia)
                   | rewrite (v_addi_m32 x) by (u_norm; lia)
                   | rewrite (v_addi_m16 x) by (u_norm; lia)
                   | rewrite (v_addi_m1 x) by (u_norm; lia)
                   | rewrite (v_addi_nneg_t x i) by (u_norm; lia) ]
      end
  end; u_norm; cbn [Z.to_N]).

Section WithFP23.
Context {fx : DFP}.

End WithFP23.
Ltac stepi_at F D val :=
  chain_step;
  [ reflexivity
  | eapply step_addi_at with (v := val);
    [ exact F | reflexivity | exact D
    | reflexivity
    | getr_resolve; regupd_resolve; reduce_bv_eqb_ifs; sp_norm;
      first [ reflexivity | lia | f_equal; lia
            | apply bv_eq;
              lazymatch goal with |- ?g => check_closed_term g end;
              vm_compute; reflexivity ] ]
  | step_simpl ].

Section WithFP24.
Context {fx : DFP}.

End WithFP24.
Ltac bveq :=
  apply bv_eq;
  lazymatch goal with
  | |- ?g =>
      tryif check_closed_term g then
        first
          [ (vm_compute; reflexivity)
          | fail 1 "bveq: vm_compute did not close this closed goal: "
                   "its two sides compute to different values." ]
      else tryif has_evar g then
        fail 1 "bveq: the goal contains an evar — vm_compute must not "
               "see it; instantiate the machine state (eexists / "
               "chain_step) before normalizing."
      else

        first
          [ reflexivity
          | fail 1 "bveq: the goal is OPEN (it mentions a context "
                   "variable) and kernel conversion did not close it — "
                   "resolve the register and memory projections first "
                   "(getr_resolve, regupd_resolve) and try again." ]
  end.

Section WithFP25.
Context {fx : DFP}.









End WithFP25.
Ltac stepw_addr :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].
Ltac stepw_val :=
  getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs;
  first [ reflexivity | sp_norm; first [ reflexivity | f_equal; lia ] | bveq ].

Ltac stepw_addr_hyps :=
  getr_resolve; regupd_resolve;
  repeat match goal with
  | H : Sem.reg_get ?R ?r = _ |- context [Sem.reg_get ?R ?r] => rewrite H
  end;
  imm_norm; rewrite ?v_addi_0;
  sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

Section WithFP27.
Context {fx : DFP}.

End WithFP27.
Ltac stepw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply BMmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val
        | reflexivity | oktac ]
    end
  | step_simpl ].

Ltac stepsd F D aexp vexp vtac oktac :=
  step_intro;
  [ reflexivity
  | eapply step_sd_at with (a := aexp) (v := vexp);
    [ exact F | reflexivity | exact D | stepw_addr_hyps | vtac | oktac ]
  | step_simpl ].

Ltac stepld F D aexp vexp readtac :=
  step_intro;
  [ reflexivity
  | eapply step_ld with (bs := word_to_le_bytes 8 vexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | match goal with |- rdn _ _ ?ad _ = _ =>
        replace ad with aexp by stepw_addr_hyps
      end; readtac
    | exact (bytes_le_to_Z_8 _) ]
  | step_simpl ].

Section WithFP28.
Context {fx : DFP}.

End WithFP28.
Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP29.
Context {fx : DFP}.

End WithFP29.
Ltac wlit_closed p :=
  check_closed_term p;
  let u := vm_eval (bv_unsigned p) in
  replace p with (Z_to_bv 64 u) by bveq.

Section WithFP30.
Context {fx : DFP}.

End WithFP30.
Ltac wlits_closed :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_add ?a ?b] => wlit_closed (v_add a b)
  | |- context [v_sub ?a ?b] => wlit_closed (v_sub a b)
  end.

Section WithFP32.
Context {fx : DFP}.

End WithFP32.
Ltac rdn_ext_lit :=
  erewrite rdn_ext;
    [
    | imm_norm; u_norm; lia
    | let x := fresh "x" in
      let Hx := fresh "Hx" in
      intros x Hx; revert Hx; imm_norm; u_norm; intros Hx ].

Section WithFP33.
Context {fx : DFP}.

Lemma word_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_r.
  reflexivity.
Qed.

Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof.
  intros x y. apply bv_eq.
  change (v_add x y) with (x + y).
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

Lemma bsb_bound : forall ph (sp : word) (a e : list (list byte)) uid hw rnd,
  valid_argv a -> valid_envp e ->
  (Z.of_nat (length (build_stack_bytes ph sp a e uid hw rnd)) <= 2240000)%Z.
Proof.
  intros ph sp a e uid hw rnd Hva Hve.
  pose proof (build_stack_bytes_within_span ph sp a e uid hw rnd).
  pose proof (entry_stack_span_bound a e Hva Hve).
  unfold entry_stack_span_max in *. lia.
Qed.

Definition ro_segs_below (segs : list Segment) (data_base : Z) : bool :=
  forallb (fun seg =>
             seg_writable seg
             || Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) data_base)
          segs.

Section DispatchSmoke.
  Variable segs : list Segment.
  Variable regs : bvmap 5 word.
  Variable mem rom : word -> option byte.

  Ltac smoke enc sh :=
    let F := fresh "F" in
    intro F;
    let D := fresh "D" in
    assert (D : decode_any enc = Some (sh, 4%Z)) by vm_refl_bv;
    eexists; stepi F D; apply mst_refl.

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

  

End DispatchSmoke.
End WithFP33.
