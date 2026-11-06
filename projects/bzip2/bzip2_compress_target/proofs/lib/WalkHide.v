(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
Import ListNotations.
Local Open Scope bv_scope.

(* [comment removed for export] *)
Definition hid {A : Type} (x : A) : A := x.     (* [comment removed for export] *)
Definition hidt {A : Type} (x : A) : A := x.    (* [comment removed for export] *)
Definition hidl (l : list (reg * word)) : list (reg * word) := l.   (* [comment removed for export] *)
Definition wh_mark : unit := tt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac check_closed_term_old p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term_old:" p "contains an evar"
  else tryif (match p' with context [?x] => is_var x end)
  then fail 0 "check_closed_term_old:" p "mentions a context variable"
  else idtac.

(* [comment removed for export] *)
Ltac stepi_search_old F D :=
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
    | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    (* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac stepi_old F D :=
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
        exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
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
    | _ => stepi_search_old F D
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepiv_old F D vv tac :=
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

(* [comment removed for export] *)
Ltac stepiwv_old F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_addiw_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepj_old F D :=
  chain_step;
  [ reflexivity
  | first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
          | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepjr_old F D tv tac :=
  chain_step;
  [ reflexivity
  | first [ eapply step_jalr_x0 with (tgt := tv);
            [ exact F | reflexivity | exact D | tac ]
          | eapply step_jalr_link with (tgt := tv);
            [ exact F | reflexivity | exact D | reflexivity | tac ] ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac vnorm_old :=
  gres; imm_norm;
  match goal with |- context [v_addi _ Z0] => rewrite ?v_addi_0 | _ => idtac end;
  match goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  match goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.

(* [comment removed for export] *)
Ltac stepn_old F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj_old F D; vnorm_old
  | _ => stepi_old F D; vnorm_old
  end.

(* [comment removed for export] *)
Ltac vres_old := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].

(* [comment removed for export] *)
Ltac stepv_old F D v := stepiv_old F D v vres_old.

(* [comment removed for export] *)
Ltac stepb_tk_old F D tac :=
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
  | step_simpl; vnorm_old ].

(* [comment removed for export] *)
Ltac stepb_ft_old F D tac :=
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
  | step_simpl; vnorm_old ].

(* [comment removed for export] *)
Ltac stepret_old F D k tac :=
  stepjr_old F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac wh_expand B L :=
  lazymatch L with
  | @cons _ (@pair _ _ ?rd ?v) ?L' => let Y := wh_expand B L' in uconstr:(regupd Y rd v)
  | @nil _ => B
  | hidl ?l => wh_expand B l
  | _ => let b := eval cbv delta [L] in L in wh_expand B b
  end.

(* [comment removed for export] *)
Ltac wh_list_val L r :=
  lazymatch L with
  | @cons _ (@pair _ _ ?rd ?v) ?L' =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in constr:(@Some word v)
      | _ => wh_list_val L' r
      end
  | @nil _ => constr:(@None word)
  | hidl ?l => wh_list_val l r
  | _ => let b := eval cbv delta [L] in L in wh_list_val b r
  end.

(* [comment removed for export] *)
Ltac wh_gres_deep X r :=
  let b := chain_base X in
  let l := chain_list X in
  let L := fresh "WH_GL" in
  pose (L := l);
  change (getr X r) with (getr (chain_apply b L) r);
  first [ (let v := chain_find X r in
           rewrite (getr_chain_hit b L r v (@eq_refl bool false) (@eq_refl (option word) (Some v))))
        | rewrite (getr_chain_miss b L r (@eq_refl (option word) None)) ];
  clear L.

(* [comment removed for export] *)
Ltac wh_gres :=
  repeat match goal with
         | |- context [getr ?R ?r] =>
             is_var R;
             let b := eval cbv delta [R] in R in
             lazymatch b with
             | chain_apply ?B ?L =>
                 let ov := wh_list_val L r in
                 lazymatch ov with
                 | Some ?v => let p := constr:(getr_chain_hit B L r v (@eq_refl bool false) (@eq_refl (option word) (Some v)) : getr R r = v) in rewrite p
                 | None => let p := constr:(getr_chain_miss B L r (@eq_refl (option word) None) : getr R r = getr B r) in rewrite p
                 end
             end
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             first [ chain_deep X; wh_gres_deep X r
                   | chain_deep X; let p := getr_proof_fast X r in rewrite p
                   | let p := getr_proof X r in
                     let p' := constr:(p) in rewrite p' ]
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac wh_foldable v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else check_closed_term v
  | @BV _ _ _ => fail
  | _ => check_closed_term v
  end.

(* [comment removed for export] *)
Ltac wh_pin_sensitive := fail.

(* [comment removed for export] *)
Ltac wh_check_closed_term p :=
  tryif has_evar p then fail 0 "check_closed_term:" p "contains an evar"
  else tryif (match p with context [?x] => is_var x end)
  then (tryif (match p with context [?x] => is_var x; assert_fails (let b := eval cbv delta [x] in x in idtac) end)
        then fail 0 "check_closed_term:" p "mentions a context variable"
        else check_closed_term_old p)
  else idtac.

(* [comment removed for export] *)
Ltac wh_active t :=
  first
  [ lazymatch t with context [getr (regupd _ _ _) _] => idtac end
  | wh_pin_sensitive; match goal with H : getr ?rs ?r = _ |- _ => lazymatch t with context [getr rs r] => idtac end end
  | lazymatch t with context [bv_signed (@BV _ _ _)] => idtac end
  | lazymatch t with context [bv_unsigned (@BV _ _ _)] => idtac end
  | lazymatch t with context [v_addi _ Z0] => idtac end
  | lazymatch t with context [v_add _ (Z_to_bv 64 0)] => idtac end
  | lazymatch t with context [v_add (Z_to_bv 64 0) _] => idtac end
  | match t with context [regupd _ _ ?v] => wh_foldable v end
  | lazymatch t with context [v_addi (@BV _ _ _) _] => idtac end
  | lazymatch t with context [btgt _ _] => idtac end
  | lazymatch t with context [v_jalr _ _] => idtac end
  | lazymatch t with context [v_auipc _ _] => idtac end
  | lazymatch t with context [if _ then _ else _] => idtac end
  | lazymatch t with context [skipn O _] => idtac end ].
Ltac wh_dirty v := first [ wh_foldable v | wh_active v ].

(* [comment removed for export] *)
Ltac wh_hide_point Y best :=
  lazymatch Y with
  | regupd ?Y' ?rd ?v =>
      let b := match tt with
               | _ => let chk := match tt with _ => wh_dirty v end in Y'
               | _ => best
               end in
      wh_hide_point Y' b
  | _ => best
  end.

(* [comment removed for export] *)
Ltac wh_list Y :=
  lazymatch Y with
  | regupd ?Y' ?rd ?v =>
      let bl := wh_list Y' in
      lazymatch bl with (?B, ?l) => constr:((B, @cons (reg * word) (rd, v) l)) end
  | _ => match tt with
         | _ => let chk := match tt with _ => is_var Y end in
                let b := eval cbv delta [Y] in Y in
                lazymatch b with chain_apply ?B ?L => constr:((B, L)) end
         | _ => constr:((Y, @nil (reg * word)))
         end
  end.

(* [comment removed for export] *)
Ltac wh_find_hid t :=
  match goal with
  | V := @hid _ ?b |- _ => let chk := match tt with _ => constr_eq b t end in V
  end.
Ltac wh_find_hidt t :=
  match goal with
  | V := @hidt _ ?b |- _ => let chk := match tt with _ => constr_eq b t end in V
  end.

(* [comment removed for export] *)
Ltac wh_clear_old_mem := repeat match goal with V := @hid _ _ |- _ => clear V end.
Ltac wh_clear_old_regs := repeat match goal with R := chain_apply _ _ |- _ => clear R end.
(* [comment removed for export] *)
Ltac wh_run L :=
  match tt with
  | _ => let chk := match tt with _ => is_var L end in
         let b := eval cbv delta [L] in L in
         lazymatch b with
         | hidl (@cons _ ?e ?L') =>
             lazymatch L' with
             | @cons _ _ _ => constr:((O, @nil (reg * word), @nil (list (reg * word)), L))
             | _ => let r := wh_run L' in
                    lazymatch r with
                    | (?k, ?l, ?vs, ?T) => constr:((S k, @cons (reg * word) e l, @cons (list (reg * word)) L vs, T))
                    end
             end
         | _ => constr:((O, @nil (reg * word), @nil (list (reg * word)), L))
         end
  | _ => constr:((O, @nil (reg * word), @nil (list (reg * word)), L))
  end.
Ltac wh_app l1 l2 :=
  lazymatch l1 with
  | @cons _ ?e ?t => let r := wh_app t l2 in constr:(@cons (reg * word) e r)
  | _ => l2
  end.
(* [comment removed for export] *)
Ltac wh_split l :=
  lazymatch l with
  | @cons _ ?e ?t => let r := wh_split t in lazymatch r with (?h, ?T) => constr:((@cons (reg * word) e h, T)) end
  | _ => constr:((@nil (reg * word), l))
  end.
Ltac wh_clear_vars vs :=
  lazymatch vs with
  | @cons _ ?V ?t => clear V; wh_clear_vars t
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac wh_hide_mem_hook := fail.          (* [comment removed for export] *)
Ltac wh_unhid_mem_hook M := fail.       (* [comment removed for export] *)
Ltac wh_structured_mem M := fail.       (* [comment removed for export] *)
Ltac wh_hide_mem :=
  first
  [ wh_hide_mem_hook
  | lazymatch goal with
    | |- msteps ?S (mkst ?X ?P ?M ?ROM) ?T =>
        tryif is_var M then idtac else
        first [ let V := wh_find_hid M in change_no_check (msteps S (mkst X P V ROM) T)      (* [comment removed for export] *)
              | tryif wh_active M then idtac else
                (let V := fresh "WH_M" in pose (V := hid M); change_no_check (msteps S (mkst X P V ROM) T); wh_clear_old_mem) ]
    end ].
Ltac wh_hide_tgt :=
  lazymatch goal with
  | |- msteps ?S ?ST ?T =>
      tryif is_var T then idtac else
      first [ let V := wh_find_hidt T in change_no_check (msteps S ST V)
            | tryif wh_active T then idtac else
              (let V := fresh "WH_T" in pose (V := hidt T); change_no_check (msteps S ST V)) ]
  end.
(* [comment removed for export] *)
Ltac wh_hide_regs_reuse :=
  try lazymatch goal with
  | R := chain_apply ?B ?L |- msteps ?S (mkst ?X ?P ?M ?ROM) ?T =>
      let E := wh_expand B L in let E := constr:(E) in
      lazymatch X with context C [E] => let X' := context C [R] in change_no_check (msteps S (mkst X' P M ROM) T) end
  end.
Ltac wh_hide_regs_new :=
  lazymatch goal with
  | |- msteps ?S (mkst ?X ?P ?M ?ROM) ?T =>
      let Y := wh_hide_point X X in
      lazymatch Y with
      | regupd _ _ _ =>
          let bl := wh_list Y in
          lazymatch bl with
          | (?B, ?l) =>
              let Ln := fresh "WH_L" in let Rn := fresh "WH_R" in
              let sp := wh_split l in
              lazymatch sp with
              | (?h, ?T0) =>
                  let r := wh_run T0 in
                  lazymatch r with
                  | (S (S (S (S (S (S (S _)))))), ?l7, ?vs, ?T1) =>
                      (* [comment removed for export] *)
                      let t1 := wh_app l7 T1 in let l' := wh_app h t1 in
                      pose (Ln := hidl l'); pose (Rn := chain_apply B Ln);
                      lazymatch X with context C [Y] => let X' := context C [Rn] in change_no_check (msteps S (mkst X' P M ROM) T) end;
                      wh_clear_old_regs; wh_clear_vars vs
                  | _ =>
                      pose (Ln := hidl l); pose (Rn := chain_apply B Ln);
                      lazymatch X with context C [Y] => let X' := context C [Rn] in change_no_check (msteps S (mkst X' P M ROM) T) end;
                      wh_clear_old_regs
                  end
              end
          end
      | _ => idtac
      end
  end.
Ltac wh_hide_core := wh_hide_mem; wh_hide_tgt; wh_hide_regs_reuse; wh_hide_regs_new.

(* [comment removed for export] *)
Ltac wh_hid_body V :=
  let chk := match tt with _ => is_var V end in
  let b := eval cbv delta [V] in V in
  lazymatch b with @hid _ ?x => x | @hidt _ ?x => x end.
(* [comment removed for export] *)
Ltac wh_unhid_mem M :=
  lazymatch M with
  | wbytes ?m' ?a ?bs => let m'' := wh_unhid_mem m' in constr:(wbytes m'' a bs)
  | _ => match tt with
         | _ => wh_unhid_mem_hook M
         | _ => wh_hid_body M
         | _ => M
         end
  end.
Ltac wh_unhid_var T :=
  match tt with
  | _ => wh_hid_body T
  | _ => T
  end.
Ltac wh_regs_plain X :=
  lazymatch X with
  | regupd ?Y ?rd ?v => let Y' := wh_regs_plain Y in uconstr:(regupd Y' rd v)
  | _ => match tt with
         | _ => let chk := match tt with _ => is_var X end in
                let b := eval cbv delta [X] in X in
                lazymatch b with chain_apply ?B ?L => wh_expand B L end
         | _ => X
         end
  end.
Ltac wh_restore_generic :=
  repeat match goal with
         | V := @hid _ ?b |- ?G => lazymatch G with context C [V] => let G' := context C [b] in change_no_check G' end
         | V := @hidt _ ?b |- ?G => lazymatch G with context C [V] => let G' := context C [b] in change_no_check G' end
         | R := chain_apply ?B ?L |- ?G =>
             lazymatch G with context C [R] =>
               let E := wh_expand B L in let E := constr:(E) in let G' := context C [E] in change_no_check G' end
         end.
Ltac wh_restore :=
  lazymatch goal with
  | |- msteps ?S (mkst ?X ?P ?M ?ROM) ?T =>
      let Xp := wh_regs_plain X in
      let Mp := wh_unhid_mem M in
      let Tp := wh_unhid_var T in
      change_no_check (msteps S (mkst Xp P Mp ROM) Tp)
  | |- _ => wh_restore_generic
  end.
(* [comment removed for export] *)
Ltac wh_reveal_state_mem :=
  lazymatch goal with
  | |- msteps ?S (mkst ?X ?P ?M ?ROM) ?T => let Mp := wh_unhid_mem M in change_no_check (msteps S (mkst X P Mp ROM) T)
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac wh_mem_core M := lazymatch M with wbytes ?m' _ _ => wh_mem_core m' | _ => M end.
Ltac wh_reveal_state_mem_lite :=
  lazymatch goal with
  | |- msteps _ (mkst _ _ ?M _) _ => let M0 := wh_mem_core M in tryif wh_structured_mem M0 then idtac else wh_reveal_state_mem
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac wh_reveal_rdn_var :=
  lazymatch goal with
  | |- rdn ?S ?M ?a ?n = ?r => first [ let b := wh_hid_body M in change_no_check (rdn S b a n = r) | idtac ]
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac wh_clear_side :=
  repeat match goal with R := chain_apply _ _ |- _ => clear R end;
  repeat match goal with V := hidl _ |- _ => clear V end;
  repeat match goal with V := @hid _ _ |- _ => clear V end;
  repeat match goal with V := @hidt _ _ |- _ => clear V end;
  repeat match goal with V := wh_mark |- _ => clear V end.

(* [comment removed for export] *)
Ltac wh_reveal_scan :=
  repeat match goal with
         | V := @hid _ ?b |- ?G => lazymatch G with context C [V] => let G' := context C [b] in change_no_check G' end
         end.
Ltac wh_reveal :=
  lazymatch goal with
  | |- rdn ?S ?M ?a ?n = ?r =>
      first [ let b := wh_hid_body M in change_no_check (rdn S b a n = r) | wh_reveal_scan ]
  | |- store_ok ?S ?M ?a ?n = ?r =>
      first [ let b := wh_hid_body M in change_no_check (store_ok S b a n = r) | wh_reveal_scan ]
  | |- _ => wh_reveal_scan
  end;
  wh_clear_side.
(* [comment removed for export] *)
Ltac wh_user_mem tac :=
  first [ (lazymatch goal with
           | |- rdn _ ?M _ _ = _ => wh_structured_mem M
           | |- store_ok _ ?M _ _ = _ => wh_structured_mem M
           end); wh_clear_side; tac
        | wh_reveal; tac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope Z_scope.
Inductive aexp : Set := AX | AY | ALit (z : Z) | AAdd (a b : aexp) | ASub (a b : aexp).
Fixpoint aval (x y : Z) (e : aexp) : Z :=
  match e with
  | AX => x | AY => y | ALit z => z
  | AAdd a b => aval x y a + aval x y b
  | ASub a b => aval x y a - aval x y b
  end.
(* [comment removed for export] *)
Fixpoint anf (e : aexp) : Z * Z * Z :=
  match e with
  | AX => (1, 0, 0) | AY => (0, 1, 0) | ALit z => (0, 0, z)
  | AAdd a b => (fst (fst (anf a)) + fst (fst (anf b)), snd (fst (anf a)) + snd (fst (anf b)), snd (anf a) + snd (anf b))
  | ASub a b => (fst (fst (anf a)) - fst (fst (anf b)), snd (fst (anf a)) - snd (fst (anf b)), snd (anf a) - snd (anf b))
  end.
Lemma anf_ok : forall x y e, aval x y e = fst (fst (anf e)) * x + snd (fst (anf e)) * y + snd (anf e).
Proof. intros x y e. induction e as [| | z | a IHa b IHb | a IHa b IHb]; cbn [aval anf fst snd]; try rewrite IHa, IHb; ring. Qed.

Definition two64 : Z := 18446744073709551616.
(* [comment removed for export] *)
Definition cb01 (c lo hi : Z) : option (Z * Z) := if c =? 0 then Some (0, 0) else if c =? 1 then Some (lo, hi) else None.
Definition abounds (lox hix loy hiy : Z) (e : aexp) : option (Z * Z) :=
  match cb01 (fst (fst (anf e))) lox hix, cb01 (snd (fst (anf e))) loy hiy with
  | Some (lx, hx), Some (ly, hy) => Some (lx + ly + snd (anf e), hx + hy + snd (anf e))
  | _, _ => None
  end.
Definition disj_ok (lox hix loy hiy : Z) (ea : aexp) (n : Z) (eb : aexp) (len : Z) : bool :=
  match abounds lox hix loy hiy ea, abounds lox hix loy hiy eb with
  | Some (la, ha), Some (lb, hb) =>
      (0 <=? la) && (ha <? two64) && (ha + n <=? two64) && (0 <=? lb) && (hb <? two64) && (hb + len <=? two64) &&
      (if (fst (fst (anf ea)) =? fst (fst (anf eb))) && (snd (fst (anf ea)) =? snd (fst (anf eb)))
       then (snd (anf ea) + n <=? snd (anf eb)) || (snd (anf eb) + len <=? snd (anf ea))
       else (ha + n <=? lb) || (hb + len <=? la))
  | _, _ => false
  end.

Lemma cb01_sound : forall c lo hi v l h, lo <= v <= hi -> cb01 c lo hi = Some (l, h) -> l <= c * v <= h.
Proof.
  intros c lo hi v l h Hv. unfold cb01.
  destruct (c =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. subst c. intros H. injection H as <- <-. lia.
  - destruct (c =? 1) eqn:E1; [|discriminate]. apply Z.eqb_eq in E1. subst c. intros H. injection H as <- <-. lia.
Qed.
Lemma abounds_sound : forall lox hix loy hiy x y e l h, lox <= x <= hix -> loy <= y <= hiy ->
  abounds lox hix loy hiy e = Some (l, h) -> l <= aval x y e <= h.
Proof.
  intros lox hix loy hiy x y e l h Hx Hy. unfold abounds. rewrite (anf_ok x y e).
  destruct (cb01 (fst (fst (anf e))) lox hix) as [[lx hx]|] eqn:Ex; [|discriminate].
  destruct (cb01 (snd (fst (anf e))) loy hiy) as [[ly hy]|] eqn:Ey; [|discriminate].
  intros H. injection H as <- <-.
  pose proof (cb01_sound _ _ _ x _ _ Hx Ex). pose proof (cb01_sound _ _ _ y _ _ Hy Ey). lia.
Qed.

Lemma disj_ok_sound : forall lox hix loy hiy x y ea n eb len, lox <= x <= hix -> loy <= y <= hiy ->
  disj_ok lox hix loy hiy ea n eb len = true ->
  0 <= aval x y ea < 2^64 /\ aval x y ea + n <= 2^64 /\ 0 <= aval x y eb < 2^64 /\ aval x y eb + len <= 2^64 /\
  (aval x y ea + n <= aval x y eb \/ aval x y eb + len <= aval x y ea).
Proof.
  intros lox hix loy hiy x y ea n eb len Hx Hy. unfold disj_ok.
  destruct (abounds lox hix loy hiy ea) as [[la ha]|] eqn:Ea; [|discriminate].
  destruct (abounds lox hix loy hiy eb) as [[lb hb]|] eqn:Eb; [|discriminate].
  pose proof (abounds_sound _ _ _ _ x y ea la ha Hx Hy Ea) as Ba.
  pose proof (abounds_sound _ _ _ _ x y eb lb hb Hx Hy Eb) as Bb.
  change (2^64) with two64.
  rewrite !andb_true_iff. intros [[[[[[H1 H2] H3] H4] H5] H6] H7].
  apply Z.leb_le in H1, H3, H4, H6. apply Z.ltb_lt in H2, H5.
  repeat split; try lia.
  destruct ((fst (fst (anf ea)) =? fst (fst (anf eb))) && (snd (fst (anf ea)) =? snd (fst (anf eb)))) eqn:Ec.
  - apply andb_true_iff in Ec. destruct Ec as [Ec1 Ec2]. apply Z.eqb_eq in Ec1, Ec2.
    rewrite (anf_ok x y ea), (anf_ok x y eb), Ec1, Ec2.
    apply orb_true_iff in H7. destruct H7 as [H7|H7]; apply Z.leb_le in H7; [left|right]; lia.
  - apply orb_true_iff in H7. destruct H7 as [H7|H7]; apply Z.leb_le in H7; [left|right]; lia.
Qed.

Fixpoint wchainA (x y : Z) (m : word -> option byte) (l : list (aexp * list byte)) : word -> option byte :=
  match l with
  | nil => m
  | (e, bs) :: l' => wbytes (wchainA x y m l') (Z_to_bv 64 (aval x y e)) bs
  end.

Lemma rdn_wchainA_out : forall segs (x y lox hix loy hiy : Z) m (l : list (aexp * list byte)) (ea : aexp) (n : nat),
  lox <= x <= hix -> loy <= y <= hiy ->
  forallb (fun p => disj_ok lox hix loy hiy ea (Z.of_nat n) (fst p) (Z.of_nat (length (snd p)))) l = true ->
  rdn segs (wchainA x y m l) (Z_to_bv 64 (aval x y ea)) n = rdn segs m (Z_to_bv 64 (aval x y ea)) n.
Proof.
  intros segs x y lox hix loy hiy m l ea n Hx Hy. induction l as [|[e bs] l IH]; cbn [forallb wchainA fst snd]; intros H; [reflexivity|].
  apply andb_true_iff in H. destruct H as [H1 H2].
  pose proof (disj_ok_sound lox hix loy hiy x y ea (Z.of_nat n) e (Z.of_nat (length bs)) Hx Hy H1) as K.
  rewrite rdn_wbytes_out; [exact (IH H2)| | |]; rewrite ?u_Z2bv by lia; lia.
Qed.

Lemma wh_u64_bounds : forall w : word, 0 <= bv_unsigned w <= 18446744073709551615.
Proof. intro w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with 18446744073709551616 in H. lia. Qed.
Lemma wh_zero_bounds : 0 <= 0 <= 0.
Proof. split; apply Z.le_refl. Qed.

(* [comment removed for export] *)
Definition overlap_sure (ea : aexp) (n : Z) (eb : aexp) (len : Z) : bool :=
  (fst (fst (anf ea)) =? fst (fst (anf eb))) && (snd (fst (anf ea)) =? snd (fst (anf eb))) &&
  (snd (anf eb) <? snd (anf ea) + n) && (snd (anf ea) <? snd (anf eb) + len) && (0 <? n) && (0 <? len).
Definition wh_bnd (lo x hi : Z) : Prop := lo <= x <= hi.
Definition wh_nb_mark (x : Z) : unit := tt.
Local Close Scope Z_scope.

(* [comment removed for export] *)
Ltac wh_is_atom z := first [ is_var z | lazymatch z with bv_unsigned _ => idtac end ].
Ltac wh_atom z xo yo :=
  lazymatch xo with
  | Some ?x =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq x z end in constr:((xo, yo, AX))
      | _ => lazymatch yo with
             | Some ?y => let chk := match tt with _ => constr_eq y z end in constr:((xo, yo, AY))
             | @None _ => constr:((xo, Some z, AY))
             end
      end
  | @None _ => constr:((Some z, yo, AX))
  end.
Ltac wh_ap z xo yo :=
  lazymatch z with
  | (?a + ?b)%Z =>
      let pa := wh_ap a xo yo in
      lazymatch pa with (?x1, ?y1, ?ea) =>
        let pb := wh_ap b x1 y1 in
        lazymatch pb with (?x2, ?y2, ?eb) => constr:((x2, y2, AAdd ea eb)) end end
  | (?a - ?b)%Z =>
      let pa := wh_ap a xo yo in
      lazymatch pa with (?x1, ?y1, ?ea) =>
        let pb := wh_ap b x1 y1 in
        lazymatch pb with (?x2, ?y2, ?eb) => constr:((x2, y2, ASub ea eb)) end end
  | _ => match tt with
         | _ => let chk := match tt with _ => wh_is_atom z end in wh_atom z xo yo
         | _ => let chk := match tt with _ => is_Z_lit z end in constr:((xo, yo, ALit z))
         end
  end.
Ltac wh_list_len bs :=
  lazymatch bs with
  | @nil _ => constr:(O)
  | @cons _ _ ?t => let n := wh_list_len t in constr:(S n)
  end.
(* [comment removed for export] *)
Ltac wh_blen_extra bs := fail.
Ltac wh_blen bs :=
  lazymatch bs with
  | word_to_le_bytes ?n _ => n
  | repeat _ ?n => n
  | _ => match tt with
         | _ => wh_blen_extra bs
         | _ => wh_list_len bs
         end
  end.
(* [comment removed for export] *)
Ltac wh_atoms M xo yo :=
  lazymatch M with
  | wbytes ?m' (Z_to_bv 64 ?zb) _ =>
      match tt with
      | _ => let pb := wh_ap zb xo yo in lazymatch pb with (?x1, ?y1, _) => wh_atoms m' x1 y1 end
      | _ => constr:((xo, yo))
      end
  | _ => constr:((xo, yo))
  end.
Ltac wh_first_atom_mem M :=
  lazymatch M with
  | wbytes ?m' (Z_to_bv 64 ?zb) _ =>
      match tt with
      | _ => let pb := wh_ap zb (@None Z) (@None Z) in lazymatch pb with (Some ?x, _, _) => x end
      | _ => wh_first_atom_mem m'
      end
  end.
(* [comment removed for export] *)
Ltac wh_zclosed t :=
  lazymatch t with
  | (?a + ?b)%Z => wh_zclosed a; wh_zclosed b
  | (?a - ?b)%Z => wh_zclosed a; wh_zclosed b
  | (?a * ?b)%Z => wh_zclosed a; wh_zclosed b
  | (- ?a)%Z => wh_zclosed a
  | _ => is_Z_lit t
  end.
Ltac wh_zval t := let chk := match tt with _ => wh_zclosed t end in let v := eval cbv in t in v.
(* [comment removed for export] *)
Ltac wh_nat_lit_go n k :=
  lazymatch k with
  | O => fail
  | S ?k' => lazymatch n with O => idtac | S ?m => wh_nat_lit_go m k' end
  end.
Ltac wh_nat_lit n := wh_nat_lit_go n 1024%nat.
Ltac wh_lower x :=
  match goal with
  | H : (?L <= x)%Z |- _ => wh_zval L
  | H : (?L <= x - ?k)%Z |- _ => wh_zval (L + k)%Z
  | H : (?L < x)%Z |- _ => wh_zval (L + 1)%Z
  | _ => constr:(0%Z)
  end.
Ltac wh_upper x :=
  match goal with
  | H : (x <= ?U)%Z |- _ => wh_zval U
  | H : (x < ?U)%Z |- _ => wh_zval (U - 1)%Z
  | H : (x + ?k <= ?U)%Z |- _ => wh_zval (U - k)%Z
  | _ => constr:(18446744073709551615%Z)
  end.
(* [comment removed for export] *)
Ltac wh_bounds_prepare_atom x :=
  lazymatch goal with
  | B : wh_bnd _ x _ |- _ => idtac
  | _ := wh_nb_mark x |- _ => idtac
  | |- _ =>
      let lo := wh_lower x in let hi := wh_upper x in
      first [ (let B := fresh "WH_B" in
               assert (B : wh_bnd lo x hi)
                 by (unfold wh_bnd; (lazymatch x with bv_unsigned ?w => pose proof (wh_u64_bounds w) | _ => idtac end); split; lia))
            | (let N := fresh "WH_NB" in pose (N := wh_nb_mark x)) ]
  end.
(* [comment removed for export] *)
Ltac wh_bounds_prepare :=
  lazymatch goal with
  | |- msteps _ (mkst _ _ ?M _) _ =>
      try (let x := match M with
                    | wbytes _ _ _ => wh_first_atom_mem M
                    | ?f _ _ ?J ?D => match tt with
                                      | _ => wh_first_atom_mem J
                                      | _ => wh_first_atom_mem D
                                      end
                    end in
           wh_bounds_prepare_atom x)
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Ltac wh_entry xo :=
  lazymatch xo with
  | @None _ => constr:((0%Z, 0%Z, 0%Z, wh_zero_bounds))
  | Some ?x =>
      match goal with
      | B : wh_bnd ?lo x ?hi |- _ => constr:((x, lo, hi, (B : (lo <= x <= hi)%Z)))
      | _ => lazymatch x with bv_unsigned ?w => constr:((x, 0%Z, 18446744073709551615%Z, wh_u64_bounds w)) end
      end
  end.
(* [comment removed for export] *)
Ltac wh_collect M xo yo lox hix loy hiy ea nZ :=
  lazymatch M with
  | wbytes ?m' (Z_to_bv 64 ?zb) ?bs =>
      match tt with
      | _ => let pb := wh_ap zb xo yo in
             lazymatch pb with
             | (?x1, ?y1, ?eb) =>
                 let chk := match tt with _ => (constr_eq x1 xo; constr_eq y1 yo) end in
                 let n := wh_blen bs in
                 let chk2 := match tt with _ => wh_nat_lit n end in
                 let ok := eval vm_compute in (disj_ok lox hix loy hiy ea nZ eb (Z.of_nat n)) in
                 lazymatch ok with
                 | true =>
                     let r := wh_collect m' xo yo lox hix loy hiy ea nZ in
                     lazymatch r with (?mj, ?l) => constr:((mj, @cons (aexp * list byte) (eb, bs) l)) end
                 end
             end
      | _ => constr:((M, @nil (aexp * list byte)))
      end
  | _ => constr:((M, @nil (aexp * list byte)))
  end.

Ltac wh_peel_table :=
  lazymatch goal with
  | |- rdn ?S ?M (Z_to_bv 64 ?za) ?n = ?R =>
      let pa := wh_ap za (@None Z) (@None Z) in
      lazymatch pa with (?x0, ?y0, _) => wh_atoms M x0 y0 end
  end.
Ltac wh_peel_batch :=
  lazymatch goal with
  | |- rdn ?S ?M (Z_to_bv 64 ?za) ?n = ?R =>
      lazymatch M with wbytes _ _ _ => idtac end;
      let tb := wh_peel_table in
      lazymatch tb with
      | (?xo, ?yo) =>
          (lazymatch xo with Some ?x => try wh_bounds_prepare_atom x | _ => idtac end);
          (lazymatch yo with Some ?y => try wh_bounds_prepare_atom y | _ => idtac end);
          let pa := wh_ap za xo yo in
          lazymatch pa with
          | (_, _, ?ea) =>
              let ex := wh_entry xo in let ey := wh_entry yo in
              lazymatch ex with
              | (?x, ?lox, ?hix, ?HBx) =>
                  lazymatch ey with
                  | (?y, ?loy, ?hiy, ?HBy) =>
                      let chkn := match tt with _ => wh_nat_lit n end in
                      let nZ := eval vm_compute in (Z.of_nat n) in
                      let r := wh_collect M xo yo lox hix loy hiy ea nZ in
                      lazymatch r with
                      | (?mj, ?l) =>
                          lazymatch l with @nil _ => fail | _ => idtac end;
                          let L := fresh "WH_PL" in
                          pose (L := l);
                          (* [comment removed for export] *)
                          let k mj' :=
                            (change (rdn S (wchainA x y mj' L) (Z_to_bv 64 (aval x y ea)) n = R);
                             rewrite (rdn_wchainA_out S x y lox hix loy hiy mj' L ea n HBx HBy (@eq_refl bool true));
                             change (rdn S mj' (Z_to_bv 64 za) n = R);
                             clear L) in
                          first
                          [ lazymatch mj with
                            | wbytes ?m' (Z_to_bv 64 ?zb') ?bs' =>
                                (tryif is_var m' then fail else idtac);
                                let pb := wh_ap zb' xo yo in
                                lazymatch pb with
                                | (?x1, ?y1, ?eb') =>
                                    let chk := match tt with _ => (constr_eq x1 xo; constr_eq y1 yo) end in
                                    let len := wh_blen bs' in
                                    let chk2 := match tt with _ => wh_nat_lit len end in
                                    let ov := eval vm_compute in (overlap_sure ea nZ eb' (Z.of_nat len)) in
                                    lazymatch ov with
                                    | true => let V := fresh "WH_PM" in pose (V := hid m'); k (wbytes V (Z_to_bv 64 zb') bs')
                                    end
                                end
                            end
                          | k mj ]
                      end
                  end
              end
          end
      end
  end.
Ltac wh_top_overlaps :=
  lazymatch goal with
  | |- rdn _ (wbytes _ (Z_to_bv 64 ?zb) ?bs) (Z_to_bv 64 ?za) ?n = _ =>
      let pa := wh_ap za (@None Z) (@None Z) in
      lazymatch pa with (?x1, ?y1, ?ea) =>
        let pb := wh_ap zb x1 y1 in
        lazymatch pb with (_, _, ?eb) =>
          let len := wh_blen bs in
          let chk2 := match tt with _ => (wh_nat_lit len; wh_nat_lit n) end in
          let r := eval vm_compute in (overlap_sure ea (Z.of_nat n) eb (Z.of_nat len)) in
          lazymatch r with true => idtac end end end
  end.

(* [comment removed for export] *)
Ltac wh_with tac :=
  lazymatch goal with
  | |- msteps _ (mkst _ _ _ _) _ =>
      lazymatch goal with
      | _ := wh_mark |- _ => tac ()
      | |- _ => let K := fresh "WH_K" in pose (K := wh_mark); wh_bounds_prepare; wh_hide_core; tac (); wh_restore; clear K
      end
  | |- _ => tac ()
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac vnorm_new := wh_with ltac:(fun _ => vnorm_old).
Ltac stepi_new F D := wh_with ltac:(fun _ => stepi_old F D).
Ltac stepiv_new F D vv tac := wh_with ltac:(fun _ => stepiv_old F D vv ltac:(gres; wh_clear_side; tac)).
Ltac stepiwv_new F D vv tac := wh_with ltac:(fun _ => stepiwv_old F D vv ltac:(gres; wh_clear_side; tac)).
Ltac stepj_new F D := wh_with ltac:(fun _ => stepj_old F D).
Ltac stepjr_new F D tv tac := wh_with ltac:(fun _ => stepjr_old F D tv ltac:(gres; wh_clear_side; tac)).
Ltac stepn_new F D := wh_with ltac:(fun _ => stepn_old F D).
Ltac stepv_new F D v := wh_with ltac:(fun _ => stepv_old F D v).
Ltac stepb_tk_new F D tac := wh_with ltac:(fun _ => stepb_tk_old F D ltac:(wh_clear_side; tac)).
Ltac stepb_ft_new F D tac := wh_with ltac:(fun _ => stepb_ft_old F D ltac:(wh_clear_side; tac)).
Ltac stepret_new F D k tac := wh_with ltac:(fun _ => stepret_old F D k ltac:(wh_clear_side; tac)).
Ltac stepsd_new F D aa vv oktac :=
  wh_with ltac:(fun _ =>
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; wh_clear_side; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | wh_reveal; oktac ]
  | step_simpl ]).
Ltac stepld_new F D vv rtac :=
  wh_with ltac:(fun _ =>
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; wh_clear_side; imm_norm; rewrite ?v_addi_0; sp_norm; wh_reveal; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm_old ]).

(* [comment removed for export] *)
Module OptIn.
#[export] Ltac StepTac.check_closed_term p ::= wh_check_closed_term p.
#[export] Ltac WalkTac.gres ::= wh_gres.
#[export] Ltac WalkTac.vnorm ::= vnorm_new.
#[export] Ltac StepTac.stepi F D ::= stepi_new F D.
#[export] Ltac StepTac.stepiv F D vv tac ::= stepiv_new F D vv tac.
#[export] Ltac StepTac.stepiwv F D vv tac ::= stepiwv_new F D vv tac.
#[export] Ltac StepTac.stepj F D ::= stepj_new F D.
#[export] Ltac StepTac.stepjr F D tv tac ::= stepjr_new F D tv tac.
#[export] Ltac WalkTac.stepn F D ::= stepn_new F D.
#[export] Ltac WalkTac.stepv F D v ::= stepv_new F D v.
#[export] Ltac WalkTac.stepb_tk F D tac ::= stepb_tk_new F D tac.
#[export] Ltac WalkTac.stepb_ft F D tac ::= stepb_ft_new F D tac.
#[export] Ltac WalkTac.stepret F D k tac ::= stepret_new F D k tac.
#[export] Ltac WalkTac.stepsd F D aa vv oktac ::= stepsd_new F D aa vv oktac.
#[export] Ltac WalkTac.stepld F D vv rtac ::= stepld_new F D vv rtac.
End OptIn.
