(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim DrainSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_StepTac () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C6ARocqVerifyHarness?AgentSubmission2K52AS7SeqExec8v_addi_mK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic3notC45stdpp9bitvector;definitions5bv_eqI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00C6ARocqVerifyHarness?AgentSubmission2K52AS8PropExec8u8_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07c6ARocqVerifyHarness?AgentSubmission2K52AS7StepTac6u_Z2bvI47Corelib4Init5Logic4True00K46Stdlib9micromega5Tauto8GFormula05C45stdpp9bitvector;definitions=bv_wrap_smallc6ARocqVerifyHarness?AgentSubmission2K52AS7StepTac7u_zext8C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqc6ARocqVerifyHarness?AgentSubmission2K52AS7StepTac>byte_neq_lit_uC6ARocqVerifyHarness?AgentSubmission2K52AS8PropExec4c_eqK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordI47Corelib4Init9Datatypes3nat00C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitionsCbv_wrap_add_idemp_rC45stdpp9bitvector;definitions?bv_add_unsignedC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC6ARocqVerifyHarness?AgentSubmission2K52AS8PropExec9u64_rangec6ARocqVerifyHarness?AgentSubmission2K52AS7StepTac<word_add_natC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C6ARocqVerifyHarness?AgentSubmission2K52AS8PropExec6v_addiK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega6VarMap1t03C35stdpp7tactics<f_equal_helpC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC6ARocqVerifyHarness?AgentSubmission2K52AS8PropExec=bv_wrap64_modC56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums1Z03C6ARocqVerifyHarness?AgentSubmission2K52AS8PropExec5v_addC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3oppC6ARocqVerifyHarness?AgentSubmission2K52AS8PropExec5v_subK46Stdlib9micromega7EnvRing5PExpr06C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC6ARocqVerifyHarness?AgentSubmission2K52AS8PropExecMbuild_stack_bytes_within_spanC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC4ELinuxProcessSemantics?LinuxProcessSem3RunFentry_stack_span_boundK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem3RunDentry_stack_span_maxK46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC56Stdlib6ZArith6BinInt1Z3ltbC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool:orb_true_rC46Stdlib4Bool4Bool<andb_false_rC46Stdlib5Lists4List7forallbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDrange_avoids_ro_segsI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00c6ARocqVerifyHarness?AgentSubmission2K52AS7StepTac=ro_segs_belowC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z3lebC47Corelib7Classes9MorphismsDiff_impl_subrelationC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib4Bool4Bool=negb_true_iffI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init5Logic2or02C47Corelib7Classes9MorphismsIiff_flip_impl_subrelation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
Ltac chain_step :=
  first [ eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply MmapSim.twmt_step
        | eapply tmw_step
        | eapply StreamSim.twr_step
        | eapply StreamSim.trd_step
        | eapply WallSim.twt_step
        | eapply WallSim.twe_step
        | eapply DrainSim.tout_step
        | eapply DrainSim.trd_step
        | eapply te_step ].

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP2.
Ltac step_intro := chain_step.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP4.
Ltac check_closed_term p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term:" p "contains an evar"
  else tryif match goal with
             | H : _ |- _ => lazymatch p' with context [H] => idtac end
             end
  then fail 0 "check_closed_term:" p "mentions a context variable"
  else idtac.

Section WithFP5.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP5.
Ltac vm_eval t :=
  let _ := match goal with _ => check_closed_term t end in
  eval vm_compute in t.

Section WithFP6.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP6.
Ltac word_lit p :=
  let u := vm_eval (bv_unsigned p) in
  constr:(@BV 64 u ltac:(vm_compute; exact I)).

Section WithFP7.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP7.
Ltac wlit_replace p :=
  let l := word_lit p in
  replace p with l by (apply bv_eq; vm_compute; reflexivity).

Section WithFP8.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP8.
Ltac wlit p :=
  try (lazymatch p with
       | @BV _ _ _ => idtac
       | _ => wlit_replace p
       end).

Section WithFP9.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP9.
Ltac wlits :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_replace (v_addi a b)
  | |- context [btgt ?a ?b] => wlit_replace (btgt a b)
  | |- context [v_jalr ?a ?b] => wlit_replace (v_jalr a b)
  | |- context [v_auipc ?a ?b] => wlit_replace (v_auipc a b)
  end.

Section WithFP10.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
  | |- MmapSim.twm_pend _ ?st _ _ _ _ => norm_pc_state st
  | |- MmapSim.twm_tail _ ?st _ _ _ _ => norm_pc_state st
  | |- tmw _ ?st _ _ _ _ _ => norm_pc_state st
  | |- StreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- StreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- WallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
  | |- to_exit _ _ ?st => norm_pc_state st
  | |- DrainSim.to_out _ _ ?st => norm_pc_state st
  | |- DrainSim.to_rd _ _ _ _ _ _ _ ?st => norm_pc_state st
  end.

Section WithFP12.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP13.
Ltac step_simpl := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pc.

Section WithFP14.
Context {fx : FPState}.

(* [comment removed for export] *)
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

Section WithFP15.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
    | _ => stepi_search F D
    end
  | step_simpl ].

Section WithFP16.
Context {fx : FPState}.

(* [comment removed for export] *)
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
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP17.
Ltac stepiwv F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_addiw_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP18.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP18.
Ltac stepj F D :=
  chain_step;
  [ reflexivity
  | first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
          | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
  | step_simpl ].

Section WithFP19.
Context {fx : FPState}.

(* [comment removed for export] *)
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
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_Z2bv : forall z, (0 <= z)%Z -> (z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP20"] "h01zh13Hhih23Hlop;2p;1p;3p;4p;6p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9g0022j25Tg002Nj10Tg0033j11Tg003Qj24Tg003nj23Tg004Jj1<Tg004hj2;Tg005Nj32Tg005hj18Tg006Fj47Tg006aj36Tg007Dj29Tg007jj2:Tg008Tj2>Tg009Cj6=Tg009aR0g00:?R1f0R2'5f1R3g00:]#0R4#1R5%04#0#0#0#0R4#1'4'3P0%<4R4f2R6';R7f39202X00%84,45R515161365P3P2C7566A2076e1946,:41>46E=W1W2W0o"). Qed.

(* [comment removed for export] *)
Lemma v_addi_m1 : forall x, (1 <= bv_unsigned x)%Z ->
  v_addi x (-1) = Z_to_bv 64 (bv_unsigned x - 1).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP20"] "h07__arithh14__ffh28__varmaph35__with44__x1h52H1h61xp;1p;2p;4p;8p;3p;7g002Nj10Tg004Jj1JTg00;Bj1<Tg0033j16Tg007jj23Tg0022j21Tg00;ej1=Tg00<Ej1;Tg00<ej2:Tg00=Cj18Tg00=aj17Tg00>Lj22Tg00>oj29Tg00?Rj45Tg00@=j1ITg00@_j8HTg00ACj2GTg00Aej2>Tg00B?j2?Tg005Nj3@Tg00Bkj3ATg00CJj4BTg00D<j1CTg003nj2DTg00DZj4ETg00EUj7FTf1R0g00F9R1g00FXR2P2g00G8R3f0R4g00GXFFp=4g00:]R5#0#0#0#0#0#0#JR6#<%65R71364'1P0P7g009aR8g00H8R9#=R:%;9R91:80%88R;%78R<P1P2P2P3P81287R1g00Hd1985C5,4<R5%I2P5GH1G<3R3P4f2R5g00IKR2g00IkR='>1?45=@2=dg00:?R==A80CBR2b1b2b3W411741170[^48P41365P0O2b0P:P9%C8P;P8128=g00JKP1C5,4<P3P2b1b2b31D=7P4b0CEW5W6o"). Qed.

Lemma v_addi_m16 : forall x, (16 <= bv_unsigned x)%Z ->
  v_addi x (-16) = Z_to_bv 64 (bv_unsigned x - 16).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP20"] "h07__arithh14__ffh28__varmaph35__with44__x1h53H16h61xp;1p;2p;4p;8p;3p;7g002Nj10Tg004Jj1JTg00;Bj1<Tg0033j16Tg007jj23Tg0022j21Tg00;ej1=Tg00<Ej1;Tg00<ej2:Tg00=Cj18Tg00=aj17Tg00>Lj22Tg00>oj29Tg00?Rj45Tg00@=j1ITg00@_j8HTg00ACj2GTg00Aej2>Tg00B?j2?Tg005Nj3@Tg00Bkj3ATg00CJj4BTg00D<j1CTg003nj2DTg00DZj4ETg00EUj7FTf1R0g00F9R1g00FXR2P2g00G8R3f0R4g00GXFFp=4g00:]R5#0#0#0#0R6#0#0#JR7#<%66R61374'1P0P6g009aR8g00H8R9#=R:%;9R91:80%88R;%78R<P1P2P2P3P81286R1g00Hd1985C5,4<R5%I2P5GH1G<3R3P4f2R5g00IKR2g00IkR='>1?45=@2=dg00:?R==A80CBR2b1b2b3W411641160[^48P41375P0O2b0P:P9%C8P;P8128=g00JKP1C5,4<P3P2b1b2b31D=6P4b0CEW5W6o"). Qed.

Lemma v_addi_m32 : forall x, (32 <= bv_unsigned x)%Z ->
  v_addi x (-32) = Z_to_bv 64 (bv_unsigned x - 32).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP20"] "h07__arithh14__ffh28__varmaph35__with44__x1h53H32h61xp;1p;2p;4p;8p;3p;7g002Nj10Tg004Jj1JTg00;Bj1<Tg0033j16Tg007jj23Tg0022j21Tg00;ej1=Tg00<Ej1;Tg00<ej2:Tg00=Cj18Tg00=aj17Tg00>Lj22Tg00>oj29Tg00?Rj45Tg00@=j1ITg00@_j8HTg00ACj2GTg00Aej2>Tg00B?j2?Tg005Nj3@Tg00Bkj3ATg00CJj4BTg00D<j1CTg003nj2DTg00DZj4ETg00EUj7FTf1R0g00F9R1g00FXR2P2g00G8R3f0R4g00GXFFp=4g00:]R5#0#0#0#0#0R6#0#JR7#<%66R61374'1P0P6g009aR8g00H8R9#=R:%;9R91:80%88R;%78R<P1P2P2P3P81286R1g00Hd1985C5,4<R5%I2P5GH1G<3R3P4f2R5g00IKR2g00IkR='>1?45=@2=dg00:?R==A80CBR2b1b2b3W411641160[^48P41375P0O2b0P:P9%C8P;P8128=g00JKP1C5,4<P3P2b1b2b31D=6P4b0CEW5W6o"). Qed.

Lemma v_addi_m48 : forall x, (48 <= bv_unsigned x)%Z ->
  v_addi x (-48) = Z_to_bv 64 (bv_unsigned x - 48).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP20"] "h07__arithh14__ffh28__varmaph35__with44__x1h53H48h61xp;1p;2p;4p;8p;3p;7g004Jj1LTg00;Bj1=Tg00K2j17Tg0033j1KTg007jj23Tg0022j21Tg00;ej1<Tg00<Ej1;Tg00<ej2:Tg00=Cj18Tg00=aj19Tg00>Lj24Tg00>oj2JTg00?Rj46Tg00@=j1HTg00@_j8GTg00ACj2?Tg00Aej2>Tg00B?j2@Tg005Nj3ATg00Bkj3BTg00CJj4CTg00D<j1DTg003nj2ETg00DZj4FTg002Nj15Tg00EUj7ITf0R0#5#5p=0f1R1g00F9R2g00FXR3P3g00G8R4P0g00GXFIp=2g00:]R5#0#0#0#LR6#=%75#0#0#KR71360'1P1P7g009aR8g00H8R9#<R:%;9R91:81%88R;%98R<P2P3P3P4P81487R2g00Hd1J85C6,2<R5%H3P5GG1?<4R4P0f2R5g00IKR3g00IkR='>1@05=A3=dg00:?R==B81CCR3b1b2b3W411701171[^48P01365P1O2b0P:P9%D8P;P8148=g00JKP2C6,2<P4P3b1b2b31E=7P0b0CFW5W6o"). Qed.

Lemma v_addi_m64 : forall x, (64 <= bv_unsigned x)%Z ->
  v_addi x (-64) = Z_to_bv 64 (bv_unsigned x - 64).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP20"] "h07__arithh14__ffh28__varmaph35__with44__x1h53H64h61xp;1p;2p;4p;8p;3p;7g002Nj10Tg004Jj1JTg00;Bj1<Tg0033j16Tg007jj23Tg0022j21Tg00;ej1=Tg00<Ej1;Tg00<ej2:Tg00=Cj18Tg00=aj17Tg00>Lj22Tg00>oj29Tg00?Rj45Tg00@=j1ITg00@_j8HTg00ACj2GTg00Aej2>Tg00B?j2?Tg005Nj3@Tg00Bkj3ATg00CJj4BTg00D<j1CTg003nj2DTg00DZj4ETg00EUj7FTf1R0g00F9R1g00FXR2P2g00G8R3f0R4g00GXFFp=4g00:]R5#0#0#0#0#0#0R6#JR7#<%66R61374'1P0P6g009aR8g00H8R9#=R:%;9R91:80%88R;%78R<P1P2P2P3P81286R1g00Hd1985C5,4<R5%I2P5GH1G<3R3P4f2R5g00IKR2g00IkR='>1?45=@2=dg00:?R==A80CBR2b1b2b3W411641160[^48P41375P0O2b0P:P9%C8P;P8128=g00JKP1C5,4<P3P2b1b2b31D=6P4b0CEW5W6o"). Qed.

Lemma v_addi_m80 : forall x, (80 <= bv_unsigned x)%Z ->
  v_addi x (-80) = Z_to_bv 64 (bv_unsigned x - 80).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP20"] "h07__arithh14__ffh28__varmaph35__with44__x1h53H80h61xp;1p;2p;4p;8p;3p;7g002Nj10Tg004Jj1KTg00;Bj1<Tg00K2j16Tg0033j1JTg007jj24Tg0022j21Tg00;ej1;Tg00<Ej1:Tg00<ej29Tg00=Cj17Tg00=aj18Tg00>Lj22Tg00>oj2ITg00?Rj45Tg00@=j1@Tg00@_j8?Tg00ACj2>Tg00Aej2=Tg00B?j2ATg005Nj3BTg00Bkj3CTg00CJj4DTg00D<j1ETg003nj2FTg00DZj4GTg00EUj7HTf1R0g00F9R1g00FXR2P2g00G8R3f0R4g00GXFHp=3g00:]R5#0R6#0#0#0#0#0#KR7#<%66#0#0#0#0#JR61474'1P0P6g009aR8g00H8R9#;R:%:9R91980%78R;%88R<P1P2P2P3P81286R1g00Hd1I85C5,3<R5%@2P5G?1><3R3P4f2R5g00IKR2g00IkR='=1A45=B2=dg00:?R==C80CDR2b1b2b3W411641160[^48P41475P0O2b0P:P9%E8P;P8128=g00JKP1C5,3<P3P2b1b2b31F=6P4b0CGW5W6o"). Qed.

(* [comment removed for export] *)
Lemma v_addi_nneg_t : forall x imm, (0 <= imm)%Z ->
  (bv_unsigned x + imm < 2^64)%Z ->
  v_addi x imm = Z_to_bv 64 (bv_unsigned x + imm).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP20"] "h02_Hh13_H0h23immh31xp;1p;2g002Nj10Tg004Jj1:Tg00;Bj19Tg0022j24Tg007jj23Tg00KWj21Tg0033j12Tg003Qj28Tg003nj25Tg007Dj26Tg00Aej27Tg00:]#0R0#0#0#0#0#0R1#:R2#9R3g009ag00:?f0'4f2R4,32f1'1%20%21'8'5f3,32/14,62,73W1W0W2W3o"). Qed.

(* [comment removed for export] *)
End WithFP20.
Ltac u_norm := repeat rewrite u_Z2bv by lia.

Section WithFP21.
Context {fx : FPState}.

(* [comment removed for export] *)
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
Context {fx : FPState}.

(* [comment removed for export] *)
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
Context {fx : FPState}.

(* [comment removed for export] *)
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
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
        (* [comment removed for export] *)
        first
          [ reflexivity
          | fail 1 "bveq: the goal is OPEN (it mentions a context "
                   "variable) and kernel conversion did not close it — "
                   "resolve the register and memory projections first "
                   "(getr_resolve, regupd_resolve) and try again." ]
  end.

Section WithFP25.
Context {fx : FPState}.

(* [comment removed for export] *)
Goal v_addi (Z_to_bv 64 5) 3 = Z_to_bv 64 8.
Proof. bveq. Abort.
Goal forall regs (v : word), getr (regupd regs 11 v) 11 = v.
Proof. intros. assert_fails bveq. getr_resolve. reflexivity. Abort.

(* [comment removed for export] *)
Goal forall v : word, exists w : word, w = v.
Proof.
  intros v. eexists.
  check_closed_term (v_addi (Z_to_bv 64 5) 3).
  assert_fails (check_closed_term (v_addi v 4)).
  lazymatch goal with |- ?g => assert_fails (check_closed_term g) end.
  set (k := Z_to_bv 64 7).
  check_closed_term (v_addi k 1).
  set (k2 := v_addi v 1).
  assert_fails (check_closed_term (v_addi k2 1)).
  let u := vm_eval (bv_unsigned (v_addi (Z_to_bv 64 5) 3)) in
  lazymatch u with 8%Z => idtac end.
  (* [comment removed for export] *)
  try (let u := vm_eval (bv_unsigned (v_addi v 4)) in
       fail 1 "vm_eval accepted an open term").
Abort.

(* [comment removed for export] *)
Goal forall v : word, v_addi v 4 = v_addi v 4.
Proof. intros v. wlit (v_addi v 4). wlits. reflexivity. Abort.
Goal forall v : word,
  (v_addi (Z_to_bv 64 5) 3, v_addi v 4) = (Z_to_bv 64 8, v_addi v 4).
Proof.
  intros v. wlits.
  lazymatch goal with |- (@BV _ _ _, _) = _ => idtac end.
  f_equal. bveq.
Abort.

(* [comment removed for export] *)
End WithFP25.
Ltac stepw_addr :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].
Ltac stepw_val :=
  getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs;
  first [ reflexivity | sp_norm; first [ reflexivity | f_equal; lia ] | bveq ].

(* [comment removed for export] *)
Ltac stepw_addr_hyps :=
  getr_resolve; regupd_resolve;
  repeat match goal with
  | H : Sem.reg_get ?R ?r = _ |- context [Sem.reg_get ?R ?r] => rewrite H
  end;
  imm_norm; rewrite ?v_addi_0;
  sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

Section WithFP27.
Context {fx : FPState}.

(* [comment removed for export] *)
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
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
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
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP28.
Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP29.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP29.
Ltac wlit_closed p :=
  check_closed_term p;
  let u := vm_eval (bv_unsigned p) in
  replace p with (Z_to_bv 64 u) by bveq.

Section WithFP30.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP30.
Ltac wlits_closed :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_add ?a ?b] => wlit_closed (v_add a b)
  | |- context [v_sub ?a ?b] => wlit_closed (v_sub a b)
  end.

Section WithFP32.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP32.
Ltac rdn_ext_lit :=
  erewrite rdn_ext;
    [ (* [comment removed for export] *)
    | imm_norm; u_norm; lia
    | let x := fresh "x" in
      let Hx := fresh "Hx" in
      intros x Hx; revert Hx; imm_norm; u_norm; intros Hx ].

Section WithFP33.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma byte_nz_u : forall b : byte, b <> Z_to_bv 8 0 -> (bv_unsigned b <> 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h02b1h12b2h21nh31Hh42Hbh52Hch61bh71zp;1p;2p;3p;6g002Nj13Tg004Jj19Tg00;Bj12Tg007Dj25Tg005Nj30Tg00L4j14Tg007jj21Tg00LMj38Tg00Aej27Tg009Cj66Tg00:]#3#3#3#9R0#2R1f0R2g00:?R3,50R4501#4g009aR1f1R5,10;03R6P5g00M1R7%22R8%25R9g00MOf2R:#2?052f3R;/1:11;5501R<[11:511:2501%2;?0:5[R=f4#2?0;:\<A8:52P2n2001000000120000000W1W0W2P=^19^08^27P2P0P;P4P1P31104R49012X711714110;P5E6O4b3O1W5%46eW4W6o"). Qed.

(* [comment removed for export] *)
Lemma u_zext8 : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01Hh14__x1h22H0h32Hah47__arithh54__ffh68__varmaph75__with86__sat0h96__sat1h:1bp;1p;2p;4p;3p;7p;8g002Nj13Tg004Jj19Tg00;Bj1ATg007jj22Tg00Mjj1QTg0033j14Tg003nj21Tg00MOR0j2?Tg00;ej1>Tg00<Ej1=Tg00<ej2;Tg00=Cj1:Tg00=aj1PTg00>Lj27Tg00>oj2OTg00?Rj46Tg00@=j1LTg00ACj2CTg00Aej2BTg00B?j2@Tg005Nj3DTg00Bkj3ETg00CJj4FTg00Nfj2GTg003Qj2HTg00ONj3ITg00P2j3JTg00PUj3KTg0022j2<Tg00EUj7MTg00@_j8NTg00:?R1f0R2'<p=0f1R3g00F9R4g00FXR5P5g00G8R6P2g00GXFMp=5f3R7P4P5P5P6f2R4P3P2GNp=8g00:]R8#3R9#3#3R:#9R;#A12;2R<%Q2R=%0<%3:#3#3R:#3#3#4R>,1<'?R<P012;3R?#011?>12;4#0P212;7R7#0R?f4,2;R@/1>g009aRAg00H8RB#>RC%=BRB1;A3RD%:ARE%PARFPA17A1g00Hd1OA8R8C6,5FRG%L5R5PGC81CF6R6P2P4g00IKRGg00IkRH'B1@24=DGHdAEA13CFRHb5b6b7W1%02%03[^1AP2f6,2;RGP4O2b4W2W0P3P2O2n2001000000120000000b0P=P<%49R9%4:R<'G1119%0<1H9<R=,11[[%09R1g00QNRIAI9<3UW3%0=\I^31P0P?117>11@=P4f5,2;#011G>PCPBPDPEPFPAP8g00JKRE17A>C6,5FP5PAP8PE17A9%9:5JAC6,5FC8P6PHb5b6b7X1A112>113=[^1AP2f8,2;P3O2b4W2W0P3P2O2n2001000000120000000b8b9b03KW:o"). Qed.

(* [comment removed for export] *)
Lemma zext8_byte : forall b : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01Hh14__x1h22b1h32b2h41nh51zh62H0h77__arithh84__ffh98__varmaph:5__with;1bp;1p;3p;2p;4p;7p;6p;8g002Nj12Tg004Jj1>Tg00;Bj14Tg005Nj31Tg007jj20Tg00LMj3OTg007Dj2<Tg004hj2;Tg00Mjj1CTg0033j1ATg003nj25Tg00MOR0j26Tg00;ej1TTg00<Ej1STg00<ej2RTg00=Cj1NTg00=aj1LTg00>oj2KTg00>Lj2:Tg00?Rj48Tg00@=j1ETg00Qjj7DTg00ACj2FTg00Aej2GTg00B?j2HTg00Bkj3BTg00CJj4ITg00RNj3JTg00S:j1@Tg009Cj6=Tg008Tj2MTg0022j2?Tg00EUj7PTg00@_j8QTg00:?R1f0R2'?p=3f1R3g00F9R4g00FXR5P5g00G8R6P2g00GXFPp=9f3R7P4P5P5P6f2R8P3P2GQp=7g00:]R9#2#2#2R:#>R;#4g00M1R<%42R=%43R>P0%48?132g009aR?1078107331R@[1083108251?%47?183[RAf4RB#4?178\@AO832P2n2001000000120000000W3W2W4PA^3>^2=^4<P2P;%2:#2#2R:#>R<10;3R=,<<'0R<,<;R>P3P?1;;<10;8RA91?2X5?P?P=1;;2=1?AX5?%C3%3=%2:#2#AR:,5='6P0%3A15A:10;7R7#3157:'6P210;B#3f5,0;/5:g00H8RB#T%SB1R?3%N?%L?RBP?1K?9R9g00JK1:?:C8,9BR7%E5RAPBP?1:?1g00HdP9C8,9BR9PAPBP4P5P5P6P9P7FDC7C71FB6P2P8g00IKRBg00IkR6'G1H28=1B6dAB?13CIb8b9b:X1?152:%33%38158:'6[[^1?P2f7,0;P3P8O3b7W6W0P3P2O2n2001000000121000000b09J;=P<%@3E=10;>1M;<E=O4b0W;o"). Qed.

(* [comment removed for export] *)
Lemma byte_neq_lit_u : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z -> (bv_unsigned b <> z)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01zh11Hh24__x1h32b1h42b2h51nh62H0h72Hbh82Hch92Hzh:7__arithh;4__ffh<8__varmaph=5__with>1bp;1p;2p;3p;4p;7p;6p;8g002Nj11Tg004Jj1VTg00;Bj12Tg0033j1UTg003nj26Tg00MOR0j27Tg007Dj28Tg005Nj33Tg00L4j1=Tg007jj20Tg00LMj3@Tg004hj2TTg00Aej2?Tg00T4j1STg00T]j2OTg00;ej1NTg00<Ej1LTg00<ej2JTg00=Cj1ITg00=aj1HTg00>oj2FTg00>Lj2;Tg00?Rj4>Tg00@=j1ETg00Qjj7GTg00ACj2DTg00B?j2KTg00Bkj3CTg00CJj4BTg006aj3MTg009Cj69Tg008Tj2ATg0022j2PTg00EUj7QTg00@_j8RTg00:?R1f0R2'Pp=4g009aR3f1R4;32p=5P4g00F9R5g00FXR6P6g00G8R7P2g00GXFQp=:f3R8P5P6P6P7f2R9P4P2GRp=<g00:]R:#1#1#1R;#VR<#2R=%42%1;#1#1#1#1#UR;,62R>'718<493=9#=10<8/59R=P4g00M1R?%22R@%24RAP0%29?34210891084'5RB[10941092'5%28?394[RCf4RD#2?389\BA@942P2n2001000000120000000W4W3W5PC^4A^3@^5?P2P<f5R?18<DR@P3PD18<?,0<,52X03P31T<DRA15?2X03RCP3PDPC1?3D%S<RC,ODP0%4D16D;%4?16?;'7P8f6#4f7/6;g00H8R8#N%L81J34%I3%H3R8P31F3:R:g00JK1;3;C>,:8R0%E6RBP8P31;31g00HdP:C>,:8R:PBP8P5P6P6P7P:P0FGC<C<1D87P2P9g00IKR8g00IkR7'?1K29=387dAC314CBb;b<b=X23%44%49169;'7[\>^23P2f9P4P9O3b:W6W1P4P2O2n20010000001200000009MDCE915DAe10<@1A<DE910<?P4E9O4b1O1W8%==eW7W9X03W>o"). Qed.

(* [comment removed for export] *)
Lemma c_eq_zext_lit_false : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z ->
  c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 z) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h04__x1h11Hh21zh32H0h42Hah57__arithh64__ffh78__varmaph85__with91xh:1yh;2Hbh<2Hzh=6__sat0h>6__sat1h?1bp;1p;2p;3p;4p;6p;7p;8g002Nj12Tg004Jj1?Tg00;Bj1GTg0033j1<Tg003nj21Tg00MOR0j2MTg007Dj24Tg005Nj33Tg00L4j16Tg00U=j2;Tg00UZj2@Tg007jj25Tg00V;j4WTg00;ej1VTg00<Ej1UTg00<ej2TTg00=Cj1PTg00=aj1LTg00>Lj28Tg00>oj2KTg00?Rj4:Tg00@=j1FTg00ACj2ETg00Aej2HTg00B?j2DTg00Bkj3ITg00CJj4JTg00Nfj2CTg003Qj2BTg00ONj3NTg00P2j3ATg00PUj3OTg009Cj6=Tg00S:j1QTg00W<j2RTg0022j2STg00EUj7YTg00@_j8XTg00:?R1f0R2'Sp=0g00IKR3g00X4732p=7f1R4g00F9R5g00FXR6P6g00G8R7P2g00GXFYp=9f3R8P5P6P6P7f2R5P4P2GXp=>g00:]R9#2R:#2#2R;#?R<#GR=g009aR>%02R?%2;#2#2R;#2#2#<R@,12RA'M14<493=5#6P01;42#7A3>54#6R=[A3>42#61;54#7[RB1;85#7\=1@42P2n2001000000120000000X:>X9>PB^:>^9>P2%?;RBf4R=,5<RC,4B'5RD14B8,5BREP>PC14B=,5B93>2#6X2>P>P8f5RC,5<=3>2#6X2>P=P8P5P4CWPEP0%08118@%0=P5%0CREf6RF/1@g00H8RG#VRH%UGRG1T>4RI%P>RJ%L>RKP>18>1g00Hd1K>9R9C:,9KRL%F6R6PLC>1EK7R7P2P5g00IkRL,H31D25=33LdAI>14CJRLb6b7b8X0>%04\?^0>P2f8R?P5O2b5W3W1P4P2O2n2001000000120000000%<:R:%<;R;'C111:%0;1B:;R3,11[[%0:R1g00QNRMAN:;4UW4%03\M^41P0PE11C@11F3P=f7#011?@PHPGPIPJPKP>P9g00JKRJ18>@C:,9KP6P>P9PJ18>:=A>BC:,9KC>P7PLb6b7b8X0>1143\A^0>P2f:P4O2b5W3W1P4P2O2n2001000000120000000b=b>5O8E=PD%Q=E=O3b115<8,4B14B5'R#7eW;W<W2W?o"). Qed.

(* [comment removed for export] *)
Lemma u_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  bv_unsigned (nat_to_word n) = Z.of_nat n.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h04__x1h12Hah27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with84cstrh92Hnh:1np;1p;2p;3p;4p;7p;8g00XTj13Tg002Nj11Tg0033j16Tg003Qj2=Tg003nj22Tg00Y4j1OTg00Nfj2ATg00ONj3?Tg00;ej1>Tg00<Ej1<Tg00<ej2;Tg00=Cj1:Tg00=aj1QTg00>Lj29Tg00>oj2PTg00?Rj48Tg00@=j1NTg00ACj2CTg00Aej2BTg00B?j2@Tg005Nj34Tg00Bkj3DTg00CJj4ETg004Jj1FTg00P2j3GTg00PUj3HTg00YYj1ITg007jj2JTg0022j2KTg00EUj7LTg00@_j8MTg00:?R0f0R1'Kp=0f1R2g00F9R3g00FXR4P4g00G8R5P1g00GXFLp=5f3R6P3P4P4P5f2R3P2P1GMp=7g00ZT%31g00:]R7#1R8#6R9%18#1#1#1#1R8#6R:'=R;'2%32R<%O2R=%0<R>1A9:R?1209%0:120;[[R@%09RAg00QNRBA?9:2UW1R:%0;\B^1ARAg009aRBg00H8RC#>RD%<CRC1;B2RE%:BRF%QBRGPB19B0g00Hd1PB7R7C8,5GRH%N4R4PHC71CG5R5P1P3g00IKRHg00IkRI'B1@13=4HIdADB02CER0b3b6b7W0%01%02[^0BP1f5#3RIP6O2b2b4b5b8P=P>P?P@P:PAPDPCPEPFPGPBP7g00JK19B9%F8R85GBC8,5GRGP4PGC7P5P0b3b6b7X0B121;122;[^0BP1PIf4O2b2b4b5b83H%I2,J8=4B<eW9W:o"). Qed.

(* [comment removed for export] *)
Lemma word_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01zh11nh22b1h32b2h41Hh51ap;1p;3p;2p;6g002Nj15Tg004Jj1ATg00;Bj14Tg005Nj36Tg007jj20Tg00LMj3=Tg00YYj1<Tg00[3j3:Tg00XTj19Tg00KWj23Tg007Dj28Tg004hj21Tg00Aej2@Tg00[Xj3?Tg009Cj67Tg008Tj2;Tg00\Jj3>Tg009aR0f1R1f0R236p=2g00:]#5#5#5#5#5#5#AR3#4g00ZTg00M1R4%42R5%41R6g00MOf2R7#4?612f3R8/071081'2R9[10711072'2%48?671[R:f4#4?687\9A=712P2n2001000000120000000W3W2W1P:^36^25^14P2P3%<19:37R41037R5%91R1'3R6,83R:P01831R9,03R;,35,131038R8%97R<'3R=,83,03R>,22X00P01131R?1382,13/2>X00P01136R>113<,38,13/22X00P0P>113=,22X001@0>135?,13A?351E7103:R:1;36E7P;1;31E7A:379,03A>379E71034/2:eO4b4W1W5o"). Qed.

(* [comment removed for export] *)
Lemma word_add_nat_0 : forall x : word, x + nat_to_word 0 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h04__x1h11xh21Hh37__arithh44__ffh58__varmaph65__with71nh81yh92H0h:2Hah;6__sat0h<6__sat1h=2b1h>2b2h?1bh@1mhA1zp;1p;3p;2p;4p;<p;6p;Bp;7p;8g002Nj17Tg004Jj1eTg00;Bj16Tg005Nj39j1ETg007jj20Tg00LMj3WTg00YYj1QTg00[3j3LTg00XTR0j1>Tg00KWR1j23Tg007Dj2FTg00]8j1<Tg00]Vj4bTg00Aej25Tg00^9l<=Tg00;ej1VTg00<Ej1UTg00<ej2TTg00=Cj1PTg00=aj1OTg00>oj2MTg00>Lj2?Tg00^^j3KTg00?Rj4:Tg00ACj2ITg00B?j2JTg00Bkj3HTg00CJj4GTg00_Aj4;Tg00_lj1NTg0033j1@Tg003Qj2RTg003nR2j21Tg00MOR3j2STg0022R4j2DTg00Nfj2cTg00ONj3aTg00@=j1_Tg00P2j3\Tg00PUj3[Tg009Cj6ATg00`ij2YTg00ahl<]Tg00bMlB^Tg00EUj7XTg00@_j8`Tg009aR5f1R6f0R739p=4g00ZTR8P5P5P5P0P0f3R0f2R9P6g00c3R:g00:?R;P7M<]p=ZP5P5P5P5P5P5P1P7P6P9P1P0f4R1f5R<f6R=f7R>P;f8MB^p=BP6g00F9R?g00FXR@P@g00G8RAP7g00GXFXp=81D;7p=2P5P5P4P<P4P1P;P;P0P9P6P7M<=p=dP0P?P@P@PAP9P6P7G`p=Cg00:]R?#7R4#7#7#7#7#7RB#eRC#6RDg00M1RE%67RF%66RGP3%69?96710091006'4RH[10961097'4%60?996[RI%61?909\HAW967P7n2001000000120000000W>W=W7PI^>G^=F^7EP7PC%Q:9LC6REP6PD10C6RF%>:RG'3RI,FCRH10C710C9R0'4X?DP5PI1470XA514IF13F;RD/4FP5P5%E5RJP7X15RKPJ1467#<X85X15PIPDPKPKPKP5P5g00cR1367Cb,55X@5X75RDPFPF155FRJPGPKPK%>7,55X18155;R8CZRLM9BPFPFPJM<=g00H8RJ#VRM%UJRJ1T56RN%P5RO%O5RPP51M5?R?1?5;RQ5K5RRg00d6P?C:'81IPARAP7P9g00IKRSg00IkRT'51J79=9STdAH5;6CGRTb4b5b6X05137;/47^05P7P0O1b3C;10CH%N6RH%2F%@4R4%@BRB'RRS,1F'SRF130GRU#2130;RV#2PK1D67#<X85X15P8PUPVPKPKPKPDP0P01550PGPLM9BRLEd1c4BRG11;4%2B11;S[[R0%24RDg00QNR8Aa4B6UW:RB%2S\8^:DRDP310C1R1#2R8111SR110C</3;R<#2P910C=#2R=10C>/1SR>PMPJPNPOPPP5PQg00HdRWP?C:,8P%_@R@P5PQPWPRC:,8PCCPAPTb4b5b6X05%27136;R;#2[^05P7f9,0CRWP9O2b3W9W2P6P7O2n2001000000120000000b;b<C;b2PHPF11US11VSP5P5P2PKP21167#<X85X15PUPVPLPSPS155SM<=PGP0PBPDP3P8P111<SP9PMPJPNPOPPP5P?g00JKR?1?54=\5CRCC:,8PP@P5PRP?PCC:,8PCCPAPTb4b5b6X05117S11;S[^05P7PWP6O2b3X9>X2=P6P7O2n2001000000120000000b;b<C;b25[IEAPE1Y6:EAO4b2W1o"). Qed.

(* [comment removed for export] *)
Lemma word_add_nat_1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 1 = a + nat_to_word (S m).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01zh11xh21nh34__x1h44__x2h51bh62b1h72b2h81mh91Hh:7__arithh;4__ffh<8__varmaph=5__with>1ah?4cstrh@1yp;1p;2p;3p;4p;<p;7p;8p;6p;Bg002Nj1;Tg004Jj1gTg00;Bj1:Tg007jj22Tg00XTR0j16Tg00KWR1j20Tg007Dj29Tg0033j1ATg00d]j2@Tg00eWR2j1?Tg00YYj1>Tg00[3j3=Tg005Nj35j1[Tg00LMj3cTg004hj24Tg003Qj2]Tg00T]R3j23j1JTg00Aej2CTg00]8j1ZTg00]Vj4YTg00^9l<UTg00Y4j1TTg0022j2STg00;ej1RTg00<Ej1NTg00<ej2MTg00D<j1OTg00f6j4LTg00=Cj1PTg00=aj1QTg00>oj2FTg00^^j3<Tg00>Lj2KTg00?Rj4fTg00EUj7eTg00ACj2dTg00B?j2bTg00Bkj3aTg00CJj4`Tg00_Aj4_Tg00fTj8HTg00g1j3^Tg00gXj1DTg008Tj2ETg00`ij2GTg009Cj6BTg00ahl<ITg00bMlB\Tg009aR4f1R5f0R635p=11C46p=8g00ZTR7P7P4P4P2P0P0f3R2g00hYf2R8P5P6M<Ip=XP7P4P4P4P0P0f5R0f4R9P2P8P5P6M<Ip=WP4P4P4P4P4P4P1P6P5P8P1P2P9P0f6f7f8f9MB\p=VP4P9P2P8P5P6EBp=7g00:]R0#;R1#;#;#;#;#;R:#gR;#:R<P<12;5R=%66R>'0,9;R?%A0R@,@6%?5RA#>9=;855<X5<P<%?6RB#6,0=,9;R=12;8RC%65RD'0RE,9;RF/@@=5<6X5<g00M1RG%:6RH%:5RIg00MO%:8?55612281225'1RJ[12851286'1%:2?585[RK%:9?528\JAc856P6n2001000000120000000W7W6W2PK^7I^6H^2GP6P;12;FRF/0@RG,9;RH%6ARI,0CRK,9;RJ14;G12;2RL%?8#6'0RM,9;,2;RN,16X0414;ERO106@RP,4;/1NX0414;KRN%68,0LRL,4;/0@,4;/16X0410O@RQ%A1%A:']R:'314;MRR,16X0413E:RS13P:/1RX0413K:13L:/0@/3:/16X0410E@RL/3:13M:,16X04P4P4%JL%JKP:P:P4P4\4RMP3P3PLPKPM\4/C311LK10D@R3,0CRM,1LP4P4%[4RRP6X14RTPR1156#ZX@4X14PLPL%8LPKPMPTPTPTP4P4g00cR1056CY#8X84X24PCPC%8CPIP3PTPT%8>X17PAP3PPX14P5PD%8DCXEWM:VM<U%T5g00:?RP/SDg00H8RD#R%NDP41M48P5%O4CL%P4%Q4RDg00F9g00FXR3P3g00G8R3P41F40R01F41R15<41K4@RA5<4g00d6A<41A9<40Cfg00GXFe1dD3P6P8g00IKR3g00IkRD'C1b68=53DdAa4P5C`b;b<b=X34X441065/0@105@,06'1^34^44P6%6212;9O2b:b?C_GH%8:GH10S@/3:A^E@:D7PN%DKD7PO%DED714;Q%DQD712;J1E;KD7PF1E;ED712;H1E;GD7O4b91@?@=5<=e%>B9=;51G5BEB%>69=;51G56EBX87W>o"). Qed.

Lemma word_add_nat_m1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word (S m)) (-1) = a + nat_to_word m.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01zh11xh21nh34__x1h44__x2h51bh62b1h72b2h81mh91Hh:7__arithh;4__ffh<8__varmaph=5__with>1ah?4cstrh@1yp;1p;2p;3p;4p;<p;7p;8p;6p;Bg002Nj19Tg004Jj1hTg00;Bj1:Tg007jj22Tg00eWR0j1ETg00XTR1j17Tg00KWR2j20Tg007Dj2;Tg00i=j1YTg00d]j2DTg00YYj1>Tg00[3j3=Tg005Nj35j1\Tg00LMj3eTg004hj24Tg0033j1BTg003Qj2^Tg00T]R3j23j1ITg00Aej2?Tg00]8j1[Tg00]Vj4ZTg00^9l<VTg00Y4j1UTg0022j2TTg00;ej1STg00<Ej1RTg00<ej2QTg00D<j1NTg00f6j4OTg00=Cj1PTg00=aj1MTg00>oj2FTg00>Lj2GTg00^^j3<Tg00?Rj4gTg00EUj7fTg00ACj2dTg00B?j2cTg00Bkj3bTg00CJj4aTg00_Aj4`Tg00fTj8JTg00g1j3_Tg00gXj1@Tg008Tj2ATg00`ij2KTg009Cj6CTg00ahl<LTg00bMlB]Tg009aR4f1R5f0R635p=11?46p=6g00ZTR7P7P4P4P0P1P1f3R0g00hYf2R8P5P6M<Lp=XP7P4P4P4P1P1f5R1f4R9P0P8P5P6M<Lp=WP4P4P4P4P4P4P2P6P5P8P2P0P9P1f6f7f8f9MB]p=HP4P9P0P8P5P6ECp=8g00:]R1#9R2#9#9#9#9#9R:#hR;#:R<P<12;5R=%E6R>#7'0,;;R?%Y1R@,D6%>59=;855<X5<P<%76RA,0=,;;R=12;8RB%E5RC#7RD'0RE,;;RF/D@=5<6X5<g00M1RG%:6RH%:5RIg00MO%:8?55612081205'1RJ[12851286'1%:0?585[RK%:9?508\JAe856P6n2001000000120000000W7W6W2PK^7I^6H^2GP6P;12;FRF/0@RG,;;RH%75RI,0BRK,;;RJ14;G12;0RL%78'0RM,;;,2;RN,16X0414;ERO106@RP,4;/1NX0414;KRN%E8#7,0LRL,4;/0@,4;/16X0410O@RQ%B2%B:'^R:'314;MRR,16X0413E:RS13P:/1RX0413K:13L:/0@/3:/16X0410E@RL/3:13M:,16X04P4P4%IL%IKP:P:P4P4\4RMP3P3PLPKPM\4/?311LK%B1R3,0IRM,0BRR/0@RP/1KP4P4%\4RTP6X14RUPT1156#[X@4X14PLPPPUPUPUP4P4g00cR1056CZ#6X84X24RPPEPRPUPUPUPPPBPB%6BPDPMPUPU%6AX17PCPM1063X14P5PI%6ICXEWM:HP@P@%6@M:HPKPK%6KM<V%U5g00:?RM/TIg00H8RI#S%RIP41Q48P5%N4CO%P4%M4RIg00F9g00FXRCPCg00G8RCP41F41R11F42R21G435<45<41G4@5<4g00d6A<412Cgg00GXFf1dICP6P8g00IKRCg00IkRI'?1c68=5CIdAb4M5Cab;b<b=X34X441053,06/0@1065'1^34^44P6%7012;9O2b:b?C`GJ%6:GJ10S@/3:A_E@:D8PN%@KD8PO%@ED814;Q%@QD812;J1A;KD8PF1A;ED812;H1A;GD8O4b91D?@=5<=e%>69=;51K56EC%>>9=;51K5>ECX87W>o"). Qed.

(* [comment removed for export] *)
Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h04__x1h14__x2h22b1h32b2h41nh51zh61Hh77__arithh84__ffh98__varmaph:5__with;1xh<1yp;1p;3p;2p;4p;7p;8p;6g002Nj13Tg004Jj1MTg00;Bj12Tg005Nj31Tg007jj20Tg00LMj3ITg00i[j2ATg00[3j35Tg00KWj24Tg004hj26j1=Tg00Aej27Tg00;ej1<Tg00<Ej1LTg00<ej2KTg00D<j1JTg00f6j4HTg00=Cj1ETg00=aj1CTg00>oj29Tg00^^j3:Tg00?Rj4BTg00EUj7@Tg00ACj2?Tg00B?j2DTg00Bkj3>Tg00CJj4FTg00fTj8GTg00\Jj38Tg009Cj6;Tg00:]R0#3R1#3#3#3#3#3#MR2#2R3g00M1R4f0R5#2R6f1R7#2R8g00MOf2R9#2?175g009aR:f3R;/0910;731R<[1097109551:%2;?197[R=f4#2?1;9\<AI975P5n2001000000120000000W3W2W4P=^38^26^44P5P21A97A5279R4P:1029R61027R8'4R=,62A529;,0291:5X5:P:1486R8,62102;R;/46,62=1:5X5:P:P:%=2R<P<P=P8P:\:/7<g00H8R<#<%L<P:1K:9P7%J:CH%E:%C:R<g00F9g00FXR8P8g00G8R8P:19:0R019:1R15::g00d6A::10CBg00GXF@1?<8P5P9g00IKR8g00IkR<'71D59=18<dg00:?=>:7CFb8b9b:X0:X1:1457147551:^0:^1:P5P6P;O2b7GG1024A8279E;A5297,02A8297E;O4b6X<3W;o"). Qed.

(* [comment removed for export] *)
Lemma v_add_wrap : forall x y : word,
  (2^64 <= bv_unsigned x + bv_unsigned y)%Z ->
  v_add x y = Z_to_bv 64 (bv_unsigned x + bv_unsigned y - 2^64).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01zh12Hah27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with84__x1h94__x2h:2b1h;2b2h<1nh=1Hh>2Hwh?1xh@1yp;1p;2p;3p;4p;8p;6p;7g002Nj14Tg004Jj1`Tg00;Bj15Tg0033j1=Tg003Qj2_Tg007jj20Tg00KWj23Tg0022j29Tg005Nj31Tg00LMj3KTg007Dj2:Tg00jTj2;Tg004hj27Tg00T]R0j28j1DTg00k1j2YTg00Aej2>Tg00Nfj2XTg003nj2CTg00ONj3WTg00;ej1VTg00<Ej1STg00<ej2RTg00D<j1QTg00f6j4PTg00=Cj1OTg00=aj1NTg00>oj2?Tg00^^j3ATg00>Lj2<Tg00P2j3JTg00kNj3LTg00l1j3MTg00?Rj4@Tg00ACj2ITg00B?j2HTg00Bkj3TTg00CJj4UTg00fTj8GTg00lTj6^Tg00m8j4]Tg00mYj6ZTg00gXj1ETg009Cj66Tg008Tj2FTg00i[j2[Tg00EUj7\Tg009aR1f1R2f0R331p=2P2g00F9R4g00FXR5P5g00G8R6P3g00GXF\p=Bg00:]R7#4R8#4#4#4#4#4R9#`R:#5R;%=8R<%=9R9'_R=10:2R>10:3'3'9g00M1R?%53R@%52RAg00MOf2RB#5?123f3RC/0B10C2'2RD[10B210B3'2%5C?1B2[REf4RF#5?1CB\DAKB23P3n2001000000120000000W;W:W<PE^;A^:@^<?P3P:10:CRC10:BR?'3R@,::RA1;@=RE,::RDP117:@RG10:F/3CRC/;=RF,::,0:,23X01P117:ERH17:C/23X01P118@=17:F,23X01P118E=RF18C=/23X01RCP1%=7RI/Y=RJ,3ERK/8=PCP1P1%D@%DKP=P=P1P1\1RCP0P0P@PKPC\1/>01X<9R0g00:?RC/C<19C91CC=[[RK19C<RLg00QNRMAW<92UW1R919C=\M^1LRLg00H8RM#VRN%SMRMP11R1BP2%Q1ROCP%O1RP%N1RQP11?171?185A1R8g00d6R71<1<=J1:R<9L181<1I=M1<5A1C@'B1IQ6R8P3PBg00IKRRg00IkRS'>1H3B=1RSdAT1C2CURSb3b6b7X81X911332RR1;R=/3J'2^81^91P3f5,0:f6,0:O2b2b4b5GG1>1=GGPFPEPIP=P0PKP9PLPNPMPOPPPQP4P5P5P6P1P<P71<1CC@,BQE^P8PSb3b6b7A11=Cg00n5[P3b2b4b5C]EZPH%EEE6PG%E@E610:D1F:EE610:A1F:@E6O4b=1[B213?>/;=,::51;eW>X@;W?o"). Qed.

(* [comment removed for export] *)
Lemma v_sub_0_neg : forall y : word,
  v_sub (Z_to_bv 64 0) y = Z_to_bv 64 (- bv_unsigned y).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01yp;1p;2p;3g002Nj10Tg004Jj18Tg00;Bj13Tg007jj22Tg00nRj17Tg007Dj21Tg00Aej26Tg00noj24Tg005Nj35Tg00:]#0#0#0#0#0#0#8R0#3R1f0R2,20#7,10R3,61g00:?,10/42=513eW0o"). Qed.

(* [comment removed for export] *)
Lemma u_neg_small : forall z : Z, (0 < z)%Z -> (z <= 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 (- z)) = (2^64 - z)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h04__x1h11zh27__arithh34__ffh46__sat1h56__sat2h68__varmaph75__with82Hah91Hh:2Hzh;3Hz0p;2p;1p;3p;4p;7p;6p;8g003nj25Tg002Nj12Tg0033j1<Tg003Qj2ATg0022j24Tg004Jj1UTg00nRj19Tg004hj2GTg00jTj26Tg005Nj30Tg00T]j27Tg00Nfj2?Tg00ONj3>Tg00;ej1bTg00<Ej1WTg00<ej2VTg00=Cj1TTg00=aj1QTg00>Lj28Tg00P2j3LTg00>oj2KTg00kNj3HTg00i=j1FTg00l1j3ETg00^^j3DTg00ohj2CTg00?Rj41Tg00ACj2BTg00Aej2ITg00B?j2JTg00Bkj3@Tg00CJj4MTg00k1j2NTg00KWj2:Tg00@=j1OTg00Qjj7PTg00MOj2RTg006aj3STg00D<j1aTg00lTj6`Tg00m8j4_Tg009Cj6;Tg00mYj6XTg00gXj1YTg007Dj2ZTg007jj2[Tg008Tj2\Tg00EUj7]Tg00@_j8^Tf1R0g00F9R1g00FXR2P2g00G8R3f0R4g00GXF]p=3f3R5P1P2P2P3f2R6P0P4G^p==g009aR7g00:?R8/54g00:]R9#2R:#<R;%2:#2#2#2#2R:#<R<'AR=,40P7%U:R:%96R>'GR?16=5R@9074X17RAP717>=PA1?;<RA158;148<158=[[RB148;RCg00QNRDA>;<0UW8R<148=\D^8CRCg00H8RD#bRE%WDRD1V70RF%T7RG%Q7RHP7187;=L7:R;1K79RI5H7RJ%F9R9,87=E7;5D7g00d6RK1C7IC1'31BH3RLP4P6g00IKRMg00IkRN'I1J46=0MNdA@780CMRNb3b6b7X0716=41N9=RM':%94507^07P4f5ROO1b2b4b516=6R6/:M=07>P71:@MRM174=f4RP,6=RQ507X17P717@=A074QX17PAPBP<PCPEPDPFPGPHP7PIg00HdRFP;C1,3H%O2RQPHP71878RRg00JKRSPIC1,3HPQPHP1P2P2P3P7PRPFPJC1,3HP7PJPSP;C1,3HFPC=C=PLPNb3b6b7X07144=15801486156='R[[^07P4f6PPPOO3b2b4b59S@=17M=P@P9P=PAPBP<PCPEPD%a7PGPHP1P2P2P3P7P;PKPRC1,3HE`PLPNb3b6b7A07=8g00n5[P4b2b4b5C_E;%95P4EXb9P?%Y>E;1Z:>,[:1\:>E;W:W;W1o"). Qed.

(* [comment removed for export] *)
Lemma v_addi_neg_S : forall d : nat,
  v_addi (Z_to_bv 64 (- Z.of_nat (S d))) 1 = Z_to_bv 64 (- Z.of_nat d).
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01zh11xh21nh34__x1h42b1h52b2h61Hh77__arithh84__ffh98__varmaph:5__with;4cstrh<1dh=1mh>1yp;1p;3p;2p;<p;4p;7p;8p;Bp;6g00;Bj1:Tg005Nj3<j1ZTg007jj25Tg00LMj3fTg002Nj1;Tg004Jj1YTg00eWR0j1>Tg00XTR1j16Tg00nRR2j12Tg007Dj29Tg0033j1=Tg00KWR3j21Tg004hj24Tg003Qj2aTg00T]R4j23j1FTg00Aej2BTg00]8j1XTg00^9l<RTg00Y4j1QTg0022j2OTg00;ej1NTg00<Ej1LTg00<ej2KTg00=Cj1JTg00=aj1MTg00>oj2ITg00>Lj2PTg00^^j3CTg00ohj2DTg00?Rj4HTg00EUj7TTg00ACj2eTg00B?j2dTg00Bkj3cTg00CJj4`Tg00_Aj4_Tg00fTj8GTg00g1j3^Tg00gXj1ATg008Tj2@Tg00d]j2]Tg00]Vj4\Tg00ahl<?Tg00bMlB[Tg009Cj6bTg009aR5f1R6f0R73<p=0P5P5g00cRP7C\p=E1B57p=7g00ZTR8P8P5P5P0P1P1f3R0g00hYf2R9P6P7M<?p=WP8P5P5P5P1P1f5R1f4R:P0P9P6P7M<?p=VP5P5P5P5P2P1P:P2P0P9P6P7M<?p=UP5P5P5P5P5P5P3P7P6P9P3P0P:P1f6f7f8f9MB[p=SP5P:P0P9P6P7Ebp=8g00M1R1%:7R3%:6R2g00MO%:9?<6715091506'0R;[15961597'0%:0?<96[R<%::?<09\;Af967P7n2001000000120000000W5W4W2P<^52^43^21P7g00:]R1#;R3#;#;#;#;#;R2#YR<%>6R;#6R:#2R=,9<,5<R>%=1R?'1R@,9<RA%66RB#2RC,9<RD14<@%69#2RE,9<,5<RF,07X0514<=RG117?RH,4</0FX0514<CRF%>9#6#2RI,4</1?,4</07X0511G?RJ%=3%=2'aR2'314<ER3,07X0513=2RK13H2/03X0513C213I2/1?/32/07X0511=?RI/3213E2,07X05P5P5%FI%FCP2P2P5P5\5REP4P4PIPCPE\5/B410IC11B?R4#2RE/1?R3/0CP5P5%Z5RLP7X15RMPL1067#XX>5X15PIP3PMPMPM1167#E#7X=5X25P=PEPMPM%27RE#E#7X15P:P4PMPM%67RM#7X18P;P4PHX15P6PB%7BCWEVEUP?P?%7?M:SPCPC%7CM<R%Q6g00:?R4/OBg00H8RB#N%LB1K56%J5%M5RBg00F9g00FXR;P;g00G8R;P51I51R11P5?R:5C5,D5=C5:g00d61D51CHg00GXFT1eB;P7P9g00IKR;g00IkRB'B1d79=<;BdAc546C`b8b9b:X35%2H/1?/0E^35P7%60O1b7b;C_GG%72GG11K?/32A^=?2D8PF%ACD8PG%A=D814<J%AJD815<D1@<CD8P>1@<=D815<A1@<@D8O4b6%:<%>7#6#2,9</]?%2M,9<3<eX<8o"). Qed.

(* [comment removed for export] *)
Lemma bsb_bound : forall ph (sp : word) (a e : list (list byte)) uid hw rnd,
  valid_argv a -> valid_envp e ->
  (Z.of_nat (length (build_stack_bytes ph sp a e uid hw rnd)) <= 2240000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h04__p1h14__x1h24__x2h31Hh42H0h53Hvah63Hveh77__arithh84__ffh98__varmaph:5__with;1ah<4cstrh=1eh>2hwh?2phh@3rndhA2sphB3uidp;1p;7p;2p;4p;3p;6p;8g002Nj13Tg004Jj1?Tg00;Bj1ATg00<Ej1;Tg010Kj1UTg011Bj1RTg0129j7NTg013Jj75Tg014Pj24Tg00XTj19Tg0150j26Tg0022j22Tg015mj4]Tg00MOj2DTg00Y4j1VTg00eWj1CTg0170j27Tg017Yj3BTg018Bj2QTg00;ej1PTg018nj3OTg00<ej2MTg00D<j1LTg00f6j4KTg00=Cj1JTg00=aj1ITg019Nj6HTg00>oj2=Tg00K2j10Tg0033j1>Tg00>Lj2<Tg00Qjj7GTg00@=j1FTg00ACj2ETg00Aej2STg00B?j2TTg005Nj3\Tg00Bkj3[Tg00CJj4ZTg00?Rj4WTg00EUj7XTg00@_j8YTf0R0#3#3p=1g009aR1f1R2g00HdP0CWp=:P2g00F9R3g00FXR4P4g00G8R5P0g00GXFXp=8f3R6P3P4P4P5f2R7P2P0GYp=@g01:2g00:]R8#3R9#1R:#3#1#?#AR;%?:#AR<#;#;R=g01;2f4R>#U%R>f8R?f7R@f6RAf5RBP>P6P7FNP?P@PAPBP>P6P7F5,4<#916AB'2P@PAP7P2C]g00:?RC16@ARD'2g01<2,2D'Df:RDf9REP?P@PAPBP>F5,4<RB#V%9BRB,2Cp-0RFg00H8RGg00c3RH#CRI#C,71171I171H5B15B1g01=3'Q%PG3O%;GP11M17P2%L1CK%J1%I1RGPGP3P4P4P5PGP3P4P4P5P>EH1=19R9%0:#3#1#0#3#0R:#3#1#0#0#1#0#0#0#0#>R>,<1':,8GFG%F4R4PG1=18R8/:9,8GP4%0:#0#3#1#1#1#1#>R:,<1,:8,8GC@C@1EG5P0P7g00IKRGg00IkR5'S1T07=\G5dA[1C2CZb8b9b:X11X21W0122>,D71227127:[[^11^21^0FP016DER0,2CP0f<f;PDPEP?P@PAF5,4<#9P7P6O5b7b<12B:eb4b3W6W5W@X>;XB;X==W;WAW?o"). Qed.

(* [comment removed for export] *)
Lemma range_avoids_two : forall (s0 s1 : Segment) (a n : Z),
  Z.ltb a (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) = false ->
  Z.ltb a (Z.of_N (seg_base s1) + Z.of_N (seg_size s1)) = false ->
  range_avoids_ro_segs [s0; s1] a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "h01bh12H0h22H1h31ah41nh52s0h62s1h73segp;1p;2p;3p;6g01=_j18Tg005hj13Tg01>]j19Tg00KWj27Tg01?[j22Tg005Nj3<Tg01@8j1:Tg01A:j20Tg01AXj15Tg01B6j21Tg00Aej2ATg01BSj1@Tg009Cj6=Tg01C1j1?Tg00;ej1DTg018nj3>Tg01CQj3CTg01Cmj3BTf0R0g00IkR1'0p=6g00IKR2?<01p=4P2g00X4R3f3R4f2R5f1R6P0E=p=;g01E9R7g009aR8%84#3%94#3'7R9,26=<231259=<23f6R9#:R:%89#3f4R9/74R;'2R</00#5'1f5R=#:R>%8=#3R?/2;R@%9=#3,7?RA,29'0#5'1#6'0#4X0210<3#5,1:10@0#5,1>#6'0#4X02%50R<,1:10@3#5,1>#6'0#4X02%53R@,1:11><#6'0#4X02P2P111>1R<#6,00#4X02P2P1%60,01#4X021A21%:9R2/11%@2E=P<%@>E=11>@112@#6'0#4e%89#3R21745R@'2R>/03%?>C;12?@R@/03%?@C;%99#3,72,24P0C;124AP6C;%:0%80#3R6/2;%90#3,76,29'0#5'1X77%D79>799>7=R=5C7#4eAB=45#4eW2W1X48W3X67W5o"). Qed.

(* [comment removed for export] *)
Definition ro_segs_below (segs : list Segment) (data_base : Z) : bool :=
  forallb (fun seg =>
             seg_writable seg
             || Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) data_base)
          segs.

Lemma range_avoids_ro_above : forall (segs : list Segment) (data_base addr n : Z),
  ro_segs_below segs data_base = true ->
  (data_base <= addr)%Z ->
  range_avoids_ro_segs segs addr n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_StepTac ()) ["WithFP33"] "p'0h03segh16Hbelowh21xh31Hh41Wh51bi001bh61nh71yh84__x1h94__x2h:4__x3h;4__x4h<2b1h=2b2h>5lemmah?1mh@5HaddrhA3HinhB7__arithhC4__ffhD8__varmaphE5__withF4addrhG4cstrhH5cstr0hI9data_basehJ4segsp;1p;2p;3p;7p;4p;8g00<Ej1STg01F8j2mTg0022j24Tg01@8j1<Tg01>]j19Tg01?[j25Tg01A:j26Tg01AXj18Tg01B6j21Tg01CQj3>Tg01G8j3PTg01GOR0j2OTg01Ghj2eTg01HFj7_Tg01Hhj3NTg01IKj27Tg01Ihj3[Tg00Aej2LTg005Nj3?Tg01JYj2ZTg01K9j1YTg01KZj2KTg01L4j2XTg01LVj2WTg01=_j1JTg005hj1=Tg01M6j1ITg00eWj1HTg0170j2ETg017Yj3GTg018Bj2VTg00;ej1UTg018nj3TTg00<ej2FTg00D<j1lTg00f6j4RTg00=Cj1kTg00=aj1jTg002Nj1QTg00>oj2@Tg00K2j1gTg00@=j1dTg00^^j3cTg00ACj2`Tg00B?j2aTg00Bkj3bTg00CJj4^Tg00KWj2ATg01MYj3fTg01Cmj3]Tg00?Rj4\Tg00EUj7hTg00@_j8iTg00IKR1f0R2g00IkR33?p=0%J2#=p=:f2R4f1R5/A2'5p=3%=2,A5p=;g00X4R69?12p=2%92#=p=Bg009aR7P5g00HdP2C\p=CP5g00F9R8g00FXR9P9g00G8R:P2g00GXFhp=Df3R;P8P9P9P:P4P5P2Gip=Mg01E9R8#S1m;4#014;4R<%<2R=%:2R>f4R?;3;%92,;>R@,5?'6#8'1X08RAf5RB5>8#0f6RC9P82RDA3>CB15C@'6#8,1=X08P5O1#0[^28'Op-0REP01e25X7EX2Eg01N3A3>B?15B@'6#8,1=X08=>8C#0f7RE9P82R0A3>EC15E@'6#8,1=X08P5O1#0[^28P2F_W>AN8AB17@B,1=X08RA=>8B#017@E,1=X08P5O1#0\D^28RD'O17@C,1=X08=>8C#0f8,7@,1=X08P5O1#0\0^28;[2W>AN8ABP5O2PDP4P5P2O2%<5%:5%95';/7E'1#0%<4P11L12%<;=?12P1%<B=?12%:CRD%9C';RAf<R='7,15#0%:ER@f;R>73=%9E,;@R@,5='6#8,14#0]1]4P5%<?RE#0%:B%9B';/7>RF,13#01L13RGf:RH93D>15>A'6#8RA,13#0eW1W4%2E116F#0g00MORF1752#01445[RE14521745#0R3[P<\31Z52P5n2001000000120000000X?7X67PE^?7^67P2P@f=REP5O314@EPF%82#0%25R@[%22R3%85#0[RD%84#0\@%Y2P2n2001000000120000000X51PD^51P2f9RD#:RIf>RJ;3E%BD93JI'6PF1652#2%24/K@RI[1K@31645#2[R316;4#2\I1X52P2n2001000000120000000X=1X<1P3^=1^<1P2%:HR1f?R3;3JRI%BH9331R3%2I%23PF1552#21454RF[14251545#2[R315;4#2\F1W52P2n2001000000120000000X77X27P3^77^27P2f@R3%J>RF#=RI%9>';%IFg00:?RF/4I%9=R=#I%==,4Fg00H8R=g00c3RI#HR>#H,E71E7>1E7I5G75G7g01=3'V%U=3T%S=P7P71F7?P4%l7CRP51F7;CR%k7%j7R=g00:]RI#QR>#Q,@7R1%gI,@7RH'C,D=%d9R9P=1@7I1@7>5c7R>/C1,D=P91C>H,D=CMCM1`=:P2P4PG1a24#0dAb7F5C^bCbDbEX87X97X:7X;71A54/4?1A4;/4?[\<^87^97^:7^;7P2fDfC%BJ%:JP3PCO6bBbHbGO3b33fO3b3O2b3b1b3116A#0eW1W4n0110000020001P2P4O2b4b5b1XA0X08b1O2A]B;4#0eW@W1X67XF7XI7WJo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section DispatchSmoke.
  Variable segs : list Segment.
  Variable regs : bvmap 5 word.
  Variable mem rom : word -> option byte.

  (* [comment removed for export] *)
  Ltac smoke enc sh :=
    let F := fresh "F" in
    intro F;
    let D := fresh "D" in
    assert (D : decode_any enc = Some (sh, 4%Z)) by vm_refl_bv;
    eexists; stepi F D; apply mst_refl.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00152513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00152513 : bv 32) (OpImm ALU_SLT 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40155513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40155513 : bv 32) (ShiftImm ALU_SRA 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B57533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B57533 : bv 32) (Op ALU_AND 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B56533 : bv 32) (Op ALU_OR 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B54533 : bv 32) (Op ALU_XOR 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B51533 : bv 32) (Op ALU_SLL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B55533 : bv 32) (Op ALU_SRL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B55533 : bv 32) (Op ALU_SRA 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B52533 : bv 32) (Op ALU_SLT 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B53533 : bv 32) (Op ALU_SLTU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5053B : bv 32) (Op32 ALU_ADD 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5153B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5153B : bv 32) (Op32 ALU_SLL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5553B : bv 32) (Op32 ALU_SRL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B5553B : bv 32) (Op32 ALU_SRA 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015051B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015051B : bv 32) (OpImm32 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015151B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015151B : bv 32) (ShiftImm32 ALU_SLL 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015551B : bv 32) (ShiftImm32 ALU_SRL 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x4015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x4015551B : bv 32) (ShiftImm32 ALU_SRA 10 10 1). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B51533 : bv 32) (Mul M_MULH 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B52533 : bv 32) (Mul M_MULHSU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B53533 : bv 32) (Mul M_MULHU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B54533 : bv 32) (Mul M_DIV 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B56533 : bv 32) (Mul M_REM 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5053B : bv 32) (Mul32 M_MUL 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5453B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5453B : bv 32) (Mul32 M_DIV 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5553B : bv 32) (Mul32 M_DIVU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5653B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5653B : bv 32) (Mul32 M_REM 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5753B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5753B : bv 32) (Mul32 M_REMU 10 10 11). Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B55533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B55533 : bv 32)
                = Some (Mul M_DIVU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B57533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B57533 : bv 32)
                = Some (Mul M_REMU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00151513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00151513 : bv 32)
                = Some (ShiftImm ALU_SLL 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_slli (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00157513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00157513 : bv 32)
                = Some (OpImm ALU_AND 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_andi (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A13023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 8%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A13023 : bv 32)
                = Some (Store SZ8 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A12023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 4%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A12023 : bv 32)
                = Some (Store SZ4 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A11023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 2%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A11023 : bv 32)
                = Some (Store SZ2 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A10023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 1%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A10023 : bv 32)
                = Some (Store SZ1 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0080006F : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x0080006F : bv 32)
                = Some (Jal 0 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x008000EF : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x008000EF : bv 32)
                = Some (Jal 1 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00008067 : bv 32) ->
    getr regs 1 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x00008067 : bv 32)
                = Some (Jalr 0 1 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

  (* [comment removed for export] *)
  Goal fetch_word segs (0x10000 : word) = Some (0x000500E7 : bv 32) ->
    getr regs 10 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x000500E7 : bv 32)
                = Some (Jalr 1 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

End DispatchSmoke.
End WithFP33.
