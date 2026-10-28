(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim DrainSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__StepTac () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OssFuzzTheorems.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StepTac.WithFP33."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1S"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1true"; "2and"; "2eq"; "2not"; "3Z"; "4nat_to_word"; "5PhdrInfo"]; ["5Segment"; "5seg_base"; "5seg_size"; "6range_avoids_ro_segs"; "7valid_argv"; "7valid_envp"; "8EntryDraw"; "8build_stack_bytes"; "9c_eq"; "9v_add"; "9v_addi"; "9v_sub"; ":ro_segs_below"; ";add"; ";le"; ";lt"]; [";ltb"; ";of_N"; ";of_nat"; ";opp"; ";pow"; ";sub"; "0a"; "0addr"; "0b"; "0d"; "0data_base"; "0e"; "0hw"; "0imm"; "0m"; "0n"]; ["0ph"; "0rnd"; "0s0"; "0s1"; "0segs"; "0sp"; "<Z_to_bv"; "<bv"; "<bv_add"; "<bv_unsigned"; "0uid"; "0x"; "0y"; "0z"]]).
Section WithFP1.
Context {fx : FPState}.
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
End WithFP2.
Ltac step_intro := chain_step.
Section WithFP3.
Context {fx : FPState}.
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
End WithFP5.
Ltac vm_eval t :=
let _ := match goal with _ => check_closed_term t end in
eval vm_compute in t.
Section WithFP6.
Context {fx : FPState}.
End WithFP6.
Ltac word_lit p :=
let u := vm_eval (bv_unsigned p) in
constr:(@BV 64 u ltac:(vm_compute; exact I)).
Section WithFP7.
Context {fx : FPState}.
End WithFP7.
Ltac replace_nb c1 c2 tac :=
let T := type of c2 in
let E := constr:(ltac:(solve [tac]) : @eq T c2 c1) in
try (rewrite <- E).
Ltac wlit_replace p :=
let l := word_lit p in
replace_nb p l ltac:(apply bv_eq; vm_compute; reflexivity).
Section WithFP8.
Context {fx : FPState}.
End WithFP8.
Ltac wlit p :=
try (lazymatch p with
| @BV _ _ _ => idtac
| _ => wlit_replace p
end).
Section WithFP9.
Context {fx : FPState}.
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
End WithFP13.
Ltac step_simpl := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pc.
Section WithFP14.
Context {fx : FPState}.
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
End WithFP17.
Ltac stepiwv F D vv tac :=
chain_step;
[ reflexivity
| eapply step_addiw_at with (v := vv);
[ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Section WithFP18.
Context {fx : FPState}.
End WithFP18.
Ltac stepj F D :=
chain_step;
[ reflexivity
| first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
| exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
| step_simpl ].
Section WithFP19.
Context {fx : FPState}.
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
Lemma u_Z2bv : ltac2:(TCodec.tc2 tcn__StepTac "G'=&Nzr1%3221&Or2&Q4+2+R0%3221%6251';&QIyR0&QFr3%2231%5241%73C13p091p0A1pSLF1").
Proof.
intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
exact Hhi.
Qed.
Lemma v_addi_m1 : ltac2:(TCodec.tc2 tcn__StepTac "F'QGyR0%211&N+1&QIr1%2261%5241';&Jr2-1%3221&QF&Q5%;2?5%221=%42A1%:3A61p0<1pSHC1").
Proof. intros x H1. apply (v_addi_m x 1); lia. Qed.
Lemma v_addi_m16 : ltac2:(TCodec.tc2 tcn__StepTac "F'QGyR0%211&N+@&QIr1%2261%5241';&Jr2-@%3221&QF&Q5%;2?5%221=%42A1%:3A61p0<1pSHC1").
Proof. intros x H16. apply (v_addi_m x 16); lia. Qed.
Lemma v_addi_m32 : ltac2:(TCodec.tc2 tcn__StepTac "F'QGyR0%211&N+Q0&QIr1%2261%5241';&Jr2-Q0%3221&QF&Q5%;2?5%221=%42A1%:3A61p0<1pSHC1").
Proof. intros x H32. apply (v_addi_m x 32); lia. Qed.
Lemma v_addi_m48 : ltac2:(TCodec.tc2 tcn__StepTac "F'QGyR0%211&N+Q@&QIr1%2261%5241';&Jr2-Q@%3221&QF&Q5%;2?5%221=%42A1%:3A61p0<1pSHC1").
Proof. intros x H48. apply (v_addi_m x 48); lia. Qed.
Lemma v_addi_m64 : ltac2:(TCodec.tc2 tcn__StepTac "F'QGyR0%211&N+R0&QIr1%2261%5241';&Jr2-R0%3221&QF&Q5%;2?5%221=%42A1%:3A61p0<1pSHC1").
Proof. intros x H64. apply (v_addi_m x 64); lia. Qed.
Lemma v_addi_m80 : ltac2:(TCodec.tc2 tcn__StepTac "F'QGyR0%211&N+R@&QIr1%2261%5241';&Jr2-R@%3221&QF&Q5%;2?5%221=%42A1%:3A61p0<1pSHC1").
Proof. intros x H80. apply (v_addi_m x 80); lia. Qed.
Lemma v_addi_nneg_t : ltac2:(TCodec.tc2 tcn__StepTac "Q1'QGyR0%211'=&Nzr1%3221&O&M&QIr3%22;1r2%5221&Q4+2+R0%3221%;251';&Jr4%221<&QF%?2H3%A21?%32J1%83J51p0:1p0G1pRLL1pSHN1").
Proof. intros x imm _ _. reflexivity. Qed.
End WithFP20.
Ltac u_norm := repeat rewrite u_Z2bv by lia.
Section WithFP21.
Context {fx : FPState}.
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
Context {fx : FPState}.
Goal v_addi (Z_to_bv 64 5) 3 = Z_to_bv 64 8.
Proof. bveq. Abort.
Goal forall regs (v : word), getr (regupd regs 11 v) 11 = v.
Proof. intros. assert_fails bveq. getr_resolve. reflexivity. Abort.
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
try (let u := vm_eval (bv_unsigned (v_addi v 4)) in
fail 1 "vm_eval accepted an open term").
Abort.
Goal forall v : word, v_addi v 4 = v_addi v 4.
Proof. intros v. wlit (v_addi v 4). wlits. reflexivity. Abort.
Goal forall v : word,
(v_addi (Z_to_bv 64 5) 3, v_addi v 4) = (Z_to_bv 64 8, v_addi v 4).
Proof.
intros v. wlits.
lazymatch goal with |- (@BV _ _ _, _) = _ => idtac end.
f_equal. bveq.
Abort.
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
Context {fx : FPState}.
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
End WithFP28.
Ltac vm_refl_bv :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Section WithFP29.
Context {fx : FPState}.
End WithFP29.
Ltac wlit_closed p :=
check_closed_term p;
let u := vm_eval (bv_unsigned p) in
replace_nb p (Z_to_bv 64 u) ltac:(bveq).
Section WithFP30.
Context {fx : FPState}.
End WithFP30.
Ltac wlits_closed :=
repeat match goal with
| |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
| |- context [v_add ?a ?b] => wlit_closed (v_add a b)
| |- context [v_sub ?a ?b] => wlit_closed (v_sub a b)
end.
Section WithFP32.
Context {fx : FPState}.
End WithFP32.
Ltac rdn_ext_lit :=
erewrite rdn_ext;
[
| imm_norm; u_norm; lia
| let x := fresh "x" in
let Hx := fresh "Hx" in
intros x Hx; revert Hx; imm_norm; u_norm; intros Hx ].
Section WithFP33.
Context {fx : FPState}.
Lemma byte_nz_u : ltac2:(TCodec.tc2 tcn__StepTac "C'QGy8%211&<';r1&QFz%2271%53741%711'=&QIr2%22=1%;3418%=11p071pRB@1").
Proof.
intros b Hb Hc. apply Hb. apply bv_eq. rewrite Hc. reflexivity.
Qed.
Lemma u_zext8 : ltac2:(TCodec.tc2 tcn__StepTac ">'QGy8%211';'=&QIyR0&QFr1%4281%3241%6251%93813pRB;1").
Proof.
intro b. apply u_Z2bv; pose proof (u8_range b); lia.
Qed.
Lemma zext8_byte : ltac2:(TCodec.tc2 tcn__StepTac ">'QGy8%211';&QF&QIyR0r1%3271%5231%5241%72:1%93:15pRB;1").
Proof.
intro b. apply bv_eq.
rewrite Z_to_bv_unsigned, u_zext8.
apply bv_wrap_small. pose proof (u8_range b).
change (bv_modulus 8) with 256%Z. lia.
Qed.
Lemma byte_neq_lit_u : ltac2:(TCodec.tc2 tcn__StepTac "N'QGy8%211'=':&Nzr1%3221&O+X0%2241%8241&<';r3&QFr2%22A1%53A41%711&QIr4%22F1%:3E19%<11p061p0?1pSLI1pRBK1").
Proof.
intros b z Hz Hb Hc. apply Hb. apply bv_eq.
rewrite Hc, Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.mod_small; [reflexivity |].
change (bv_modulus 8) with 256%Z. lia.
Qed.
Lemma c_eq_zext_lit_false : ltac2:(TCodec.tc2 tcn__StepTac "Q4'QGy8%211'=':&Nzr1%3221&O+X0%2241%8241&<';r3&QFr2%22A1%53A41%711'2&HyR0&QIr4%22I1%;241%<25=%7221(4%A3:21p0<1p0E1pSLO1pRBQ11").
Proof.
intros b z Hz Hb. unfold c_eq, bv_eqb. apply Z.eqb_neq.
rewrite u_zext8, u_Z2bv by lia.
exact (byte_neq_lit_u b z Hz Hb).
Qed.
Lemma u_ntw : ltac2:(TCodec.tc2 tcn__StepTac "F'7&O&Q2r1%211&Q4+2+R0%3221%8251';'=&QIyR0&>r2%211%5241%@13%93821p0;1pS0E1").
Proof. intros n Hn. unfold nat_to_word. apply u_Z2bv; lia. Qed.
Lemma word_add_nat : ltac2:(TCodec.tc2 tcn__StepTac "F'QGyR0%211'7';&QHr2&>r1%211%53941&QF&M&QI%12=8&Q2%118%5231%72A1%?3A91pS0A1pR>C1").
Proof.
intros a n. apply bv_eq. unfold nat_to_word.
rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_r.
reflexivity.
Qed.
Lemma word_add_nat_0 : ltac2:(TCodec.tc2 tcn__StepTac "<'QGyR0%211';&QHr1&>(0%211%53841%73815pSH91").
Proof.
intro x. apply bv_eq. rewrite word_add_nat.
rewrite u_Z2bv by (pose proof (u64_range x); lia). lia.
Qed.
Lemma word_add_nat_1 : ltac2:(TCodec.tc2 tcn__StepTac "E'QGyR0%211'7';&J&QHr2&>r1%211%53:41+1%8221(1%116%811%;3@:1%>3@51pRN@1pR>B1").
Proof.
intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma word_add_nat_m1 : ltac2:(TCodec.tc2 tcn__StepTac "E'QGyR0%211'7';&J&QHr2&>(1r1%211%411%73<61-1%:221%816%;3@:1%>3@31pRN@1pR>B1").
Proof.
intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma v_add_comm : ltac2:(TCodec.tc2 tcn__StepTac "='QGyR0%211';&Ir2r1%3221&QH%13834%73831pSJ91pSH:1").
Proof.
intros x y. apply bv_eq.
change (v_add x y) with (x + y).
rewrite !bv_add_unsigned. f_equal. lia.
Qed.
Lemma v_add_wrap : ltac2:(TCodec.tc2 tcn__StepTac "N'QGyR0%211&N&Q4+2+R0%3221&M&QIr2%22:1r1%42<1%6231%<281';&Ir3%2219&QF&Q5%=2E4%?21<%321A%52H1%:3H71p0<1pSJJ1pSHK1").
Proof.
intros x y Hw. unfold v_add. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite <- (Z.mod_add (bv_unsigned x + bv_unsigned y - 2^64) 1 (2^64)) by lia.
f_equal. lia.
Qed.
Lemma v_sub_0_neg : ltac2:(TCodec.tc2 tcn__StepTac "A'QGyR0%211';&K&QFz%2261r1%5221&Q3&QI%12;4%311%92=1%<3=61pSJ>1").
Proof.
intro y. unfold v_sub.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
f_equal.
Qed.
Lemma u_neg_small : ltac2:(TCodec.tc2 tcn__StepTac "K'=&Ozr1%3221&Nr2&Q4+2+R0%3221%6251';&QIyR0&QF&Q3r3%211%4251%7261&Q5%12<5%;3G31p0=1p0E1pSLJ1").
Proof.
intros z Hz0 Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
replace (- z)%Z with ((2^64 - z) + (-1) * 2^64)%Z by lia.
rewrite Z.mod_add by lia.
apply Z.mod_small. lia.
Qed.
Lemma v_addi_neg_S : ltac2:(TCodec.tc2 tcn__StepTac "F'7';'QGyR0%211&J&QF&Q3&Q2(1r1%211%411%611%82;1+1%;221%917%;11%=2@1%C3@41pRDE1").
Proof.
intro d. unfold v_addi. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma bsb_bound : ltac2:(TCodec.tc2 tcn__StepTac "Q7'?'QGyR0%211'6y8%511%311%411'F&Dr5%211&E%113&N&Q2&5&Gr9r8r7r6r4r3%776543>21%92D1%;11+RT[`0%>221p0@1p0C1pS4G1pRJN1pSFO1pRHK1pR>L1pS<Q21pS2Q61").
Proof.
intros ph sp a e uid hw rnd Hva Hve.
pose proof (build_stack_bytes_within_span ph sp a e uid hw rnd).
pose proof (entry_stack_span_bound a e Hva Hve).
unfold entry_stack_span_max in *. lia.
Qed.
Lemma range_avoids_two : ltac2:(TCodec.tc2 tcn__StepTac "Q7'@'=';'2&Q0r2&M&Q1&Ar4%211%411&B%114%711%9241%<2;1(4%@3?21r3%@215%C3B14&C(3r6r5(8%11K%53L31%63M51%831E;(9%N3M21p0<1p0@1pS0Q21pR>Q31pS8Q51pS6Q61").
Proof.
intros s0 s1 a n H0 H1. unfold range_avoids_ro_segs. cbn [forallb].
rewrite H0, H1. rewrite !andb_false_r. cbn [negb]. rewrite !orb_true_r.
reflexivity.
Qed.
Definition ro_segs_below (segs : list Segment) (data_base : Z) : bool :=
forallb (fun seg =>
seg_writable seg
|| Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) data_base)
segs.
Lemma range_avoids_ro_above : ltac2:(TCodec.tc2 tcn__StepTac "H'6'@%211'=';'2&Lr4r3%3221(9%73621&N%1265&Cr6%23198%=3<17p051p081pS0A1pR@B1pRFC1pS:E1").
Proof.
intros segs data_base addr n Hbelow Haddr.
unfold ro_segs_below in Hbelow. unfold range_avoids_ro_segs.
rewrite forallb_forall in *. intros seg Hin.
specialize (Hbelow seg Hin).
destruct (seg_writable seg) eqn:W; cbn [orb] in *; [reflexivity|].
apply Z.leb_le in Hbelow.
apply negb_true_iff. apply andb_false_iff. right.
apply Z.ltb_ge. lia.
Qed.
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
Goal fetch_word segs (0x10000 : word) = Some (0x00152513 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00152513 : bv 32) (OpImm ALU_SLT 10 10 1). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x40155513 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x40155513 : bv 32) (ShiftImm ALU_SRA 10 10 1). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B57533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B57533 : bv 32) (Op ALU_AND 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B56533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B56533 : bv 32) (Op ALU_OR 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B54533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B54533 : bv 32) (Op ALU_XOR 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B51533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B51533 : bv 32) (Op ALU_SLL 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B55533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B55533 : bv 32) (Op ALU_SRL 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x40B55533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x40B55533 : bv 32) (Op ALU_SRA 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B52533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B52533 : bv 32) (Op ALU_SLT 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B53533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B53533 : bv 32) (Op ALU_SLTU 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B5053B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B5053B : bv 32) (Op32 ALU_ADD 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B5153B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B5153B : bv 32) (Op32 ALU_SLL 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00B5553B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x00B5553B : bv 32) (Op32 ALU_SRL 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x40B5553B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x40B5553B : bv 32) (Op32 ALU_SRA 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x0015051B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x0015051B : bv 32) (OpImm32 10 10 1). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x0015151B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x0015151B : bv 32) (ShiftImm32 ALU_SLL 10 10 1). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x0015551B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x0015551B : bv 32) (ShiftImm32 ALU_SRL 10 10 1). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x4015551B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x4015551B : bv 32) (ShiftImm32 ALU_SRA 10 10 1). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B51533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B51533 : bv 32) (Mul M_MULH 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B52533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B52533 : bv 32) (Mul M_MULHSU 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B53533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B53533 : bv 32) (Mul M_MULHU 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B54533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B54533 : bv 32) (Mul M_DIV 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B56533 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B56533 : bv 32) (Mul M_REM 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B5053B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B5053B : bv 32) (Mul32 M_MUL 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B5453B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B5453B : bv 32) (Mul32 M_DIV 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B5553B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B5553B : bv 32) (Mul32 M_DIVU 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B5653B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B5653B : bv 32) (Mul32 M_REM 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B5753B : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof. smoke (0x02B5753B : bv 32) (Mul32 M_REMU 10 10 11). Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B55533 : bv 32) ->
(bv_unsigned (getr regs 11) <> 0)%Z ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof.
intros F NZ.
assert (D : decode_any (0x02B55533 : bv 32)
= Some (Mul M_DIVU 10 10 11, 4%Z)) by vm_refl_bv.
eexists. stepi F D. apply mst_refl.
Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x02B57533 : bv 32) ->
(bv_unsigned (getr regs 11) <> 0)%Z ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof.
intros F NZ.
assert (D : decode_any (0x02B57533 : bv 32)
= Some (Mul M_REMU 10 10 11, 4%Z)) by vm_refl_bv.
eexists. stepi F D. apply mst_refl.
Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00151513 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof.
intro F.
assert (D : decode_any (0x00151513 : bv 32)
= Some (ShiftImm ALU_SLL 10 10 1, 4%Z)) by vm_refl_bv.
eexists. stepiv F D (v_slli (getr regs 10) 1) ltac:(reflexivity).
apply mst_refl.
Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x00157513 : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof.
intro F.
assert (D : decode_any (0x00157513 : bv 32)
= Some (OpImm ALU_AND 10 10 1, 4%Z)) by vm_refl_bv.
eexists. stepiv F D (v_andi (getr regs 10) 1) ltac:(reflexivity).
apply mst_refl.
Abort.
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
Goal fetch_word segs (0x10000 : word) = Some (0x0080006F : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof.
intro F.
assert (D : decode_any (0x0080006F : bv 32)
= Some (Jal 0 8, 4%Z)) by vm_refl_bv.
eexists. stepj F D. apply mst_refl.
Abort.
Goal fetch_word segs (0x10000 : word) = Some (0x008000EF : bv 32) ->
exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
Proof.
intro F.
assert (D : decode_any (0x008000EF : bv 32)
= Some (Jal 1 8, 4%Z)) by vm_refl_bv.
eexists. stepj F D. apply mst_refl.
Abort.
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
