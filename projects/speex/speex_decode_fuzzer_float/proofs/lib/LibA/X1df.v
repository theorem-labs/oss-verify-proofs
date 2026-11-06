(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cj X1cm X1dd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Export X1co.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac fold_lit_fmv_s :=
repeat match goal with
| |- context [fmv_s (Z_to_bv 64 ?z)] =>
is_Zlit z; let t := constr:(fmv_s (Z_to_bv 64 z)) in
let z' := eval vm_compute in (bv_unsigned t) in rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
| |- context [fneg_s (Z_to_bv 64 ?z)] =>
is_Zlit z; let t := constr:(fneg_s (Z_to_bv 64 z)) in
let z' := eval vm_compute in (bv_unsigned t) in rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
| |- context [fabs_s (Z_to_bv 64 ?z)] =>
is_Zlit z; let t := constr:(fabs_s (Z_to_bv 64 z)) in
let z' := eval vm_compute in (bv_unsigned t) in rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
end.

Ltac exec_cbv ::=
let g := lazymatch goal with |- ?g => g end in
let g' := eval cbv beta iota zeta delta [lift_result interp_eff exec with_pc with_regs with_fregs with_fcsr with_resv
rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
width_bytes accrue fari_d fcmp_d fari_s fcmp_s fma_d fma_s fminmax_d fminmax_s] in g in
set_concl g'.

Ltac vnorm_rw_for i ::=
lazymatch i with
| OpImm ALU_ADD _ _ _ => rewrite ?alu_addi
| OpImm ALU_AND _ _ _ => rewrite ?alu_andi
| OpImm ALU_OR _ _ _ => rewrite ?alu_ori
| OpImm ALU_XOR _ _ _ => rewrite ?alu_xori
| OpImm ALU_SLT _ _ _ => rewrite ?alu_slti
| OpImm ALU_SLTU _ _ _ => rewrite ?alu_sltiu
| ShiftImm ALU_SLL _ _ _ => rewrite ?alu_slli
| ShiftImm ALU_SRL _ _ _ => rewrite ?alu_srli
| ShiftImm ALU_SRA _ _ _ => rewrite ?alu_srai
| Op ALU_ADD _ _ _ => rewrite ?alu_add
| Op ALU_SUB _ _ _ => rewrite ?alu_sub
| Op ALU_SLT _ _ _ => rewrite ?alu_slt
| Op ALU_SLTU _ _ _ => rewrite ?alu_sltu
| Op ALU_AND _ _ _ => rewrite ?alu_and
| Op ALU_OR _ _ _ => rewrite ?alu_or
| Op ALU_XOR _ _ _ => rewrite ?alu_xor
| Op ALU_SLL _ _ _ => rewrite ?alu_sll
| Op ALU_SRL _ _ _ => rewrite ?alu_srl
| Op ALU_SRA _ _ _ => rewrite ?alu_sra
| OpImm32 _ _ _ => rewrite ?w_addiw
| ShiftImm32 ALU_SLL _ _ _ => rewrite ?w_slliw
| ShiftImm32 ALU_SRL _ _ _ => rewrite ?w_srliw
| ShiftImm32 ALU_SRA _ _ _ => rewrite ?w_sraiw
| Op32 ALU_ADD _ _ _ => rewrite ?w_addw
| Op32 ALU_SUB _ _ _ => rewrite ?w_subw
| Op32 ALU_SLL _ _ _ => rewrite ?w_sllw
| Op32 ALU_SRL _ _ _ => rewrite ?w_srlw
| Op32 ALU_SRA _ _ _ => rewrite ?w_sraw
| Mul M_MUL _ _ _ => rewrite ?m_mul
| Mul M_MULH _ _ _ => rewrite ?m_mulh
| Mul M_MULHSU _ _ _ => rewrite ?m_mulhsu
| Mul M_MULHU _ _ _ => rewrite ?m_mulhu
| Mul M_DIV _ _ _ => rewrite ?m_div
| Mul M_REM _ _ _ => rewrite ?m_rem
| Mul32 M_MUL _ _ _ => rewrite ?w_mulw
| Mul32 M_DIV _ _ _ => rewrite ?w_divw
| Mul32 M_REM _ _ _ => rewrite ?w_remw
| Mul32 M_DIVU _ _ _ => rewrite ?w_divuw
| Mul32 M_REMU _ _ _ => rewrite ?w_remuw
| Lui _ _ => rewrite ?b_lui
| Auipc _ _ => rewrite ?b_auipc
| Load _ _ _ _ _ => rewrite ?b_addsext
| Store _ _ _ _ => rewrite ?b_addsext
| FLoad _ _ _ _ => rewrite ?b_addsext, ?extract_le4_low32
| FStore _ _ _ _ => rewrite ?b_addsext
| Jalr _ _ _ => rewrite ?b_addsext
| Jal _ _ => rewrite ?b_addsext
| Branch _ _ _ _ => rewrite ?b_addsext

| Fsgnj _ FMT_D _ _ _ => rewrite ?sgnj_self, ?sgnjx_self, ?sgnjn_self
| Fsgnj _ FMT_S _ _ _ => rewrite ?fsgnj_s_self, ?fsgnjx_s_self, ?fsgnjn_s_self; rewrite ?fmv_s_nan_box; fold_lit_fmv_s
| Fmv _ _ _ _ => rewrite ?fmv_x_w_val; fold_lit_load
| Fma _ _ _ _ _ _ _ => idtac
| Fari _ _ _ _ _ _ => idtac
| Fcmp _ _ _ _ _ => idtac
| Fcvt _ _ _ _ _ => idtac
| Fsqrt _ _ _ _ => idtac
| Fminmax _ _ _ _ _ => idtac
| Fclass _ _ _ => idtac
| Csr _ _ _ _ => idtac
| CsrI _ _ _ _ => idtac
| _ =>
rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
?b_addsext, ?b_lui, ?b_auipc
end.

Ltac exec_pre i ::=
lazymatch goal with
| |- context [exec ?sz _ ?c] =>
lazymatch i with
| Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
| Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
| Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
| Fsqrt FMT_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_s sz rd rs1 rm c _ H)
| Fma ?op FMT_D ?rd ?rs1 ?rs2 ?rs3 ?rm => let H := rm_proof rm c in rewrite (exec_fma_d sz op rd rs1 rs2 rs3 rm c _ H)
| Fma ?op FMT_S ?rd ?rs1 ?rs2 ?rs3 ?rm => let H := rm_proof rm c in rewrite (exec_fma_s sz op rd rs1 rs2 rs3 rm c _ H)
| Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
| Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
| Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv_concl_zeta
| Fminmax ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_s sz op rd rs1 rs2 c)
| Fclass FMT_D ?rd ?rs1 => rewrite (exec_fclass_d sz rd rs1 c)
| Fclass FMT_S ?rd ?rs1 => rewrite (exec_fclass_s sz rd rs1 c)
| Fsgnj ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fsgnj_s sz op rd rs1 rs2 c)
| Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
| Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
| Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
| Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
| Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
| Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
| Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
| Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
| Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
| Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
| Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
| Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
| Fcvt FC_W FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_s sz rd rs1 rm c _ H)
| Fcvt FC_WU FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_s sz rd rs1 rm c _ H)
| Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
| Fcvt FC_LU FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_s sz rd rs1 rm c _ H)
| Fcvt FC_S FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_l sz rd rs1 rm c _ H)
| Fcvt FC_S FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_lu sz rd rs1 rm c _ H)
| Csr ?op ?rd ?rs1 ?csr =>
let sl := eval vm_compute in (csr_slice csr) in
lazymatch sl with
| Some (?lo, ?len) =>
rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv_concl_zeta;
simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv_concl_iota
| None => fail 100 "CSR access to an unknown CSR:" csr
end
| CsrI ?op ?rd ?uimm ?csr =>
let sl := eval vm_compute in (csr_slice csr) in
lazymatch sl with
| Some (?lo, ?len) =>
rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv_concl_zeta;
let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv_concl_iota
| None => fail 100 "CSR access to an unknown CSR:" csr
end
| _ => idtac
end
end;

try match goal with
| FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
end.
