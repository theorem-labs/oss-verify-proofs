(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition syscalls_prog (B B_15f44 : Z) : RStep.ptree :=
  PLeaf
    (PJ_Lui_nn 0 11 1048575 4
    (PJ_OpImm32_nnn 4 11 11 1 4
    (PJ_Branch_BC_LTU_nnn 8 10 11 44 4
    (PJ_OpImm_ALU_ADD_nnn 12 2 2 4080 4
    (PJ_Store_SZ8_nnn 16 2 1 8 4
    (PJ_Store_SZ8_nnn 20 2 8 0 4
    (PJ_Op32_ALU_SUB_nnn 24 8 0 10 4
    (PJ_Jal_nt 28 1 (jimm21 (B_15f44 - (B + 28))) 4
    (PJ_Store_SZ4_nnn 32 10 8 0 4
    (PJ_OpImm_ALU_ADD_nnn 36 10 0 4095 4
    (PJ_Load_SZ8_true_nnn 40 1 2 8 4
    (PJ_Load_SZ8_true_nnn 44 8 2 0 4
    (PJ_OpImm_ALU_ADD_nnn 48 2 2 16 4
    (PJ_Jalr_nnn 52 0 1 0 4 nil)))))))))))))).
(* [comment removed for export] *)
Definition syscalls_prog_1 (B B_15f44 : Z) : RStep.ptree :=
  PLeaf
    (PJ_OpImm_ALU_ADD_nnn 0 10 4 0 4
    (PJ_OpImm_ALU_ADD_nnn 4 10 10 3932 4
    (PJ_Jalr_nnn 8 0 1 0 4 nil))).

(* [comment removed for export] *)
Definition syscalls_prog_r1 (B B_21c60 : Z) : RStep.ptree :=
  PLeaf
    (PJ_OpImm_ALU_ADD_nnn 0 17 10 0 4
    (PJ_OpImm_ALU_ADD_nnn 4 10 11 0 4
    (PJ_OpImm_ALU_ADD_nnn 8 11 12 0 4
    (PJ_OpImm_ALU_ADD_nnn 12 12 13 0 4
    (PJ_OpImm_ALU_ADD_nnn 16 13 14 0 4
    (PJ_OpImm_ALU_ADD_nnn 20 14 15 0 4
    (PJ_OpImm_ALU_ADD_nnn 24 15 16 0 4
    (PJ_Ecall_ 28  4
    (PJ_Jalr_nnn 32 0 1 0 4 nil))))))))).
(* [comment removed for export] *)
Definition syscalls_prog_r1_1 (B B_21c60 : Z) : RStep.ptree :=
  PLeaf
    (PJ_Jal_nt 0 0 (jimm21 (B_21c60 - B)) 4 nil).

(* [comment removed for export] *)
Definition syscalls_prog_r2 (B B_21c84 B_15f0c : Z) : RStep.ptree :=
  PLeaf
    (PJ_OpImm_ALU_ADD_nnn 0 2 2 4080 4
    (PJ_Store_SZ8_nnn 4 2 1 8 4
    (PJ_OpImm_ALU_ADD_nnn 8 13 12 0 4
    (PJ_OpImm_ALU_ADD_nnn 12 12 11 0 4
    (PJ_OpImm_ALU_ADD_nnn 16 11 10 0 4
    (PJ_OpImm_ALU_ADD_nnn 20 10 0 63 4
    (PJ_OpImm_ALU_ADD_nnn 24 14 0 0 4
    (PJ_OpImm_ALU_ADD_nnn 28 15 0 0 4
    (PJ_OpImm_ALU_ADD_nnn 32 16 0 0 4
    (PJ_Jal_nt 36 1 (jimm21 (B_21c84 - (B + 36))) 4
    (PJ_Load_SZ8_true_nnn 40 1 2 8 4
    (PJ_OpImm_ALU_ADD_nnn 44 2 2 16 4
    (PJ_Jal_nt 48 0 (jimm21 (B_15f0c - (B + 48))) 4 nil))))))))))))).

(* [comment removed for export] *)
Definition syscalls_prog_r3 (B B_1838c B_21c84 B_15f0c : Z) : RStep.ptree :=
  PNode 40%Z
  (PLeaf
      (PJ_OpImm_ALU_ADD_nnn 0 2 2 4080 4
      (PJ_Store_SZ8_nnn 4 2 1 8 4
      (PJ_Jal_nt 8 1 (jimm21 (B_1838c - (B + 8))) 4
      (PJ_OpImm_ALU_ADD_nnn 12 11 10 0 4
      (PJ_OpImm_ALU_ADD_nnn 16 10 0 57 4
      (PJ_OpImm_ALU_ADD_nnn 20 12 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 24 13 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 28 14 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 32 15 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 36 16 0 0 4 nil)))))))))))
  (PLeaf
      (PJ_Jal_nt 40 1 (jimm21 (B_21c84 - (B + 40))) 4
      (PJ_OpImm32_nnn 44 10 10 0 4
      (PJ_OpImm_ALU_ADD_nnn 48 11 10 4 4
      (PJ_OpImm_ALU_SLTU_nnn 52 11 11 1 4
      (PJ_OpImm_ALU_ADD_nnn 56 11 11 4095 4
      (PJ_Op_ALU_AND_nnn 60 10 11 10 4
      (PJ_Jal_nt 64 1 (jimm21 (B_15f0c - (B + 64))) 4
      (PJ_OpImm32_nnn 68 10 10 0 4
      (PJ_Load_SZ8_true_nnn 72 1 2 8 4
      (PJ_OpImm_ALU_ADD_nnn 76 2 2 16 4
      (PJ_Jalr_nnn 80 0 1 0 4 nil)))))))))))).

(* [comment removed for export] *)
Definition syscalls_prog_r4 (B got_ssp B_21c84 B_15f0c B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 112%Z
  (PNode 56%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4000 4
        (PJ_Store_SZ8_nnn 4 2 1 40 4
        (PJ_Store_SZ8_nnn 8 2 8 32 4
        (PJ_Store_SZ8_nnn 12 2 9 24 4
        (PJ_OpImm_ALU_ADD_nnn 16 8 11 0 4
        (PJ_OpImm_ALU_ADD_nnn 20 5 10 0 4
        (PJ_Store_SZ8_nnn 24 2 16 80 4
        (PJ_Store_SZ8_nnn 28 2 17 88 4
        (PJ_Auipc_nt 32 10 (hi20 (got_ssp - (B + 32))) 4
        (PJ_Load_SZ8_true_nnt 36 9 10 (lo12 (got_ssp - (B + 32))) 4
        (PJ_Store_SZ8_nnn 40 2 12 48 4
        (PJ_Store_SZ8_nnn 44 2 13 56 4
        (PJ_Store_SZ8_nnn 48 2 14 64 4
        (PJ_Store_SZ8_nnn 52 2 15 72 4 nil)))))))))))))))
    (PLeaf
        (PJ_Load_SZ8_true_nnn 56 10 9 0 4
        (PJ_OpImm_ALU_AND_nnn 60 11 11 64 4
        (PJ_Store_SZ8_nnn 64 2 10 16 4
        (PJ_Branch_BC_NE_nnn 68 11 0 24 4
        (PJ_Lui_nn 72 10 1040 4
        (PJ_Op_ALU_AND_nnn 76 11 8 10 4
        (PJ_Branch_BC_EQ_nnn 80 11 10 12 4
        (PJ_OpImm_ALU_ADD_nnn 84 14 0 0 4
        (PJ_Jal_nn 88 0 8 4
        (PJ_Load_SZ4_false_nnn 92 14 2 48 4
        (PJ_Lui_nn 96 13 8 4
        (PJ_Op_ALU_OR_nnn 100 13 8 13 4
        (PJ_OpImm_ALU_ADD_nnn 104 10 0 56 4
        (PJ_OpImm_ALU_ADD_nnn 108 11 0 3996 4 nil))))))))))))))))
  (PNode 168%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 112 12 5 0 4
        (PJ_OpImm_ALU_ADD_nnn 116 15 0 0 4
        (PJ_OpImm_ALU_ADD_nnn 120 16 0 0 4
        (PJ_Jal_nt 124 1 (jimm21 (B_21c84 - (B + 124))) 4
        (PJ_ShiftImm_ALU_SLL_nnn 128 8 8 44 4
        (PJ_OpImm_ALU_ADD_nnn 132 13 10 0 4
        (PJ_Branch_BC_GE_nnn 136 8 0 44 4
        (PJ_Lui_nn 140 10 524288 4
        (PJ_OpImm32_nnn 144 10 10 4095 4
        (PJ_OpImm_ALU_ADD_nnn 148 11 10 1 4
        (PJ_Op_ALU_AND_nnn 152 11 13 11 4
        (PJ_Branch_BC_NE_nnn 156 11 0 24 4
        (PJ_Op_ALU_AND_nnn 160 10 13 10 4
        (PJ_OpImm_ALU_ADD_nnn 164 17 0 25 4 nil)))))))))))))))
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 168 11 0 2 4
        (PJ_OpImm_ALU_ADD_nnn 172 12 0 1 4
        (PJ_Ecall_ 176  4
        (PJ_OpImm32_nnn 180 10 13 0 4
        (PJ_Jal_nt 184 1 (jimm21 (B_15f0c - (B + 184))) 4
        (PJ_Load_SZ8_true_nnn 188 11 9 0 4
        (PJ_Load_SZ8_true_nnn 192 12 2 16 4
        (PJ_Branch_BC_NE_nnn 196 11 12 28 4
        (PJ_OpImm32_nnn 200 10 10 0 4
        (PJ_Load_SZ8_true_nnn 204 1 2 40 4
        (PJ_Load_SZ8_true_nnn 208 8 2 32 4
        (PJ_Load_SZ8_true_nnn 212 9 2 24 4
        (PJ_OpImm_ALU_ADD_nnn 216 2 2 96 4
        (PJ_Jalr_nnn 220 0 1 0 4
        (PJ_Jal_nt 224 1 (jimm21 (B_stack_chk_fail - (B + 224))) 4 nil))))))))))))))))).

(* [comment removed for export] *)
Definition syscalls_prog_r5 (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_Jalr_nnn 0 0 1 0 4 nil).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m. (* [comment removed for export] *) Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_syscalls (IMG : RImg) := syscalls_prog (sym 0x15f0c) (sym 0x15f44).
Definition PROGAT_CODE_syscalls_1 (IMG : RImg) := syscalls_prog_1 (sym 0x15f44) (sym 0x15f44).
Definition PROGAT_CODE_syscalls_2 (IMG : RImg) := syscalls_prog_r1 (sym 0x21c60) (sym 0x21c60).
Definition PROGAT_CODE_syscalls_3 (IMG : RImg) := syscalls_prog_r1_1 (sym 0x21c84) (sym 0x21c60).
Definition PROGAT_CODE_syscalls_4 (IMG : RImg) := syscalls_prog_r2 (sym 0x21cf4) (sym 0x21c84) (sym 0x15f0c).
Definition PROGAT_CODE_syscalls_5 (IMG : RImg) := syscalls_prog_r3 (sym 0x21c94) (sym 0x1838c) (sym 0x21c84) (sym 0x15f0c).
Definition PROGAT_CODE_syscalls_6 (IMG : RImg) := syscalls_prog_r4 (sym 0x15dc0) (sym 0x22e18) (sym 0x21c84) (sym 0x15f0c) (sym 0x15f04).
Definition PROGAT_CODE_syscalls_7 (IMG : RImg) := syscalls_prog_r5 (sym 0x1838c).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_syscalls : CodeAtT img_segs (sym 0x15f0c) (PROGAT_CODE_syscalls IMG)}.
  Context {RB_syscalls : RelCode (sym 0x15f0c) 56}.
  Context {CODE_syscalls_1 : CodeAtT img_segs (sym 0x15f44) (PROGAT_CODE_syscalls_1 IMG)}.
  Context {RB_syscalls_1 : RelCode (sym 0x15f44) 12}.
  Context {CODE_syscalls_2 : CodeAtT img_segs (sym 0x21c60) (PROGAT_CODE_syscalls_2 IMG)}.
  Context {RB_syscalls_2 : RelCode (sym 0x21c60) 36}.
  Context {CODE_syscalls_3 : CodeAtT img_segs (sym 0x21c84) (PROGAT_CODE_syscalls_3 IMG)}.
  Context {RB_syscalls_3 : RelCode (sym 0x21c84) 4}.
  Context {CODE_syscalls_4 : CodeAtT img_segs (sym 0x21cf4) (PROGAT_CODE_syscalls_4 IMG)}.
  Context {RB_syscalls_4 : RelCode (sym 0x21cf4) 52}.
  Context {CODE_syscalls_5 : CodeAtT img_segs (sym 0x21c94) (PROGAT_CODE_syscalls_5 IMG)}.
  Context {RB_syscalls_5 : RelCode (sym 0x21c94) 84}.
  Context {CODE_syscalls_6 : CodeAtT img_segs (sym 0x15dc0) (PROGAT_CODE_syscalls_6 IMG)}.
  Context {RB_syscalls_6 : RelCode (sym 0x15dc0) 228}.
  Context {CODE_syscalls_7 : CodeAtT img_segs (sym 0x1838c) (PROGAT_CODE_syscalls_7 IMG)}.
  Context {RB_syscalls_7 : RelCode (sym 0x1838c) 4}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_15f44_15f0c : GLRN 0x15f0c 0x15f44}.
  Context {RN_B_15f44_15f44 : GLRN 0x15f44 0x15f44}.
  Context {RN_B_21c60_21c60 : GLRN 0x21c60 0x21c60}.
  Context {RN_B_21c60_21c84 : GLRN 0x21c84 0x21c60}.
  Context {RN_B_21c84_21cf4 : GLRN 0x21cf4 0x21c84}.
  Context {RN_B_15f0c_21cf4 : GLRN 0x21cf4 0x15f0c}.
  Context {RN_B_1838c_21c94 : GLRN 0x21c94 0x1838c}.
  Context {RN_B_21c84_21c94 : GLRN 0x21c94 0x21c84}.
  Context {RN_B_15f0c_21c94 : GLRN 0x21c94 0x15f0c}.
  Context {RN_B_21c84_15dc0 : GLRN 0x15dc0 0x21c84}.
  Context {RN_B_15f0c_15dc0 : GLRN 0x15dc0 0x15f0c}.
  Context {RN_B_stack_chk_fail_15dc0 : GLRN 0x15dc0 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Collection ImgHyps := IMG CODE_syscalls RB_syscalls CODE_syscalls_1 RB_syscalls_1 CODE_syscalls_2 RB_syscalls_2 CODE_syscalls_3 RB_syscalls_3 CODE_syscalls_4 RB_syscalls_4 CODE_syscalls_5 RB_syscalls_5 CODE_syscalls_6 RB_syscalls_6 CODE_syscalls_7 RB_syscalls_7 RN_B_15f44_15f0c RN_B_15f44_15f44 RN_B_21c60_21c60 RN_B_21c60_21c84 RN_B_21c84_21cf4 RN_B_15f0c_21cf4 RN_B_1838c_21c94 RN_B_21c84_21c94 RN_B_15f0c_21c94 RN_B_21c84_15dc0 RN_B_15f0c_15dc0 RN_B_stack_chk_fail_15dc0 RS_got_ssp RS_34288 rp_34288 RL0_0 rl0_0.



Definition sysret_entry := (sym 0x15f0c)%Z.
Definition read_entry := (sym 0x21cf4)%Z.
Definition close_entry := (sym 0x21c94)%Z.
Definition open_entry := (sym 0x15dc0)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ rw_cells img_segs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  rw_cells img_segs m (errno_addr tp) [C4 errv] ->
  mem_inv img_segs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt img_segs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x15f0c)) fc None m (seg_rom img_segs)).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.

(* [comment removed for export] *)
Definition sysret_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  rw_cells img_segs m (errno_addr tp) [C4 errv] ->
  mem_inv img_segs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt img_segs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x15f0c)) fc None m (seg_rom img_segs)).
Lemma sysret_spec_c_ok : sysret_spec_c.
Proof. exact sysret_spec. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells img_segs m' B [CB n junk]
                    /\ rw_cells img_segs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells img_segs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells img_segs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Lemma read_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  rw_cells img_segs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells img_segs m (errno_addr tp) [C4 errv] ->
  mem_inv img_segs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (0 <= count < 2^63)%Z ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl img_segs (at_node img_segs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 (sym 0x21cf4)) fc None m (seg_rom img_segs)).
Proof.
  intros until lo. intros ST DST ERR MI -> -> FD CNT LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_read_Some in Hdec; [|lia].
  destruct ans as [e|bs].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    finish; lia.
  - destruct Hdec as [-> Hlen]. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    finish; lia.
Qed.

(* [comment removed for export] *)
Definition read_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  rw_cells img_segs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells img_segs m (errno_addr tp) [C4 errv] ->
  mem_inv img_segs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (0 <= count < 2^63)%Z ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl img_segs (at_node img_segs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 (sym 0x21cf4)) fc None m (seg_rom img_segs)).
Lemma read_spec_c_ok : read_spec_c.
Proof. exact read_spec. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma eintr_mask_errno : forall e, (1 <= e <= 4095)%Z ->
  Z_to_bv 64 (Z.land ((Z.b2z ((bv_unsigned (errno_ret e) + 4) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                     (bv_unsigned (errno_ret e)))
  = if (e =? 4)%Z then Z_to_bv 64 0 else errno_ret e.
Proof.
  intros e He. rewrite unsigned_errno_ret by lia.
  destruct (Z.eqb_spec e 4) as [->|Hne].
  - replace ((2 ^ 64 - 4 + 4) mod 18446744073709551616)%Z with 0%Z by reflexivity.
    cbn. reflexivity.
  - assert (Hnz : ((2 ^ 64 - e + 4) mod 18446744073709551616 <? 1)%Z = false).
    { apply Z.ltb_ge. destruct (Z.ltb_spec0 e 4).
      - replace (2 ^ 64 - e + 4)%Z with ((4 - e) + 1 * 18446744073709551616)%Z by lia.
        rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    rewrite Hnz. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. change (2^64)%Z with 18446744073709551616%Z.
    rewrite Z.mod_small by lia. unfold errno_ret. rewrite <- (Z_to_bv_minus_mod (18446744073709551616 - e)). f_equal. lia.
Qed.

Definition close_ret (a : sret) : word :=
  match a with
  | SVal _ => Z_to_bv 64 0
  | SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
  end.
Definition close_errno (a : sret) (errv : word) : word :=
  match a with
  | SVal _ => errv
  | SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
  end.

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ rw_cells img_segs m' (errno_addr tp) [C4 (close_errno a errv)].

Lemma close_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  rw_cells img_segs m (errno_addr tp) [C4 errv] ->
  mem_inv img_segs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl img_segs (at_node img_segs) (enode (NClose fd) dec_close)
       (epost (close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 (sym 0x21c94)) fc None m (seg_rom img_segs)).
Proof.
  intros until lo. intros ST ERR MI -> FD LO SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|v].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 2 step. rewrite sextw_errno by lia.
    do 4 zstep. rewrite eintr_mask_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *.
    destruct (Z.eqb_spec e 4) as [->|Hne].
    + rewrite errno_of_lit in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. rewrite Z.eqb_refl. finish.
    + rewrite errno_of_errno_ret in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. replace (e =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). finish.
  - (nelim Hdec 3%nat; intros -> Hv _). apply Z.eqb_eq in Hv. subst v. unfold eff0. sys_nret.
    do 6 zstep. rewrite Z.land_0_r. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed.

(* [comment removed for export] *)
Definition close_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  rw_cells img_segs m (errno_addr tp) [C4 errv] ->
  mem_inv img_segs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl img_segs (at_node img_segs) (enode (NClose fd) dec_close)
       (epost (close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 (sym 0x21c94)) fc None m (seg_rom img_segs)).
Lemma close_spec_c_ok : close_spec_c.
Proof. exact close_spec. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := (sym 0x22e18)%Z.
Definition ssp_guard := (sym 0x34288)%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' lo (bv_unsigned sp)
    /\ rw_cells img_segs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at img_segs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells img_segs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells img_segs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Lemma open_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  bytes_at img_segs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells img_segs m (errno_addr tp) [C4 errv] ->
  rw_cells img_segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells img_segs m ssp_guard [C8 canary] ->
  mem_inv img_segs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl img_segs (at_node img_segs) (enode (NOpen path) dec_open)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 (sym 0x15dc0)) fc None m (seg_rom img_segs)).
Proof.
  intros until lo. intros ST SRC ERR GOT SSP MI -> NUL LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply impl_enode.
  carve_frame 96%nat ST.
  do 18 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - (nelim Hdec 3%nat; intros -> Hfd Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. unfold eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.

(* [comment removed for export] *)
Definition open_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk img_segs m lo (bv_unsigned sp) ->
  bytes_at img_segs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells img_segs m (errno_addr tp) [C4 errv] ->
  rw_cells img_segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells img_segs m ssp_guard [C8 canary] ->
  mem_inv img_segs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl img_segs (at_node img_segs) (enode (NOpen path) dec_open)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 (sym 0x15dc0)) fc None m (seg_rom img_segs)).
Lemma open_spec_c_ok : open_spec_c.
Proof. exact open_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class sysret_spec_c.
Existing Class read_spec_c.
Existing Class close_spec_c.
Existing Class open_spec_c.
