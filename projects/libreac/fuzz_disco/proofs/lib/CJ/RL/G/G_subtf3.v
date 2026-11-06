(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require SFW1_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgAt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgNotJ.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgNot.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require JunkAbs.
Module G_fe_getround.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW1_lemmas.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac. Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgNotJ. Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgNot.   
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition fe_getround_prog (B K_1145c : Z) : RStep.ptree :=
  PLeaf
    (PJ_Csr_CSR_RS_nnn 0 10 0 2 4
    (PJ_OpImm32_nnn 4 10 10 4095 4
    (PJ_OpImm_ALU_ADD_nnn 8 11 0 2 4
    (PJ_Branch_BC_LTU_nnn 12 11 10 28 4
    (PJ_ShiftImm_ALU_SLL_nnn 16 10 10 2 4
    (PJ_Auipc_nt 20 11 (hi20 (K_1145c - (B + 20))) 4
    (PJ_OpImm_ALU_ADD_nnt 24 11 11 (lo12 (K_1145c - (B + 20))) 4
    (PJ_Op_ALU_ADD_nnn 28 10 11 10 4
    (PJ_Load_SZ4_true_nnn 32 10 10 0 4
    (PJ_Jalr_nnn 36 0 1 0 4
    (PJ_OpImm_ALU_ADD_nnn 40 10 0 0 4
    (PJ_Jalr_nnn 44 0 1 0 4 nil)))))))))))).
(* [comment removed for export] *)
Definition fe_getround_prog_1 (B K_1145c : Z) : RStep.ptree :=
  PLeaf
    (PJ_CsrI_CSR_RS_nnn 0 0 1 1 4
    (PJ_OpImm_ALU_ADD_nnn 4 10 0 0 4
    (PJ_Jalr_nnn 8 0 1 0 4 nil))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_fe_getround (IMG : RImg) := fe_getround_prog (sym 0x1c44c) (sym 0x1145c).
Definition PROGAT_CODE_fe_getround_1 (IMG : RImg) := fe_getround_prog_1 (sym 0x1c47c) (sym 0x1145c).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_fe_getround : CodeAtT img_segs (sym 0x1c44c) (PROGAT_CODE_fe_getround IMG)}.
  Context {RB_fe_getround : RelCode (sym 0x1c44c) 48}.
  Context {CODE_fe_getround_1 : CodeAtT img_segs (sym 0x1c47c) (PROGAT_CODE_fe_getround_1 IMG)}.
  Context {RB_fe_getround_1 : RelCode (sym 0x1c47c) 12}.
  Context {RS_K_1145c : RelSym (sym 0x1145c)}.
  Collection ImgHyps := IMG CODE_fe_getround RB_fe_getround CODE_fe_getround_1 RB_fe_getround_1 RS_K_1145c.



Definition fe_getround_entry := (sym 0x1c44c)%Z.
Definition fe_raise_inexact_entry := (sym 0x1c47c)%Z.

(* [comment removed for export] *)
Definition fe_getround_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom img_segs)
    /\ munch [] m m /\ wmono img_segs m m /\ mem_inv img_segs m.

Lemma fe_getround_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m -> frm0 fc ->
  evt img_segs (fe_getround_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c44c)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI FRM.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  do 4 zstep. if_cases K; zify_cond K.
  - zstep. zstep. finish.
  - exfalso. revert K. vm_compute. congruence.
Qed.

(* [comment removed for export] *)
Definition fe_getround_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m -> frm0 fc ->
  evt img_segs (fe_getround_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c44c)) fc None m (seg_rom img_segs)).
Lemma fe_getround_spec_c_ok : fe_getround_spec_c.
Proof. exact fe_getround_spec. Qed.


(* [comment removed for export] *)
Definition fe_raise_inexact_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists fc',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc' None m (seg_rom img_segs)
    /\ munch [] m m /\ wmono img_segs m m /\ mem_inv img_segs m /\ frm0 fc'.

Lemma fe_raise_inexact_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m -> frm0 fc ->
  evt img_segs (fe_raise_inexact_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c47c)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI FRM.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  do 3 zstep. finish.
Qed.

(* [comment removed for export] *)
Definition fe_raise_inexact_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m -> frm0 fc ->
  evt img_segs (fe_raise_inexact_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c47c)) fc None m (seg_rom img_segs)).
Lemma fe_raise_inexact_spec_c_ok : fe_raise_inexact_spec_c.
Proof. exact fe_raise_inexact_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class fe_getround_spec_c.
Existing Class fe_raise_inexact_spec_c.
End G_fe_getround.

(* [comment removed for export] *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require SFW_add_split.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G Require ProgAt3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require F_sf_helpers2.
From Stdlib Require Zify.
Module G_addtf3_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW1_lemmas OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW_add_split.
Import G_fe_getround.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.Prog_addtf3.   Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.ProgAt. 
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_addtf3_A : CodeAtT img_segs (sym 0x1bc80) (addtf3_prog_at IMG)}.
  Context {RB_addtf3_A : RelCode (sym 0x1bc80) 1996}.
  Context {RN_B_fe_getround_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c44c)}.
  Context {RN_B_fe_raise_inexact_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c47c)}.
  Context {SPEC_fe_getround_spec : fe_getround_spec_c}.
  Context {SPEC_fe_raise_inexact_spec : fe_raise_inexact_spec_c}.
  Collection ImgHyps := IMG CODE_addtf3_A RB_addtf3_A RN_B_fe_getround_1bc80 RN_B_fe_raise_inexact_1bc80 SPEC_fe_getround_spec SPEC_fe_raise_inexact_spec.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

Definition addtf3_entry := (sym 0x1bc80)%Z.

(* [comment removed for export] *)
Definition addtf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc' None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ frm0 fc'
    /\ stk img_segs m' (bv_unsigned sp - 48) (bv_unsigned sp).

Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
                                   ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].

  Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "t3=" x28; idtac "t4=" x29.


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
  Hypothesis FRM : frm0 fc.
  Hypothesis MI : mem_inv img_segs m1.
  Hypothesis FR : rw_cells img_segs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis STK : stk img_segs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono img_segs m m1.
  Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

  Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).
  (* [comment removed for export] *)
  Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fcx None m1 (seg_rom img_segs)).

  (* [comment removed for export] *)
  Lemma add_Lret : forall fcx x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (lo hi r : Z),
    frm0 fcx -> (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z ->
    r = mk128 hi lo ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1924) fcx x1 x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR MI MU STK WM ImgHyps.
    intros until r. intros FRMx Rlo Rhi HR. subst r.
    pose proof FR as FR'. pose proof STK as ST'.
    do 10 zstep.
    release_frame FR' ST' (bv_unsigned sp).
    replace (bv_unsigned sp + -48)%Z with (bv_unsigned sp - 48)%Z in ST' by lia.
    sf_finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma add_Lround : forall x1 x5 x6 x7 x8 x9 x14 x16 x17 x19 x20 x28 x29 x30 x31 (SHi SLo aExp signHi r : Z),
    (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= signHi < 2^64)%Z ->
    r = round_mirror SHi SLo aExp signHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1784) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 (Z_to_bv 64 aExp) x16 x17 (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 HR. subst r. unfold round_mirror. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. name_reg 19%Z rgs.
    do 5 zstep. name_reg 20%Z resLo0.
    do 2 zstep. zstep. showregs. name_reg 9%Z resLo. zstep. name_reg 8%Z resHi.
    zstep. call SPEC_fe_getround_spec. 1-2: assumption.
    zstep. zstep. if_cases Kc; zify_cond Kc; [exfalso; clear -Kc; lia|].
    zstep. zstep. if_cases Kc2; zify_cond Kc2; [exfalso; clear -Kc2; lia|].
    zstep. if_cases Kc3; zify_cond Kc3. { exfalso. clear -Kc3. lia. }
    zstep. zstep. if_cases Kt; zify_cond Kt; decide_test1_try (rgs =? 4%Z)%Z; decide_test1_try (rgs <? 5%Z)%Z.
    - (* [comment removed for export] *)
      zstep. zstep. rewrite lxor1_b2z. name_reg 10%Z inc. zstep.
      zstep. model_reg 10%Z sumLo (Z.land (resLo + inc) W64).
      zstep. zstep. model_reg 8%Z resHi2 (Z.land (resHi + Z.b2z (sumLo <? resLo)) W64).
      zstep. zstep. if_cases Kz; zify_cond Kz.
      + (* [comment removed for export] *)
        eapply add_Lret; [exact FRM | zrange | zrange | reflexivity].
      + zstep. call SPEC_fe_raise_inexact_spec. 1-2: assumption.
        eapply add_Lret; [assumption | zrange | zrange | reflexivity].
    - (* [comment removed for export] *)
      zstep. name_reg 10%Z inc.
      zstep. model_reg 10%Z sumLo (Z.land (resLo + inc) W64).
      zstep. zstep. model_reg 8%Z resHi2 (Z.land (resHi + Z.b2z (sumLo <? resLo)) W64).
      zstep. zstep. zstep. call SPEC_fe_raise_inexact_spec. 1-2: assumption.
      eapply add_Lret; [assumption | zrange | zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma add_L704 : forall x1 x6 x7 x8 x9 x10 x14 x15 x19 x20 x28 x29 x30 x31 (signHi hiSh mask4 sticky newLo r : Z),
    (0 <= signHi < 2^64)%Z -> (0 <= hiSh < 2^64)%Z -> (0 <= mask4 < 2^64)%Z -> (0 <= sticky < 2^64)%Z -> (0 <= newLo < 2^64)%Z ->
    r = denorm_3 signHi hiSh mask4 sticky newLo ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1772) fc x1 (Z_to_bv 64 mask4) x6 x7 x8 x9 x10 (Z_to_bv 64 newLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 x15 (Z_to_bv 64 hiSh) (Z_to_bv 64 sticky) (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 HR. subst r. unfold denorm_3.
    do 3 zstep.
    eapply add_Lround; [zrange | zrange | lia | zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma add_L6c0 : forall x1 x5 x6 x7 x8 x9 x19 x20 x28 x29 x30 x31 (signHi SHi SLo shift d3 mask3 t outHi r : Z),
    (0 <= signHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= shift < 2^64)%Z ->
    (0 <= d3 < 2^64)%Z -> (0 <= t < 2^64)%Z -> (0 <= outHi < 2^64)%Z ->
    (if 9223372036854775808 <=? d3 then 18446744073709551615 else 0)%Z = mask3 ->
    r = denorm_2 signHi SHi SLo shift mask3 t outHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1704) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 shift) (Z_to_bv 64 t) (Z_to_bv 64 d3) (Z_to_bv 64 outHi) (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 Hm HR. subst r. unfold denorm_2. unfold_sfw. rewrite ?b2z_Zb2z.
    assert (Rm3 : (0 <= mask3 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. rewrite (srai63_word d3), Hm by lia.
    zstep. name_as_by hiSh (Z.shiftr SHi (Z.land shift 63))
      (change (inr64 (Z.shiftr SHi (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
    zstep. zstep. name_reg 5%Z outLo.
    zstep. name_reg 15%Z n3.
    zstep. name_reg 17%Z lor1. rewrite (zb_negb_eqb0 lor1) by zrange_nonneg.
    zstep. model_reg 6%Z d4 (Z.land (n3 - 64) W64).
    rewrite (sra63_leb d4) by lia.
    zstep. name_reg 17%Z sticky.
    zstep. rewrite (srai63_word d4) by lia. name_reg 5%Z mask4.
    zstep. if_cases K4; zify_cond K4; decide_test1 ((d4 ≫ 63)%Z =? 0%Z)%Z.
    - (* [comment removed for export] *)
      zstep. name_as_by sr1 (Z.shiftr SLo (Z.land shift 63))
        (change (inr64 (Z.shiftr SLo (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      do 4 zstep. name_reg 11%Z newLo.
      eapply add_L704; [zrange | zrange | zrange | zrange | zrange | reflexivity].
    - zstep. name_as_by newLo (Z.shiftr SHi (Z.land n3 63))
        (change (inr64 (Z.shiftr SHi (Z.land n3 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. eapply add_L704; [zrange | zrange | zrange | zrange | zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma add_LM8 : forall x1 x5 x6 x7 x8 x9 x14 x16 x17 x19 x20 x28 x29 x30 x31 (SHi SLo aExp signHi r : Z),
    (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= signHi < 2^64)%Z ->
    r = add_M8 SHi SLo aExp signHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1636) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 (Z_to_bv 64 aExp) x16 x17 (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 HR. subst r. unfold add_M8. unfold_sfw.
    zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_test1 (9223372036854775808%Z <? (Z.lxor aExp 9223372036854775808))%Z.
    - (* [comment removed for export] *) eapply add_Lround; [zrange | zrange | zrange | zrange | reflexivity].
    - (* [comment removed for export] *)
      unfold denorm_mirror. unfold_sfw. rewrite ?b2z_Zb2z.
      do 3 zstep. model_reg 14%Z shift (Z.land (1 - aExp) W64).
      zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (0 - shift)).
      name_as_by negsh (sext32 (0 - shift)) (apply sext32_range).
      zstep. model_reg 16%Z d3 (Z.land (64 - shift) W64).
      zstep. model_reg 15%Z t (Z.land (Z.shiftl SLo (Z.land negsh 63)) W64).
      zstep. if_cases K3; zify_cond K3; decide_test1 ((d3 ≫ 63)%Z =? 0%Z)%Z.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (128 - shift)).
        name_as_by mm (sext32 (128 - shift)) (apply sext32_range).
        zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor mm W64) 63))
          (change (inr64 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor mm W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
        zstep. name_reg 17%Z outHi.
        eapply add_L6c0 with (mask3 := 18446744073709551615%Z);
          [zrange | zrange | zrange | zrange | zrange | zrange | zrange | decide_tests_b; reflexivity | reflexivity].
      + (* [comment removed for export] *)
        zstep. zstep.
        eapply add_L6c0 with (mask3 := 0%Z);
          [zrange | zrange | zrange | zrange | zrange | zrange | zrange | decide_tests_b; reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma add_LM7 : forall x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x28 x29 x30 x31 (xHi SHi SLo aExp r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    r = add_M7 xHi SHi SLo aExp ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1500) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 HR. subst r. unfold add_M7. unfold_sfw.
    do 3 zstep. zstep. model_reg 18%Z signHi (Z.land (Z.shiftl (Z.shiftr xHi 63) 63) W64).
    zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_test1 ((Z.lxor aExp 9223372036854775808) <? 9223372036854808575%Z)%Z.
    - (* [comment removed for export] *) eapply add_LM8; [zrange | zrange | zrange | zrange | reflexivity].
    - (* [comment removed for export] *)
      do 5 zstep. eapply add_Lret; [exact FRM | lia | zrange | reflexivity].
  Qed.
End Proofs.

End Img.
(* [comment removed for export] *)
Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
                                   ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].
Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "t3=" x28; idtac "t4=" x29.
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.
End G_addtf3_A.

(* [comment removed for export] *)
Module G_addtf3_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW1_lemmas OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW_add_split.
Import G_fe_getround G_addtf3_A.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.Prog_addtf3.   Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.ProgAt. 
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_addtf3_B : CodeAtT img_segs (sym 0x1bc80) (addtf3_prog_at IMG)}.
  Context {RB_addtf3_B : RelCode (sym 0x1bc80) 1996}.
  Context {RN_B_fe_getround_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c44c)}.
  Context {RN_B_fe_raise_inexact_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c47c)}.
  Context {SPEC_fe_getround_spec : fe_getround_spec_c}.
  Context {SPEC_fe_raise_inexact_spec : fe_raise_inexact_spec_c}.
  Collection ImgHyps := IMG CODE_addtf3_B RB_addtf3_B RN_B_fe_getround_1bc80 RN_B_fe_raise_inexact_1bc80 SPEC_fe_getround_spec SPEC_fe_raise_inexact_spec.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
  Hypothesis FRM : frm0 fc.
  Hypothesis MI : mem_inv img_segs m1.
  Hypothesis FR : rw_cells img_segs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis STK : stk img_segs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono img_segs m m1.
  Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

  Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).
  (* [comment removed for export] *)
  Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fcx None m1 (seg_rom img_segs)).


  (* [comment removed for export] *)
  Lemma add_L658 : forall x1 x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 (xHi SLo aExp shiftS d mask nhi r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= shiftS < 2^64)%Z ->
    (0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
    (if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
    r = subR3 xHi SLo aExp shiftS mask nhi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1600) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 nhi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 shiftS) (Z_to_bv 64 d) x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 Hm HR. subst r. unfold subR3, shl128_lo, add_M7. unfold_sfw.
    assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. zstep. rewrite (srai63_word d), Hm by lia.
    zstep. name_reg 11%Z nlo.
    zstep. model_reg 15%Z aExp2 (Z.land (aExp - shiftS) W64).
    do 3 zstep. zstep. model_reg 18%Z signHi (Z.land (Z.shiftl (Z.shiftr xHi 63) 63) W64).
    zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_test1 ((Z.lxor aExp2 9223372036854775808) <? 9223372036854808575%Z)%Z.
    - (* [comment removed for export] *)
      do 5 zstep. eapply add_Lret; finL.
    - eapply add_LM8; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L488 : forall x1 x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 (xHi SHi SLo aExp word hz r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
    r = subR2 xHi SHi SLo aExp word hz ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1136) fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 hz) (Z_to_bv 64 word) x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold subR2, clz128_w. unfold shl128_mirror. unfold_sfw.
    (* [comment removed for export] *)
    do 5 zstep. model_reg 17%Z x1_ (Z.lor word (Z.shiftr word 1)).
    do 5 zstep. model_reg 17%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
    do 8 zstep. model_reg 17%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
    do 2 zstep. model_reg 17%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
    do 2 zstep. model_reg 17%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
    do 2 zstep. model_reg 17%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
    zstep. model_reg 17%Z y_ (Z.lxor x6_ W64).
    do 4 zstep. model_reg 17%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
    do 6 zstep. model_reg 17%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
    do 4 zstep. model_reg 17%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
    do 3 zstep. model_reg 17%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
    replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
    name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
    zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    name_reg 16%Z clzS.
    zstep. model_reg 16%Z shiftS (Z.land (clzS - 12) W64).
    zstep. zstep. name_reg 5%Z n. zstep. model_reg 17%Z d (Z.land (n - 64) W64).
    zstep. if_cases Kd; zify_cond Kd; decide_test1 ((d ≫ 63)%Z =? 0%Z)%Z.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. name_reg 10%Z nhi.
      eapply add_L658 with (mask := 18446744073709551615%Z); finL.
    - (* [comment removed for export] *)
      zstep. model_reg 10%Z nhi (Z.land (Z.shiftl SLo (Z.land n 63)) W64). zstep.
      eapply add_L658 with (mask := 0%Z); finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_Lsub : forall x1 x6 x8 x9 x11 x17 x18 x19 x20 x28 x29 x30 x31 (xHi AHi ALo BHi BLo aExp r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= AHi < 2^64)%Z -> (0 <= ALo < 2^64)%Z -> (0 <= BHi < 2^64)%Z -> (0 <= BLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    r = add_M6s xHi AHi ALo BHi BLo aExp ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1068) fc x1 (Z_to_bv 64 ALo) x6 (Z_to_bv 64 BLo) x8 x9 (Z_to_bv 64 AHi) x11 (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 BHi) x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold add_M6s, addsub_sub. unfold_sfw. rewrite ?b2z_Zb2z.
    do 4 zstep. if_cases Kz; zify_cond Kz; decide_test1 ((Z.lor (Z.lxor ALo BLo) (Z.lxor AHi BHi)) =? 0%Z)%Z.
    - (* [comment removed for export] *)
      zstep. name_reg 11%Z borrow.
      zstep. zstep. model_reg 10%Z SHi (Z.land (Z.land (AHi - BHi) W64 - borrow) W64).
      zstep. zstep. model_reg 11%Z SLo (Z.land (ALo - BLo) W64).
      zstep. if_cases Kr; zify_cond Kr; decide_test1 ((SHi ≫ 51)%Z =? 0%Z)%Z.
      + (* [comment removed for export] *) eapply add_LM7; finL.
      + (* [comment removed for export] *)
        rewrite clz128_mirror_w. rewrite ?b2z_Zb2z.
        zstep. rewrite (ltb1_eqb0 SHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_test1 (SHi =? 0%Z)%Z.
        * (* [comment removed for export] *) change (Z.b2z true) with 1%Z. eapply add_L488; finL.
        * change (Z.b2z false) with 0%Z. zstep. eapply add_L488; finL.
    - (* [comment removed for export] *)
      do 3 zstep. eapply add_Lret; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_Ladd : forall x1 x6 x8 x9 x11 x17 x18 x19 x20 x28 x29 x30 x31 (xHi AHi ALo BHi BLo aExp r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= AHi < 2^64)%Z -> (0 <= ALo < 2^64)%Z -> (0 <= BHi < 2^64)%Z -> (0 <= BLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    r = add_M6a xHi AHi ALo BHi BLo aExp ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1448) fc x1 (Z_to_bv 64 ALo) x6 (Z_to_bv 64 BLo) x8 x9 (Z_to_bv 64 AHi) x11 (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 BHi) x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold add_M6a, addsub_add. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. model_reg 11%Z SLo (Z.land (BLo + ALo) W64).
    zstep. name_reg 17%Z carry.
    zstep. zstep.
    replace (Z_to_bv 64 (BHi + AHi + carry)) with (Z_to_bv 64 (Z.land (Z.land (BHi + AHi) W64 + carry) W64))
      by (apply Z_to_bv_eqm; rewrite !land_W64; Z.div_mod_to_equations; lia).
    name_as SHi (Z.land (Z.land (BHi + AHi) W64 + carry) W64).
    zstep. zstep. if_cases Kc; zify_cond Kc; decide_test1 ((Z.land (SHi ≪ 11) 18446744073709551615 ≫ 63)%Z =? 0%Z)%Z.
    - (* [comment removed for export] *) eapply add_LM7; finL.
    - (* [comment removed for export] *)
      zstep. name_reg 16%Z st.
      do 5 zstep. name_reg 11%Z SLo2.
      zstep. model_reg 15%Z aExp2 (Z.land (aExp + 1) W64).
      eapply add_LM7; finL.
  Qed.
End Proofs.

End Img.
(* [comment removed for export] *)
Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.
End G_addtf3_B.

(* [comment removed for export] *)
Module G_addtf3_C.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW1_lemmas OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW_add_split.
Import G_fe_getround G_addtf3_A G_addtf3_B.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.Prog_addtf3.   Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.ProgAt. 
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_addtf3_C : CodeAtT img_segs (sym 0x1bc80) (addtf3_prog_at IMG)}.
  Context {RB_addtf3_C : RelCode (sym 0x1bc80) 1996}.
  Context {RN_B_fe_getround_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c44c)}.
  Context {RN_B_fe_raise_inexact_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c47c)}.
  Context {SPEC_fe_getround_spec : fe_getround_spec_c}.
  Context {SPEC_fe_raise_inexact_spec : fe_raise_inexact_spec_c}.
  Collection ImgHyps := IMG CODE_addtf3_C RB_addtf3_C RN_B_fe_getround_1bc80 RN_B_fe_raise_inexact_1bc80 SPEC_fe_getround_spec SPEC_fe_raise_inexact_spec.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
  Hypothesis FRM : frm0 fc.
  Hypothesis MI : mem_inv img_segs m1.
  Hypothesis FR : rw_cells img_segs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis STK : stk img_segs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono img_segs m m1.
  Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

  Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).
  (* [comment removed for export] *)
  Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fcx None m1 (seg_rom img_segs)).


  (* [comment removed for export] *)
  Lemma add_L5a4 : forall x1 x8 x9 x18 x19 x20 x30 x31 (xHi sw aSigHi3 aSigLo aExp bSigHi3 align d2 mask2 sticky newLo r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= sw < 2^64)%Z -> (0 <= aSigHi3 < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigHi3 < 2^64)%Z -> (0 <= align < 2^64)%Z -> (0 <= d2 < 2^64)%Z -> (0 <= sticky < 2^64)%Z -> (0 <= newLo < 2^64)%Z ->
    (if 9223372036854775808 <=? d2 then 18446744073709551615 else 0)%Z = mask2 ->
    r = align_4 xHi (Z.shiftr sw 63) (Z.lor aSigHi3 2251799813685248) (Z.land (Z.shiftl aSigLo 3) W64) aExp bSigHi3 align mask2 sticky newLo ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1420) fc x1 (Z_to_bv 64 align) (Z_to_bv 64 2251799813685248) (Z_to_bv 64 sticky) x8 x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 sw) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigHi3) (Z_to_bv 64 aSigHi3)
                           x18 x19 x20 (Z_to_bv 64 newLo) (Z_to_bv 64 d2) x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 Hm HR. subst r. unfold align_4.
    assert (Rm : (0 <= mask2 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. name_as_by srH (Z.shiftr bSigHi3 (Z.land align 63))
      (change (inr64 (Z.shiftr bSigHi3 (Z.land align 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
    zstep. rewrite (srai63_word d2), Hm by lia.
    zstep. name_reg 16%Z newHi.
    zstep. name_reg 7%Z BLo.
    zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64).
    zstep. name_reg 10%Z AHi.
    unfold add_M6, addsub_mirror. unfold_sfw.
    zstep. if_cases Ks; zify_cond Ks; decide_test1 (Z.shiftr sw 63 =? 0)%Z.
    - (* [comment removed for export] *) eapply add_Lsub; finL.
    - eapply add_Ladd; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L564 : forall x1 x8 x9 x18 x19 x20 x31 (xHi sw aSigHi3 aSigLo aExp bSigHi3 bSigLo3 align d1 mask1 negal outHi r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= sw < 2^64)%Z -> (0 <= aSigHi3 < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigHi3 < 2^64)%Z -> (0 <= bSigLo3 < 2^64)%Z -> (0 <= align < 2^64)%Z -> (0 <= d1 < 2^64)%Z -> (0 <= negal < 2^64)%Z -> (0 <= outHi < 2^64)%Z ->
    (if 9223372036854775808 <=? d1 then 18446744073709551615 else 0)%Z = mask1 ->
    r = align_3 xHi (Z.shiftr sw 63) (Z.lor aSigHi3 2251799813685248) (Z.land (Z.shiftl aSigLo 3) W64) aExp bSigHi3 bSigLo3 align mask1 negal outHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 1356) fc x1 (Z_to_bv 64 align) (Z_to_bv 64 2251799813685248) (Z_to_bv 64 d1) x8 x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 sw) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigHi3) (Z_to_bv 64 aSigHi3)
                           x18 x19 x20 (Z_to_bv 64 bSigLo3) (Z_to_bv 64 negal) (Z_to_bv 64 outHi) x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold align_3. unfold_sfw. rewrite ?b2z_Zb2z.
    assert (Rm : (0 <= mask1 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. model_reg 29%Z outLoRaw (Z.land (Z.shiftl bSigLo3 (Z.land negal 63)) W64).
    zstep. rewrite (srai63_word d1), Hm by lia.
    zstep. name_reg 7%Z outLo.
    zstep. zstep. name_reg 31%Z n2.
    zstep. name_reg 7%Z lor1. rewrite (zb_negb_eqb0 lor1) by zrange_nonneg.
    zstep. model_reg 29%Z d2 (Z.land (n2 - 64) W64).
    zstep. name_reg 7%Z sticky.
    zstep. if_cases Kd; zify_cond Kd; decide_test1 (Z.shiftr d2 63 =? 0)%Z.
    - (* [comment removed for export] *)
      zstep. name_as_by srL (Z.shiftr bSigLo3 (Z.land align 63))
        (change (inr64 (Z.shiftr bSigLo3 (Z.land align 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      do 4 zstep. name_reg 28%Z newLo.
      eapply add_L5a4 with (mask2 := 18446744073709551615%Z); finL.
    - zstep. name_as_by newLo (Z.shiftr bSigHi3 (Z.land n2 63))
        (change (inr64 (Z.shiftr bSigHi3 (Z.land n2 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. eapply add_L5a4 with (mask2 := 0%Z); finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_LM4 : forall x1 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
    (0 <= aExp < 2^64)%Z -> (0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
    r = add_M4 aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 936) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 bSigHi) x7 (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 HR. subst r. unfold add_M4. unfold align_mirror. unfold_sfw.
    zstep. name_reg 11%Z sw.
    do 6 zstep. name_reg 17%Z aSigHi3.
    zstep. zstep. model_reg 28%Z bSigLo3 (Z.land (Z.shiftl bSigLo 3) W64).
    zstep. zstep. name_reg 16%Z bSigHi3.
    zstep. if_cases Ke; zify_cond Ke; decide_test1 (aExp =? bExp)%Z.
    - (* [comment removed for export] *)
      zstep. model_reg 5%Z align (Z.land (aExp - bExp) W64).
      zstep. zstep. if_cases Kb; zify_cond Kb; decide_test1 (127 <? align)%Z.
      + (* [comment removed for export] *)
        zstep. zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64). zstep. name_reg 10%Z AHi.
        unfold add_M6, addsub_mirror. unfold_sfw.
        zstep. if_cases Ks; zify_cond Ks; decide_test1 (Z.shiftr sw 63 =? 0)%Z.
        * eapply add_Ladd; finL.
        * eapply add_Lsub; finL.
      + (* [comment removed for export] *)
        do 4 zstep. rewrite (landM32_swrap_land64 (128 - align)). name_reg 30%Z n1.
        zstep. model_reg 7%Z d1 (Z.land (n1 - 64) W64).
        zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (0 - align)).
        name_as_by negal (sext32 (0 - align)) (apply sext32_range).
        zstep. if_cases Kd; zify_cond Kd; decide_test1 (Z.shiftr d1 63 =? 0)%Z.
        * (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr bSigLo3 1) (Z.land (Z.lxor n1 W64) 63))
            (change (inr64 (Z.shiftr (Z.shiftr bSigLo3 1) (Z.land (Z.lxor n1 W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
          zstep. name_reg 30%Z outHi.
          eapply add_L564 with (mask1 := 18446744073709551615%Z); finL.
        * zstep. model_reg 30%Z outHi (Z.land (Z.shiftl bSigLo3 (Z.land n1 63)) W64). zstep.
          eapply add_L564 with (mask1 := 0%Z); finL.
    - (* [comment removed for export] *)
      zstep. zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64). zstep. name_reg 10%Z AHi.
      unfold add_M6, addsub_mirror. unfold_sfw.
      zstep. if_cases Ks; zify_cond Ks; decide_test1 (Z.shiftr sw 63 =? 0)%Z.
      + eapply add_Ladd; finL.
      + zstep. eapply add_Lsub; finL.
  Qed.
End Proofs.

End Img.
(* [comment removed for export] *)
Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
End G_addtf3_C.

(* [comment removed for export] *)
Module G_addtf3_D.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW1_lemmas OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW_add_split.
Import G_fe_getround G_addtf3_A G_addtf3_B G_addtf3_C.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.Prog_addtf3.   Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.ProgAt. 
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_addtf3_D : CodeAtT img_segs (sym 0x1bc80) (addtf3_prog_at IMG)}.
  Context {RB_addtf3_D : RelCode (sym 0x1bc80) 1996}.
  Context {RN_B_fe_getround_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c44c)}.
  Context {RN_B_fe_raise_inexact_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c47c)}.
  Context {SPEC_fe_getround_spec : fe_getround_spec_c}.
  Context {SPEC_fe_raise_inexact_spec : fe_raise_inexact_spec_c}.
  Collection ImgHyps := IMG CODE_addtf3_D RB_addtf3_D RN_B_fe_getround_1bc80 RN_B_fe_raise_inexact_1bc80 SPEC_fe_getround_spec SPEC_fe_raise_inexact_spec.


(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
  Hypothesis FRM : frm0 fc.
  Hypothesis MI : mem_inv img_segs m1.
  Hypothesis FR : rw_cells img_segs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis STK : stk img_segs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono img_segs m m1.
  Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

  Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).
  (* [comment removed for export] *)
  Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fcx None m1 (seg_rom img_segs)).


  (* [comment removed for export] *)
  Lemma add_L3ac : forall x1 x9 x18 x19 x20 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigLo clz sh d mask nhi r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigLo < 2^64)%Z -> (0 <= clz < 2^64)%Z -> (0 <= sh < 2^64)%Z -> (0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
    (if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
    r = normB3 aHi bHi xHi aSigHi aSigLo aExp bSigLo clz sh mask nhi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 916) fc x1 (Z_to_bv 64 clz) (Z_to_bv 64 nhi) (Z_to_bv 64 sh) (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 (Z_to_bv 64 d) x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold normB3, shl128_lo. unfold_sfw.
    assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. zstep. rewrite (srai63_word d), Hm by lia.
    zstep. zstep. name_reg 16%Z nlo.
    zstep. model_reg 5%Z bExp2 (Z.land (16 - clz) W64).
    eapply add_LM4; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L2d0 : forall x1 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo word hz r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z -> (0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
    r = (let '(h, l, e) := norm_w2 bSigHi bSigLo word hz in add_M4 aHi bHi xHi aSigHi aSigLo aExp h l e) ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 696) fc x1 (Z_to_bv 64 hz) (Z_to_bv 64 bSigHi) (Z_to_bv 64 word) (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 HR. subst r. unfold norm_w2, clz128_w. unfold shl128_mirror. unfold_sfw.
    (* [comment removed for export] *)
    do 5 zstep. model_reg 7%Z x1_ (Z.lor word (Z.shiftr word 1)).
    do 5 zstep. model_reg 7%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
    do 8 zstep. model_reg 7%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
    do 2 zstep. model_reg 7%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
    do 2 zstep. model_reg 7%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
    do 2 zstep. model_reg 7%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
    zstep. model_reg 7%Z y_ (Z.lxor x6_ W64).
    do 4 zstep. model_reg 7%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
    do 6 zstep. model_reg 7%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
    do 4 zstep. model_reg 7%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
    do 3 zstep. model_reg 7%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
    replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
    name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
    zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    name_as_by clz (Z.lor clz64v (Z.shiftl hz 6))
      (change (inr64 (Z.lor clz64v (Z.shiftl hz 6))); apply zr_lor; [zrange | apply zr_lit; rewrite Z.shiftl_mul_pow2 by lia; lia]).
    zstep. model_reg 7%Z sh (Z.land (clz - 15) W64).
    zstep. zstep. name_reg 29%Z n. zstep. model_reg 28%Z d (Z.land (n - 64) W64).
    zstep. if_cases Kd; zify_cond Kd; decide_test1 ((d ≫ 63)%Z =? 0%Z)%Z.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr bSigLo 1) (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr (Z.shiftr bSigLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. name_reg 6%Z nhi.
      eapply add_L3ac with (mask := 18446744073709551615%Z); finL.
    - zstep. model_reg 6%Z nhi (Z.land (Z.shiftl bSigLo (Z.land n 63)) W64). zstep.
      eapply add_L3ac with (mask := 0%Z); finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L2c0 : forall x1 x5 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z ->
    r = (let '(h, l, e) := normalize_mirror bSigHi bSigLo in add_M4 aHi bHi xHi aSigHi aSigLo aExp h l e) ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 680) fc x1 x5 (Z_to_bv 64 bSigHi) x7 (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 HR. subst r. rewrite normalize_mirror_w. rewrite ?b2z_Zb2z.
    zstep. rewrite (ltb1_eqb0 bSigHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_test1 (bSigHi =? 0%Z)%Z.
    - (* [comment removed for export] *) change (Z.b2z true) with 1%Z. eapply add_L2d0; finL.
    - change (Z.b2z false) with 0%Z. zstep. eapply add_L2d0; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L2a4 : forall x1 x9 x18 x19 x20 x29 x30 x31 (aHi bHi xHi aSigLo yHi yLo bExp clz sh d mask nhi r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z ->
    (0 <= bExp < 2^64)%Z -> (0 <= clz < 2^64)%Z -> (0 <= sh < 2^64)%Z -> (0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
    (if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
    r = normA3 aHi bHi xHi aSigLo yHi yLo bExp clz sh mask nhi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 652) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) (Z_to_bv 64 sh) (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 clz) (Z_to_bv 64 yLo) (Z_to_bv 64 nhi)
                           x18 x19 x20 (Z_to_bv 64 d) x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold normA3, shl128_lo.
    assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    unfold add_M3b. unfold_sfw.
    zstep. zstep. rewrite (srai63_word d), Hm by lia.
    zstep. zstep. name_reg 10%Z nlo.
    zstep. model_reg 15%Z aExp2 (Z.land (16 - clz) W64).
    zstep. name_reg 6%Z bSigHi.
    zstep. if_cases Kb; zify_cond Kb; decide_test1 (bExp =? 0%Z)%Z.
    - (* [comment removed for export] *) eapply add_LM4; finL.
    - (* [comment removed for export] *) eapply add_L2c0; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L194 : forall x1 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo yHi yLo bExp word hz r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
    (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z -> (0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
    r = (let '(h, l, e) := norm_w2 aSigHi aSigLo word hz in add_M3b aHi bHi xHi h l e (Z.land yHi MASK48) yLo bExp) ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 380) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) (Z_to_bv 64 word) (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 hz) (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 HR. subst r. unfold norm_w2, clz128_w. unfold shl128_mirror. unfold_sfw.
    (* [comment removed for export] *)
    do 5 zstep. model_reg 7%Z x1_ (Z.lor word (Z.shiftr word 1)).
    do 5 zstep. model_reg 7%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
    do 8 zstep. model_reg 7%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
    do 2 zstep. model_reg 7%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
    do 2 zstep. model_reg 7%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
    do 2 zstep. model_reg 7%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
    zstep. model_reg 7%Z y_ (Z.lxor x6_ W64).
    do 4 zstep. model_reg 7%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
    do 6 zstep. model_reg 7%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
    do 4 zstep. model_reg 7%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
    do 3 zstep. model_reg 7%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
    replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
    name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
    zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    name_as_by clz (Z.lor clz64v (Z.shiftl hz 6))
      (change (inr64 (Z.lor clz64v (Z.shiftl hz 6))); apply zr_lor; [zrange | apply zr_lit; rewrite Z.shiftl_mul_pow2 by lia; lia]).
    zstep. model_reg 7%Z sh (Z.land (clz - 15) W64).
    zstep. zstep. name_reg 29%Z n. zstep. model_reg 28%Z d (Z.land (n - 64) W64).
    zstep. if_cases Kd; zify_cond Kd; decide_test1 ((d ≫ 63)%Z =? 0%Z)%Z.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr aSigLo 1) (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr (Z.shiftr aSigLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. name_reg 17%Z nhi.
      eapply add_L2a4 with (mask := 18446744073709551615%Z); finL.
    - zstep. model_reg 17%Z nhi (Z.land (Z.shiftl aSigLo (Z.land n 63)) W64). zstep.
      eapply add_L2a4 with (mask := 0%Z); finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L184 : forall x1 x7 x9 x15 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo yHi yLo bExp r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
    (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
    r = (let '(h, l, e) := normalize_mirror aSigHi aSigLo in add_M3b aHi bHi xHi h l e (Z.land yHi MASK48) yLo bExp) ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 364) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) x7 (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) x15 (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 HR. subst r. rewrite normalize_mirror_w. rewrite ?b2z_Zb2z.
    zstep. rewrite (ltb1_eqb0 aSigHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_test1 (aSigHi =? 0%Z)%Z.
    - change (Z.b2z true) with 1%Z. eapply add_L194; finL.
    - change (Z.b2z false) with 0%Z. zstep. eapply add_L194; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L0d4 : forall x1 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp yHi yLo bExp r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
    r = add_M3b aHi bHi xHi aSigHi aSigLo aExp (Z.land yHi MASK48) yLo bExp ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 188) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) x7 (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 HR. subst r. unfold add_M3b. unfold_sfw.
    zstep. name_reg 6%Z bSigHi.
    zstep. if_cases Kb; zify_cond Kb; decide_test1 (bExp =? 0%Z)%Z.
    - eapply add_LM4; finL.
    - zstep. eapply add_L2c0; finL.
  Qed.
End Proofs.

End Img.
(* [comment removed for export] *)
Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.
End G_addtf3_D.

(* [comment removed for export] *)
Module G_addtf3_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW1_lemmas OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.SFW_add_split.
Import G_fe_getround G_addtf3_A G_addtf3_B G_addtf3_C G_addtf3_D.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.Prog_addtf3.   Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.G.ProgAt3.ProgAt. 
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_addtf3_E : CodeAtT img_segs (sym 0x1bc80) (addtf3_prog_at IMG)}.
  Context {RB_addtf3_E : RelCode (sym 0x1bc80) 1996}.
  Context {RN_B_fe_getround_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c44c)}.
  Context {RN_B_fe_raise_inexact_1bc80 : RelNear (sym 0x1bc80) (sym 0x1c47c)}.
  Context {SPEC_fe_getround_spec : fe_getround_spec_c}.
  Context {SPEC_fe_raise_inexact_spec : fe_raise_inexact_spec_c}.
  Collection ImgHyps := IMG CODE_addtf3_E RB_addtf3_E RN_B_fe_getround_1bc80 RN_B_fe_raise_inexact_1bc80 SPEC_fe_getround_spec SPEC_fe_raise_inexact_spec.


(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].

(* [comment removed for export] *)
Ltac reg_eq_ev := first [ reflexivity | (symmetry; apply Z_to_bv_bv_unsigned) | apply Z_to_bv_bv_unsigned ].
Ltac tree_eq_ev :=
  first [ reflexivity
        | lazymatch goal with
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; tree_eq_ev
          | |- Some _ = Some _ => f_equal; reg_eq_ev
          | |- _ => reg_eq_ev
          end ].
Ltac ms_eq_ev :=
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => unfold mkR; f_equal; [ tree_eq_ev | reflexivity .. ]
  end.
(* [comment removed for export] *)
Ltac jump L := eapply evt_eq; [ | eapply L ]; first [ ms_eq_ev | finL ].


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
(* [comment removed for export] *)
Ltac decide_test1_f t := replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia); cbn [andb orb negb].
Ltac decide_test1_t t := replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia); cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
  Hypothesis FRM : frm0 fc.
  Hypothesis MI : mem_inv img_segs m1.
  Hypothesis FR : rw_cells img_segs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis STK : stk img_segs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono img_segs m m1.
  Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

  Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).
  (* [comment removed for export] *)
  Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fcx None m1 (seg_rom img_segs)).


  (* [comment removed for export] *)
  Lemma add_LM1 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_M1 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 128) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 HR. subst r. unfold add_M1. pose_word_ranges.
    zstep. zstep. if_cases Ke; zify_cond Ke; [ decide_test1_t (bAbsHi =? aAbsHi)%Z | decide_test1_f (bAbsHi =? aAbsHi)%Z ].
    - (* [comment removed for export] *)
      do 3 zstep. if_cases Ks; zify_cond Ks; [ decide_test1_t ((bv_unsigned wa0) <? (bv_unsigned wb0))%Z | decide_test1_f ((bv_unsigned wa0) <? (bv_unsigned wb0))%Z ].
      + (* [comment removed for export] *)
        unfold add_M2. unfold_sfw.
        do 8 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
        zstep. if_cases Ka; zify_cond Ka; [ decide_test1_t (aExp =? 0%Z)%Z | decide_test1_f (aExp =? 0%Z)%Z ].
        * jump add_L184.
        * jump add_L0d4.
      + unfold add_M2. unfold_sfw.
        do 7 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
        zstep. if_cases Ka; zify_cond Ka; [ decide_test1_f (aExp =? 0%Z)%Z | decide_test1_t (aExp =? 0%Z)%Z ].
        * jump add_L0d4.
        * jump add_L184.
    - do 3 zstep. if_cases Ks; zify_cond Ks; [ decide_test1_f (aAbsHi <? bAbsHi)%Z | decide_test1_t (aAbsHi <? bAbsHi)%Z ].
      + (* [comment removed for export] *)
        unfold add_M2. unfold_sfw.
        do 7 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
        zstep. if_cases Ka; zify_cond Ka; [ decide_test1_f (aExp =? 0%Z)%Z | decide_test1_t (aExp =? 0%Z)%Z ].
        * jump add_L0d4.
        * jump add_L184.
      + unfold add_M2. unfold_sfw.
        do 8 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
        zstep. if_cases Ka; zify_cond Ka; [ decide_test1_t (aExp =? 0%Z)%Z | decide_test1_f (aExp =? 0%Z)%Z ].
        * jump add_L184.
        * jump add_L0d4.
  Qed.


  (* [comment removed for export] *)
  Lemma add_L108 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_S3 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 240) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_S3. unfold_sfw. rewrite ?b2z_Zb2z.
    do 4 zstep. zstep. if_cases Ki; zify_cond Ki; [ decide_test1_f ((Z.lor (bv_unsigned wa0) (Z.lxor aAbsHi 9223090561878065152)) =? 0%Z)%Z | decide_test1_t ((Z.lor (bv_unsigned wa0) (Z.lxor aAbsHi 9223090561878065152)) =? 0%Z)%Z ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases Kb; zify_cond Kb; [ decide_test1_t ((Z.lor (bv_unsigned wb0) (Z.lxor bAbsHi 9223090561878065152)) =? 0%Z)%Z | decide_test1_f ((Z.lor (bv_unsigned wb0) (Z.lxor bAbsHi 9223090561878065152)) =? 0%Z)%Z ].
      + (* [comment removed for export] *) jump add_Lret.
      + zstep. zstep. if_cases Kz; zify_cond Kz; [ decide_test1_t ((Z.lor (bv_unsigned wa0) aAbsHi) =? 0%Z)%Z | decide_test1_f ((Z.lor (bv_unsigned wa0) aAbsHi) =? 0%Z)%Z ].
        * (* [comment removed for export] *)
          zstep. zstep. if_cases Kbz; zify_cond Kbz; [ decide_test1_f ((Z.lor (bv_unsigned wb0) bAbsHi) =? 0%Z)%Z | decide_test1_t ((Z.lor (bv_unsigned wb0) bAbsHi) =? 0%Z)%Z ].
          -- (* [comment removed for export] *) jump add_Lret.
          -- (* [comment removed for export] *) do 3 zstep. jump add_Lret.
        * zstep. zstep. if_cases Kbz; zify_cond Kbz; [ decide_test1_f ((Z.lor (bv_unsigned wb0) bAbsHi) =? 0%Z)%Z | decide_test1_t ((Z.lor (bv_unsigned wb0) bAbsHi) =? 0%Z)%Z ].
          -- (* [comment removed for export] *) eapply add_LM1; finL.
          -- (* [comment removed for export] *) do 3 zstep. jump add_Lret.
    - (* [comment removed for export] *)
      do 6 zstep. name_reg 9%Z xw.
      zstep. rewrite (ltb1_eqb0 xw) by zrange_nonneg. zstep. if_cases Kx; zify_cond Kx; [ decide_test1_f (xw =? 0%Z)%Z | decide_test1_t (xw =? 0%Z)%Z ].
      + (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (Z.b2z false + -1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
        change (Z.land (Z.b2z false - 1) 18446744073709551615) with 18446744073709551615%Z.
        do 3 zstep. jump add_Lret.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. replace (Z_to_bv 64 (Z.b2z true + -1)) with (Z_to_bv 64 0) by (apply Z_to_bv_eqm; reflexivity).
        change (Z.land (Z.b2z true - 1) 18446744073709551615) with 0%Z.
        do 3 zstep. jump add_Lret.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L0f4 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_S2 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 220) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_S2. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb; [ decide_test1_t (bAbsHi =? 9223090561878065152%Z)%Z | decide_test1_f (bAbsHi =? 9223090561878065152%Z)%Z ].
    - (* [comment removed for export] *)
      zstep. rewrite (ltb1_eqb0 (bv_unsigned wb0)) by lia. zstep. if_cases Kbl; zify_cond Kbl; [ decide_test1_t ((bv_unsigned wb0) =? 0%Z)%Z | decide_test1_f ((bv_unsigned wb0) =? 0%Z)%Z ].
      + (* [comment removed for export] *) eapply add_L108; finL.
      + (* [comment removed for export] *) do 4 zstep. jump add_Lret.
    - zstep. zstep. if_cases Kbl; zify_cond Kbl; [ decide_test1_f (bAbsHi <? 9223090561878065152%Z)%Z | decide_test1_t (bAbsHi <? 9223090561878065152%Z)%Z ].
      + (* [comment removed for export] *) do 4 zstep. jump add_Lret.
      + eapply add_L108; finL.
  Qed.
  (* [comment removed for export] *)
  Lemma add_LS : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_S (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 200) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 HR. subst r. pose_word_ranges.
    unfold add_S. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. zstep. zstep. if_cases Ka; zify_cond Ka; [ decide_test1_t (aAbsHi =? 9223090561878065152%Z)%Z | decide_test1_f (aAbsHi =? 9223090561878065152%Z)%Z ].
    - (* [comment removed for export] *)
      zstep. rewrite (ltb1_eqb0 (bv_unsigned wa0)) by lia. zstep. if_cases Kal; zify_cond Kal; [ decide_test1_t ((bv_unsigned wa0) =? 0%Z)%Z | decide_test1_f ((bv_unsigned wa0) =? 0%Z)%Z ].
      + (* [comment removed for export] *) eapply add_L0f4; finL.
      + (* [comment removed for export] *) do 5 zstep. jump add_Lret.
    - zstep. zstep. if_cases Kal; zify_cond Kal; [ decide_test1_f (aAbsHi <? 9223090561878065152%Z)%Z | decide_test1_t (aAbsHi <? 9223090561878065152%Z)%Z ].
      + (* [comment removed for export] *) do 5 zstep. jump add_Lret.
      + eapply add_L0f4; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L074 : forall x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_top2 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 92) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 (Z_to_bv 64 9223653511831486464) (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_top2. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. model_reg 12%Z tb (Z.land (bAbsHi + 9223653511831486464) W64).
    zstep. zstep. zstep. if_cases Kt; zify_cond Kt; [ decide_test1_t (tb =? 9223653511831486464%Z)%Z | decide_test1_f (tb =? 9223653511831486464%Z)%Z ].
    - (* [comment removed for export] *)
      zstep. zstep. if_cases Kl; zify_cond Kl; decide_test1_try ((bv_unsigned wb0) =? 0%Z)%Z; decide_test1_try (0%Z <? (bv_unsigned wb0))%Z.
      + (* [comment removed for export] *) eapply add_LS; finL.
      + eapply add_LM1; finL.
    - zstep. zstep. if_cases Kl; zify_cond Kl; [ decide_test1_t (9223653511831486464%Z <? tb)%Z | decide_test1_f (9223653511831486464%Z <? tb)%Z ].
      + eapply add_LM1; finL.
      + zstep. eapply add_LS; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L034 : forall x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (r : Z),
    r = add_top (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) ->
    evt img_segs (POST r) (ST (sym 0x1bc80 + 28) fc ra x5 x6 x7 x8 x9 wa0 wa1 wb0 wb1 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM ImgHyps.
    intros until r. intros HR. subst r. pose_word_ranges. unfold add_top. unfold_sfw. rewrite ?b2z_Zb2z.
    do 5 zstep. name_reg 13%Z aAbsHi.
    zstep. zstep. zstep. if_cases K0; zify_cond K0; [ decide_test1_t (aAbsHi =? 0%Z)%Z | decide_test1_f (aAbsHi =? 0%Z)%Z ].
    - (* [comment removed for export] *)
      zstep. rewrite (ltb1_eqb0 (bv_unsigned wa0)) by lia. zstep. name_reg 14%Z bAbsHi.
      zstep. if_cases Kl; zify_cond Kl; [ decide_test1_t ((bv_unsigned wa0) =? 0%Z)%Z | decide_test1_f ((bv_unsigned wa0) =? 0%Z)%Z ].
      + (* [comment removed for export] *) eapply add_LS; finL.
      + eapply add_L074; finL.
    - zstep. zstep. zstep. name_reg 14%Z bAbsHi.
      zstep. if_cases Kl; zify_cond Kl; [ decide_test1_f ((Z.land (aAbsHi + 9223653511831486464) 18446744073709551615) <? 9223653511831486464%Z)%Z | decide_test1_t ((Z.land (aAbsHi + 9223653511831486464) 18446744073709551615) <? 9223653511831486464%Z)%Z ].
      + eapply add_L074; finL.
      + zstep. eapply add_LS; finL.
  Qed.
End Proofs.

Lemma addtf3_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk img_segs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  frm0 fc ->
  evt img_segs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
               (f128_add (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bc80)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros ST MI FRM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  assert (SPLO : (48 <= bv_unsigned sp)%Z) by (destruct ST as [? _]; lia).
  pose_word_ranges.
  rewrite f128_add_split by lia.
  carve_frame 48%nat ST.
  do 7 zstep.
  eapply add_L034; try eassumption; reflexivity.
Qed.

(* [comment removed for export] *)
Definition addtf3_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk img_segs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  frm0 fc ->
  evt img_segs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
               (f128_add (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bc80)) fc None m (seg_rom img_segs)).
Lemma addtf3_spec_c_ok : addtf3_spec_c.
Proof. exact addtf3_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].
Ltac reg_eq_ev := first [ reflexivity | (symmetry; apply Z_to_bv_bv_unsigned) | apply Z_to_bv_bv_unsigned ].
Ltac tree_eq_ev :=
  first [ reflexivity
        | lazymatch goal with
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; tree_eq_ev
          | |- Some _ = Some _ => f_equal; reg_eq_ev
          | |- _ => reg_eq_ev
          end ].
Ltac ms_eq_ev :=
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => unfold mkR; f_equal; [ tree_eq_ev | reflexivity .. ]
  end.
Ltac jump L := eapply evt_eq; [ | eapply L ]; first [ ms_eq_ev | finL ].
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_f t := replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia); cbn [andb orb negb].
Ltac decide_test1_t t := replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia); cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

(* [comment removed for export] *)
Existing Class addtf3_spec_c.
End G_addtf3_E.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.P Require Import SFW1_lemmas SFW_add_split.
Import G_fe_getround.
Import G_addtf3_A.
Import G_addtf3_E.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition subtf3_prog (B B_addtf3 : Z) : RStep.ptree :=
  PLeaf
    (PJ_OpImm_ALU_ADD_nnn 0 14 0 4095 4
    (PJ_ShiftImm_ALU_SLL_nnn 4 14 14 63 4
    (PJ_Op_ALU_XOR_nnn 8 13 13 14 4
    (PJ_Jal_nt 12 0 (jimm21 (B_addtf3 - (B + 12))) 4 nil)))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_subtf3 (IMG : RImg) := subtf3_prog (sym 0x1bc70) (sym 0x1bc80).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_subtf3 : CodeAtT img_segs (sym 0x1bc70) (PROGAT_CODE_subtf3 IMG)}.
  Context {RB_subtf3 : RelCode (sym 0x1bc70) 16}.
  Context {RN_B_addtf3_1bc70 : RelNear (sym 0x1bc70) (sym 0x1bc80)}.
  Context {SPEC_addtf3_spec : addtf3_spec_c}.
  Collection ImgHyps := IMG CODE_subtf3 RB_subtf3 RN_B_addtf3_1bc70 SPEC_addtf3_spec.



Definition subtf3_entry := (sym 0x1bc70)%Z.

Lemma land_shl64_low : forall h l, (0 <= l < 2^64)%Z -> Z.land (Z.shiftl h 64) l = 0%Z.
Proof.
  intros h l Hl. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - replace (Z.testbit l i) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec l 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma f128_sub_split : forall aLo aHi bLo bHi,
  (0 <= bLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
  f128_sub (aLo + 2^64 * aHi) (bLo + 2^64 * bHi) = f128_add (aLo + 2^64 * aHi) (bLo + 2^64 * Z.lxor bHi 9223372036854775808).
Proof.
  intros aLo aHi bLo bHi Hl Hh. unfold f128_sub. rewrite lo64_words, hi64_words by lia.
  unfold mk128, SIGN64. rewrite Z.lor_comm, lor_disjoint_add.
  - rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
  - rewrite Z.land_comm. apply land_shl64_low. lia.
Qed.

Lemma subtf3_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk img_segs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  frm0 fc ->
  evt img_segs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
               (f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bc70)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros ST MI FRM. pose_word_ranges.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  rewrite f128_sub_split by lia.
  do 4 zstep.
  eapply evt_mono; [ eapply SPEC_addtf3_spec; eassumption | ].
  intros ms' PO. unfold addtf3_post in *.
  rewrite (inr64_unsigned_lit (Z.lxor (bv_unsigned a3) 9223372036854775808)) in PO by zrange.
  exact PO.
Qed.

(* [comment removed for export] *)
Definition subtf3_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk img_segs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  frm0 fc ->
  evt img_segs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
               (f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bc70)) fc None m (seg_rom img_segs)).
Lemma subtf3_contract_ok : subtf3_contract.
Proof. exact subtf3_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class subtf3_contract.
