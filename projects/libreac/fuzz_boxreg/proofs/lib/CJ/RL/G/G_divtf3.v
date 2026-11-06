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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.G.ProgAt3.Prog_divtf3. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.G.ProgAt3.ProgAt. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_divtf3 : CodeAtT img_segs (sym 0x1c6b0) (divtf3_prog_at IMG)}.
  Context {RB_divtf3 : RelCode (sym 0x1c6b0) 2308}.
  Collection ImgHyps := IMG CODE_divtf3 RB_divtf3.



Definition divtf3_entry := (sym 0x1c6b0)%Z.

(* [comment removed for export] *)
Definition divtf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - 112) (bv_unsigned sp).

Definition divtf3_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte),
    stk img_segs m (bv_unsigned sp - 112) (bv_unsigned sp) ->
    mem_inv img_segs m ->
    (4096 <= bv_unsigned sp)%Z ->
    evt img_segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (f128_div (mk128 (bv_unsigned a1) (bv_unsigned a0)) (mk128 (bv_unsigned a3) (bv_unsigned a2))) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x1c6b0)) fc None m (seg_rom img_segs)).

End Img.
